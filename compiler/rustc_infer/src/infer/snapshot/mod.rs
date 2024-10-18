use std::fmt::Debug;

use rustc_data_structures::undo_log::UndoLogs;
use rustc_middle::ty::{self, Ty, TyCtxt, TypeVisitable, TypeVisitor};
use rustc_type_ir::visit::{TypeSuperVisitable, TypeVisitableExt};
use tracing::{debug, instrument};

use super::region_constraints::RegionSnapshot;
use super::InferCtxt;

mod fudge;
pub(crate) mod undo_log;

use undo_log::{Snapshot, UndoLog};

#[must_use = "once you start a snapshot, you should always consume it"]
pub struct CombinedSnapshot<'tcx> {
    pub(super) undo_snapshot: Snapshot<'tcx>,
    region_constraints_snapshot: RegionSnapshot,
    universe: ty::UniverseIndex,
}

struct VariableLengths {
    type_var_len: usize,
    const_var_len: usize,
    int_var_len: usize,
    float_var_len: usize,
    region_constraints_len: usize,
}

impl<'tcx> InferCtxt<'tcx> {
    pub fn in_snapshot(&self) -> bool {
        UndoLogs::<UndoLog<'tcx>>::in_snapshot(&self.inner.borrow_mut().undo_log)
    }

    pub fn num_open_snapshots(&self) -> usize {
        UndoLogs::<UndoLog<'tcx>>::num_open_snapshots(&self.inner.borrow_mut().undo_log)
    }

    fn variable_lengths(&self) -> VariableLengths {
        let mut inner = self.inner.borrow_mut();
        VariableLengths {
            type_var_len: inner.type_variables().num_vars(),
            const_var_len: inner.const_unification_table().len(),
            int_var_len: inner.int_unification_table().len(),
            float_var_len: inner.float_unification_table().len(),
            region_constraints_len: inner.unwrap_region_constraints().num_region_vars(),
        }
    }

    fn start_snapshot(&self) -> CombinedSnapshot<'tcx> {
        debug!("start_snapshot()");

        let mut inner = self.inner.borrow_mut();

        CombinedSnapshot {
            undo_snapshot: inner.undo_log.start_snapshot(),
            region_constraints_snapshot: inner.unwrap_region_constraints().start_snapshot(),
            universe: self.universe(),
        }
    }

    #[instrument(skip(self, snapshot), level = "debug")]
    fn rollback_to(&self, snapshot: CombinedSnapshot<'tcx>) {
        let CombinedSnapshot { undo_snapshot, region_constraints_snapshot, universe } = snapshot;

        self.universe.set(universe);

        let mut inner = self.inner.borrow_mut();
        inner.rollback_to(undo_snapshot);
        inner.unwrap_region_constraints().rollback_to(region_constraints_snapshot);
    }

    #[instrument(skip(self, snapshot), level = "debug")]
    fn commit_from(&self, snapshot: CombinedSnapshot<'tcx>) {
        let CombinedSnapshot { undo_snapshot, region_constraints_snapshot: _, universe: _ } =
            snapshot;

        self.inner.borrow_mut().commit(undo_snapshot);
    }

    /// Execute `f` and commit the bindings if closure `f` returns `Ok(_)`.
    #[instrument(skip(self, f), level = "debug")]
    pub fn commit_if_ok<T, E, F>(&self, f: F) -> Result<T, E>
    where
        F: FnOnce(&CombinedSnapshot<'tcx>) -> Result<T, E>,
        E: TypeVisitable<TyCtxt<'tcx>>,
    {
        let snapshot = self.start_snapshot();
        let variable_lengths = cfg!(debug_assertions).then(|| self.variable_lengths());
        let r = f(&snapshot);
        debug!("commit_if_ok() -- r.is_ok() = {}", r.is_ok());
        match r {
            Ok(ok) => {
                self.commit_from(snapshot);
                Ok(ok)
            }
            Err(err) => {
                if let Some(variable_lengths) = variable_lengths {
                    assert_no_leaked_vars(variable_lengths, &err);
                }
                self.rollback_to(snapshot);
                Err(err)
            }
        }
    }

    /// Execute `f` then unroll any bindings it creates.
    #[instrument(skip(self, f), level = "debug")]
    pub fn probe<R, F>(&self, f: F) -> R
    where
        F: FnOnce(&CombinedSnapshot<'tcx>) -> R,
        R: TypeVisitable<TyCtxt<'tcx>>,
    {
        let snapshot = self.start_snapshot();
        let variable_lengths = cfg!(debug_assertions).then(|| self.variable_lengths());
        let r = f(&snapshot);
        if let Some(variable_lengths) = variable_lengths {
            assert_no_leaked_vars(variable_lengths, &r);
        }
        self.rollback_to(snapshot);
        r
    }

    /// Scan the constraints produced since `snapshot` and check whether
    /// we added any region constraints.
    pub fn region_constraints_added_in_snapshot(&self, snapshot: &CombinedSnapshot<'tcx>) -> bool {
        self.inner
            .borrow_mut()
            .unwrap_region_constraints()
            .region_constraints_added_in_snapshot(&snapshot.undo_snapshot)
    }

    pub fn opaque_types_added_in_snapshot(&self, snapshot: &CombinedSnapshot<'tcx>) -> bool {
        self.inner.borrow().undo_log.opaque_types_in_snapshot(&snapshot.undo_snapshot)
    }
}

fn assert_no_leaked_vars<'tcx, T: TypeVisitable<TyCtxt<'tcx>>>(
    variable_lengths: VariableLengths,
    value: &T,
) {
    struct NoLeakedVars {
        variable_lengths: VariableLengths,
    }

    impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for NoLeakedVars {
        fn visit_ty(&mut self, t: Ty<'tcx>) {
            if let ty::Infer(infer_ty) = t.kind() {
                match infer_ty {
                    ty::TyVar(ty_vid) => {
                        assert!(ty_vid.index() < self.variable_lengths.type_var_len)
                    }
                    ty::IntVar(int_vid) => {
                        assert!(int_vid.index() < self.variable_lengths.int_var_len)
                    }
                    ty::FloatVar(float_vid) => {
                        assert!(float_vid.index() < self.variable_lengths.float_var_len)
                    }
                    ty::FreshTy(_) | ty::FreshIntTy(_) | ty::FreshFloatTy(_) => {
                        unreachable!("unexpected fresh infer var");
                    }
                }
            } else if t.has_infer() {
                t.super_visit_with(self)
            }
        }

        fn visit_region(&mut self, r: ty::Region<'tcx>) {
            if let ty::ReVar(re_vid) = r.kind() {
                assert!(re_vid.index() < self.variable_lengths.region_constraints_len);
            }
        }

        fn visit_const(&mut self, c: ty::Const<'tcx>) {
            if let ty::ConstKind::Infer(infer_ct) = c.kind() {
                match infer_ct {
                    ty::InferConst::Var(const_vid) => {
                        assert!(const_vid.index() < self.variable_lengths.const_var_len)
                    }
                    // FIXME(effects): We do not fudge effect variables.
                    ty::InferConst::EffectVar(_) => {}
                    ty::InferConst::Fresh(_) => {
                        unreachable!("unexpected fresh infer var");
                    }
                }
            } else if c.has_infer() {
                c.super_visit_with(self)
            }
        }
    }

    struct OnDrop<'a, T: Debug>(&'a T);
    impl<'a, T: Debug> Drop for OnDrop<'a, T> {
        fn drop(&mut self) {
            println!("{:?}", self.0)
        }
    }

    let guar = OnDrop(value);
    value.visit_with(&mut NoLeakedVars { variable_lengths });
    std::mem::forget(guar);
}
