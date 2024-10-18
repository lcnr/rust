use std::fmt::{Debug, Display};

use rustc_ast_ir::visit::VisitorResult;

use crate::fold::{FallibleTypeFolder, TypeFoldable, TypeFolder, TypeSuperFoldable};
use crate::inherent::*;
use crate::relate::Relate;
use crate::solve::{Goal, NoSolution, SolverMode};
use crate::visit::{TypeVisitable, TypeVisitableExt, TypeVisitor};
use crate::{self as ty, InferConst, InferTy, Interner};

pub trait InferCtxtLike: Sized {
    type Interner: Interner;
    fn cx(&self) -> Self::Interner;

    fn solver_mode(&self) -> SolverMode;

    fn universe(&self) -> ty::UniverseIndex;
    fn create_next_universe(&self) -> ty::UniverseIndex;

    fn universe_of_ty(&self, ty: ty::TyVid) -> Option<ty::UniverseIndex>;
    fn universe_of_lt(&self, lt: ty::RegionVid) -> Option<ty::UniverseIndex>;
    fn universe_of_ct(&self, ct: ty::ConstVid) -> Option<ty::UniverseIndex>;

    fn root_ty_var(&self, var: ty::TyVid) -> ty::TyVid;
    fn root_const_var(&self, var: ty::ConstVid) -> ty::ConstVid;

    fn opportunistic_resolve_ty_var(&self, vid: ty::TyVid) -> <Self::Interner as Interner>::Ty;
    fn opportunistic_resolve_int_var(&self, vid: ty::IntVid) -> <Self::Interner as Interner>::Ty;
    fn opportunistic_resolve_float_var(
        &self,
        vid: ty::FloatVid,
    ) -> <Self::Interner as Interner>::Ty;
    fn opportunistic_resolve_ct_var(
        &self,
        vid: ty::ConstVid,
    ) -> <Self::Interner as Interner>::Const;
    fn opportunistic_resolve_effect_var(
        &self,
        vid: ty::EffectVid,
    ) -> <Self::Interner as Interner>::Const;
    fn opportunistic_resolve_lt_var(
        &self,
        vid: ty::RegionVid,
    ) -> <Self::Interner as Interner>::Region;

    fn defining_opaque_types(&self) -> <Self::Interner as Interner>::DefiningOpaqueTypes;

    fn next_region_infer(&self) -> <Self::Interner as Interner>::Region;
    fn next_ty_infer(&self) -> <Self::Interner as Interner>::Ty;
    fn next_int_infer(&self) -> <Self::Interner as Interner>::Ty;
    fn next_float_infer(&self) -> <Self::Interner as Interner>::Ty;
    fn next_const_infer(&self) -> <Self::Interner as Interner>::Const;
    fn next_effect_infer(&self) -> <Self::Interner as Interner>::Const;
    fn fresh_args_for_item(
        &self,
        def_id: <Self::Interner as Interner>::DefId,
    ) -> <Self::Interner as Interner>::GenericArgs;

    fn instantiate_binder_with_infer<T: TypeFoldable<Self::Interner> + Copy>(
        &self,
        value: ty::Binder<Self::Interner, T>,
    ) -> T;

    fn enter_forall<T: TypeFoldable<Self::Interner> + Copy, U>(
        &self,
        value: ty::Binder<Self::Interner, T>,
        f: impl FnOnce(T) -> U,
    ) -> U;

    fn relate<T: Relate<Self::Interner>>(
        &self,
        param_env: <Self::Interner as Interner>::ParamEnv,
        lhs: T,
        variance: ty::Variance,
        rhs: T,
    ) -> Result<Vec<Goal<Self::Interner, <Self::Interner as Interner>::Predicate>>, NoSolution>;

    fn eq_structurally_relating_aliases<T: Relate<Self::Interner>>(
        &self,
        param_env: <Self::Interner as Interner>::ParamEnv,
        lhs: T,
        rhs: T,
    ) -> Result<Vec<Goal<Self::Interner, <Self::Interner as Interner>::Predicate>>, NoSolution>;

    fn shallow_resolve(
        &self,
        ty: <Self::Interner as Interner>::Ty,
    ) -> <Self::Interner as Interner>::Ty;

    fn resolve_vars_if_possible<T>(&self, value: T) -> T
    where
        T: TypeFoldable<Self::Interner>;

    fn probe<T>(&self, probe: impl FnOnce() -> T) -> T
    where
        T: TypeVisitable<Self::Interner>;

    fn sub_regions(
        &self,
        sub: <Self::Interner as Interner>::Region,
        sup: <Self::Interner as Interner>::Region,
    );

    fn register_ty_outlives(
        &self,
        ty: <Self::Interner as Interner>::Ty,
        r: <Self::Interner as Interner>::Region,
    );
}

/// A type which may contain inference variables which have been invalidated
/// when reverting a snapshot.
///
/// This type implements `TypeFoldable` without recursing into its contained
/// value and accessing the value must either fudge all inference variables
/// or be careful to not access any leaked inference variables.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WithLeakedVars<T> {
    value: T,
}

impl<T: Display> Display for WithLeakedVars<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.value.fmt(f)
    }
}

impl<T> WithLeakedVars<T> {
    pub fn new(value: T) -> WithLeakedVars<T> {
        WithLeakedVars { value }
    }

    /// Access the contained value without fudging the inference
    /// variables. As the contained inference variables may no longer
    /// be valid, you must not try to resolve these inference variables
    /// or get their metadata.
    pub fn into_leaked_value(self) -> T {
        self.value
    }

    pub fn leaked_value_ref(&self) -> &T {
        &self.value
    }

    /// Unlike `fudge_inference_if_ok` this does not track the metadata of the
    /// inference variables and replaces all inference variables with dummy vars.
    ///
    /// The fudged value may still contain invalid placeholders.
    pub fn get_fudged_value<I, Infcx>(self, infcx: &Infcx) -> T
    where
        I: Interner,
        Infcx: InferCtxtLike<Interner = I>,
        T: TypeFoldable<I>,
    {
        struct FudgeVars<'a, Infcx> {
            infcx: &'a Infcx,
        }

        impl<I: Interner, Infcx: InferCtxtLike<Interner = I>> TypeFolder<I> for FudgeVars<'_, Infcx> {
            fn cx(&self) -> I {
                self.infcx.cx()
            }

            fn fold_ty(&mut self, t: I::Ty) -> I::Ty {
                if let ty::Infer(infer_ty) = t.kind() {
                    match infer_ty {
                        InferTy::TyVar(_) => self.infcx.next_ty_infer(),
                        InferTy::IntVar(_) => self.infcx.next_int_infer(),
                        InferTy::FloatVar(_) => self.infcx.next_float_infer(),
                        InferTy::FreshTy(_) | InferTy::FreshIntTy(_) | InferTy::FreshFloatTy(_) => {
                            unreachable!("unexpected fresh infer var")
                        }
                    }
                } else if t.has_infer() {
                    t.super_fold_with(self)
                } else {
                    t
                }
            }

            fn fold_region(&mut self, r: I::Region) -> I::Region {
                if let ty::ReVar(_) = r.kind() { self.infcx.next_region_infer() } else { r }
            }

            fn fold_const(&mut self, c: I::Const) -> I::Const {
                if let ty::ConstKind::Infer(infer_ct) = c.kind() {
                    match infer_ct {
                        InferConst::Var(_) => self.infcx.next_const_infer(),
                        InferConst::EffectVar(_) => self.infcx.next_effect_infer(),
                        InferConst::Fresh(_) => {
                            unreachable!("unexpected fresh infer var")
                        }
                    }
                } else if c.has_infer() {
                    c.super_fold_with(self)
                } else {
                    c
                }
            }
        }

        self.value.fold_with(&mut FudgeVars { infcx })
    }
}

impl<I: Interner, T: Clone + Debug> TypeVisitable<I> for WithLeakedVars<T> {
    fn visit_with<V: TypeVisitor<I>>(&self, _: &mut V) -> V::Result {
        V::Result::output()
    }
}

impl<I: Interner, T: Clone + Debug> TypeFoldable<I> for WithLeakedVars<T> {
    fn try_fold_with<F: FallibleTypeFolder<I>>(self, _: &mut F) -> Result<Self, F::Error> {
        Ok(self)
    }
}
