//! A subset of the thir used for const evaluatability checking.
use crate::mir::interpret::ErrorHandled;
use crate::ty::{self, EarlyBinder, Ty, TyCtxt};
use crate::ty::{TypeFoldable, TypeFolder, TypeSuperFoldable, TypeVisitable};
use rustc_errors::ErrorGuaranteed;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;

#[derive(Hash, Debug, Clone, Copy, Ord, PartialOrd, PartialEq, Eq)]
#[derive(TyDecodable, TyEncodable, HashStable, TypeVisitable, TypeFoldable)]
pub enum CastKind {
    /// thir::ExprKind::As
    As,
    /// thir::ExprKind::Use
    Use,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, HashStable, TyEncodable, TyDecodable)]
pub enum NotConstEvaluatable {
    Error(ErrorGuaranteed),
    MentionsInfer,
    MentionsParam,
}

impl From<ErrorGuaranteed> for NotConstEvaluatable {
    fn from(e: ErrorGuaranteed) -> NotConstEvaluatable {
        NotConstEvaluatable::Error(e)
    }
}

TrivialTypeTraversalAndLiftImpls! {
    NotConstEvaluatable,
}

pub type BoundAbstractConst<'tcx> = Result<Option<EarlyBinder<ty::Const<'tcx>>>, ErrorGuaranteed>;

impl<'tcx> TyCtxt<'tcx> {
    /// Returns a const with substs applied by
    pub fn bound_abstract_const(
        self,
        def: ty::WithOptConstParam<DefId>,
    ) -> BoundAbstractConst<'tcx> {
        if let Some((did, param_did)) = def.as_const_arg() {
            self.thir_abstract_const_of_const_arg((did, param_did))
        } else {
            self.thir_abstract_const(def.did)
        }
        .map(|ac| ac.map(|ac| EarlyBinder(ac)))
    }

    pub fn expand_abstract_consts<T: TypeFoldable<'tcx>>(self, value: T) -> T {
        struct Expander<'tcx> {
            tcx: TyCtxt<'tcx>,
        }

        impl<'tcx> TypeFolder<'tcx> for Expander<'tcx> {
            fn tcx(&self) -> TyCtxt<'tcx> {
                self.tcx
            }
            fn fold_ty(&mut self, ty: Ty<'tcx>) -> Ty<'tcx> {
                if ty.has_type_flags(ty::TypeFlags::HAS_CT_PROJECTION) {
                    ty.super_fold_with(self)
                } else {
                    ty
                }
            }
            fn fold_const(&mut self, ct: ty::Const<'tcx>) -> ty::Const<'tcx> {
                let tcx = self.tcx;
                let ct = match ct.kind() {
                    ty::ConstKind::Unevaluated(uv) => match tcx.bound_abstract_const(uv.def) {
                        Ok(Some(ac)) => ac.subst(tcx, uv.substs),
                        Ok(None) if tcx.def_kind(uv.def.did) == DefKind::AnonConst => {
                            let substs = ty::InternalSubsts::identity_for_item(tcx, uv.def.did);
                            let eval_result = self.tcx.const_eval_resolve_for_typeck(
                                tcx.param_env(uv.def.did),
                                ty::UnevaluatedConst { def: uv.def, substs },
                                None,
                            );
                            match eval_result {
                                Ok(Some(value)) => ty::Const::from_value(tcx, value, ct.ty()),
                                Ok(None) => bug!(
                                    "FIXME(adt_const_params): deal with non-valtree consts for {uv:?}"
                                ),
                                Err(ErrorHandled::TooGeneric) => tcx.const_error_with_message(
                                    ct.ty(),
                                    tcx.def_span(uv.def.did),
                                    "Missing value for constant, but no error reported?",
                                ),
                                Err(ErrorHandled::Linted | ErrorHandled::Reported(..)) => tcx
                                    .const_error_with_message(
                                        ct.ty(),
                                        tcx.def_span(uv.def.did),
                                        "failed to evaluate concrete constant",
                                    ),
                            }
                        }
                        Ok(None) => ct,
                        Err(_err_guaranteed) => tcx.const_error(ct.ty()),
                    },
                    _ => ct,
                };
                ct.super_fold_with(self)
            }
        }

        value.fold_with(&mut Expander { tcx: self })
    }
}
