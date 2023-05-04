use rustc_data_structures::fx::FxHashSet;
use rustc_hir::{def::DefKind, def_id::LocalDefId};
use rustc_middle::ty::util::IgnoreRegions;
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_middle::ty::{TypeSuperVisitable, TypeVisitable, TypeVisitor};
use rustc_type_ir::AliasKind;
use rustc_span::def_id::DefId;
use std::ops::ControlFlow;

struct OpaqueTypeCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    // FIXME: We only recurse into the first instance of
    // an opaque even if a later instance uses different substs.
    seen: FxHashSet<DefId>,
    opaques: Vec<Ty<'tcx>>,
}

impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for OpaqueTypeCollector<'tcx> {
    fn visit_ty(&mut self, t: Ty<'tcx>) -> ControlFlow<!> {
        match t.kind() {
            ty::Alias(AliasKind::Opaque, alias_ty) => {
                if self.tcx.uses_unique_generic_params(alias_ty.substs, IgnoreRegions::No).is_ok() {
                    if !self.opaques.contains(&t) {
                        self.opaques.push(t);
                    }
                } else {
                    warn!(?t, "opaque types with non-unique params in sig: {t:?}");
                    t.super_visit_with(self)?;
                }

                if self.seen.insert(alias_ty.def_id) {
                    for pred in self.tcx.explicit_item_bounds(alias_ty.def_id).subst_iter_copied(self.tcx, alias_ty.substs) {
                        pred.visit_with(self)?;
                    }
                }

                ControlFlow::Continue(())
            }
            _ => t.super_visit_with(self),
        }
    }
}

fn opaque_types_defined_by<'tcx>(
    tcx: TyCtxt<'tcx>,
    item: LocalDefId,
) -> ty::EarlyBinder<&'tcx ty::List<Ty<'tcx>>> {
    // FIXME(type_alias_impl_trait): This is definitely still wrong except for RPIT.
    match tcx.def_kind(item) {
        DefKind::Fn | DefKind::AssocFn => {
            let sig = tcx.fn_sig(item).subst_identity();
            let mut collector = OpaqueTypeCollector { tcx, seen: Default::default(), opaques: Vec::new() };
            sig.visit_with(&mut collector);

            let defined_opaques = tcx.mk_type_list(&collector.opaques);
            ty::EarlyBinder(defined_opaques)
        }
        DefKind::Mod
        | DefKind::Struct
        | DefKind::Union
        | DefKind::Enum
        | DefKind::Variant
        | DefKind::Trait
        | DefKind::TyAlias
        | DefKind::ForeignTy
        | DefKind::TraitAlias
        | DefKind::AssocTy
        | DefKind::TyParam
        | DefKind::Const
        | DefKind::ConstParam
        | DefKind::Static(_)
        | DefKind::Ctor(_, _)
        | DefKind::AssocConst
        | DefKind::Macro(_)
        | DefKind::ExternCrate
        | DefKind::Use
        | DefKind::ForeignMod
        | DefKind::AnonConst
        | DefKind::InlineConst
        | DefKind::OpaqueTy
        | DefKind::ImplTraitPlaceholder
        | DefKind::Field
        | DefKind::LifetimeParam
        | DefKind::GlobalAsm
        | DefKind::Impl { .. }
        | DefKind::Closure
        | DefKind::Generator => ty::EarlyBinder(ty::List::empty()),
    }
}

pub(super) fn provide(providers: &mut ty::query::Providers) {
    *providers = ty::query::Providers { opaque_types_defined_by, ..*providers };
}
