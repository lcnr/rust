use crate::rustc_middle::ty::DefIdTree;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{self, Ty, TyCtxt};

pub fn provide(providers: &mut ty::query::Providers) {
    *providers = ty::query::Providers { assumed_wf_types, ..*providers };
}

fn assumed_wf_types<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> ty::Binder<'tcx, &'tcx ty::List<Ty<'tcx>>> {
    match tcx.def_kind(def_id) {
        DefKind::Fn => tcx.fn_sig(def_id).inputs_and_output(),
        DefKind::AssocFn => tcx.fn_sig(def_id).map_bound(|fn_sig| {
            let mut assumed_wf_types: Vec<_> = tcx
                .assumed_wf_types(tcx.parent(def_id))
                .no_bound_vars()
                .expect("bound vars for impl")
                .as_slice()
                .into();
            assumed_wf_types.extend(fn_sig.inputs_and_output);
            tcx.intern_type_list(&assumed_wf_types)
        }),
        DefKind::Impl => ty::Binder::dummy(match tcx.impl_trait_ref(def_id) {
            Some(trait_ref) => {
                let types: Vec<_> = trait_ref.substs.types().collect();
                tcx.intern_type_list(&types)
            }
            // Only the impl self type
            None => tcx.intern_type_list(&[tcx.type_of(def_id)]),
        }),
        DefKind::AssocConst | DefKind::AssocTy => tcx.assumed_wf_types(tcx.parent(def_id)),
        DefKind::Mod
        | DefKind::Struct
        | DefKind::Union
        | DefKind::Enum
        | DefKind::Variant
        | DefKind::Trait
        | DefKind::TyAlias
        | DefKind::ForeignTy
        | DefKind::TraitAlias
        | DefKind::TyParam
        | DefKind::Const
        | DefKind::ConstParam
        | DefKind::Static(_)
        | DefKind::Ctor(_, _)
        | DefKind::Macro(_)
        | DefKind::ExternCrate
        | DefKind::Use
        | DefKind::ForeignMod
        | DefKind::AnonConst
        | DefKind::InlineConst
        | DefKind::OpaqueTy
        | DefKind::Field
        | DefKind::LifetimeParam
        | DefKind::GlobalAsm
        | DefKind::Closure
        | DefKind::Generator => ty::Binder::dummy(ty::List::empty()),
    }
}
