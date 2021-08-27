#![allow(unused)]
use crate::astconv::{AstConv, SizedByDefault};
use crate::bounds::Bounds;
use crate::check::intrinsic::intrinsic_operation_unsafety;
use crate::constrained_generic_params as cgp;
use crate::errors;
use crate::middle::resolve_lifetime as rl;
use rustc_ast as ast;
use rustc_ast::Attribute;
use rustc_ast::{MetaItemKind, NestedMetaItem};
use rustc_attr::{list_contains_name, InlineAttr, InstructionSetAttr, OptimizeAttr};
use rustc_data_structures::captures::Captures;
use rustc_data_structures::fx::{FxHashMap, FxHashSet, FxIndexSet};
use rustc_errors::{struct_span_err, Applicability};
use rustc_hir as hir;
use rustc_hir::def::{CtorKind, DefKind, Res};
use rustc_hir::def_id::{DefId, LocalDefId, LOCAL_CRATE};
use rustc_hir::intravisit::{self, NestedVisitorMap, Visitor};
use rustc_hir::weak_lang_items;
use rustc_hir::{GenericParamKind, HirId, Node};
use rustc_middle::hir::map::Map;
use rustc_middle::middle::codegen_fn_attrs::{CodegenFnAttrFlags, CodegenFnAttrs};
use rustc_middle::mir::mono::Linkage;
use rustc_middle::ty::fold::TypeFoldable;
use rustc_middle::ty::query::Providers;
use rustc_middle::ty::subst::{InternalSubsts, SubstsRef};
use rustc_middle::ty::util::Discr;
use rustc_middle::ty::util::IntTypeExt;
use rustc_middle::ty::{self, AdtKind, Const, DefIdTree, ToPolyTraitRef, Ty, TyCtxt};
use rustc_middle::ty::{ReprOptions, ToPredicate, WithConstness};
use rustc_session::lint;
use rustc_session::parse::feature_err;
use rustc_span::symbol::{kw, sym, Ident, Symbol};
use rustc_span::{Span, DUMMY_SP};
use rustc_target::spec::{abi, SanitizerSet};
use rustc_trait_selection::traits::error_reporting::suggestions::NextTypeParamName;
use std::iter;

pub(super) fn generics_of_anon_const(
    tcx: TyCtxt<'tcx>,
    parent_def_id: LocalDefId,
    def_id: DefId,
) -> ty::Generics {
    let query_cycle = tcx.filter_anon_const_generics(parent_def_id);

    let generics = tcx.generics_of(parent_def_id);
    let parent_has_self = generics.has_self;
    let parent_count = generics.parent_count + generics.params.len();

    ty::Generics {
        parent: Some(parent_def_id.to_def_id()),
        parent_count,
        params: Vec::new(),
        param_def_id_to_index: FxHashMap::default(),
        has_self: parent_has_self,
        has_late_bound_regions: None,
    }
}

pub(super) fn filter_anon_const_generics<'tcx>(
    tcx: TyCtxt<'tcx>,
    parent_def_id: LocalDefId,
) -> ty::AnonConstGenerics<'tcx> {
    let _cycle_check = tcx.predicates_of(parent_def_id);
    ty::AnonConstGenerics { consts: FxHashMap::default() }
}

pub(super) fn default_anon_const_substs(tcx: TyCtxt<'_>, def_id: DefId) -> SubstsRef<'_> {
    let generics = tcx.generics_of(def_id);
    let substs = InternalSubsts::identity_for_item(tcx, def_id);

    // We only expect substs with the following type flags as default substs.
    //
    // Getting this wrong can lead to ICE and unsoundness, so we assert it here.
    for arg in substs.iter().flat_map(|s| s.walk(tcx)) {
        let allowed_flags = ty::TypeFlags::MAY_NEED_DEFAULT_CONST_SUBSTS
            | ty::TypeFlags::STILL_FURTHER_SPECIALIZABLE;
        assert!(!arg.has_type_flags(!allowed_flags));
    }
    substs
}
