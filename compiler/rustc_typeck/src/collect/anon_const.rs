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
use rustc_data_structures::fx::{FxHashMap, FxHashSet, FxIndexMap, FxIndexSet};
use rustc_errors::{struct_span_err, Applicability};
use rustc_hir as hir;
use rustc_hir::def::{CtorKind, DefKind, Res};
use rustc_hir::def_id::{DefId, LocalDefId, LOCAL_CRATE};
use rustc_hir::intravisit::{self, NestedVisitorMap, Visitor};
use rustc_hir::weak_lang_items;
use rustc_hir::{GenericParamKind, HirId, Node};
use rustc_index::bit_set::BitSet;
use rustc_middle::hir::map::Map;
use rustc_middle::middle::codegen_fn_attrs::{CodegenFnAttrFlags, CodegenFnAttrs};
use rustc_middle::mir::mono::Linkage;
use rustc_middle::ty::fold::TypeFoldable;
use rustc_middle::ty::query::Providers;
use rustc_middle::ty::subst::{InternalSubsts, SubstsRef};
use rustc_middle::ty::util::Discr;
use rustc_middle::ty::util::IntTypeExt;
use rustc_middle::ty::TypeVisitor;
use rustc_middle::ty::{self, AdtKind, Const, DefIdTree, ToPolyTraitRef, Ty, TyCtxt};
use rustc_middle::ty::{ReprOptions, ToPredicate, WithConstness};
use rustc_session::lint;
use rustc_session::parse::feature_err;
use rustc_span::symbol::{kw, sym, Ident, Symbol};
use rustc_span::{Span, DUMMY_SP};
use rustc_target::spec::{abi, SanitizerSet};
use rustc_trait_selection::traits::error_reporting::suggestions::NextTypeParamName;
use std::iter;
use std::ops::ControlFlow;

pub(super) fn generics_of_anon_const(
    tcx: TyCtxt<'tcx>,
    parent_def_id: LocalDefId,
    def_id: LocalDefId,
) -> ty::Generics {
    let filter = &tcx.filter_anon_const_generics(parent_def_id).consts[&def_id];

    let params = anon_const_params(tcx, filter, parent_def_id.to_def_id());
    let param_def_id_to_index = params.iter().map(|param| (param.def_id, param.index)).collect();

    let parent = tcx.generics_of(parent_def_id);
    let parent_has_self = parent.has_self;

    ty::Generics {
        parent: None,
        parent_count: 0,
        params,
        param_def_id_to_index,
        has_self: parent_has_self && filter.contains(0),
        // FIXME(generic_const_exprs): Not yet sure how to deal with late bound regions
        // here, but this is probably fine.
        has_late_bound_regions: parent.has_late_bound_regions,
    }
}

fn anon_const_params<'tcx>(
    tcx: TyCtxt<'tcx>,
    filter: &BitSet<u32>,
    parent_def_id: DefId,
) -> Vec<ty::GenericParamDef> {
    let generics = tcx.generics_of(parent_def_id);
    let mut params = if let Some(parent) = generics.parent {
        anon_const_params(tcx, filter, parent)
    } else {
        Vec::new()
    };

    for param in &generics.params {
        if filter.contains(param.index) {
            let index = params.len() as u32;
            params.push(ty::GenericParamDef {
                name: param.name,
                def_id: param.def_id,
                index,
                pure_wrt_drop: param.pure_wrt_drop,
                kind: param.kind.clone(),
            });
        }
    }

    params
}

pub(super) fn default_anon_const_substs(tcx: TyCtxt<'_>, def_id: DefId) -> SubstsRef<'_> {
    let generics = tcx.generics_of(def_id);
    let substs = InternalSubsts::identity_for_item(tcx, def_id);
    // We only expect substs with the following type flags as default substs.
    //
    // Getting this wrong can lead to ICE and unsoundness, so we assert it here.
    for arg in substs.iter() {
        let allowed_flags = ty::TypeFlags::MAY_NEED_DEFAULT_CONST_SUBSTS
            | ty::TypeFlags::STILL_FURTHER_SPECIALIZABLE;
        assert!(!arg.has_type_flags(!allowed_flags));
    }
    substs
}

#[instrument(level = "debug", skip(tcx))]
pub(super) fn filter_anon_const_generics<'tcx>(
    tcx: TyCtxt<'tcx>,
    parent_def_id: LocalDefId,
) -> ty::AnonConstGenerics {
    // We first search for all anonymous constants with the given parent.
    let children = collect_anon_consts_in_def(tcx, parent_def_id);
    debug!(?children);
    if children.is_empty() {
        return ty::AnonConstGenerics { consts: FxHashMap::default() };
    }

    // We then figure out which generic parameters are explicitly mentioned
    // by each children.
    let parent_generics = tcx.generics_of(parent_def_id);
    let mentioned_params = children
        .iter()
        .map(|&def_id| (def_id, explicitly_mentioned_params(tcx, parent_generics, def_id)))
        .collect::<FxIndexMap<_, _>>();
    debug!(?mentioned_params);

    // Get all predicates applying to the parent.
    let parent_predicates = tcx.predicates_of(parent_def_id).instantiate_identity(tcx);

    // We then compute all parameters which are somehow reachable for a given constant,
    // even if not mentioned itself.
    let reachable_params =
        compute_transitive_closure(tcx, mentioned_params, &parent_predicates.predicates);
    debug!(?reachable_params);

    ty::AnonConstGenerics { consts: reachable_params.into_iter().collect() }
}

struct AnonConstCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    consts: Vec<LocalDefId>,
}

impl<'tcx> Visitor<'tcx> for AnonConstCollector<'tcx> {
    type Map = Map<'tcx>;

    fn nested_visit_map(&mut self) -> NestedVisitorMap<Self::Map> {
        NestedVisitorMap::OnlyBodies(self.tcx.hir())
    }

    fn visit_anon_const(&mut self, c: &'tcx hir::AnonConst) {
        self.consts.push(self.tcx.hir().local_def_id(c.hir_id));
    }
}

fn collect_anon_consts_in_def<'tcx>(
    tcx: TyCtxt<'tcx>,
    parent_def_id: LocalDefId,
) -> Vec<LocalDefId> {
    let hir_id = tcx.hir().local_def_id_to_hir_id(parent_def_id);
    let parent_node = tcx.hir().get(hir_id);
    let mut visitor = AnonConstCollector { tcx, consts: Vec::new() };
    match parent_node {
        Node::Item(item) => visitor.visit_item(item),
        Node::ImplItem(item) => visitor.visit_impl_item(item),
        Node::TraitItem(item) => visitor.visit_trait_item(item),
        _ => tcx.sess.delay_span_bug(
            tcx.def_span(parent_def_id),
            &format!("unexpected parent: {:?}", parent_node),
        ),
    }

    visitor.consts
}

struct GenericParamCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    params: BitSet<u32>,
}

impl<'tcx> Visitor<'tcx> for GenericParamCollector<'tcx> {
    type Map = Map<'tcx>;

    fn nested_visit_map(&mut self) -> NestedVisitorMap<Self::Map> {
        NestedVisitorMap::OnlyBodies(self.tcx.hir())
    }

    fn visit_path(&mut self, path: &'tcx hir::Path<'tcx>, id: HirId) {
        match path.res {
            Res::Def(DefKind::LifetimeParam | DefKind::TyParam | DefKind::ConstParam, def_id) => {
                let hir_id = self.tcx.hir().local_def_id_to_hir_id(def_id.expect_local());
                let item_id = self.tcx.hir().get_parent_node(hir_id);
                let item_def_id = self.tcx.hir().local_def_id(item_id);
                let generics = self.tcx.generics_of(item_def_id);
                let index = generics.param_def_id_to_index[&def_id];
                self.params.insert(index);
            }
            _ => intravisit::walk_path(self, path),
        };
    }
}

fn explicitly_mentioned_params<'tcx>(
    tcx: TyCtxt<'tcx>,
    parent_generics: &'tcx ty::Generics,
    def_id: LocalDefId,
) -> BitSet<u32> {
    let hir_id = tcx.hir().local_def_id_to_hir_id(def_id);
    let node = tcx.hir().get(hir_id);
    let mut visitor =
        GenericParamCollector { tcx, params: BitSet::new_empty(parent_generics.count()) };
    match node {
        Node::AnonConst(ct) => visitor.visit_anon_const(ct),
        _ => bug!("expected const: {:?}", node),
    }
    visitor.params
}

// FIXME(generic_const_exprs): How should we deal with trait bounds with a concrete lhs, e.g. `u32: Trait<T>`.
// These can introduce `T` to any anonymous constant.
//
// Even worse `[u8; anon_const]: Trait<T>` can only introduce `T` to any anonymous constant if `anon_const`
// does not refer to any generic parameter. So whether we have to consider this depends on the way we compute
// the transitive closure here.
//
// Add tests for this when removing this fixme!
struct PredicateInfo {
    params: BitSet<u32>,
    consts: BitSet<usize>,
}

impl PredicateInfo {
    fn new(consts: &FxIndexMap<LocalDefId, BitSet<u32>>) -> PredicateInfo {
        PredicateInfo {
            params: BitSet::new_empty(consts[0].domain_size()),
            consts: BitSet::new_empty(consts.len()),
        }
    }
}

fn compute_transitive_closure<'tcx>(
    tcx: TyCtxt<'tcx>,
    mut consts: FxIndexMap<LocalDefId, BitSet<u32>>,
    predicates: &[ty::Predicate<'tcx>],
) -> FxIndexMap<LocalDefId, BitSet<u32>> {
    let predicate_info: Vec<_> =
        predicates.iter().map(|&pred| predicate_info(tcx, &consts, pred)).collect();

    let mut current_set = BitSet::new_empty(consts[0].domain_size());

    let mut changed = true;
    while changed {
        changed = false;
        for ct_idx in 0..consts.len() {
            for pred in predicate_info.iter() {
                current_set.clear();
                current_set.union(&pred.params);
                for pred_ct_idx in pred.consts.iter() {
                    current_set.union(&consts[pred_ct_idx]);
                }

                // FIXME(generic_const_exprs): We currently consider a predicate mentioning one of our parameters
                // to mention all of them, figure out the exact way this should work.
                if consts[ct_idx].intersects(&current_set) {
                    changed |= consts[ct_idx].union(&current_set);
                }
            }
        }
    }
    consts
}

struct PredicateInfoCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    consts: &'a FxIndexMap<LocalDefId, BitSet<u32>>,
    info: PredicateInfo,
}

impl<'tcx> TypeVisitor<'tcx> for PredicateInfoCollector<'_, 'tcx> {
    fn tcx_for_anon_const_substs(&self) -> Option<TyCtxt<'tcx>> {
        bug!("this visitor should manually deal with consts")
    }

    fn visit_ty(&mut self, t: Ty<'tcx>) -> ControlFlow<Self::BreakTy> {
        match t.kind() {
            ty::Param(param) => {
                self.info.params.insert(param.index);
                ControlFlow::CONTINUE
            }
            _ => t.super_visit_with(self),
        }
    }

    fn visit_region(&mut self, r: ty::Region<'tcx>) -> ControlFlow<Self::BreakTy> {
        match r {
            ty::ReEarlyBound(re) => {
                self.info.params.insert(re.index);
                ControlFlow::CONTINUE
            }
            _ => r.super_visit_with(self),
        }
    }

    fn visit_const(&mut self, c: &'tcx ty::Const<'tcx>) -> ControlFlow<Self::BreakTy> {
        match c.val {
            ty::ConstKind::Param(param) => {
                self.info.params.insert(param.index);
                ControlFlow::CONTINUE
            }
            ty::ConstKind::Unevaluated(uv) => uv.visit_with(self),
            ty::ConstKind::Value(_) | ty::ConstKind::Error(_) => {
                // these can't contain any parameters.
                ControlFlow::CONTINUE
            }
            _ => bug!("expected const in predicate: {:?}", c),
        }
    }

    fn visit_unevaluated_const(&mut self, uv: ty::Unevaluated<'tcx>) -> ControlFlow<Self::BreakTy> {
        if let Some(idx) = self.consts.get_index_of(&uv.def.did.expect_local()) {
            self.info.consts.insert(idx);
            ControlFlow::CONTINUE
        } else {
            // subtle: when encountering a predicate with a const
            // we did not find while walking the parent item,
            // we know that it is a predicate of the parents parent, so
            // we can look at its substs without any issues.
            uv.substs(self.tcx).visit_with(self)
        }
    }

    fn visit_predicate(&mut self, p: ty::Predicate<'tcx>) -> ControlFlow<Self::BreakTy> {
        p.super_visit_with(self)
    }
}

fn predicate_info<'tcx>(
    tcx: TyCtxt<'tcx>,
    consts: &FxIndexMap<LocalDefId, BitSet<u32>>,
    pred: ty::Predicate<'tcx>,
) -> PredicateInfo {
    let mut collector = PredicateInfoCollector { tcx, consts, info: PredicateInfo::new(consts) };
    pred.visit_with(&mut collector);
    collector.info
}
