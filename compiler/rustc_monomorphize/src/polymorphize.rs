//! Polymorphization Analysis
//! =========================
//!
//! This module implements an analysis of functions, methods and closures to determine which
//! generic parameters are unused (and eventually, in what ways generic parameters are used - only
//! for their size, offset of a field, etc.).

use crate::collector::neighbor::Neighbor;
use rustc_hir::{def::DefKind, def_id::DefId, ConstContext};
use rustc_index::bit_set::FiniteBitSet;
use rustc_infer::infer::type_variable::{TypeVariableOrigin, TypeVariableOriginKind};
use rustc_infer::infer::unify_key::{ConstVariableOrigin, ConstVariableOriginKind};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_infer::infer::{InferCtxt, InferOk};
use rustc_middle::mir::visit::{TyContext, Visitor};
use rustc_middle::mir::{Local, LocalDecl, Location};
use rustc_middle::traits::ObligationCause;
use rustc_middle::ty::fold::{TypeFoldable, TypeVisitor};
use rustc_middle::ty::subst::Subst;
use rustc_middle::ty::subst::{GenericArg, InternalSubsts, SubstsRef};
use rustc_middle::ty::ParamTy;
use rustc_middle::ty::TypeFolder;
use rustc_middle::ty::{self, query::Providers, Const, ParamEnv, Ty, TyCtxt};
use rustc_span::symbol::sym;
use rustc_span::{Span, Symbol};
use std::convert::TryInto;
use std::mem;
use std::ops::ControlFlow;
/// Provide implementations of queries relating to polymorphization analysis.
pub fn provide(providers: &mut Providers) {
    providers.unused_generic_params = unused_generic_params;
    providers.is_polymorphic_parent = |tcx, (a, b, c)| is_polymorphic_parent(tcx, a, b, c);
}

/// Determine which generic parameters are used by the instance.
///
/// Returns a bitset where bits representing unused parameters are set (`is_empty` indicates all
/// parameters are used).
#[instrument(level = "debug", skip(tcx))]
fn unused_generic_params<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::InstanceDef<'tcx>,
) -> FiniteBitSet<u32> {
    if !tcx.sess.opts.debugging_opts.polymorphize {
        // If polymorphization disabled, then all parameters are used.
        return FiniteBitSet::new_empty();
    }

    let def_id = instance.def_id();
    // Exit early if this instance should not be polymorphized.
    if !should_polymorphize(tcx, def_id, instance) {
        return FiniteBitSet::new_empty();
    }

    let generics = tcx.generics_of(def_id);
    debug!(?generics);

    // Exit early when there are no parameters to be unused.
    if generics.count() == 0 {
        return FiniteBitSet::new_empty();
    }

    // Create a bitset with N rightmost ones for each parameter.
    let generics_count: u32 =
        generics.count().try_into().expect("more generic parameters than can fit into a `u32`");
    let mut unused_parameters = FiniteBitSet::<u32>::new_empty();
    unused_parameters.set_range(0..generics_count);
    debug!(?unused_parameters, "(start)");

    mark_used_by_default_parameters(tcx, def_id, generics, &mut unused_parameters);
    debug!(?unused_parameters, "(after default)");

    // Visit MIR and accumululate used generic parameters.
    let body = match tcx.hir().body_const_context(def_id.expect_local()) {
        // Const functions are actually called and should thus be considered for polymorphization
        // via their runtime MIR.
        Some(ConstContext::ConstFn) | None => tcx.optimized_mir(def_id),
        Some(_) => tcx.mir_for_ctfe(def_id),
    };
    let mut vis = MarkUsedGenericParams { tcx, def_id, unused_parameters: &mut unused_parameters };
    vis.visit_body(body);
    debug!(?unused_parameters, "(end)");

    // Emit errors for debugging and testing if enabled.
    if !unused_parameters.is_empty() {
        emit_unused_generic_params_error(tcx, def_id, generics, &unused_parameters);
    }

    unused_parameters
}

/// Returns `true` if the instance should be polymorphized.
fn should_polymorphize<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    instance: ty::InstanceDef<'tcx>,
) -> bool {
    // If an instance's MIR body is not polymorphic then the modified substitutions that are
    // derived from polymorphization's result won't make any difference.
    if !instance.has_polymorphic_mir_body() {
        return false;
    }

    // Don't polymorphize intrinsics or virtual calls - calling `instance_mir` will panic.
    if matches!(instance, ty::InstanceDef::Intrinsic(..) | ty::InstanceDef::Virtual(..)) {
        return false;
    }

    // Polymorphization results are stored in cross-crate metadata only when there are unused
    // parameters, so assume that non-local items must have only used parameters (else this query
    // would not be invoked, and the cross-crate metadata used instead).
    if !def_id.is_local() {
        return false;
    }

    // Foreign items have no bodies to analyze.
    if tcx.is_foreign_item(def_id) {
        return false;
    }

    // Make sure there is MIR available.
    match tcx.hir().body_const_context(def_id.expect_local()) {
        Some(ConstContext::ConstFn) | None if !tcx.is_mir_available(def_id) => {
            debug!("no mir available");
            return false;
        }
        Some(_) if !tcx.is_ctfe_mir_available(def_id) => {
            debug!("no ctfe mir available");
            return false;
        }
        _ => true,
    }
}

/// Some parameters are considered used-by-default, such as non-generic parameters and the dummy
/// generic parameters from closures, this function marks them as used. `leaf_is_closure` should
/// be `true` if the item that `unused_generic_params` was invoked on is a closure.
#[instrument(level = "debug", skip(tcx, def_id, generics, unused_parameters))]
fn mark_used_by_default_parameters<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    generics: &'tcx ty::Generics,
    unused_parameters: &mut FiniteBitSet<u32>,
) {
    match tcx.def_kind(def_id) {
        DefKind::Closure | DefKind::Generator => {
            for param in &generics.params {
                debug!(?param, "(closure/gen)");
                unused_parameters.clear(param.index);
            }
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
        | DefKind::Fn
        | DefKind::Const
        | DefKind::ConstParam
        | DefKind::Static
        | DefKind::Ctor(_, _)
        | DefKind::AssocFn
        | DefKind::AssocConst
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
        | DefKind::Impl => {
            for param in &generics.params {
                debug!(?param, "(other)");
                if let ty::GenericParamDefKind::Lifetime = param.kind {
                    unused_parameters.clear(param.index);
                }
            }
        }
    }

    if let Some(parent) = generics.parent {
        mark_used_by_default_parameters(tcx, parent, tcx.generics_of(parent), unused_parameters);
    }
}

/// Emit errors for the function annotated by `#[rustc_polymorphize_error]`, labelling each generic
/// parameter which was unused.
#[instrument(level = "debug", skip(tcx, generics))]
fn emit_unused_generic_params_error<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    generics: &'tcx ty::Generics,
    unused_parameters: &FiniteBitSet<u32>,
) {
    let base_def_id = tcx.typeck_root_def_id(def_id);
    if !tcx.get_attrs(base_def_id).iter().any(|a| a.has_name(sym::rustc_polymorphize_error)) {
        return;
    }

    let fn_span = match tcx.opt_item_name(def_id) {
        Some(ident) => ident.span,
        _ => tcx.def_span(def_id),
    };

    let mut err = tcx.sess.struct_span_err(fn_span, "item has unused generic parameters");

    let mut next_generics = Some(generics);
    while let Some(generics) = next_generics {
        for param in &generics.params {
            if unused_parameters.contains(param.index).unwrap_or(false) {
                debug!(?param);
                let def_span = tcx.def_span(param.def_id);
                err.span_label(def_span, &format!("generic parameter `{}` is unused", param.name));
            }
        }

        next_generics = generics.parent.map(|did| tcx.generics_of(did));
    }

    err.emit();
}

/// Visitor used to aggregate generic parameter uses.
struct MarkUsedGenericParams<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    unused_parameters: &'a mut FiniteBitSet<u32>,
}

impl<'a, 'tcx> MarkUsedGenericParams<'a, 'tcx> {
    /// Invoke `unused_generic_params` on a body contained within the current item (e.g.
    /// a closure, generator or constant).
    #[instrument(level = "debug", skip(self, def_id, substs))]
    fn visit_child_body(&mut self, def_id: DefId, substs: SubstsRef<'tcx>) {
        let instance = ty::InstanceDef::Item(ty::WithOptConstParam::unknown(def_id));
        let unused = self.tcx.unused_generic_params(instance);
        debug!(?self.unused_parameters, ?unused);
        for (i, arg) in substs.iter().enumerate() {
            let i = i.try_into().unwrap();
            if !unused.contains(i).unwrap_or(false) {
                arg.visit_with(self);
            }
        }
        debug!(?self.unused_parameters);
    }
}

impl<'a, 'tcx> Visitor<'tcx> for MarkUsedGenericParams<'a, 'tcx> {
    #[instrument(level = "debug", skip(self, local))]
    fn visit_local_decl(&mut self, local: Local, local_decl: &LocalDecl<'tcx>) {
        if local == Local::from_usize(1) {
            let def_kind = self.tcx.def_kind(self.def_id);
            if matches!(def_kind, DefKind::Closure | DefKind::Generator) {
                // Skip visiting the closure/generator that is currently being processed. This only
                // happens because the first argument to the closure is a reference to itself and
                // that will call `visit_substs`, resulting in each generic parameter captured being
                // considered used by default.
                debug!("skipping closure substs");
                return;
            }
        }

        self.super_local_decl(local, local_decl);
    }

    fn visit_const(&mut self, c: &&'tcx Const<'tcx>, _: Location) {
        c.visit_with(self);
    }

    fn visit_ty(&mut self, ty: Ty<'tcx>, _: TyContext) {
        ty.visit_with(self);
    }
}

impl<'a, 'tcx> TypeVisitor<'tcx> for MarkUsedGenericParams<'a, 'tcx> {
    fn tcx_for_anon_const_substs(&self) -> Option<TyCtxt<'tcx>> {
        Some(self.tcx)
    }
    #[instrument(level = "debug", skip(self))]
    fn visit_const(&mut self, c: &'tcx Const<'tcx>) -> ControlFlow<Self::BreakTy> {
        if !c.potentially_has_param_types_or_consts() {
            return ControlFlow::CONTINUE;
        }

        match c.val {
            ty::ConstKind::Param(param) => {
                debug!(?param);
                self.unused_parameters.clear(param.index);
                ControlFlow::CONTINUE
            }
            ty::ConstKind::Unevaluated(ty::Unevaluated { def, substs_: _, promoted: Some(p)})
                // Avoid considering `T` unused when constants are of the form:
                //   `<Self as Foo<T>>::foo::promoted[p]`
                if self.def_id == def.did && !self.tcx.generics_of(def.did).has_self =>
            {
                // If there is a promoted, don't look at the substs - since it will always contain
                // the generic parameters, instead, traverse the promoted MIR.
                let promoted = self.tcx.promoted_mir(def.did);
                self.visit_body(&promoted[p]);
                ControlFlow::CONTINUE
            }
            ty::ConstKind::Unevaluated(uv)
                if matches!(self.tcx.def_kind(uv.def.did), DefKind::AnonConst | DefKind::InlineConst) =>
            {
                self.visit_child_body(uv.def.did, uv.substs(self.tcx));
                ControlFlow::CONTINUE
            }
            _ => c.super_visit_with(self),
        }
    }

    #[instrument(level = "debug", skip(self))]
    fn visit_ty(&mut self, ty: Ty<'tcx>) -> ControlFlow<Self::BreakTy> {
        if !ty.potentially_has_param_types_or_consts() {
            return ControlFlow::CONTINUE;
        }

        match *ty.kind() {
            ty::Closure(def_id, substs) | ty::Generator(def_id, substs, ..) => {
                debug!(?def_id);
                // Avoid cycle errors with generators.
                if def_id == self.def_id {
                    return ControlFlow::CONTINUE;
                }

                // Consider any generic parameters used by any closures/generators as used in the
                // parent.
                self.visit_child_body(def_id, substs);
                ControlFlow::CONTINUE
            }
            ty::Param(param) => {
                debug!(?param);
                self.unused_parameters.clear(param.index);
                ControlFlow::CONTINUE
            }
            _ => ty.super_visit_with(self),
        }
    }
}

/// Visitor used to check if a generic parameter is used.
struct HasUsedGenericParams<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    unused_parameters: &'a FiniteBitSet<u32>,
}

impl<'a, 'tcx> TypeVisitor<'tcx> for HasUsedGenericParams<'a, 'tcx> {
    type BreakTy = ();

    fn tcx_for_anon_const_substs(&self) -> Option<TyCtxt<'tcx>> {
        Some(self.tcx)
    }

    #[instrument(level = "debug", skip(self))]
    fn visit_const(&mut self, c: &'tcx Const<'tcx>) -> ControlFlow<Self::BreakTy> {
        if !c.potentially_has_param_types_or_consts() {
            return ControlFlow::CONTINUE;
        }

        match c.val {
            ty::ConstKind::Param(param) => {
                if self.unused_parameters.contains(param.index).unwrap_or(false) {
                    ControlFlow::CONTINUE
                } else {
                    ControlFlow::BREAK
                }
            }
            _ => c.super_visit_with(self),
        }
    }

    #[instrument(level = "debug", skip(self))]
    fn visit_ty(&mut self, ty: Ty<'tcx>) -> ControlFlow<Self::BreakTy> {
        if !ty.potentially_has_param_types_or_consts() {
            return ControlFlow::CONTINUE;
        }

        match ty.kind() {
            ty::Param(param) => {
                if self.unused_parameters.contains(param.index).unwrap_or(false) {
                    ControlFlow::CONTINUE
                } else {
                    ControlFlow::BREAK
                }
            }
            _ => ty.super_visit_with(self),
        }
    }
}

#[instrument(skip(tcx, neighbors), level = "debug")]
pub(crate) fn compute_polymorphized_substs<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::InstanceDef<'tcx>,
    concrete_substs: SubstsRef<'tcx>,
    neighbors: Vec<Neighbor<'tcx>>,
) -> SubstsRef<'tcx> {
    // Not a great, but this shouldn't error and it is better than just using `DUMMY_SP` in
    // case something goes wrong.
    let span = tcx.def_span(instance.def_id());
    let cause = &ObligationCause::dummy_with_span(span);
    let maximal_substs = maximal_polymorphized_substs(tcx, instance, concrete_substs);
    debug!(?maximal_substs);
    let result = tcx.infer_ctxt().enter(|infcx| {
        let infer_substs = InternalSubsts::for_item(tcx, instance.def_id(), |param, _| {
            infcx.var_for_def(span, param)
        });
        let maximal_substs = maximal_substs.subst(tcx, infer_substs);
        for neighbor in neighbors {
            debug!(?neighbor.source);
            match neighbor.source {
                // Not yet explicitly supported, mark all generic parameters mentioned
                // by the source as used.
                _ => {
                    let maximal_source_substs = neighbor.source.subst(tcx, maximal_substs);
                    let concrete_source_substs = neighbor.source.subst(tcx, concrete_substs);
                    for (a, b) in collect_roots(maximal_source_substs, concrete_source_substs) {
                        match infcx.at(cause, ParamEnv::reveal_all()).eq(a, b) {
                            Ok(InferOk { value: (), obligations }) if obligations.is_empty() => {}
                            err => {
                                warn!("unexpected polymorphize result: {:?}", err);
                                return concrete_substs;
                            }
                        }
                    }
                }
            }
        }

        infer_to_param(infcx, maximal_substs)
    });
    debug!(?result);
    result
}

#[instrument(skip(tcx), level = "debug")]
pub(crate) fn maximal_polymorphized_substs(
    tcx: TyCtxt<'tcx>,
    instance: ty::InstanceDef<'tcx>,
    substs: SubstsRef<'tcx>,
) -> SubstsRef<'tcx> {
    let unused = tcx.unused_generic_params(instance);
    debug!(?unused);

    // If this is a closure or generator then we need to handle the case where another closure
    // from the function is captured as an upvar and hasn't been polymorphized. In this case,
    // the unpolymorphized upvar closure would result in a polymorphized closure producing
    // multiple mono items (and eventually symbol clashes).
    let def_id = instance.def_id();
    let polymorphic_ty = tcx.type_of(def_id);
    let closure_upvars = match polymorphic_ty.kind() {
        ty::Closure(_, substs) => Some(substs.as_closure().tupled_upvars_ty()),
        ty::Generator(_, substs, _) => Some(substs.as_generator().tupled_upvars_ty()),
        _ => None,
    };

    InternalSubsts::for_item(tcx, def_id, |param, prev_params| {
        let is_unused = unused.contains(param.index).unwrap_or(false);
        debug!(?param, ?is_unused);
        match param.kind {
            // Upvar case: If parameter is a type parameter..
            ty::GenericParamDefKind::Type { .. } if
                let Some(generic_upvars) =
                    closure_upvars.filter(|_| param.index as usize == substs.len() - 1) => {
                    // ..then double-check that polymorphization marked it used..
                    debug_assert!(!is_unused);
                    let substs_no_upvars = tcx.intern_substs(prev_params);
                    let resulting_substs = generic_upvars.subst(tcx, substs_no_upvars).into();
                    let resulting_substs = tcx.normalize_erasing_regions(ty::ParamEnv::reveal_all(), resulting_substs);
                    resulting_substs
                },

            // Simple case: If parameter is a const or type parameter..
            ty::GenericParamDefKind::Const { .. } | ty::GenericParamDefKind::Type { .. } if
                // ..and is within range and unused..
               is_unused =>
                    // ..then use the identity for this parameter.
                    tcx.mk_param_from_def(param),

            // Otherwise, use the parameter as before.
            _ => substs[param.index as usize],
        }
    })
}

fn collect_roots<'tcx, T: TypeFoldable<'tcx>>(
    a: T,
    b: T,
) -> impl Iterator<Item = (GenericArg<'tcx>, GenericArg<'tcx>)> {
    struct RootCollector<'tcx> {
        roots: Vec<GenericArg<'tcx>>,
    }
    impl<'tcx> TypeVisitor<'tcx> for RootCollector<'tcx> {
        fn tcx_for_anon_const_substs(&self) -> Option<TyCtxt<'tcx>> {
            None
        }
        fn visit_ty(&mut self, t: Ty<'tcx>) -> ControlFlow<Self::BreakTy> {
            self.roots.push(t.into());
            ControlFlow::CONTINUE
        }
        fn visit_const(&mut self, c: &'tcx Const<'tcx>) -> ControlFlow<Self::BreakTy> {
            self.roots.push(c.into());
            ControlFlow::CONTINUE
        }
    }

    let mut root_collector = RootCollector { roots: Vec::new() };
    a.visit_with(&mut root_collector);
    let a_roots = mem::take(&mut root_collector.roots);

    b.visit_with(&mut root_collector);
    let b_roots = root_collector.roots;

    a_roots.into_iter().zip(b_roots)
}

fn infer_to_param<'a, 'tcx, T: TypeFoldable<'tcx>>(infcx: InferCtxt<'a, 'tcx>, v: T) -> T {
    struct Folder<'a, 'tcx> {
        infcx: InferCtxt<'a, 'tcx>,
        param_map: Vec<(GenericArg<'tcx>, GenericArg<'tcx>)>,
    }

    impl<'a, 'tcx> TypeFolder<'tcx> for Folder<'a, 'tcx> {
        fn tcx(&self) -> TyCtxt<'tcx> {
            self.infcx.tcx
        }

        fn fold_ty(&mut self, t: Ty<'tcx>) -> Ty<'tcx> {
            let tn = self.infcx.shallow_resolve(t);
            if t != tn {
                tn.fold_with(self)
            } else {
                match t.kind() {
                    ty::Infer(_) => {
                        if let Some(&(_, param)) =
                            self.param_map.iter().find(|&&(arg, _)| arg == t.into())
                        {
                            param.expect_ty()
                        } else {
                            let idx = self.param_map.len() as u32;
                            let param_ty = ParamTy::new(idx, Symbol::intern(&format!("T{}", idx)))
                                .to_ty(self.infcx.tcx);
                            self.param_map.push((t.into(), param_ty.into()));
                            param_ty
                        }
                    }
                    _ => t.super_fold_with(self),
                }
            }
        }

        fn fold_const(&mut self, c: &'tcx Const<'tcx>) -> &'tcx Const<'tcx> {
            let cn = self.infcx.shallow_resolve(c);
            if c != cn {
                cn.fold_with(self)
            } else {
                match c.val {
                    ty::ConstKind::Infer(_) => {
                        if let Some(&(_, param)) =
                            self.param_map.iter().find(|&&(arg, _)| arg == c.into())
                        {
                            param.expect_const()
                        } else {
                            let idx = self.param_map.len() as u32;
                            let param_const = self.infcx.tcx.mk_const_param(
                                idx,
                                Symbol::intern(&format!("N{}", idx)),
                                c.ty,
                            );
                            self.param_map.push((c.into(), param_const.into()));
                            param_const
                        }
                    }
                    _ => c.super_fold_with(self),
                }
            }
        }
    }

    v.fold_with(&mut Folder { infcx, param_map: Vec::new() })
}

fn param_to_infer<'a, 'tcx, T: TypeFoldable<'tcx>>(
    infcx: &InferCtxt<'a, 'tcx>,
    span: Span,
    v: T,
) -> T {
    struct Folder<'a, 'tcx> {
        infcx: &'a InferCtxt<'a, 'tcx>,
        span: Span,
        param_map: Vec<Option<GenericArg<'tcx>>>,
    }

    impl<'a, 'tcx> TypeFolder<'tcx> for Folder<'a, 'tcx> {
        fn tcx(&self) -> TyCtxt<'tcx> {
            self.infcx.tcx
        }

        fn fold_ty(&mut self, t: Ty<'tcx>) -> Ty<'tcx> {
            match t.kind() {
                ty::Param(p) => {
                    while self.param_map.len() <= p.index as usize {
                        self.param_map.push(None);
                    }

                    (*self.param_map[p.index as usize].get_or_insert_with(|| {
                        self.infcx
                            .next_ty_var(TypeVariableOrigin {
                                kind: TypeVariableOriginKind::MiscVariable,
                                span: self.span,
                            })
                            .into()
                    }))
                    .expect_ty()
                }
                _ => t.super_fold_with(self),
            }
        }

        fn fold_const(&mut self, c: &'tcx Const<'tcx>) -> &'tcx Const<'tcx> {
            match c.val {
                ty::ConstKind::Param(p) => {
                    while self.param_map.len() <= p.index as usize {
                        self.param_map.push(None);
                    }

                    (*self.param_map[p.index as usize].get_or_insert_with(|| {
                        self.infcx
                            .next_const_var(
                                c.ty,
                                ConstVariableOrigin {
                                    kind: ConstVariableOriginKind::MiscVariable,
                                    span: self.span,
                                },
                            )
                            .into()
                    }))
                    .expect_const()
                }
                _ => c.super_fold_with(self),
            }
        }
    }

    v.fold_with(&mut Folder { infcx, span, param_map: Vec::new() })
}

#[instrument(skip(tcx), level = "debug")]
pub fn is_polymorphic_parent(
    tcx: TyCtxt<'tcx>,
    instance: ty::InstanceDef<'tcx>,
    a: SubstsRef<'tcx>,
    b: SubstsRef<'tcx>,
) -> bool {
    // Not a great, but this shouldn't error and it is better than just using `DUMMY_SP` in
    // case something goes wrong.
    let span = tcx.def_span(instance.def_id());
    let cause = &ObligationCause::dummy_with_span(span);
    let result = tcx.infer_ctxt().enter(|infcx| {
        let a_infer = param_to_infer(&infcx, span, a);
        for (a, b) in a_infer.iter().zip(b) {
            match infcx.at(cause, ParamEnv::reveal_all()).eq(a, b) {
                Ok(InferOk { value: (), obligations }) if obligations.is_empty() => {}
                _ => return false,
            }
        }

        true
    });
    debug!(?result);
    result
}
