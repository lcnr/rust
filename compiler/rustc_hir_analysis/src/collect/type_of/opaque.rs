use rustc_hir::def::DefKind;
use rustc_hir::def_id::LocalDefId;
use rustc_hir::{self as hir, Expr, ImplItem, Item, Node, TraitItem, def, intravisit};
use rustc_middle::bug;
use rustc_middle::hir::nested_filter;
use rustc_middle::ty::{self, Ty, TyCtxt, TypeVisitableExt};
use rustc_span::DUMMY_SP;
use tracing::{debug, instrument, trace};

use crate::errors::{TaitForwardCompat2, UnconstrainedOpaqueType};

#[instrument(skip(tcx), level = "debug")]
pub(super) fn find_opaque_ty_constraints_for_impl_trait_in_assoc_type(
    tcx: TyCtxt<'_>,
    def_id: LocalDefId,
    collect_hir_tys: bool,
) -> Ty<'_> {
    let mut parent_def_id = def_id;
    while tcx.def_kind(parent_def_id) == def::DefKind::OpaqueTy {
        // Account for `type Alias = impl Trait<Foo = impl Trait>;` (#116031)
        parent_def_id = tcx.local_parent(parent_def_id);
    }
    let impl_def_id = tcx.local_parent(parent_def_id);
    match tcx.def_kind(impl_def_id) {
        DefKind::Impl { .. } => {}
        other => bug!("invalid impl trait in assoc type parent: {other:?}"),
    }

    let mut locator = TaitConstraintLocator { def_id, tcx, collect_hir_tys, found: None };

    for &assoc_id in tcx.associated_item_def_ids(impl_def_id) {
        let assoc = tcx.associated_item(assoc_id);
        match assoc.kind {
            ty::AssocKind::Const | ty::AssocKind::Fn => locator.check(assoc_id.expect_local()),
            // Associated types don't have bodies, so they can't constrain hidden types
            ty::AssocKind::Type => {}
        }
    }

    if let Some(hidden) = locator.found {
        hidden.ty
    } else {
        let guar = tcx.dcx().emit_err(UnconstrainedOpaqueType {
            span: tcx.def_span(def_id),
            name: tcx.item_ident(parent_def_id.to_def_id()),
            what: "impl",
        });
        Ty::new_error(tcx, guar)
    }
}

/// Checks "defining uses" of opaque `impl Trait` types to ensure that they meet the restrictions
/// laid for "higher-order pattern unification".
/// This ensures that inference is tractable.
/// In particular, definitions of opaque types can only use other generics as arguments,
/// and they cannot repeat an argument. Example:
///
/// ```ignore (illustrative)
/// type Foo<A, B> = impl Bar<A, B>;
///
/// // Okay -- `Foo` is applied to two distinct, generic types.
/// fn a<T, U>() -> Foo<T, U> { .. }
///
/// // Not okay -- `Foo` is applied to `T` twice.
/// fn b<T>() -> Foo<T, T> { .. }
///
/// // Not okay -- `Foo` is applied to a non-generic type.
/// fn b<T>() -> Foo<T, u32> { .. }
/// ```
#[instrument(skip(tcx), level = "debug")]
pub(super) fn find_opaque_ty_constraints_for_tait(
    tcx: TyCtxt<'_>,
    def_id: LocalDefId,
    collect_hir_tys: bool,
) -> Ty<'_> {
    let mut locator = TaitConstraintLocator { tcx, def_id, collect_hir_tys, found: None };

    tcx.hir_walk_toplevel_module(&mut locator);

    if let Some(hidden) = locator.found {
        hidden.ty
    } else {
        let mut parent_def_id = def_id;
        while tcx.def_kind(parent_def_id) == def::DefKind::OpaqueTy {
            // Account for `type Alias = impl Trait<Foo = impl Trait>;` (#116031)
            parent_def_id = tcx.local_parent(parent_def_id);
        }
        let guar = tcx.dcx().emit_err(UnconstrainedOpaqueType {
            span: tcx.def_span(def_id),
            name: tcx.item_ident(parent_def_id.to_def_id()),
            what: "crate",
        });
        Ty::new_error(tcx, guar)
    }
}

struct TaitConstraintLocator<'tcx> {
    tcx: TyCtxt<'tcx>,

    /// def_id of the opaque type whose defining uses are being checked
    def_id: LocalDefId,

    /// Whether to search for HIR typeck types instead of MIR types.
    collect_hir_tys: bool,

    /// as we walk the defining uses, we are checking that all of them
    /// define the same hidden type. This variable is set to `Some`
    /// with the first type that we find, and then later types are
    /// checked against it (we also carry the span of that first
    /// type).
    found: Option<ty::OpaqueHiddenType<'tcx>>,
}

impl TaitConstraintLocator<'_> {
    #[instrument(skip(self), level = "debug")]
    fn check(&mut self, item_def_id: LocalDefId) {
        // Don't try to check items that cannot possibly constrain the type.
        if !self.tcx.has_typeck_results(item_def_id) {
            debug!("no constraint: no typeck results");
            return;
        }

        let opaque_types_defined_by = self.tcx.opaque_types_defined_by(item_def_id);
        // Don't try to check items that cannot possibly constrain the type.
        if !opaque_types_defined_by.contains(&self.def_id) {
            debug!("no constraint: no opaque types defined");
            return;
        }

        // Function items with `_` in their return type already emit an error, skip any
        // "non-defining use" errors for them.
        // Note that we use `Node::fn_sig` instead of `Node::fn_decl` here, because the former
        // excludes closures, which are allowed to have `_` in their return type.
        let hir_node = self.tcx.hir_node_by_def_id(item_def_id);
        debug_assert!(
            !matches!(hir_node, Node::ForeignItem(..)),
            "foreign items cannot constrain opaque types",
        );
        if let Some(hir_sig) = hir_node.fn_sig()
            && hir_sig.decl.output.is_suggestable_infer_ty().is_some()
        {
            let guar = self.tcx.dcx().span_delayed_bug(
                hir_sig.decl.output.span(),
                "inferring return types and opaque types do not mix well",
            );
            self.found =
                Some(ty::OpaqueHiddenType { span: DUMMY_SP, ty: Ty::new_error(self.tcx, guar) });
            return;
        }

        if self.collect_hir_tys {
            let tables = self.tcx.typeck(item_def_id);
            if let Some(guar) = tables.tainted_by_errors {
                self.found = Some(ty::OpaqueHiddenType {
                    span: DUMMY_SP,
                    ty: Ty::new_error(self.tcx, guar),
                });
                return;
            }

            if let Some(&concrete_type) = tables.concrete_opaque_types.get(&self.def_id) {
                if let Some(prev) = &mut self.found {
                    if concrete_type.ty != prev.ty {
                        let (Ok(guar) | Err(guar)) =
                            prev.build_mismatch_error(&concrete_type, self.tcx).map(|d| d.emit());
                        prev.ty = Ty::new_error(self.tcx, guar);
                    }
                } else {
                    self.found = Some(concrete_type);
                }
            } else {
                debug!("no constraints in typeck results");
                let guar = self.tcx.dcx().emit_err(TaitForwardCompat2 {
                    span: self
                        .tcx
                        .def_ident_span(item_def_id)
                        .unwrap_or_else(|| self.tcx.def_span(item_def_id)),
                    opaque_type_span: self.tcx.def_span(self.def_id),
                    opaque_type: self.tcx.def_path_str(self.def_id),
                });
                // Avoid "opaque type not constrained" errors on the opaque itself.
                self.found = Some(ty::OpaqueHiddenType {
                    span: DUMMY_SP,
                    ty: Ty::new_error(self.tcx, guar),
                });
            }
        } else {
            // Use borrowck to get the type with unerased regions.
            let borrowck_results = &self.tcx.mir_borrowck(item_def_id);
            // If the body was tainted, then assume the opaque may have been constrained and just set it to error.
            if let Some(guar) = borrowck_results.tainted_by_errors {
                self.found = Some(ty::OpaqueHiddenType {
                    span: DUMMY_SP,
                    ty: Ty::new_error(self.tcx, guar),
                });
                return;
            }

            debug!(?borrowck_results.concrete_opaque_types);
            if let Some(&concrete_type) = borrowck_results.concrete_opaque_types.get(&self.def_id) {
                debug!(?concrete_type, "found constraint");
                if let Some(prev) = &mut self.found {
                    if concrete_type.ty != prev.ty {
                        let (Ok(guar) | Err(guar)) =
                            prev.build_mismatch_error(&concrete_type, self.tcx).map(|d| d.emit());
                        prev.ty = Ty::new_error(self.tcx, guar);
                    }
                } else {
                    self.found = Some(concrete_type);
                }
            } else {
                let guar = self.tcx.dcx().emit_err(TaitForwardCompat2 {
                    span: self
                        .tcx
                        .def_ident_span(item_def_id)
                        .unwrap_or_else(|| self.tcx.def_span(item_def_id)),
                    opaque_type_span: self.tcx.def_span(self.def_id),
                    opaque_type: self.tcx.def_path_str(self.def_id),
                });
                // Avoid "opaque type not constrained" errors on the opaque itself.
                self.found = Some(ty::OpaqueHiddenType {
                    span: DUMMY_SP,
                    ty: Ty::new_error(self.tcx, guar),
                });
            }
        }
    }
}

impl<'tcx> intravisit::Visitor<'tcx> for TaitConstraintLocator<'tcx> {
    type NestedFilter = nested_filter::All;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }
    fn visit_expr(&mut self, ex: &'tcx Expr<'tcx>) {
        if let hir::ExprKind::Closure(closure) = ex.kind {
            self.check(closure.def_id);
        }
        intravisit::walk_expr(self, ex);
    }
    fn visit_item(&mut self, it: &'tcx Item<'tcx>) {
        trace!(?it.owner_id);
        self.check(it.owner_id.def_id);
        intravisit::walk_item(self, it);
    }
    fn visit_impl_item(&mut self, it: &'tcx ImplItem<'tcx>) {
        trace!(?it.owner_id);
        self.check(it.owner_id.def_id);
        intravisit::walk_impl_item(self, it);
    }
    fn visit_trait_item(&mut self, it: &'tcx TraitItem<'tcx>) {
        trace!(?it.owner_id);
        self.check(it.owner_id.def_id);
        intravisit::walk_trait_item(self, it);
    }
    fn visit_foreign_item(&mut self, it: &'tcx hir::ForeignItem<'tcx>) {
        trace!(?it.owner_id);
        assert_ne!(it.owner_id.def_id, self.def_id);
        // No need to call `check`, as we do not run borrowck on foreign items.
        intravisit::walk_foreign_item(self, it);
    }
}

// Get the hidden type computed by HIR typeck.
pub(super) fn find_hir_opaque_ty_constraints_for_rpit<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    owner_def_id: LocalDefId,
) -> Ty<'tcx> {
    let tables = tcx.typeck(owner_def_id);
    if let Some(guar) = tables.tainted_by_errors {
        Ty::new_error(tcx, guar)
    } else if let Some(&concrete_type) = tables.concrete_opaque_types.get(&def_id) {
        concrete_type.ty
    } else {
        // We failed to resolve the opaque type or it
        // resolves to itself. We interpret this as the
        // no values of the hidden type ever being constructed,
        // so we can just make the hidden type be `!`.
        // For backwards compatibility reasons, we fall back to
        // `()` until we the diverging default is changed.
        Ty::new_diverging_default(tcx)
    }
}

pub(super) fn find_opaque_ty_constraints_for_rpit<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    owner_def_id: LocalDefId,
) -> Ty<'tcx> {
    let mir_opaque_ty = tcx.mir_borrowck(owner_def_id).concrete_opaque_types.get(&def_id).copied();
    if let Some(mir_opaque_ty) = mir_opaque_ty {
        if mir_opaque_ty.references_error() {
            return mir_opaque_ty.ty;
        }

        debug!(?owner_def_id);
        let mut locator = RpitConstraintChecker { def_id, tcx, found: mir_opaque_ty };

        match tcx.hir_node_by_def_id(owner_def_id) {
            Node::Item(it) => intravisit::walk_item(&mut locator, it),
            Node::ImplItem(it) => intravisit::walk_impl_item(&mut locator, it),
            Node::TraitItem(it) => intravisit::walk_trait_item(&mut locator, it),
            other => bug!("{:?} is not a valid scope for an opaque type item", other),
        }

        mir_opaque_ty.ty
    } else {
        // FIXME(#112417): This treats the type computed during HIR typeck as the final
        // hidden type. We never check region constraints of these types so this is
        // at least theoretically unsound.
        find_hir_opaque_ty_constraints_for_rpit(tcx, def_id, owner_def_id)
    }
}

struct RpitConstraintChecker<'tcx> {
    tcx: TyCtxt<'tcx>,

    /// def_id of the opaque type whose defining uses are being checked
    def_id: LocalDefId,

    found: ty::OpaqueHiddenType<'tcx>,
}

impl RpitConstraintChecker<'_> {
    #[instrument(skip(self), level = "debug")]
    fn check(&self, def_id: LocalDefId) {
        // Use borrowck to get the type with unerased regions.
        let concrete_opaque_types = &self.tcx.mir_borrowck(def_id).concrete_opaque_types;
        debug!(?concrete_opaque_types);
        if let Some(&concrete_type) = concrete_opaque_types.get(&def_id) {
            debug!(?concrete_type, "found constraint");
            if concrete_type.ty != self.found.ty {
                if let Ok(d) = self.found.build_mismatch_error(&concrete_type, self.tcx) {
                    d.emit();
                }
            }
        }
    }
}

impl<'tcx> intravisit::Visitor<'tcx> for RpitConstraintChecker<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }
    fn visit_expr(&mut self, ex: &'tcx Expr<'tcx>) {
        if let hir::ExprKind::Closure(closure) = ex.kind {
            self.check(closure.def_id);
        }
        intravisit::walk_expr(self, ex);
    }
    fn visit_item(&mut self, it: &'tcx Item<'tcx>) {
        trace!(?it.owner_id);
        // The opaque type itself or its children are not within its reveal scope.
        if it.owner_id.def_id != self.def_id {
            self.check(it.owner_id.def_id);
            intravisit::walk_item(self, it);
        }
    }
    fn visit_impl_item(&mut self, it: &'tcx ImplItem<'tcx>) {
        trace!(?it.owner_id);
        // The opaque type itself or its children are not within its reveal scope.
        if it.owner_id.def_id != self.def_id {
            self.check(it.owner_id.def_id);
            intravisit::walk_impl_item(self, it);
        }
    }
    fn visit_trait_item(&mut self, it: &'tcx TraitItem<'tcx>) {
        trace!(?it.owner_id);
        self.check(it.owner_id.def_id);
        intravisit::walk_trait_item(self, it);
    }
}
