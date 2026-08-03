//! Computes implied outlives bounds for MIR borrowck before entering its NLL inference context.
//!
//! The query and its caller view the same signature through different region representations.
//! Here, erased signature regions are made into rigid root-universe placeholders; in MIR borrowck,
//! those same occurrences are NLL universal `RegionVid`s. Both sides construct a parallel list of
//! query input values, allowing canonical response instantiation to map one representation to the
//! other without unifying NLL universals.
//!
//! The response also carries the exact normalized signature used to derive the implied bounds.
//! Normalization can create fresh region variables, so independently normalizing the signature in
//! the caller could disconnect those variables from the returned bounds.

use rustc_data_structures::fx::FxHashSet;
use rustc_hir::def::DefKind;
use rustc_infer::infer::{RegionVariableOrigin, TyCtxtInferExt};
use rustc_infer::traits::ObligationCause;
use rustc_infer::traits::query::OutlivesBound;
use rustc_middle::infer::canonical::{self, Canonical, CanonicalVarValues};
use rustc_middle::query::Providers;
use rustc_middle::traits::query::{MirBorrowckImpliedOutlivesBounds, NoSolution};
use rustc_middle::ty::{
    self, GenericArg, GenericArgs, RegionExt, Ty, TyCtxt, TypeVisitableExt, TypingMode,
    fold_regions,
};
use rustc_span::Span;
use rustc_span::def_id::LocalDefId;
use rustc_trait_selection::traits::ObligationCtxt;
use rustc_trait_selection::traits::query::type_op::implied_outlives_bounds::{
    compute_implied_outlives_bounds_from_normalized,
    extend_implied_bounds_with_registered_region_obligations,
};
use tracing::debug;

use crate::SmallVec;
use crate::universal_regions::{DefiningTy, for_each_late_bound_region_in_recursive_scope};

pub(crate) fn provide(providers: &mut Providers) {
    *providers = Providers { mir_borrowck_implied_outlives_bounds, ..*providers };
}

fn mir_borrowck_implied_outlives_bounds<'tcx>(
    tcx: TyCtxt<'tcx>,
    body_def_id: LocalDefId,
) -> Result<
    &'tcx Canonical<'tcx, canonical::QueryResponse<'tcx, MirBorrowckImpliedOutlivesBounds<'tcx>>>,
    NoSolution,
> {
    let infcx = tcx.infer_ctxt().build(TypingMode::non_body_analysis());
    let ocx = ObligationCtxt::new(&infcx);
    let defining_ty = DefiningTy::new(tcx, body_def_id);
    let param_env = tcx.param_env(body_def_id);
    let span = tcx.def_span(body_def_id);

    let bound_inputs_and_output =
        defining_ty.inputs_and_output(tcx, body_def_id, || tcx.lifetimes.re_erased);
    if let Err(error) = bound_inputs_and_output.error_reported() {
        infcx.set_tainted_by_errors(error);
    }

    // Collect these before liberation so even bound lifetimes unused by the signature's types are
    // present in the named-region prefix shared with the NLL caller.
    let own_late_bound_regions = bound_inputs_and_output
        .bound_vars()
        .iter()
        .enumerate()
        .filter_map(|(idx, bound_var)| {
            let ty::BoundVariableKind::Region(kind) = bound_var else { return None };
            let kind = ty::LateParamRegionKind::from_bound(ty::BoundVar::from_usize(idx), kind);
            Some(ty::Region::new_late_param(tcx, body_def_id.to_def_id(), kind))
        })
        .collect::<Vec<_>>();

    let liberated_inputs_and_output =
        tcx.liberate_late_bound_regions(body_def_id.to_def_id(), bound_inputs_and_output);
    let query_inputs_and_output =
        replace_erased_regions_with_root_placeholders(tcx, liberated_inputs_and_output);

    let mut outlives_bounds = Vec::new();
    let mut normalized_inputs_and_output = Vec::with_capacity(query_inputs_and_output.len());
    for &query_ty in &query_inputs_and_output {
        let region_obligation_start = infcx.clone_registered_region_obligations().len();
        let Ok(normalized_ty) = ocx.deeply_normalize(
            &ObligationCause::dummy_with_span(span),
            param_env,
            ty::Unnormalized::new_wip(query_ty),
        ) else {
            // Retry in the body inference context so ambiguity is diagnosed there instead of
            // silently treating the source type as normalized.
            normalized_inputs_and_output.push(None);
            continue;
        };

        // Both forms are WF roots (#87748). Reusing this exact normalized type also keeps any
        // normalization-created region variables connected to the returned bounds (#136547).
        if let Ok(bounds) = compute_implied_outlives_bounds_from_normalized(
            &ocx,
            param_env,
            query_ty,
            normalized_ty,
            span,
        ) {
            outlives_bounds.extend(bounds);
            let region_obligations = infcx.clone_registered_region_obligations();
            extend_implied_bounds_with_registered_region_obligations(
                tcx,
                [query_ty, normalized_ty],
                region_obligations[region_obligation_start..].iter().cloned(),
                &mut outlives_bounds,
            );
        }

        normalized_inputs_and_output.push(Some(normalized_ty));
    }

    extend_with_impl_header_bounds(
        tcx,
        &ocx,
        body_def_id,
        param_env,
        span,
        &mut outlives_bounds,
    );

    let typeck_root_def_id = tcx.typeck_root_def_id(body_def_id.to_def_id()).expect_local();
    let mut named_regions: Vec<_> =
        GenericArgs::identity_for_item(tcx, typeck_root_def_id).regions().collect();
    if body_def_id != typeck_root_def_id {
        for_each_late_bound_region_in_recursive_scope(tcx, tcx.local_parent(body_def_id), |region| {
            named_regions.push(region);
        });
    }
    named_regions.extend(own_late_bound_regions);

    // Signature regions existed before normalization and have matching NLL universals at the call
    // site. Variables introduced by normalization are instead canonical output variables shared
    // by the returned signature and bounds.
    let input_values = implied_bounds_query_input_values(
        tcx,
        typeck_root_def_id,
        named_regions,
        &query_inputs_and_output,
        |region| Some(region),
    );
    let input_values = CanonicalVarValues { var_values: tcx.mk_args(&input_values) };

    debug!(?input_values);
    ocx.make_canonicalized_query_response(
        input_values,
        MirBorrowckImpliedOutlivesBounds { outlives_bounds, normalized_inputs_and_output },
    )
}

/// Builds the input mapping shared by the query and its NLL caller.
///
/// Both sides must supply structurally corresponding pre-normalization signatures. Values are
/// ordered as the typeck root's non-region generics, its named regions, then every eligible free
/// region occurrence in the flattened signature. The occurrence tail is deliberately not
/// deduplicated.
pub(crate) fn implied_bounds_query_input_values<'tcx>(
    tcx: TyCtxt<'tcx>,
    typeck_root_def_id: LocalDefId,
    named_region_prefix: impl IntoIterator<Item = ty::Region<'tcx>>,
    pre_normalization_inputs_and_output: &[Ty<'tcx>],
    mut map_signature_region: impl FnMut(ty::Region<'tcx>) -> Option<ty::Region<'tcx>>,
) -> SmallVec<[GenericArg<'tcx>; 8]> {
    let mut values: SmallVec<[GenericArg<'tcx>; 8]> =
        GenericArgs::identity_for_item(tcx, typeck_root_def_id)
            .into_iter()
            .filter(|arg| arg.as_region().is_none())
            .collect();
    values.extend(named_region_prefix.into_iter().map(GenericArg::from));

    for ty in pre_normalization_inputs_and_output {
        tcx.for_each_free_region(ty, |region| {
            // Error regions are recovery state, not query inputs with a caller-side counterpart.
            if !region.is_static()
                && !region.is_error()
                && let Some(region) = map_signature_region(region)
            {
                values.push(region.into());
            }
        });
    }

    values
}

/// Makes would-be NLL universal inputs rigid while the query normalizes the signature.
///
/// Named parameter regions remain unchanged because they are already rigid and must stay identical
/// to the regions referenced by the `ParamEnv`. Each erased or inference-region occurrence gets a
/// distinct root-universe placeholder. The caller may map several placeholders back to one NLL
/// universal region, but the query must never infer that equality itself.
fn replace_erased_regions_with_root_placeholders<'tcx>(
    tcx: TyCtxt<'tcx>,
    inputs_and_output: &[Ty<'tcx>],
) -> Vec<Ty<'tcx>> {
    let mut used_root_placeholders = FxHashSet::default();
    for ty in inputs_and_output {
        tcx.for_each_free_region(ty, |region| {
            if let ty::RePlaceholder(placeholder) = region.kind()
                && placeholder.universe == ty::UniverseIndex::ROOT
            {
                used_root_placeholders.insert(placeholder.bound.var);
            }
        });
    }

    let mut next_placeholder = 0;
    inputs_and_output
        .iter()
        .map(|&ty| {
            fold_regions(tcx, ty, |region, _| match region.kind() {
                ty::ReErased | ty::ReVar(_) => {
                    let bound = loop {
                        let bound = ty::BoundRegion {
                            var: ty::BoundVar::from_usize(next_placeholder),
                            kind: ty::BoundRegionKind::Anon,
                        };
                        next_placeholder += 1;
                        if used_root_placeholders.insert(bound.var) {
                            break bound;
                        }
                    };
                    ty::Region::new_placeholder(
                        tcx,
                        ty::PlaceholderRegion::new(ty::UniverseIndex::ROOT, bound),
                    )
                }
                _ => region,
            })
        })
        .collect()
}

fn extend_with_impl_header_bounds<'tcx>(
    tcx: TyCtxt<'tcx>,
    ocx: &ObligationCtxt<'_, 'tcx>,
    defining_ty_def_id: LocalDefId,
    param_env: ty::ParamEnv<'tcx>,
    span: Span,
    outlives_bounds: &mut Vec<OutlivesBound<'tcx>>,
) {
    if !matches!(tcx.def_kind(defining_ty_def_id), DefKind::AssocFn | DefKind::AssocConst { .. }) {
        return;
    }

    for &(ty, _) in tcx.assumed_wf_types(tcx.local_parent(defining_ty_def_id)) {
        // These erased regions belong only to the assumed-WF type; they have no signature NLL
        // universal to which the query response must map them.
        let ty = fold_regions(tcx, ty, |region, _| match region.kind() {
            ty::ReErased => ocx.infcx.next_region_var(RegionVariableOrigin::Misc(span)),
            _ => region,
        });

        let Ok(normalized_ty) = ocx.deeply_normalize(
            &ObligationCause::dummy_with_span(span),
            param_env,
            ty::Unnormalized::new_wip(ty),
        ) else {
            continue;
        };

        // Impl-header implied bounds come from the normalized form only, matching WF checking.
        let region_obligation_start = ocx.infcx.clone_registered_region_obligations().len();
        if let Ok(bounds) = compute_implied_outlives_bounds_from_normalized(
            ocx,
            param_env,
            normalized_ty,
            normalized_ty,
            span,
        ) {
            outlives_bounds.extend(bounds);
            let region_obligations = ocx.infcx.clone_registered_region_obligations();
            extend_implied_bounds_with_registered_region_obligations(
                tcx,
                [normalized_ty],
                region_obligations[region_obligation_start..].iter().cloned(),
                outlives_bounds,
            );
        }
    }
}
