use rustc_middle::query::Providers;
use rustc_middle::ty::TyCtxt;

mod delegate;
mod fulfill;
pub mod inspect;
mod normalize;
mod select;

pub use delegate::{InferCtxtDelegateExt, SolverDelegate};
pub use fulfill::{FulfillmentCtxt, NextSolverError, StalledOnCoroutines};
pub(crate) use normalize::deeply_normalize_for_diagnostics;
pub use normalize::{
    deeply_normalize, deeply_normalize_with_skipped_universes,
    deeply_normalize_with_skipped_universes_and_ambiguous_coroutine_goals,
};
pub use rustc_next_trait_solver::canonical;
pub use rustc_next_trait_solver::resolve::eager_resolve_vars;
pub use rustc_next_trait_solver::solve::*;
pub use select::InferCtxtSelectExt;

fn evaluate_root_goal_for_proof_tree_raw<'tcx>(
    tcx: TyCtxt<'tcx>,
    canonical_input: CanonicalInput<TyCtxt<'tcx>>,
) -> (QueryResult<TyCtxt<'tcx>>, &'tcx inspect::Probe<TyCtxt<'tcx>>) {
    evaluate_root_goal_for_proof_tree_raw_provider::<SolverDelegate<'tcx>, TyCtxt<'tcx>>(
        tcx,
        canonical_input,
    )
}

pub fn provide(providers: &mut Providers) {
    *providers = Providers { evaluate_root_goal_for_proof_tree_raw, ..*providers };
}
