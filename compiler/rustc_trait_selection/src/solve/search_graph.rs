use crate::solve::inspect::{self, ProofTreeBuilder};
use crate::solve::{CanonicalResponseExt, FIXPOINT_STEP_LIMIT};
use rustc_infer::infer::InferCtxt;
use rustc_middle::traits::solve::{CanonicalInput, Certainty, QueryResult};
use rustc_middle::ty::TyCtxt;
use rustc_search_graph::{self as sg, Delegate, PathKind, UsageKind};
use rustc_type_ir::solve::MaybeCause;

pub(super) struct SearchGraphDelegate;
pub(super) type SearchGraph<I> = sg::SearchGraph<I, SearchGraphDelegate>;

impl<'tcx> Delegate<SearchGraphDelegate> for TyCtxt<'tcx> {
    const FIXPOINT_STEP_LIMIT: usize = FIXPOINT_STEP_LIMIT;

    type ProofTreeBuilder = ProofTreeBuilder<InferCtxt<'tcx>>;

    fn recursion_limit(self) -> usize {
        self.recursion_limit().0
    }

    fn initial_provisional_result(self, cycle_kind: PathKind, input: Self::Input) -> Self::Result {
        match cycle_kind {
            PathKind::Coinductive => response_no_constraints(self, input, Certainty::Yes),
            PathKind::Inductive => response_no_constraints(self, input, Certainty::overflow(false)),
        }
    }

    fn is_initial_provisional_result(
        self,
        _input: Self::Input,
        result: Self::Result,
    ) -> Option<PathKind> {
        // FIXME(trait-system-refactor-initiative#117): This is currently slightly
        // broken. Add an assert that the result actually matches the initial
        // provisional result once that issue is fixed.
        let r = result.ok().filter(|r| r.has_no_inference_or_external_constraints())?;
        match r.value.certainty {
            Certainty::Yes => Some(PathKind::Coinductive),
            Certainty::Maybe(MaybeCause::Overflow { suggest_increasing_limit: false }) => {
                Some(PathKind::Inductive)
            }
            _ => None,
        }
    }

    fn reached_fixpoint(
        self,
        input: Self::Input,
        usage_kind: UsageKind,
        provisional_result: Option<Self::Result>,
        result: Self::Result,
    ) -> bool {
        if is_response_no_constraints(result, |c| matches!(c, Certainty::Maybe(_))) {
            // If computing this goal results in ambiguity with no constraints,
            // we do not rerun it. It's incredibly difficult to get a different
            // response in the next iteration in this case. These changes would
            // likely either be caused by incompleteness or can change the maybe
            // cause from ambiguity to overflow. Returning ambiguity always
            // preserves soundness and completeness even if the goal is be known
            // to succeed or fail.
            //
            // This prevents exponential blowup affecting multiple major crates.
            true
        } else if let Some(r) = provisional_result {
            // If we already have a provisional result for this cycle head from
            // a previous iteration, simply check for a fixpoint.
            r == result
        } else {
            match self.is_initial_provisional_result(input, result) {
                Some(path_kind) => usage_kind == UsageKind::Single(path_kind),
                None => false,
            }
        }
    }

    fn on_stack_overflow(
        self,
        inspect: &mut ProofTreeBuilder<InferCtxt<'tcx>>,
        input: Self::Input,
    ) -> Self::Result {
        inspect.canonical_goal_evaluation_kind(inspect::WipCanonicalGoalEvaluationKind::Overflow);
        response_no_constraints(self, input, Certainty::overflow(true))
    }

    fn on_fixpoint_overflow(self, input: Self::Input) -> Self::Result {
        response_no_constraints(self, input, Certainty::overflow(false))
    }

    fn step_kind(self, input: Self::Input) -> PathKind {
        if input.value.goal.predicate.is_coinductive(self) {
            PathKind::Coinductive
        } else {
            PathKind::Inductive
        }
    }
}

fn response_no_constraints<'tcx>(
    tcx: TyCtxt<'tcx>,
    input: CanonicalInput<'tcx>,
    certainty: Certainty,
) -> QueryResult<'tcx> {
    Ok(super::response_no_constraints_raw(tcx, input.max_universe, input.variables, certainty))
}

fn is_response_no_constraints<'tcx>(
    result: QueryResult<'tcx>,
    check_certainty: impl FnOnce(Certainty) -> bool,
) -> bool {
    result.is_ok_and(|response| {
        response.has_no_inference_or_external_constraints()
            && check_certainty(response.value.certainty)
    })
}
