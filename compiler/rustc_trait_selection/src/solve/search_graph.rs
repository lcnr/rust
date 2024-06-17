use crate::solve::inspect::{self, ProofTreeBuilder};
use crate::solve::{CanonicalResponseExt, FIXPOINT_STEP_LIMIT};
use rustc_infer::infer::InferCtxt;
use rustc_middle::traits::solve::{CanonicalInput, Certainty, QueryResult};
use rustc_middle::ty::TyCtxt;
use rustc_search_graph::{self as sg, CycleKind, Delegate, UsageKind};

pub(super) struct SearchGraphDelegate;
pub(super) type SearchGraph<I> = sg::SearchGraph<I, SearchGraphDelegate>;

impl<'tcx> Delegate<SearchGraphDelegate> for TyCtxt<'tcx> {
    const FIXPOINT_STEP_LIMIT: usize = FIXPOINT_STEP_LIMIT;

    type ProofTreeBuilder = ProofTreeBuilder<InferCtxt<'tcx>>;

    fn recursion_limit(self) -> usize {
        self.recursion_limit().0
    }

    fn initial_provisional_result(self, cycle_kind: CycleKind, input: Self::Input) -> Self::Result {
        match cycle_kind {
            CycleKind::Coinductive => response_no_constraints(self, input, Certainty::Yes),
            CycleKind::Inductive => {
                response_no_constraints(self, input, Certainty::overflow(false))
            }
        }
    }

    fn reached_fixpoint(
        self,
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
        } else if usage_kind == UsageKind::Single(CycleKind::Coinductive) {
            // If we only used this cycle head with inductive cycles, and the final
            // response is trivially true, no need to rerun.
            is_response_no_constraints(result, |c| c == Certainty::Yes)
        } else {
            // No need to check exclusively inductive cycles, as these are covered by the
            // general overflow branch above.
            false
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

    fn step_is_coinductive(self, input: Self::Input) -> bool {
        input.value.goal.predicate.is_coinductive(self)
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
