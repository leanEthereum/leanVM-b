import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeStartAllowanceComposition

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem liveStartProbeAllowance_eq_zero_of_probeFree
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hfree : computation.IsQueryBoundP LazyRevealProbe.IsProbe 0) :
    liveStartProbeAllowance computation context fuel table = 0 := by
  induction computation using OracleComp.inductionOn generalizing context fuel table with
  | pure value => rfl
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hfree
      have hinput : ¬LazyRevealProbe.IsProbe input := by simpa using hfree.1
      have hnext : ∀ reply, (next reply).IsQueryBoundP LazyRevealProbe.IsProbe 0 := by
        intro reply
        simpa using hfree.2 reply
      have hweight : startProbeInputAllowance table context input = 0 := by
        cases input <;> simp_all [LazyRevealProbe.IsProbe, startProbeInputAllowance]
      rw [liveStartProbeAllowance_query_bind]
      by_cases hcomplete : DeferredCompletable table context
      · rw [if_pos hcomplete, hweight, zero_add]
        apply ENNReal.tsum_eq_zero.mpr
        intro result
        cases result with
        | none => simp
        | some result =>
            dsimp only
            rw [ih result.value result.context result.remaining result.table (hnext result.value), mul_zero]
      · rw [if_neg hcomplete]

theorem liveStartProbeAllowance_bind_of_tail_probeFree
    (left : OracleComp (LazyRevealProbe.World Coordinate) α)
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hfree : ∀ value, (next value).IsQueryBoundP LazyRevealProbe.IsProbe 0) :
    liveStartProbeAllowance (left >>= next) context fuel table =
      liveStartProbeAllowance left context fuel table := by
  rw [liveStartProbeAllowance_bind left next context fuel table hconsistent hstarts]
  suffices hzero : (∑' result, Pr[= result | runResolvedFromTable context fuel table left] *
      startContinuationAllowance next result) = 0 by rw [hzero, add_zero]
  apply ENNReal.tsum_eq_zero.mpr
  intro result
  cases result with
  | none => simp [startContinuationAllowance]
  | some result =>
      rw [startContinuationAllowance, liveStartProbeAllowance_eq_zero_of_probeFree
        (next result.value) result.context result.remaining result.table (hfree result.value), mul_zero]

theorem startAllowance_executeCandidate
    (candidate : Option Probe) (cache : SplitHashCache)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    liveStartProbeAllowance ((executeCandidate? candidate).run cache) context fuel table =
      if DeferredCompletable table context then unresolvedStartCandidateAllowance table context candidate else 0 := by
  cases candidate with
  | none => simp [executeCandidate?, liveStartProbeAllowance, unresolvedStartCandidateAllowance]
  | some candidate =>
      simp [executeCandidate?, probe, LazyRevealProbe.probeQuery, liveStartProbeAllowance,
        unresolvedStartCandidateAllowance, startProbeInputAllowance, map_eq_bind_pure_comp]
      split_ifs
      · calc
          _ = startProbeInputAllowance table context (.probe candidate.coordinate candidate.candidate) + 0 := by
            congr 1
            apply ENNReal.tsum_eq_zero.mpr
            intro result
            cases result <;> simp
          _ = _ := add_zero _
      · rfl

theorem startAllowance_probingHashQueryAfterPlan
    (parameter : PublicParameter) (input : HashInput) (plan : PlannedHashQuery)
    (cache : SplitHashCache) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    liveStartProbeAllowance ((probingHashQueryAfterPlan parameter input plan).run cache) context fuel table =
      if DeferredCompletable table context then unresolvedStartCandidateAllowance table context plan.candidate? else 0 := by
  unfold probingHashQueryAfterPlan executePlannedHashQuery
  rw [StateT.run_bind, liveStartProbeAllowance_bind_of_tail_probeFree _ _ context fuel table hconsistent hstarts]
  · exact startAllowance_executeCandidate plan.candidate? cache context fuel table
  · intro result
    cases plan.action with
    | ordinary => exact splitHashQuery_probeFree _ result.2
    | resolve coordinate => exact resolveKnownInput_probeFree parameter coordinate input result.2

theorem startAllowance_probingHashQuery
    (parameter : PublicParameter) (input : HashInput)
    (cache : SplitHashCache) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    liveStartProbeAllowance ((probingHashQuery parameter input).run cache) context fuel table =
      if DeferredCompletable table context then unresolvedStartCandidateAllowance table context
        (purePlanProbingHashQuery parameter input context.state).candidate? else 0 := by
  rw [probingHashQuery_eq_plan_then_afterPlan, StateT.run_bind,
    liveStartProbeAllowance_bind _ _ context fuel table hconsistent hstarts,
    liveStartProbeAllowance_eq_zero_of_probeFree _ context fuel table (planProbingHashQuery_probeFree parameter input cache),
    zero_add, runResolved_planProbingHashQuery parameter input context.state context fuel table cache rfl,
    tsum_probOutput_pure_mul]
  exact startAllowance_probingHashQueryAfterPlan parameter input _ cache context fuel table hconsistent hstarts

end SphincsSecurity.Concrete.OtsProbeSimulation
