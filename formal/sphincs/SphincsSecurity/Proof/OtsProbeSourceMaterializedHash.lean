import SphincsSecurity.Proof.OtsProbeSourceChargeComposition

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem liveMaterializedProbeAllowance_query_bind
    (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    liveMaterializedProbeAllowance ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) input) :
      OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) context fuel table =
      (if DeferredCompletable table context then
        materializedProbeInputAllowance table context input +
          ∑' result, Pr[= result | runResolvedFromTable context fuel table
            (liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) input))] *
            match result with
            | none => 0
            | some result => liveMaterializedProbeAllowance (next result.value) result.context result.remaining result.table
      else 0) := rfl

theorem liveMaterializedProbeAllowance_bind
    (left : OracleComp (LazyRevealProbe.World Coordinate) α) (next : α → OracleComp (LazyRevealProbe.World Coordinate) β)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    liveMaterializedProbeAllowance (left >>= next) context fuel table =
      liveMaterializedProbeAllowance left context fuel table +
        ∑' result, Pr[= result | runResolvedFromTable context fuel table left] *
          sourceContinuationCharge materializedProbeInputAllowance next result :=
  liveSourceCharge_bind materializedProbeInputAllowance left next context fuel table hconsistent hstarts

theorem liveMaterializedProbeAllowance_eq_zero_of_probeFree
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hfree : computation.IsQueryBoundP LazyRevealProbe.IsProbe 0) :
    liveMaterializedProbeAllowance computation context fuel table = 0 := by
  induction computation using OracleComp.inductionOn generalizing context fuel table with
  | pure value => rfl
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hfree
      have hinput : ¬LazyRevealProbe.IsProbe input := by simpa using hfree.1
      have hnext : ∀ reply, (next reply).IsQueryBoundP LazyRevealProbe.IsProbe 0 := by
        intro reply
        simpa using hfree.2 reply
      have hweight : materializedProbeInputAllowance table context input = 0 := by
        cases input <;> simp_all [LazyRevealProbe.IsProbe, materializedProbeInputAllowance]
      rw [liveMaterializedProbeAllowance_query_bind]
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

theorem liveMaterializedProbeAllowance_bind_of_tail_probeFree
    (left : OracleComp (LazyRevealProbe.World Coordinate) α)
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hfree : ∀ value, (next value).IsQueryBoundP LazyRevealProbe.IsProbe 0) :
    liveMaterializedProbeAllowance (left >>= next) context fuel table =
      liveMaterializedProbeAllowance left context fuel table := by
  rw [liveMaterializedProbeAllowance_bind left next context fuel table hconsistent hstarts]
  suffices hzero : (∑' result, Pr[= result | runResolvedFromTable context fuel table left] *
      sourceContinuationCharge materializedProbeInputAllowance next result) = 0 by rw [hzero, add_zero]
  apply ENNReal.tsum_eq_zero.mpr
  intro result
  cases result with
  | none => simp [sourceContinuationCharge]
  | some result =>
      change _ * liveMaterializedProbeAllowance (next result.value) result.context result.remaining result.table = 0
      rw [liveMaterializedProbeAllowance_eq_zero_of_probeFree
        (next result.value) result.context result.remaining result.table (hfree result.value), mul_zero]

theorem materializedAllowance_executeCandidate
    (candidate : Option Probe) (cache : SplitHashCache)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    liveMaterializedProbeAllowance ((executeCandidate? candidate).run cache) context fuel table =
      if DeferredCompletable table context then materializedCandidateAllowance table context candidate else 0 := by
  cases candidate with
  | none => simp [executeCandidate?, liveMaterializedProbeAllowance, liveSourceCharge, materializedCandidateAllowance]
  | some candidate =>
      simp [executeCandidate?, probe, LazyRevealProbe.probeQuery, liveMaterializedProbeAllowance, liveSourceCharge,
        map_eq_bind_pure_comp]
      split_ifs
      · calc
          _ = materializedProbeInputAllowance table context (.probe candidate.coordinate candidate.candidate) + 0 := by
            congr 1
            apply ENNReal.tsum_eq_zero.mpr
            intro result
            cases result <;> simp
          _ = _ := add_zero _
      · rfl

theorem materializedAllowance_probingHashQueryAfterPlan
    (parameter : PublicParameter) (input : HashInput) (plan : PlannedHashQuery)
    (cache : SplitHashCache) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    liveMaterializedProbeAllowance ((probingHashQueryAfterPlan parameter input plan).run cache) context fuel table =
      if DeferredCompletable table context then materializedCandidateAllowance table context plan.candidate? else 0 := by
  unfold probingHashQueryAfterPlan executePlannedHashQuery
  rw [StateT.run_bind, liveMaterializedProbeAllowance_bind_of_tail_probeFree _ _ context fuel table hconsistent hstarts]
  · exact materializedAllowance_executeCandidate plan.candidate? cache context fuel table
  · intro result
    cases plan.action with
    | ordinary => exact splitHashQuery_probeFree _ result.2
    | resolve coordinate => exact resolveKnownInput_probeFree parameter coordinate input result.2

theorem materializedAllowance_probingHashQuery
    (parameter : PublicParameter) (input : HashInput)
    (cache : SplitHashCache) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    liveMaterializedProbeAllowance ((probingHashQuery parameter input).run cache) context fuel table =
      if DeferredCompletable table context then materializedCandidateAllowance table context
        (purePlanProbingHashQuery parameter input context.state).candidate? else 0 := by
  rw [probingHashQuery_eq_plan_then_afterPlan, StateT.run_bind,
    liveMaterializedProbeAllowance_bind _ _ context fuel table hconsistent hstarts,
    liveMaterializedProbeAllowance_eq_zero_of_probeFree _ context fuel table (planProbingHashQuery_probeFree parameter input cache),
    zero_add, runResolved_planProbingHashQuery parameter input context.state context fuel table cache rfl,
    tsum_probOutput_pure_mul]
  exact materializedAllowance_probingHashQueryAfterPlan parameter input _ cache context fuel table hconsistent hstarts

end SphincsSecurity.Concrete.OtsProbeSimulation
