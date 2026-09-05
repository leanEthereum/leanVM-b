import SphincsSecurity.Proof.OtsProbePrivateMissingComposition

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem privateLiveMissingProbeAllowance_eq_zero_of_probeFree
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hfree : computation.IsQueryBoundP LazyRevealProbe.IsProbe 0) :
    privateLiveMissingProbeAllowance target computation context fuel table = 0 := by
  induction computation using OracleComp.inductionOn generalizing context fuel table with
  | pure value => rfl
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hfree
      have hinput : ¬LazyRevealProbe.IsProbe input := by simpa using hfree.1
      have hnext : ∀ reply, (next reply).IsQueryBoundP LazyRevealProbe.IsProbe 0 := by
        intro reply
        simpa using hfree.2 reply
      have hweight : privateMissingProbeInputAllowance target table context input = 0 := by
        cases input <;> simp_all [LazyRevealProbe.IsProbe, privateMissingProbeInputAllowance, privateProbeInputAllowance]
      rw [privateLiveMissingProbeAllowance_query_bind]
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

theorem privateLiveMissingProbeAllowance_bind_of_tail_probeFree
    (target : Position) (left : OracleComp (LazyRevealProbe.World Coordinate) α)
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hfree : ∀ value, (next value).IsQueryBoundP LazyRevealProbe.IsProbe 0) :
    privateLiveMissingProbeAllowance target (left >>= next) context fuel table =
      privateLiveMissingProbeAllowance target left context fuel table := by
  rw [privateLiveMissingProbeAllowance_bind target left next context fuel table hconsistent hstarts]
  suffices hzero : (∑' result, Pr[= result | runResolvedFromTable context fuel table left] *
      privateMissingContinuationAllowance target next result) = 0 by rw [hzero, add_zero]
  apply ENNReal.tsum_eq_zero.mpr
  intro result
  cases result with
  | none => simp [privateMissingContinuationAllowance]
  | some result =>
      rw [privateMissingContinuationAllowance, privateLiveMissingProbeAllowance_eq_zero_of_probeFree
        target (next result.value) result.context result.remaining result.table (hfree result.value), mul_zero]

noncomputable def privateMissingCandidateAllowance (target : Position) (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) : Option Probe → ENNReal
  | none => 0
  | some candidate => privateMissingProbeInputAllowance target table context (.probe candidate.coordinate candidate.candidate)

theorem privateMissingAllowance_executeCandidate
    (target : Position) (candidate : Option Probe) (cache : SplitHashCache)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    privateLiveMissingProbeAllowance target ((executeCandidate? candidate).run cache) context fuel table =
      if DeferredCompletable table context then privateMissingCandidateAllowance target table context candidate else 0 := by
  cases candidate with
  | none => simp [executeCandidate?, privateLiveMissingProbeAllowance, privateMissingCandidateAllowance]
  | some candidate =>
      simp [executeCandidate?, probe, LazyRevealProbe.probeQuery, privateLiveMissingProbeAllowance,
        privateMissingCandidateAllowance, map_eq_bind_pure_comp]
      split_ifs
      · calc
          _ = privateMissingProbeInputAllowance target table context (.probe candidate.coordinate candidate.candidate) + 0 := by
            congr 1
            apply ENNReal.tsum_eq_zero.mpr
            intro result
            cases result <;> simp
          _ = _ := add_zero _
      · rfl

theorem privateMissingAllowance_probingHashQueryAfterPlan
    (target : Position) (parameter : PublicParameter) (input : HashInput) (plan : PlannedHashQuery)
    (cache : SplitHashCache) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    privateLiveMissingProbeAllowance target ((probingHashQueryAfterPlan parameter input plan).run cache) context fuel table =
      if DeferredCompletable table context then privateMissingCandidateAllowance target table context plan.candidate? else 0 := by
  unfold probingHashQueryAfterPlan executePlannedHashQuery
  rw [StateT.run_bind, privateLiveMissingProbeAllowance_bind_of_tail_probeFree target _ _ context fuel table hconsistent hstarts]
  · exact privateMissingAllowance_executeCandidate target plan.candidate? cache context fuel table
  · intro result
    cases plan.action with
    | ordinary => exact splitHashQuery_probeFree _ result.2
    | resolve coordinate => exact resolveKnownInput_probeFree parameter coordinate input result.2

theorem privateMissingAllowance_probingHashQuery
    (target : Position) (parameter : PublicParameter) (input : HashInput)
    (cache : SplitHashCache) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    privateLiveMissingProbeAllowance target ((probingHashQuery parameter input).run cache) context fuel table =
      if DeferredCompletable table context then privateMissingCandidateAllowance target table context
        (purePlanProbingHashQuery parameter input context.state).candidate? else 0 := by
  rw [probingHashQuery_eq_plan_then_afterPlan, StateT.run_bind,
    privateLiveMissingProbeAllowance_bind target _ _ context fuel table hconsistent hstarts,
    privateLiveMissingProbeAllowance_eq_zero_of_probeFree target _ context fuel table (planProbingHashQuery_probeFree parameter input cache),
    zero_add, runResolved_planProbingHashQuery parameter input context.state context fuel table cache rfl,
    tsum_probOutput_pure_mul]
  exact privateMissingAllowance_probingHashQueryAfterPlan target parameter input _ cache context fuel table hconsistent hstarts

end SphincsSecurity.Concrete.OtsProbeSimulation
