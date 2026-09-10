import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeHistoryCandidateSampling
import SphincsSecurity.Proof.OtsProbeHistoryOuterPrefix
import SphincsSecurity.Proof.OtsProbeNativeRootHashAction
import SphincsSecurity.Proof.OtsProbeNativeRootInputObservation
import SphincsSecurity.Proof.OtsProbeNativeRootProbe

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem NativeRootContextRel.afterCandidate
    {target : Position} {before after : HashOutput} {left right : DeferredContext}
    (h : NativeRootContextRel target before after left right) (candidate : Option Probe)
    (hsafe : ∀ value, candidate = some value →
      ¬IsPrivateValueExposure target before after (.probe value.coordinate value.candidate)) :
    NativeRootContextRel target before after (afterCandidateContext left candidate) (afterCandidateContext right candidate) := by
  cases candidate with
  | none => exact h
  | some candidate =>
      simp only [afterCandidateContext, ← h.revealed_eq]
      by_cases hrevealed : candidate.coordinate ∈ left.state.revealed
      · rw [if_pos hrevealed, if_pos hrevealed]
        exact h
      · rw [if_neg hrevealed, if_neg hrevealed]
        exact h.addPending candidate.coordinate candidate.candidate (hsafe candidate rfl)

theorem relTriple_nativeRoot_probingHashQueryAfterPlan_of_safe
    (parameter : PublicParameter) (target : Position) (before after : HashOutput) (input : HashInput) (plan : PlannedHashQuery)
    (left right : DeferredContext) (hcontext : NativeRootContextRel target before after left right)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (leftCache rightCache : SplitHashCache)
    (hcache : RootHiddenCacheRel target before after leftCache rightCache)
    (hprobe : ∀ candidate, plan.candidate? = some candidate →
      ¬IsPrivateValueExposure target before after (.probe candidate.coordinate candidate.candidate))
    (haction : NativeRootActionSafe parameter target input left right plan.action) :
    RelTriple
      (runResolvedFromTable left fuel table ((probingHashQueryAfterPlan parameter input plan).run leftCache))
      (runResolvedFromTable right fuel table ((probingHashQueryAfterPlan parameter input plan).run rightCache))
      (NativeRootSameRel target before after) := by
  unfold probingHashQueryAfterPlan executePlannedHashQuery
  rw [StateT.run_bind, StateT.run_bind, runResolvedFromTable_bind, runResolvedFromTable_bind]
  cases fuel with
  | zero =>
      rw [runResolvedFromTable_executeCandidate_zero, runResolvedFromTable_executeCandidate_zero]
      by_cases hsome : plan.candidate?.isSome
      · rw [if_pos hsome, if_pos hsome]
        exact relTriple_pure_pure trivial
      · rw [if_neg hsome, if_neg hsome]
        simp only [pure_bind]
        exact relTriple_nativeRoot_hashAction_of_safe parameter target before after input plan.action
          left right hcontext 0 table leftCache rightCache hcache haction
  | succ fuel =>
      rw [runResolvedFromTable_executeCandidate_positive, runResolvedFromTable_executeCandidate_positive]
      simp only [pure_bind]
      exact relTriple_nativeRoot_hashAction_of_safe parameter target before after input plan.action
        (afterCandidateContext left plan.candidate?) (afterCandidateContext right plan.candidate?)
        (hcontext.afterCandidate plan.candidate? hprobe) _ table leftCache rightCache hcache
        (haction.of_values_eq (afterCandidateContext_values left plan.candidate?) (afterCandidateContext_values right plan.candidate?))

theorem relTriple_nativeRoot_probingHashQuery_of_safe
    (parameter : PublicParameter) (target : Position) (before after : HashOutput) (input : HashInput)
    (left right : DeferredContext) (hcontext : NativeRootContextRel target before after left right)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (leftCache rightCache : SplitHashCache)
    (hcache : RootHiddenCacheRel target before after leftCache rightCache)
    (hprobe : ∀ candidate, (purePlanProbingHashQuery parameter input left.state).candidate? = some candidate →
      ¬IsPrivateValueExposure target before after (.probe candidate.coordinate candidate.candidate))
    (haction : NativeRootActionSafe parameter target input left right
      (purePlanProbingHashQuery parameter input left.state).action) :
    RelTriple
      (runResolvedFromTable left fuel table ((probingHashQuery parameter input).run leftCache))
      (runResolvedFromTable right fuel table ((probingHashQuery parameter input).run rightCache))
      (NativeRootSameRel target before after) := by
  rw [runResolved_probingHashQuery_eq_afterPlan, runResolved_probingHashQuery_eq_afterPlan,
    ← purePlanProbingHashQuery_eq_of_nativeRootContextRel hcontext]
  exact relTriple_nativeRoot_probingHashQueryAfterPlan_of_safe parameter target before after input _
    left right hcontext fuel table leftCache rightCache hcache hprobe haction

end SphincsSecurity.Concrete.OtsProbeSimulation
