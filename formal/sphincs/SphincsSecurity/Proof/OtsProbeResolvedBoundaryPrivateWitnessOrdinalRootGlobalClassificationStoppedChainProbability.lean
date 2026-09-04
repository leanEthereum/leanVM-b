import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedChain

/-!
# Probability projection for unreachable chain-start observations

The named option event keeps the retained result type opaque while the support invariant is
projected to probability zero.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

def ObservedMaterializedOutput.FirstExistingHiddenChainStartHitAt
  (ordinal : Nat) :
    Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) → Prop
  | none => False
  | some result =>
      SphincsSecurity.Concrete.OtsProbeSimulation.FirstExistingHiddenChainStartHitAt
        result.observations ordinal

attribute [local irreducible] maskedPublishedTreeRoot in
set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_firstExistingHiddenChainStartHitAt_eq_zero
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel ordinal : Nat)
    (table : OtsSecretIndex → HashOutput) :
    Pr[ObservedMaterializedOutput.FirstExistingHiddenChainStartHitAt ordinal |
      observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table] = 0 := by
  apply probEvent_eq_zero
  intro output houtput hevent
  unfold observedMaterializedRetainedRunFromTable at houtput
  rw [mem_support_bind_iff] at houtput
  obtain ⟨rootResult?, hroot, hrest⟩ := houtput
  cases rootResult? with
  | none =>
      simp at hrest
      subst output
      exact hevent
  | some rootResult =>
      rw [mem_support_bind_iff] at hrest
      obtain ⟨restResult?, hrestResult, hreturn⟩ := hrest
      cases restResult? with
      | none =>
          simp at hreturn
          subst output
          exact hevent
      | some restResult =>
          simp only [support_pure, Set.mem_singleton_iff] at hreturn
          subst output
          have hrootInvariants := probeFree_invariants_of_mem_runObservedCleanFromTable
            maskedPublishedTreeRoot [] LazyRevealProbe.State.empty fuel table emptySplitHashCache
            rootResult preservesChainValid_maskedPublishedTreeRoot_true
            (maskedPublishedTreeRoot_probeFree emptySplitHashCache)
            (by intro observation hobservation; simp at hobservation)
            (ChainState.validFor_empty (fun _ => True)) hroot
          have hrestInvariants := observedMaterializedBoundary_chain_invariants parameter
            rootResult.value.1 ftsSecret
            (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩)
            rootResult.observations rootResult.state rootResult.remaining table rootResult.value.2
            restResult hrootInvariants.2 hrootInvariants.1 hrestResult
          exact hrestInvariants.2.not_firstAt ordinal hevent

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampled_firstExistingHiddenChainStartHitAt_eq_zero
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel ordinal : Nat) :
    Pr[ObservedMaterializedOutput.FirstExistingHiddenChainStartHitAt ordinal | do
      let table ← sampleOtsHashTable
      observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table] = 0 := by
  rw [probEvent_bind_eq_tsum (mx := sampleOtsHashTable)]
  apply ENNReal.tsum_eq_zero.2
  intro table
  rw [probEvent_firstExistingHiddenChainStartHitAt_eq_zero]
  simp

end SphincsSecurity.Concrete.OtsProbeSimulation
