import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeLiveGameCharge
import SphincsSecurity.Proof.OtsProbeNativeChainBound
import SphincsSecurity.Proof.OtsProbeNativeMissingStructuralCharge
import SphincsSecurity.Proof.OtsProbeNativeQueryTraceProjection
import SphincsSecurity.Proof.OtsProbeNativeStartCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem expected_nativeStartTraceCharge_eq_liveAllowance
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    (∑' trace, Pr[= trace | nativeChainTraceAfterRoot targets parameter table ftsSecret fuel
      (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩)] *
      canonicalTraceCharge (nativeStartCharge parameter table) trace.2) =
      liveStartProbeAllowance (nativeChronologicalRetainedComputation adversary parameter ftsSecret)
        (ensuredInitialContext targets) fuel table := by
  unfold nativeChainTraceAfterRoot nativeChronologicalRetainedComputation
  rw [tsum_probOutput_bind_mul, liveStartProbeAllowance_bind _ _ (ensuredInitialContext targets) fuel table
    (ensuredInitialContext_valid targets).valuesConsistent
    (startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable targets table)),
    liveStartProbeAllowance_eq_zero_of_probeFree _ _ fuel table (maskedPublishedTreeRoot_probeFree emptySplitHashCache), zero_add]
  apply tsum_congr
  intro root
  by_cases hroot : root ∈ support (runResolvedFromTable (ensuredInitialContext targets) fuel table
      (maskedPublishedTreeRoot.run emptySplitHashCache))
  · cases root with
    | none => simp [startContinuationAllowance, canonicalTraceCharge]
    | some root =>
        have hcore := resolvedCore_of_mem_runResolvedFromTable _ (ensuredInitialContext targets) fuel table root
          (ensuredInitialContext_valid targets).valuesConsistent
          (startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable targets table)) hroot
        simp only [startContinuationAllowance, hcore.1, expectedNativeTraceCharge_eq]
        rw [startAllowance_chronological_eq_nativeCharge parameter root.value.1 ftsSecret _ root.context root.remaining table root.value.2
          hcore.2.1 hcore.2.2]
  · simp [probOutput_eq_zero_of_not_mem_support hroot]

theorem expected_nativeStructuralTraceCharge_eq_liveAllowance
    (targets : Finset Position) (target : Position) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    (∑' trace, Pr[= trace | nativeChainTraceAfterRoot targets parameter table ftsSecret fuel
      (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩)] *
      canonicalTraceCharge (nativeMissingStructuralCharge target parameter table) trace.2) =
      privateLiveMissingProbeAllowance target (nativeChronologicalRetainedComputation adversary parameter ftsSecret)
        (ensuredInitialContext targets) fuel table := by
  unfold nativeChainTraceAfterRoot nativeChronologicalRetainedComputation
  rw [tsum_probOutput_bind_mul, privateLiveMissingProbeAllowance_bind target _ _ (ensuredInitialContext targets) fuel table
    (ensuredInitialContext_valid targets).valuesConsistent
    (startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable targets table)),
    privateLiveMissingProbeAllowance_eq_zero_of_probeFree target _ _ fuel table (maskedPublishedTreeRoot_probeFree emptySplitHashCache), zero_add]
  apply tsum_congr
  intro root
  by_cases hroot : root ∈ support (runResolvedFromTable (ensuredInitialContext targets) fuel table
      (maskedPublishedTreeRoot.run emptySplitHashCache))
  · cases root with
    | none => simp [privateMissingContinuationAllowance, canonicalTraceCharge]
    | some root =>
        have hcore := resolvedCore_of_mem_runResolvedFromTable _ (ensuredInitialContext targets) fuel table root
          (ensuredInitialContext_valid targets).valuesConsistent
          (startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable targets table)) hroot
        simp only [privateMissingContinuationAllowance, hcore.1, expectedNativeTraceCharge_eq]
        rw [privateMissingAllowance_chronological_eq_nativeCharge target parameter root.value.1 ftsSecret _ root.context root.remaining table root.value.2
          hcore.2.1 hcore.2.2]
  · simp [probOutput_eq_zero_of_not_mem_support hroot]

theorem expected_nativeMissingTraceCharges_eq_liveAllowances
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    (∑' trace, Pr[= trace | nativeChainTraceAfterRoot targets parameter table ftsSecret fuel
      (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩)] *
      (canonicalTraceCharge (nativeStartCharge parameter table) trace.2 +
        ∑ target ∈ targets, canonicalTraceCharge (nativeMissingStructuralCharge target parameter table) trace.2)) =
      liveStartProbeAllowance (nativeChronologicalRetainedComputation adversary parameter ftsSecret) (ensuredInitialContext targets) fuel table +
        ∑ target ∈ targets, privateLiveMissingProbeAllowance target
          (nativeChronologicalRetainedComputation adversary parameter ftsSecret) (ensuredInitialContext targets) fuel table := by
  simp only [mul_add, ENNReal.tsum_add]
  rw [expected_nativeStartTraceCharge_eq_liveAllowance]
  congr 1
  simp only [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro target _
  exact expected_nativeStructuralTraceCharge_eq_liveAllowance targets target adversary parameter table ftsSecret fuel

end SphincsSecurity.Concrete.OtsProbeSimulation
