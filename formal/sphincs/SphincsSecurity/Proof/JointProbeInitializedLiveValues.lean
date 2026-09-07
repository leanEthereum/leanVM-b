import SphincsSecurity.Proof.JointProbeLiveValueErasure
import SphincsSecurity.Proof.JointProbeOriginalRetainedFailureComparison

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.maskedPublishedTreeRoot OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

private theorem expected_evalDist_eq (computation : ProbComp α) (cost : α → ENNReal) :
    (∑' value, Pr[= value | evalDist computation] * cost value) = ∑' value, Pr[= value | computation] * cost value := rfl

theorem probEvent_initialized_live_value_le_fullShared
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : Digest → OracleComp (OracleWorld + SigningSpec) α) (event : α → Prop) (q fuel : Nat)
    (hbound : ∀ root, (computation root).IsQueryBoundP OtsProbeSimulation.IsOuterHash q) :
    (∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
      Pr[fun result => event result.1.2.1.1 ∧ result.1.2.2 = false ∧ result.2 = false |
        runWithFailure exception parameter initial.2.1 otsTable ftsTable (computation initial.2.1)
          initial.1 initial.2.2 false initial.1.isNone]) ≤
    Pr[JointReturned (fun value => event value.1) | AdaptiveRevealProbe.runDetailed ftsTable AdaptiveRevealProbe.State.empty q
      (runJointResolved ((jointSourceNativeBlock OtsProbeSimulation.maskedPublishedTreeRoot >>= fun root =>
        jointSourceComputation parameter root (computation root)).run (OtsProbeSimulation.emptySplitHashCache, emptySplitHashCache))
        (OtsProbeSimulation.ensuredInitialContext ∅) fuel otsTable)] := by
  let continuation := fun root => jointSourceComputation parameter root (computation root)
  rw [initializeRoot, tsum_probOutput_map_mul,
    runDetailed_jointResolved_bind_probeFree ftsTable AdaptiveRevealProbe.State.empty q
      (jointSourceNativeBlock OtsProbeSimulation.maskedPublishedTreeRoot) continuation
      (OtsProbeSimulation.ensuredInitialContext ∅) fuel otsTable (OtsProbeSimulation.emptySplitHashCache, emptySplitHashCache)
      (runJointResolved_nativeBlock_probeFree _ _ _ _ _), probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' raw, Pr[= raw | (rootCoupling parameter otsTable ftsTable q fuel).1] *
        Pr[JointReturned (fun value => event value.1) | resumeJointResolved ftsTable q continuation raw.1] := by
      apply ENNReal.tsum_le_tsum
      intro raw
      by_cases hr : raw ∈ support (rootCoupling parameter otsTable ftsTable q fuel).1
      · apply mul_le_mul' le_rfl
        have hs := rootCoupling_support parameter otsTable ftsTable q fuel raw hr
        dsimp only
        cases hf : rootFrame otsTable q raw.1 with
        | none =>
            simp only [Option.isNone_none]
            rw [probEvent_runWithFailure_live_failed_eq_zero]
            exact zero_le
        | some frame =>
            rw [resumeJointResolved_eq_of_rootFrame parameter otsTable ftsTable q continuation frame raw.2 raw.1 hs.1 hf]
            have hi : (some frame, raw.2) ∈ support (initializeRoot parameter otsTable ftsTable q fuel) := by
              rw [initializeRoot, support_map]
              exact ⟨raw, hr, by simp [hf]⟩
            have hv := initializeRoot_valid parameter otsTable ftsTable q fuel (some frame, raw.2) hi frame rfl
            apply probEvent_runWithFailure_live_value_le_fullShared exception parameter raw.2.1 otsTable ftsTable
              (computation raw.2.1) event frame raw.2.2 hv.2
            rw [hv.1.1]
            exact hbound raw.2.1
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ = _ := by
      have hm := tsum_probOutput_map_mul (rootCoupling parameter otsTable ftsTable q fuel).1 Prod.fst
        (fun result => Pr[JointReturned (fun value => event value.1) | resumeJointResolved ftsTable q continuation result])
      rw [(rootCoupling parameter otsTable ftsTable q fuel).2.map_fst] at hm
      exact hm.symm.trans (expected_evalDist_eq (sharedRoot otsTable ftsTable q fuel) _)

theorem probEvent_sampled_initialized_live_value_le_erasedHistory
    (exception : (OtsSecretIndex → HashOutput) → QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (ftsTable : Coordinate → Digest)
    (computation : Digest → OracleComp (OracleWorld + SigningSpec) α) (event : α → Prop) (q fuel : Nat)
    (hbound : ∀ root, (computation root).IsQueryBoundP OtsProbeSimulation.IsOuterHash q) :
    (∑' otsTable, Pr[= otsTable | OtsProbeSimulation.sampleOtsHashTable] *
      ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
        Pr[fun result => event result.1.2.1.1 ∧ result.1.2.2 = false ∧ result.2 = false |
          runWithFailure (exception otsTable) parameter initial.2.1 otsTable ftsTable (computation initial.2.1)
            initial.1 initial.2.2 false initial.1.isNone]) ≤
    Pr[JointHistoryReturned (fun value => event value.1) | AdaptiveRevealProbe.runDetailed ftsTable AdaptiveRevealProbe.State.empty q
      (runJointErasedHistory ((jointSourceNativeBlock OtsProbeSimulation.maskedPublishedTreeRoot >>= fun root =>
        jointSourceComputation parameter root (computation root)).run (OtsProbeSimulation.emptySplitHashCache, emptySplitHashCache))
        (OtsProbeSimulation.ensuredInitialContext ∅) 0 [])] := by
  let source := ((jointSourceNativeBlock OtsProbeSimulation.maskedPublishedTreeRoot >>= fun root =>
    jointSourceComputation parameter root (computation root)).run (OtsProbeSimulation.emptySplitHashCache, emptySplitHashCache))
  calc
    _ ≤ ∑' otsTable, Pr[= otsTable | OtsProbeSimulation.sampleOtsHashTable] *
        Pr[JointReturned (fun value => event value.1) | AdaptiveRevealProbe.runDetailed ftsTable AdaptiveRevealProbe.State.empty q
          (runJointResolved source (OtsProbeSimulation.ensuredInitialContext ∅) fuel otsTable)] := by
      apply ENNReal.tsum_le_tsum
      intro otsTable
      exact mul_le_mul' le_rfl
        (probEvent_initialized_live_value_le_fullShared (exception otsTable) parameter otsTable ftsTable computation event q fuel hbound)
    _ ≤ _ := probEvent_sampled_jointReturned_le_erasedHistory ∅ source (fun value => event value.1) ftsTable AdaptiveRevealProbe.State.empty q fuel

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
