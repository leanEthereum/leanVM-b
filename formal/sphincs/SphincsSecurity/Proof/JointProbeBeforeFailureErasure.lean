import SphincsSecurity.Proof.JointProbeErasedQueryPrefixes
import SphincsSecurity.Proof.JointProbeInitializedLiveValues
import SphincsSecurity.Proof.JointProbeBeforeFailurePrefixes
import SphincsSecurity.Proof.SecuritySampledBeforeSharedFailure

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.maskedPublishedTreeRoot OtsProbeSimulation.sampleOtsHashTable
attribute [local irreducible] JointOriginal.initializeRoot JointOriginal.liveQueryPrefixProbability JointOriginal.expectedBeforeFailureOuterCharge
set_option backward.isDefEq.respectTransparency false

noncomputable def jointSourceRetainedBeforeQuery (adversary : Adversary) (parameter : PublicParameter) (q : Nat)
    (select : (OracleWorld + SigningSpec).Domain → Prop) (ordinal : Nat) : JointSource Bool :=
  jointSourceNativeBlock OtsProbeSimulation.maskedPublishedTreeRoot >>= fun root =>
    jointSourceComputation parameter root (beforeQueryOccurrence select (JointOriginal.retainedComputation adversary parameter root q) ordinal)

theorem tsum_raw_retainedPrefix_eq_observer
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q : Nat)
    (select : (OracleWorld + SigningSpec).Domain → Prop) :
    (∑' ordinal, rawSourceEventProbability table (jointSourceRetainedBeforeQuery adversary parameter q select ordinal) (fun value => value = true)
      AdaptiveRevealProbe.State.empty q (OtsProbeSimulation.ensuredInitialContext ∅) 0 []
        (OtsProbeSimulation.emptySplitHashCache, emptySplitHashCache)) =
      expectedJointRetainedCharge adversary parameter table q (fun input _ _ _ _ => if select input then 1 else 0) := by
  unfold jointSourceRetainedBeforeQuery
  simp_rw [rawSourceEventProbability_bind table (jointSourceNativeBlock OtsProbeSimulation.maskedPublishedTreeRoot) _
    (liftNativeBlock OtsProbeSimulation.maskedPublishedTreeRoot) (runJointErasedHistory_nativeBlock _)]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  rw [
    AdaptiveRevealProbe.runRaw_eq_detailed_of_probeFree table AdaptiveRevealProbe.State.empty q _
      (liftNativeBlock_probeFree _ _ _ _ _ _), tsum_probOutput_map_mul]
  unfold expectedJointRetainedCharge
  apply tsum_congr
  intro result
  cases result with
  | stopped hit => simp [AdaptiveRevealProbe.rawResultWithRemaining]
  | done hit state value =>
      rcases value with ⟨entry, ftsCache⟩
      cases entry with
      | none => simp [AdaptiveRevealProbe.rawResultWithRemaining]
      | some entry =>
          simp only [AdaptiveRevealProbe.rawResultWithRemaining]
          congr 1
          exact tsum_erasedQueryPrefixProbability_eq_observer table parameter entry.value.1 select
            (JointOriginal.retainedComputation adversary parameter entry.value.1 q) q
            (JointOriginal.retainedComputation_hashBound adversary parameter entry.value.1 q) state q le_rfl
            entry.context entry.remaining entry.history (entry.value.2, ftsCache)

namespace JointOriginal

theorem beforeFailureOuterSelectedCharge_le_erased
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q fuel : Nat)
    (selected : HashInput → Prop) :
    (∑' otsTable, Pr[= otsTable | OtsProbeSimulation.sampleOtsHashTable] *
      ∑' initial, Pr[= initial | initializeRoot parameter otsTable table q fuel] *
        expectedBeforeFailureOuterCharge (parentException parameter otsTable table)
          (fun _ input => if selected input then 1 else 0) parameter initial.2.1 otsTable table
          (retainedComputation adversary parameter initial.2.1 q) initial.1 initial.2.2 false initial.1.isNone) ≤
      expectedJointRetainedCharge adversary parameter table q
        (fun input _ _ _ _ => if IsSelectedOuterHash selected input then 1 else 0) := by
  let select := IsSelectedOuterHash selected
  calc
    _ = ∑' ordinal : Nat, ∑' otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput, Pr[= otsTable | OtsProbeSimulation.sampleOtsHashTable] *
        ∑' initial, Pr[= initial | initializeRoot parameter otsTable table q fuel] *
          liveQueryPrefixProbability (parentException parameter otsTable table) select parameter initial.2.1 otsTable table
            (retainedComputation adversary parameter initial.2.1 q) ordinal initial.1 initial.2.2 false initial.1.isNone := by
      simp_rw [expectedBeforeFailureOuterCharge_eq_prefixSum, ← ENNReal.tsum_mul_left]
      conv_lhs =>
        arg 1
        ext otsTable
        rw [ENNReal.tsum_comm]
      rw [ENNReal.tsum_comm]
    _ ≤ ∑' ordinal, Pr[JointHistoryReturned (fun value => value.1 = true) |
        AdaptiveRevealProbe.runDetailed table AdaptiveRevealProbe.State.empty q
          (runJointErasedHistory ((jointSourceRetainedBeforeQuery adversary parameter q select ordinal).run
            (OtsProbeSimulation.emptySplitHashCache, emptySplitHashCache)) (OtsProbeSimulation.ensuredInitialContext ∅) 0 [])] := by
      apply ENNReal.tsum_le_tsum
      intro ordinal
      simpa only [liveQueryPrefixProbability, jointSourceRetainedBeforeQuery] using probEvent_sampled_initialized_live_value_le_erasedHistory
        (fun otsTable => parentException parameter otsTable table) parameter table
        (fun root => beforeQueryOccurrence select (retainedComputation adversary parameter root q) ordinal) (fun value => value = true) q fuel
        (fun root => beforeQueryOccurrence_queryBound select OtsProbeSimulation.IsOuterHash _ q ordinal
          (retainedComputation_hashBound adversary parameter root q))
    _ ≤ ∑' ordinal, rawSourceEventProbability table (jointSourceRetainedBeforeQuery adversary parameter q select ordinal) (fun value => value = true)
        AdaptiveRevealProbe.State.empty q (OtsProbeSimulation.ensuredInitialContext ∅) 0 []
          (OtsProbeSimulation.emptySplitHashCache, emptySplitHashCache) := by
      apply ENNReal.tsum_le_tsum
      intro ordinal
      exact probEvent_jointHistoryReturned_le_raw table
        ((jointSourceRetainedBeforeQuery adversary parameter q select ordinal).run (OtsProbeSimulation.emptySplitHashCache, emptySplitHashCache))
        (fun value : Bool × JointSourceCache => value.1 = true)
        AdaptiveRevealProbe.State.empty q (OtsProbeSimulation.ensuredInitialContext ∅) 0 []
    _ = expectedJointRetainedCharge adversary parameter table q (fun input _ _ _ _ => if select input then 1 else 0) :=
      tsum_raw_retainedPrefix_eq_observer adversary parameter table q select

theorem beforeFailureOuterNonSecretCharge_le_erased
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q fuel : Nat) :
    (∑' otsTable, Pr[= otsTable | OtsProbeSimulation.sampleOtsHashTable] *
      ∑' initial, Pr[= initial | initializeRoot parameter otsTable table q fuel] *
        expectedBeforeFailureOuterCharge (parentException parameter otsTable table)
          (fun _ input => if NonSecretHashInput parameter input then 1 else 0) parameter initial.2.1 otsTable table
          (retainedComputation adversary parameter initial.2.1 q) initial.1 initial.2.2 false initial.1.isNone) ≤
      expectedJointRetainedCharge adversary parameter table q (jointNonSecretQueryCharge parameter) := by
  calc
    _ ≤ expectedJointRetainedCharge adversary parameter table q
        (fun input _ _ _ _ => if IsSelectedOuterHash (NonSecretHashInput parameter) input then 1 else 0) :=
      beforeFailureOuterSelectedCharge_le_erased adversary parameter table q fuel (NonSecretHashInput parameter)
    _ = _ := by
      congr 1
      funext input context cache state ftsCache
      cases input with
      | inl query => cases query <;> simp [IsSelectedOuterHash, jointNonSecretQueryCharge]
      | inr message => simp [IsSelectedOuterHash, jointNonSecretQueryCharge]

theorem sampledBeforeFailureOuterNonSecretCharge_le_erased
    (adversary : Adversary) (q fuel : Nat) :
    sampledBeforeFailureOuterNonSecretCharge adversary q fuel ≤ sampledJointNonSecretQueryCharge adversary q := by
  unfold sampledBeforeFailureOuterNonSecretCharge sampledJointNonSecretQueryCharge
  apply ENNReal.tsum_le_tsum
  intro parameter
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro ftsSecret
  exact mul_le_mul' le_rfl (beforeFailureOuterNonSecretCharge_le_erased adversary parameter (curryFtsTableEquiv ftsSecret) q fuel)

end JointOriginal
end SphincsSecurity.Concrete.FtsProbeSimulation
