import SphincsSecurity.Proof.InitializedExecutionReserve
import SphincsSecurity.Proof.StoppedRemainder127

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

noncomputable def initializedStoppedIndexRemainder (adversary : Adversary) (parameter : PublicParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat) : ENNReal :=
  ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
    (expectedStoppedIndexRemainder (parentException parameter otsTable ftsTable) parameter initial.2.1 otsTable ftsTable q
      ∅ Finset.univ (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) q
      initial.1 (initial.2.2, []) false initial.1.isNone * ((2 ^ 176 : Nat) : ENNReal)⁻¹)

theorem initializedStoppedTargetCharge_add_executionReserve_remainder_le_initial
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    initializedStoppedTargetCharge adversary parameter otsTable ftsTable q fuel +
      (initializedUnusedExecutionReserve adversary parameter otsTable ftsTable q fuel +
        initializedStoppedIndexRemainder adversary parameter otsTable ftsTable q fuel) ≤
      (q : ENNReal) * initialRawIndexRate q := by
  rw [initializedStoppedTargetCharge, initializedUnusedExecutionReserve, initializedStoppedIndexRemainder, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  calc
    _ ≤ ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
        ((q : ENNReal) * initialRawIndexRate q) := by
      apply ENNReal.tsum_le_tsum
      intro initial
      rw [← mul_add, ← mul_add]
      by_cases hi : initial ∈ support (initializeRoot parameter otsTable ftsTable q fuel)
      · let key := secretKey parameter initial.2.1 otsTable ftsTable
        have hconditions := initialized_stoppedTarget_conditions adversary q hq parameter hp otsTable ftsTable hfts fuel initial hi
        have hroot := initializeRoot_original_support parameter otsTable ftsTable q fuel initial hi
        rw [originalRoot, simulateQ_romImpl_liftM] at hroot
        have hgame := isQueryBoundP_gameAfterSecrets adversary q hq hp
          (OtsProbeSimulation.mem_support_sampleOtsSecrets_all key.otsSecret) hfts
        have hbound := retainedRoot_expanded_rest_queryBound adversary parameter key.otsSecret ftsTable q hgame initial.2 hroot
        exact mul_le_mul' le_rfl (expectedStoppedArrival_add_executionReserve_remainder_scaled_le_initial
          (parentException parameter otsTable ftsTable) parameter initial.2.1 otsTable ftsTable q hqMax
          (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) hbound initial.1 initial.2.2 false initial.1.isNone
          hconditions.1 hconditions.2)
      · rw [probOutput_eq_zero_of_not_mem_support hi, zero_mul, zero_mul]
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem initializedStoppedTargetCharge_add_executionReserve_remainder_le_127
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    initializedStoppedTargetCharge adversary parameter otsTable ftsTable q fuel +
      (initializedUnusedExecutionReserve adversary parameter otsTable ftsTable q fuel +
        initializedStoppedIndexRemainder adversary parameter otsTable ftsTable q fuel) ≤
      (q : ENNReal) * ((29 / 64 : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹) :=
  (initializedStoppedTargetCharge_add_executionReserve_remainder_le_initial adversary q hq hqMax parameter hp otsTable ftsTable hfts fuel).trans
    (mul_le_mul' le_rfl (initialRawIndexRate_le_127 q hqMax))

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
