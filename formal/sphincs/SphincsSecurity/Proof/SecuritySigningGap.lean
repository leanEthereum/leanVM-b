import SphincsSecurity.Proof.StoppedSigningGapBound
import SphincsSecurity.Proof.SecurityStoppedRemainder

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def initializedStoppedSigningGap (adversary : Adversary) (parameter : PublicParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat) : ENNReal :=
  ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
    (expectedStoppedSigningGap (parentException parameter otsTable ftsTable) parameter initial.2.1 otsTable ftsTable q
      ∅ Finset.univ (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) q
      initial.1 (initial.2.2, []) false initial.1.isNone * ((2 ^ 176 : Nat) : ENNReal)⁻¹)

theorem initializedStoppedTargetCharge_add_executionReserve_remainder_gap_le_initial
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    initializedStoppedTargetCharge adversary parameter otsTable ftsTable q fuel +
      (initializedUnusedExecutionReserve adversary parameter otsTable ftsTable q fuel +
        (initializedStoppedIndexRemainder adversary parameter otsTable ftsTable q fuel +
          initializedStoppedSigningGap adversary parameter otsTable ftsTable q fuel)) ≤
      (q : ENNReal) * initialRawIndexRate q := by
  rw [initializedStoppedTargetCharge, initializedUnusedExecutionReserve, initializedStoppedIndexRemainder, initializedStoppedSigningGap,
    ← ENNReal.tsum_add, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  calc
    _ ≤ ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
        ((q : ENNReal) * initialRawIndexRate q) := by
      apply ENNReal.tsum_le_tsum
      intro initial
      rw [← mul_add, ← mul_add, ← mul_add]
      by_cases hi : initial ∈ support (initializeRoot parameter otsTable ftsTable q fuel)
      · let key := secretKey parameter initial.2.1 otsTable ftsTable
        have hconditions := initialized_stoppedTarget_conditions adversary q hq parameter hp otsTable ftsTable hfts fuel initial hi
        have hroot := initializeRoot_original_support parameter otsTable ftsTable q fuel initial hi
        rw [originalRoot, simulateQ_romImpl_liftM] at hroot
        have hgame := isQueryBoundP_gameAfterSecrets adversary q hq hp
          (OtsProbeSimulation.mem_support_sampleOtsSecrets_all key.otsSecret) hfts
        have hbound := retainedRoot_expanded_rest_queryBound adversary parameter key.otsSecret ftsTable q hgame initial.2 hroot
        exact mul_le_mul' le_rfl (expectedStoppedArrival_add_executionReserve_remainder_gap_scaled_le_initial
          (parentException parameter otsTable ftsTable) parameter initial.2.1 otsTable ftsTable q hqMax
          (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) hbound initial.1 initial.2.2 false initial.1.isNone
          hconditions.1 hconditions.2)
      · rw [probOutput_eq_zero_of_not_mem_support hi, zero_mul, zero_mul]
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

noncomputable def sampledStoppedSigningGap (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        initializedStoppedSigningGap adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel

private theorem expected_le_constant {α : Type} (computation : ProbComp α)
    (weight : α → ENNReal) (bound : ENNReal)
    (h : ∀ result ∈ support computation, weight result ≤ bound) :
    (∑' result, Pr[= result | computation] * weight result) ≤ bound := by
  calc
    _ ≤ ∑' result, Pr[= result | computation] * bound := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support computation
      · exact mul_le_mul' le_rfl (h result hr)
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem sampledStoppedTargetCharge_add_executionReserve_remainder_gap_le_initial
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledStoppedTargetCharge adversary q fuel +
      (sampledUnusedExecutionReserve adversary q fuel +
        (sampledStoppedIndexRemainder adversary q fuel + sampledStoppedSigningGap adversary q fuel)) ≤
      (q : ENNReal) * initialRawIndexRate q := by
  unfold sampledStoppedTargetCharge sampledUnusedExecutionReserve sampledStoppedIndexRemainder sampledStoppedSigningGap
  simp only [← ENNReal.tsum_add, ← mul_add]
  apply expected_le_constant
  intro parameter hp
  apply expected_le_constant
  intro ftsSecret hfts
  apply expected_le_constant
  intro table _
  exact initializedStoppedTargetCharge_add_executionReserve_remainder_gap_le_initial adversary q hq hqMax parameter hp table
    (curryFtsTableEquiv ftsSecret) hfts fuel

theorem forgeAdvantage_add_message_signing_executionReserves_remainder_gap_le_initialEnvelope
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary +
      (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1) +
        sampledSigningNonEncodingReserve adversary q (q + 1)) * (Fintype.card Digest : ENNReal)⁻¹ +
      (sampledUnusedExecutionReserve adversary q (q + 1) +
        (sampledStoppedIndexRemainder adversary q (q + 1) + sampledStoppedSigningGap adversary q (q + 1))) ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) +
      (q : ENNReal) * initialRawIndexRate q := by
  apply (add_le_add (forgeAdvantage_add_message_and_signingReserves_le_stoppedTargetCharge adversary q hq hqMax) le_rfl).trans
  rw [add_assoc]
  exact add_le_add le_rfl (sampledStoppedTargetCharge_add_executionReserve_remainder_gap_le_initial adversary q hq hqMax (q + 1))

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
