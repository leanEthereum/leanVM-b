import SphincsSecurity.Proof.JointProbeMessageHashBudget
import SphincsSecurity.Proof.SecurityJointBeforeFailureBound

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal

theorem forgeAdvantage_add_messageReserves_le_joint_beforeFailureBudget
    (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary +
      (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1)) *
        (Fintype.card Digest : ENNReal)⁻¹ ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) +
      Pr[retainedNonSecretResidual | OtsProbeSimulation.sampledFirstParentRetainedGame adversary] := by
  have hspace : q + 1 < Fintype.card Digest := by
    have hcard : Fintype.card Digest = 2 ^ 128 := by
      rw [show Fintype.card Digest = 2 ^ digestBits from card_bitVec digestBits]
      rfl
    rw [hcard]
    omega
  have hshared := (add_le_add ((sampledParentSharedFailureRisk_le_nativeCompletion adversary q (q + 1)).trans
    (sampledNativeFtsCompletionRisk_le_ots_add_fts_hit adversary q (q + 1))) le_rfl).trans
      (sampledNativeFtsOtsFailure_add_fts_hit_add_nonSecret_le_query_rate adversary q (q + 1) (by omega) hspace)
  have hstructural := (sampledBeforeFailureStructural_le_nonMessageHash_add_nonMessageNonSecret adversary q (q + 1)).trans
    (add_le_add le_rfl (sampledBeforeFailureSelectedCharge_le_erased NonMessageNonSecretHashInput adversary q (q + 1)))
  have hbound : forgeAdvantage scheme adversary + sampledJointNonSecretQueryCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (sampledBeforeFailureHashCharge nonMessageHashCharge adversary q (q + 1) + sampledSelectedJointQueryCharge NonMessageNonSecretHashInput adversary q) *
          (Fintype.card Digest : ENNReal)⁻¹ +
        ((q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ + (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal)) +
        Pr[retainedNonSecretResidual | OtsProbeSimulation.sampledFirstParentRetainedGame adversary] := by
    apply (add_le_add (forgeAdvantage_le_sharedFailure_add_beforeFailureStructural adversary q hq (q + 1)) le_rfl).trans
    calc
      _ = sampledBeforeFailureStructuralCharge adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ +
          (sampledParentSharedFailureRisk adversary q (q + 1) + sampledJointNonSecretQueryCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹) +
          Pr[retainedNonSecretResidual | OtsProbeSimulation.sampledFirstParentRetainedGame adversary] := by ac_rfl
      _ ≤ _ := add_le_add (add_le_add (mul_le_mul' hstructural le_rfl) hshared) le_rfl
  have hother : sampledSelectedJointQueryCharge NonMessageNonSecretHashInput adversary q ≤ q := by
    apply le_trans _ (sampledJointNonSecretQueryCharge_le_queryBound adversary q)
    rw [sampledJointNonSecretQueryCharge_eq_nonMessage_add_message]
    exact le_self_add
  have he : sampledSelectedJointQueryCharge NonMessageNonSecretHashInput adversary q ≠ ⊤ :=
    ne_top_of_le_ne_top (by finiteness) hother
  have hc : (Fintype.card Digest : ENNReal) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply ENNReal.le_of_add_le_add_right (ENNReal.mul_ne_top he (ENNReal.inv_ne_top.mpr hc))
  rw [sampledJointNonSecretQueryCharge_eq_nonMessage_add_message] at hbound
  have hbound' := add_le_add hbound (le_refl
    (sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹))
  rw [sampledBeforeFailureRestHashCharge_eq_nonMessage_add_message]
  simpa only [add_mul, add_assoc, add_comm, add_left_comm] using hbound'

theorem forgeAdvantage_add_messageReserves_le_joint_beforeFailureBudget_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary +
      (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1)) *
        (Fintype.card Digest : ENNReal)⁻¹ ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ + (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹)) :=
  (forgeAdvantage_add_messageReserves_le_joint_beforeFailureBudget adversary q hq hqMax).trans
    (add_le_add le_rfl ((probEvent_retainedNonSecretResidual_le_viewed adversary).trans
      (probEvent_sampled_messageOrForest_le127 adversary q hqPos hq hqMax)))

theorem forgeAdvantage_add_messageReserves_le_two_query_rates_add_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary +
      (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1)) *
        (Fintype.card Digest : ENNReal)⁻¹ ≤
      (2 * (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ + (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ + (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹)) := by
  apply (forgeAdvantage_add_messageReserves_le_joint_beforeFailureBudget_remaining127 adversary q hqPos hq hqMax).trans
  rw [two_mul]
  exact add_le_add (add_le_add (mul_le_mul'
    (add_le_add (sampledBeforeFailureRestHashCharge_le_queryBound adversary q hq (q + 1)) le_rfl) le_rfl) le_rfl) le_rfl

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
