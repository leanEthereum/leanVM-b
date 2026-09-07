import SphincsSecurity.Proof.JointProbeBeforeFailureErasure

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal

theorem sampledJointNonSecretQueryCharge_le_queryBound (adversary : Adversary) (q : Nat) :
    sampledJointNonSecretQueryCharge adversary q ≤ q :=
  (show sampledJointNonSecretQueryCharge adversary q ≤
    (sampledNativeFtsOtsCharge adversary q + sampledJointRetainedProbeCharge adversary q) +
      sampledJointNonSecretQueryCharge adversary q from le_add_left le_rfl).trans
    (sampledNativeFtsOts_add_fts_add_nonSecret_charge_le_q adversary q)

theorem forgeAdvantage_le_joint_beforeFailureBudget_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ + (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹)) := by
  have he : sampledJointNonSecretQueryCharge adversary q ≠ ⊤ :=
    ne_top_of_le_ne_top (by finiteness) (sampledJointNonSecretQueryCharge_le_queryBound adversary q)
  have hc : (Fintype.card Digest : ENNReal) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hfinite : sampledJointNonSecretQueryCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top he (ENNReal.inv_ne_top.mpr hc)
  apply ENNReal.le_of_add_le_add_right hfinite
  calc
    _ ≤ (sampledBeforeFailureRestHashCharge adversary q (q + 1) + sampledBeforeFailureOuterNonSecretCharge adversary q (q + 1)) *
          (Fintype.card Digest : ENNReal)⁻¹ +
        ((q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ + (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal)) +
        ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ + (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹)) :=
      forgeAdvantage_add_sharedNonSecret_le_beforeFailureBudget adversary q hqPos hq hqMax
    _ ≤ (sampledBeforeFailureRestHashCharge adversary q (q + 1) + sampledJointNonSecretQueryCharge adversary q) *
          (Fintype.card Digest : ENNReal)⁻¹ +
        ((q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ + (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal)) +
        ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ + (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹)) :=
      add_le_add (add_le_add
        (mul_le_mul' (add_le_add le_rfl (sampledBeforeFailureOuterNonSecretCharge_le_erased adversary q (q + 1))) le_rfl) le_rfl) le_rfl
    _ = _ := by
      simp only [add_mul]
      ac_rfl

theorem forgeAdvantage_le_two_query_rates_add_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary ≤
      (2 * (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ + (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ + (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹)) := by
  apply (forgeAdvantage_le_joint_beforeFailureBudget_remaining127 adversary q hqPos hq hqMax).trans
  rw [two_mul]
  exact add_le_add (add_le_add (mul_le_mul'
    (add_le_add (sampledBeforeFailureRestHashCharge_le_queryBound adversary q hq (q + 1)) le_rfl) le_rfl) le_rfl) le_rfl

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
