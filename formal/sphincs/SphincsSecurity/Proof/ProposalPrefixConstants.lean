import SphincsSecurity.Proof.ProposalLengthMoment

namespace SphincsSecurity.Concrete

open ENNReal

def proposalPrefixBarrierExponent : Nat := 25296896

theorem proposalPrefixBarrierExponent_twice :
    2 * proposalPrefixBarrierExponent = 3 * signatureLimit + 262144 := by
  norm_num [proposalPrefixBarrierExponent, signatureLimit]

set_option maxHeartbeats 5000000 in
theorem proposalLengthMoment_drift_block_le :
    (proposalLengthMoment ^ 2 / proposalLengthTilt ^ 3) ^ 1024 ≤ (16 / 15 : ENNReal) := by
  have ht := proposalLengthTilt_ne_top
  have ht0 := proposalLengthTilt_ne_zero
  have hm := proposalLengthMoment_ne_top
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [proposalLengthTilt, proposalLengthMoment, ENNReal.toReal_pow, ENNReal.toReal_div]
  have hbern : (15 / 16 : ℝ) ≤ (16383 / 16384 : ℝ) ^ 1024 := by
    have h := one_add_mul_le_pow (a := (-1 / 16384 : ℝ)) (by norm_num) 1024
    norm_num at h
    exact h
  have hupper : (16384 / 16383 : ℝ) ^ 1024 ≤ 16 / 15 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 15 / 16) hbern
    norm_num [one_div, inv_pow] at h
    rw [← inv_pow] at h
    norm_num at h
    exact h
  exact (pow_le_pow_left₀ (by norm_num)
    (by norm_num : (2199023255552 / 2198889170049 : ℝ) ≤ 16384 / 16383) 1024).trans hupper

set_option maxHeartbeats 5000000 in
theorem proposalLengthTilt_block_ge : (27 / 10 : ENNReal) ≤ proposalLengthTilt ^ 128 := by
  have ht := proposalLengthTilt_ne_top
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [proposalLengthTilt, ENNReal.toReal_pow, ENNReal.toReal_div]

set_option maxHeartbeats 5000000 in
theorem proposalPrefix_ratio_block_le :
    (((16 / 15 : ENNReal) ^ 8 / (27 / 10)) ^ 16) ≤ (2 ^ 11 : ENNReal)⁻¹ := by
  have hn : (27 / 10 : ENNReal) ≠ 0 := ENNReal.div_ne_zero.mpr ⟨by norm_num, by finiteness⟩
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_inv]

theorem proposalPrefixFactor_eq_blocks (tilt moment : ENNReal) :
    moment ^ signatureLimit * (tilt ^ proposalPrefixBarrierExponent)⁻¹ =
      (((moment ^ 2 / tilt ^ 3) ^ 1024) ^ 8 / tilt ^ 128) ^ 1024 := by
  simp only [div_eq_mul_inv, mul_pow, ENNReal.inv_pow, ← pow_mul]
  rw [mul_assoc, ← pow_add]
  rfl

theorem proposalPrefixFactor_le :
    proposalLengthMoment ^ signatureLimit * (proposalLengthTilt ^ proposalPrefixBarrierExponent)⁻¹ ≤
      (2 ^ 704 : ENNReal)⁻¹ := by
  rw [proposalPrefixFactor_eq_blocks]
  calc
    _ ≤ ((16 / 15 : ENNReal) ^ 8 / (27 / 10)) ^ 1024 := by
      apply pow_le_pow_left' _ 1024
      exact ENNReal.div_le_div
        (pow_le_pow_left' proposalLengthMoment_drift_block_le 8) proposalLengthTilt_block_ge
    _ = ((((16 / 15 : ENNReal) ^ 8 / (27 / 10)) ^ 16) ^ 64) := by rw [← pow_mul]
    _ ≤ ((2 ^ 11 : ENNReal)⁻¹) ^ 64 := pow_le_pow_left' proposalPrefix_ratio_block_le 64
    _ = _ := by rw [← ENNReal.inv_pow, ← pow_mul]

end SphincsSecurity.Concrete
