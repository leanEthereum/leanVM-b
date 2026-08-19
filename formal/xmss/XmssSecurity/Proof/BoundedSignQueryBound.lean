import XmssSecurity.Proof.BoundedSign
import XmssSecurity.Proof.EncodingAddressQueryBound

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

theorem Concrete.signingRandomness_queryBound_zero_encodingAddress
    (parameter : PublicParameter) (epoch : Epoch) :
    (liftM Concrete.signingRandomness : OracleComp OracleWorld Randomness).IsQueryBoundP
      (IsEncodingHashQueryAt parameter epoch) 0 := by
  apply OracleComp.IsQueryBoundP.liftComp_subSpec
    (p := fun _ : unifSpec.Domain => False)
  · intro input
    change False ↔ IsEncodingHashQueryAt parameter epoch (Sum.inl input)
    simp [IsEncodingHashQueryAt]
  · simp

theorem signingAttemptLimit_mul_lifetime_randomness_loss_le_digest_loss (q : Nat) :
    (signingAttemptLimit : ℝ≥0∞) * (lifetime : ℝ≥0∞) *
        ((q : ℝ≥0∞) / ((2 ^ randomnessBits : Nat) : ℝ≥0∞)) ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    (signingAttemptLimit : ℝ≥0∞) * (lifetime : ℝ≥0∞) *
        ((q : ℝ≥0∞) * ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹) =
      (q : ℝ≥0∞) *
        (((signingAttemptLimit : ℝ≥0∞) * (lifetime : ℝ≥0∞)) *
          ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹) := by ac_rfl
    _ ≤ (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      gcongr
      have hleft :
          ((signingAttemptLimit : ℝ≥0∞) * (lifetime : ℝ≥0∞)) *
              ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ =
            ((signingAttemptLimit : ℝ≥0∞) * (lifetime : ℝ≥0∞)) /
              ((2 ^ randomnessBits : Nat) : ℝ≥0∞) := by
        rw [div_eq_mul_inv]
      have hright : ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ =
          1 / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
        rw [div_eq_mul_inv, one_mul]
      rw [hleft, hright]
      rw [ENNReal.div_le_iff (by positivity) (by simp)]
      have hrearrange :
          (1 / ((2 ^ digestBits : Nat) : ℝ≥0∞)) *
              ((2 ^ randomnessBits : Nat) : ℝ≥0∞) =
            ((2 ^ randomnessBits : Nat) : ℝ≥0∞) /
              ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ac_rfl
      rw [hrearrange, ENNReal.le_div_iff_mul_le (by simp) (by simp)]
      exact_mod_cast (by
        norm_num [signingAttemptLimit, lifetime, treeHeight, digestBits, randomnessBits] :
          signingAttemptLimit * lifetime * 2 ^ digestBits ≤ 2 ^ randomnessBits)

end XmssSecurity
