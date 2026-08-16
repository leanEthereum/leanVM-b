import XmssSecurity.BoundedSign
import XmssSecurity.EncodingTraceBridge

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

theorem Concrete.signAttempt_lift_queryBound_encodingAddress
    (secretKey : SecretKey) (epoch targetEpoch : Epoch)
    (message : Message) (randomness : Randomness) :
    (liftM (Concrete.signAttempt secretKey epoch message randomness :
      OracleComp HashSpec (Option Signature)) :
        OracleComp OracleWorld (Option Signature)).IsQueryBoundP
      (IsEncodingHashQueryAt secretKey.parameter targetEpoch)
      (if epoch = targetEpoch then 1 else 0) := by
  apply OracleComp.IsQueryBoundP.liftComp_subSpec
    (p := AtHashAddress secretKey.parameter (.encoding targetEpoch))
  · intro input
    change AtHashAddress secretKey.parameter (.encoding targetEpoch) input ↔
      IsEncodingHashQueryAt secretKey.parameter targetEpoch (Sum.inr input)
    rfl
  · exact Concrete.signAttempt_queryBound_encodingAddress secretKey epoch targetEpoch
      message randomness

theorem Concrete.signBoundedAttempts_queryBound_encodingAddress
    (attempts : Nat) (secretKey : SecretKey) (epoch targetEpoch : Epoch)
    (message : Message) :
    (Concrete.signBoundedAttempts attempts secretKey epoch message).IsQueryBoundP
      (IsEncodingHashQueryAt secretKey.parameter targetEpoch)
      (attempts * if epoch = targetEpoch then 1 else 0) := by
  induction attempts with
  | zero => simp [Concrete.signBoundedAttempts]
  | succ attempts ih =>
      rw [Concrete.signBoundedAttempts]
      refine (OracleComp.isQueryBoundP_bind
        (n := 0)
        (m := (if epoch = targetEpoch then 1 else 0) +
          attempts * if epoch = targetEpoch then 1 else 0)
        (Concrete.signingRandomness_queryBound_zero_encodingAddress
          secretKey.parameter targetEpoch) ?_).mono (by
            by_cases hepoch : epoch = targetEpoch
            · simp [hepoch]
              omega
            · simp [hepoch])
      intro randomness _
      refine (OracleComp.isQueryBoundP_bind
        (n := if epoch = targetEpoch then 1 else 0)
        (m := attempts * if epoch = targetEpoch then 1 else 0)
        (Concrete.signAttempt_lift_queryBound_encodingAddress secretKey epoch targetEpoch
          message randomness) ?_).mono (by omega)
      intro result _
      cases result with
      | none => exact ih
      | some signature => simp

theorem Concrete.cappedSign_queryBound_encodingAddress
    (publicKey : PublicKey) (secretKey : SecretKey) (epoch targetEpoch : Epoch)
    (message : Message) :
    (Concrete.cappedSign publicKey secretKey epoch message).IsQueryBoundP
      (IsEncodingHashQueryAt secretKey.parameter targetEpoch)
      (signingAttemptLimit * if epoch = targetEpoch then 1 else 0) := by
  rw [Concrete.cappedSign_eq]
  exact Concrete.signBoundedAttempts_queryBound_encodingAddress signingAttemptLimit
    secretKey epoch targetEpoch message

/-- Union-bounding all capped signing attempts over the full lifetime still costs less than one elementary 128-bit term. -/
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
