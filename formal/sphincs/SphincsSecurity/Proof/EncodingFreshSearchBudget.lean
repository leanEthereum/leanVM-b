import SphincsSecurity.Proof.EncodingCountCertificate
import SphincsSecurity.Proof.ValidCacheCollisionBound
import SphincsSecurity.Proof.FreshCacheCharge
import SphincsSecurity.Proof.EncodingTarget
import SphincsSecurity.Proof.RomQueryChargeBind

namespace SphincsSecurity

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem validDigestRate_ge_inv32768 : (32768 : ENNReal)⁻¹ ≤ validDigestRate := by
  have hcard : Fintype.card Digest = 2 ^ 128 := card_bitVec digestBits
  calc
    _ = ((2 ^ 113 : Nat) : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ := by
      rw [hcard]
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv]
    _ ≤ _ := mul_le_mul' (Nat.cast_le.mpr TargetSum.validDigests_card_ge_pow113) le_rfl

theorem validDigestRate_ge_inv24576 : (24576 : ENNReal)⁻¹ ≤ validDigestRate := by
  rw [← one_div]
  apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).mpr
  have hc : (Fintype.card Digest : ENNReal) ≤ 24576 * (TargetSum.validDigests.card : ENNReal) := by
    exact_mod_cast (show Fintype.card Digest ≤ 24576 * TargetSum.validDigests.card by
      rw [show Fintype.card Digest = 2 ^ 128 from card_bitVec digestBits]
      exact TargetSum.pow128_le_24576_mul_validDigests_card)
  calc
    _ = (Fintype.card Digest : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ := by
      symm
      apply ENNReal.mul_inv_cancel
      · exact_mod_cast Fintype.card_ne_zero (α := Digest)
      · exact ENNReal.natCast_ne_top _
    _ ≤ (24576 * (TargetSum.validDigests.card : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ := mul_le_mul' hc le_rfl
    _ = _ := by rw [validDigestRate, div_eq_mul_inv]; ring

namespace Concrete

theorem freshCacheCharge_mul_validRate_le_validProbability (cache : QueryCache HashSpec) (input : HashInput) :
    freshCacheCharge cache input * validDigestRate ≤
      Pr[fun result => TargetSum.ValidDigest (truncateHash result.1) | (randomOracle input).run cache] := by
  by_cases hfresh : cache input = none
  · rw [freshCacheCharge, if_pos hfresh, one_mul, randomOracle, QueryImpl.withCaching_run_none _ hfresh, probEvent_map]
    exact (probEvent_uniform_encoding_valid).symm.le
  · rw [freshCacheCharge, if_neg hfresh, zero_mul]
    exact zero_le

theorem encodingSearchFrom_succ_lift
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (attempts counter : Nat) :
    (liftM (encodingSearchFrom parameter lay tree leafIdx message (attempts + 1) counter) : OracleComp OracleWorld _) =
      (liftM (OracleWorld.query (.inr (tweakableHashInput parameter (.encoding lay tree leafIdx)
        (digestBytes message ++ counterBytes (BitVec.ofNat counterBits counter))))) : OracleComp OracleWorld HashOutput) >>= fun output =>
          match TargetSum.decodeDigest (truncateHash output) with
          | none => liftM (encodingSearchFrom parameter lay tree leafIdx message attempts (counter + 1))
          | some _ => pure (some (BitVec.ofNat counterBits counter)) := by
  simp only [encodingSearchFrom, encode, tweakableHash, liftM_bind, bind_assoc, pure_bind]
  apply bind_congr
  intro output
  cases TargetSum.decodeDigest (truncateHash output) <;> rfl

theorem expected_fresh_encodingSearchFrom_mul_rate_le_success
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (attempts counter : Nat) (cache : QueryCache HashSpec) :
    expectedQueryCharge freshCacheCharge
        (liftM (encodingSearchFrom parameter lay tree leafIdx message attempts counter)) cache * validDigestRate ≤
      Pr[fun result => result.1.isSome = true |
        (simulateQ romImpl (liftM (encodingSearchFrom parameter lay tree leafIdx message attempts counter))).run cache] := by
  induction attempts generalizing counter cache with
  | zero => simp [encodingSearchFrom]
  | succ attempts ih =>
      rw [encodingSearchFrom_succ_lift]
      let input := tweakableHashInput parameter (.encoding lay tree leafIdx)
        (digestBytes message ++ counterBytes (BitVec.ofNat counterBits counter))
      rw [expectedQueryCharge_query_bind, add_mul, ← ENNReal.tsum_mul_right,
        simulateQ_query_bind, StateT.run_bind, probEvent_bind_eq_tsum]
      simp only [hashQueryCharge, Sum.elim_inr]
      have hhead : freshCacheCharge cache input * validDigestRate ≤
          ∑' result, Pr[= result | (randomOracle input).run cache] *
            (if TargetSum.ValidDigest (truncateHash result.1) then 1 else 0) := by
        simpa only [probEvent_eq_tsum_ite, mul_ite, mul_one, mul_zero] using
          freshCacheCharge_mul_validRate_le_validProbability cache input
      calc
        _ ≤ (∑' result, Pr[= result | (randomOracle input).run cache] *
              (if TargetSum.ValidDigest (truncateHash result.1) then 1 else 0)) +
            ∑' result, Pr[= result | (randomOracle input).run cache] *
              (match TargetSum.decodeDigest (truncateHash result.1) with
              | none => Pr[fun final => final.1.isSome = true |
                  (simulateQ romImpl (liftM (encodingSearchFrom parameter lay tree leafIdx message attempts (counter + 1)))).run result.2]
              | some _ => 0) := by
                apply add_le_add hhead
                apply ENNReal.tsum_le_tsum
                intro result
                rw [mul_assoc]
                apply mul_le_mul' le_rfl
                cases hd : TargetSum.decodeDigest (truncateHash result.1) with
                | none => exact ih (counter + 1) result.2
                | some encoding => simp only [expectedQueryCharge_pure, zero_mul, le_refl]
        _ = _ := by
          rw [← ENNReal.tsum_add]
          apply tsum_congr
          intro result
          rw [← mul_add]
          congr 1
          change (if TargetSum.ValidDigest (truncateHash result.1) then (1 : ENNReal) else 0) +
              (match TargetSum.decodeDigest (truncateHash result.1) with
              | none => Pr[fun final => final.1.isSome = true |
                  (simulateQ romImpl (liftM (encodingSearchFrom parameter lay tree leafIdx message attempts (counter + 1)))).run result.2]
              | some _ => 0) =
            Pr[fun final => final.1.isSome = true |
              (simulateQ romImpl (match TargetSum.decodeDigest (truncateHash result.1) with
                | none => liftM (encodingSearchFrom parameter lay tree leafIdx message attempts (counter + 1))
                | some _ => pure (some (BitVec.ofNat counterBits counter)))).run result.2]
          cases hd : TargetSum.decodeDigest (truncateHash result.1) with
          | none =>
              have hv : ¬ TargetSum.ValidDigest (truncateHash result.1) := by
                rintro ⟨encoding, he⟩
                rw [hd] at he
                cases he
              simp only [if_neg hv, zero_add]
          | some encoding =>
              have hv : TargetSum.ValidDigest (truncateHash result.1) := ⟨encoding, hd⟩
              simp only [if_pos hv, add_zero, simulateQ_pure, StateT.run_pure, probEvent_pure,
                Option.isSome_some, if_true]

theorem expected_fresh_encodingSearchFrom_le_success_budget
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (attempts counter : Nat) (cache : QueryCache HashSpec) :
    expectedQueryCharge freshCacheCharge
        (liftM (encodingSearchFrom parameter lay tree leafIdx message attempts counter)) cache ≤
      Pr[fun result => result.1.isSome = true |
        (simulateQ romImpl (liftM (encodingSearchFrom parameter lay tree leafIdx message attempts counter))).run cache] * 24576 := by
  have h := (mul_le_mul' (le_refl (expectedQueryCharge freshCacheCharge
      (liftM (encodingSearchFrom parameter lay tree leafIdx message attempts counter)) cache)) validDigestRate_ge_inv24576).trans
    (expected_fresh_encodingSearchFrom_mul_rate_le_success parameter lay tree leafIdx message attempts counter cache)
  have hs := mul_le_mul' h (le_refl (24576 : ENNReal))
  simpa only [mul_assoc, show (24576 : ENNReal)⁻¹ * 24576 = 1 from ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one] using hs

end Concrete
end SphincsSecurity
