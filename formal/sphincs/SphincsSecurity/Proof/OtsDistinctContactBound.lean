import SphincsSecurity.Proof.OtsDistinctContactProbability
import SphincsSecurity.Proof.OtsContactFirstProbability

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs

theorem referenceContactGame_distinct_cost_le (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (hsmall : q < Fintype.card Digest) :
    (1 - (q : ENNReal) / Fintype.card Digest)^2 * (Fintype.card Digest : ENNReal) *
      Pr[fun result => result.2.2.TwoContacts result.1 (referenceFamilyWords result.2.1 dummy) |
        referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      (4 * ((q : ENNReal) / Fintype.card Digest)) *
        (∑' result : ReferenceRecordedResult, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.prefixCalls dummy : ENNReal)) := by
  have hrestart := mul_le_mul' (le_refl (1 - (q : ENNReal) / Fintype.card Digest))
    (referenceContactGame_distinct_restart_le dummy adversary q hbound hsmall)
  have hfirst := mul_le_mul' (le_refl (2 * (q : ENNReal)))
    (referenceContactGame_marked_cost_le dummy adversary q hbound hsmall)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hrestart
  rw [mul_left_comm (1 - (q : ENNReal) / Fintype.card Digest) (2 * (q : ENNReal))] at hrestart
  have h := hrestart.trans hfirst
  convert h using 1 <;> first | rfl | (simp only [div_eq_mul_inv]; ring)

theorem referenceContactGame_distinct_le (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (hsmall : q < Fintype.card Digest) :
    Pr[fun result => result.2.2.TwoContacts result.1 (referenceFamilyWords result.2.1 dummy) |
      referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      (4 * ((q : ENNReal) / Fintype.card Digest) *
        (∑' result : ReferenceRecordedResult, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.prefixCalls dummy : ENNReal))) /
        ((1 - (q : ENNReal) / Fintype.card Digest)^2 * (Fintype.card Digest : ENNReal)) := by
  have hcard : (Fintype.card Digest : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hpositive : 0 < 1 - (q : ENNReal) / Fintype.card Digest := by
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl hcard) (Or.inl (by finiteness)), one_mul]
    exact_mod_cast hsmall
  apply (ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero (pow_ne_zero 2 (ne_of_gt hpositive)) hcard)) (Or.inl (by finiteness))).mpr
  simpa only [mul_comm] using referenceContactGame_distinct_cost_le dummy adversary q hbound hsmall

theorem referenceContactGame_distinct_joint_budget (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (hsmall : q < Fintype.card Digest) :
    (1 - (q : ENNReal) / Fintype.card Digest)^2 * (Fintype.card Digest : ENNReal) *
      Pr[fun result => result.2.2.TwoContacts result.1 (referenceFamilyWords result.2.1 dummy) |
        referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] +
      (4 * ((q : ENNReal) / Fintype.card Digest)) *
        (∑' result : ReferenceRecordedResult, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.remainingCalls dummy : ENNReal)) ≤
      (4 * ((q : ENNReal) / Fintype.card Digest)) * q := by
  have hrestart := mul_le_mul' (le_refl (1 - (q : ENNReal) / Fintype.card Digest))
    (referenceContactGame_distinct_restart_le dummy adversary q hbound hsmall)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hrestart
  have hscaled := _root_.add_le_add hrestart (le_refl ((4 * ((q : ENNReal) / Fintype.card Digest)) *
    (∑' result : ReferenceRecordedResult, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.remainingCalls dummy : ENNReal))))
  have hfirst := mul_le_mul' (le_refl (2 * (q : ENNReal)))
    (referenceContactGame_marked_joint_budget dummy adversary q hbound hsmall)
  have hmid : _ ≤ _ := hscaled.trans (by convert hfirst using 1; first | rfl | (simp only [div_eq_mul_inv]; ring))
  convert hmid using 1 <;> first | rfl | (simp only [div_eq_mul_inv]; ring)

end SphincsSecurity.Concrete
