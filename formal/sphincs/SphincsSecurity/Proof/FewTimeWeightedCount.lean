import SphincsSecurity.Proof.FewTimeOrigins
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Weighted count of fresh and prehit origins

For a fixed set of selected signer entries, choose the prehit subset and injectively assign its
members to direct-query sources. The total weight is at most `(1 + sources * weight)^selected`.
-/

namespace SphincsSecurity.Concrete

open ENNReal

abbrev InjectiveSources (Selected : Type) (sources : Nat) :=
  {source : Selected → Fin sources // Function.Injective source}

noncomputable instance (Selected : Type) [Fintype Selected] (sources : Nat) :
    Fintype (InjectiveSources Selected sources) :=
  Fintype.ofFinite _

theorem injectiveSources_card_le (Selected : Type) [Fintype Selected] [DecidableEq Selected]
    (sources : Nat) :
    Fintype.card (InjectiveSources Selected sources) ≤
      sources ^ Fintype.card Selected := by
  classical
  calc
    Fintype.card (InjectiveSources Selected sources) ≤
        Fintype.card (Selected → Fin sources) :=
      Fintype.card_subtype_le _
    _ = sources ^ Fintype.card Selected := by
      rw [Fintype.card_fun, Fintype.card_fin]

noncomputable def originChoiceMass (Selected : Type) [Fintype Selected] [DecidableEq Selected]
    (sources : Nat) (weight : ℝ≥0∞) : ℝ≥0∞ :=
  ∑ prehit : Finset Selected,
    Fintype.card (InjectiveSources prehit sources) * weight ^ prehit.card

theorem sum_finset_pow_card (Selected : Type) [Fintype Selected] [DecidableEq Selected]
    (value : ℝ≥0∞) :
    (∑ selected : Finset Selected, value ^ selected.card) =
      (1 + value) ^ Fintype.card Selected := by
  classical
  have hprod := Finset.prod_add (fun _ : Selected => value) (fun _ => 1)
    (Finset.univ : Finset Selected)
  simpa [Finset.prod_const, add_comm] using hprod.symm

theorem originChoiceMass_le (Selected : Type) [Fintype Selected] [DecidableEq Selected]
    (sources : Nat) (weight : ℝ≥0∞) :
    originChoiceMass Selected sources weight ≤
      (1 + sources * weight) ^ Fintype.card Selected := by
  classical
  calc
    originChoiceMass Selected sources weight ≤
        ∑ prehit : Finset Selected,
          (sources : ℝ≥0∞) ^ prehit.card * weight ^ prehit.card := by
      apply Finset.sum_le_sum
      intro prehit _
      gcongr
      have hcard := injectiveSources_card_le prehit sources
      rw [Fintype.card_coe] at hcard
      exact_mod_cast hcard
    _ = ∑ prehit : Finset Selected,
          ((sources : ℝ≥0∞) * weight) ^ prehit.card := by
      apply Finset.sum_congr rfl
      intro prehit _
      rw [mul_pow]
    _ = (1 + sources * weight) ^ Fintype.card Selected :=
      sum_finset_pow_card Selected ((sources : ℝ≥0∞) * weight)

theorem FewTimePattern.originChoiceMass_le_two {signatures distinct q : Nat}
    (pattern : FewTimePattern signatures distinct) (hq : q ≤ 2 ^ 120)
    (hdistinct : distinct ≤ 14) :
    originChoiceMass pattern.selected q ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ≤ 2 := by
  calc
    originChoiceMass pattern.selected q ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ≤
        (1 + q * ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹) ^
          Fintype.card pattern.selected :=
      originChoiceMass_le pattern.selected q ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹
    _ = (1 + q * ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹) ^ distinct := by
      rw [Fintype.card_coe, pattern.card_selected]
    _ ≤ 2 := prehit_origin_inflation_pow_le hq hdistinct

theorem FewTimePattern.originChoiceMass_le_nine_eighths {signatures distinct q : Nat}
    (pattern : FewTimePattern signatures distinct) (hq : q ≤ 2 ^ 120)
    (hdistinct : distinct ≤ 14) :
    originChoiceMass pattern.selected q ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ≤ 9 / 8 := by
  calc
    originChoiceMass pattern.selected q ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ≤
        (1 + q * ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹) ^
          Fintype.card pattern.selected :=
      originChoiceMass_le pattern.selected q ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹
    _ = (1 + q * ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹) ^ distinct := by
      rw [Fintype.card_coe, pattern.card_selected]
    _ ≤ 9 / 8 := prehit_origin_inflation_pow_le_nine_eighths hq hdistinct

noncomputable def weightedFewTimePatternBound (signatures q : Nat) : ℝ≥0∞ :=
  ∑ distinct ∈ Finset.Icc 1 14,
    ∑ pattern : FewTimePattern signatures distinct,
      originChoiceMass pattern.selected q ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ *
        ((2 ^ (26 * distinct + 140) : Nat) : ℝ≥0∞)⁻¹

theorem weightedFewTimePatternBound_le {signatures q : Nat}
    (hsignatures : signatures ≤ signatureLimit) (hq : q ≤ 2 ^ 120) :
    weightedFewTimePatternBound signatures q ≤
      ((2 ^ 121 : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  calc
    weightedFewTimePatternBound signatures q ≤
        ∑ distinct ∈ Finset.Icc 1 14,
          ∑ _pattern : FewTimePattern signatures distinct,
            2 * ((2 ^ (26 * distinct + 140) : Nat) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_le_sum
      intro distinct hdistinct
      apply Finset.sum_le_sum
      intro pattern _
      gcongr
      exact pattern.originChoiceMass_le_two hq (Finset.mem_Icc.mp hdistinct).2
    _ = 2 * (∑ distinct ∈ Finset.Icc 1 14,
          (Fintype.card (FewTimePattern signatures distinct) : ℝ≥0∞) *
            ((2 ^ (26 * distinct + 140) : Nat) : ℝ≥0∞)⁻¹) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro distinct _
      ring
    _ ≤ 2 * ((2 ^ 122 : Nat) : ℝ≥0∞)⁻¹ := by
      gcongr
      exact fewTimePattern_unionBound_le hsignatures
    _ = ((2 ^ 121 : Nat) : ℝ≥0∞)⁻¹ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
      norm_num

theorem weightedFewTimePatternBound_le_nine_mul_inv {signatures q : Nat}
    (hsignatures : signatures ≤ signatureLimit) (hq : q ≤ 2 ^ 120) :
    weightedFewTimePatternBound signatures q ≤
      9 * ((2 ^ 125 : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  calc
    weightedFewTimePatternBound signatures q ≤
        ∑ distinct ∈ Finset.Icc 1 14,
          ∑ _pattern : FewTimePattern signatures distinct,
            (9 / 8) * ((2 ^ (26 * distinct + 140) : Nat) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_le_sum
      intro distinct hdistinct
      apply Finset.sum_le_sum
      intro pattern _
      gcongr
      exact pattern.originChoiceMass_le_nine_eighths hq
        (Finset.mem_Icc.mp hdistinct).2
    _ = (9 / 8) * (∑ distinct ∈ Finset.Icc 1 14,
          (Fintype.card (FewTimePattern signatures distinct) : ℝ≥0∞) *
            ((2 ^ (26 * distinct + 140) : Nat) : ℝ≥0∞)⁻¹) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro distinct _
      ring
    _ ≤ (9 / 8) * ((2 ^ 122 : Nat) : ℝ≥0∞)⁻¹ := by
      gcongr
      exact fewTimePattern_unionBound_le hsignatures
    _ = 9 * ((2 ^ 125 : Nat) : ℝ≥0∞)⁻¹ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div,
        ENNReal.toReal_natCast]
      norm_num

end SphincsSecurity.Concrete
