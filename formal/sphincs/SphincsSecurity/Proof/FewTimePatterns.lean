import SphincsSecurity.Proof.FewTimeWitness
import SphincsSecurity.Proof.LeakArith
import Mathlib.Data.Fintype.Powerset

/-!
# Counting few-time coverage patterns

A pattern chooses the distinct signing invocations used by a leak and assigns each of the fourteen
few-time trees to one of them.  Its exact cardinality is the binomial and power appearing in the
few-time union bound.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

structure FewTimePattern (signatures distinct : Nat) where
  selected : Finset (Fin signatures)
  card_selected : selected.card = distinct
  assignment : FtsTree → selected

def fewTimePatternEquiv (signatures distinct : Nat) :
    FewTimePattern signatures distinct ≃
      Σ selected : {s : Finset (Fin signatures) // s.card = distinct}, FtsTree → selected.1 where
  toFun pattern := ⟨⟨pattern.selected, pattern.card_selected⟩, pattern.assignment⟩
  invFun pattern := ⟨pattern.1.1, pattern.1.2, pattern.2⟩
  left_inv pattern := by cases pattern; rfl
  right_inv pattern := by cases pattern with | mk selected assignment => cases selected; rfl

noncomputable instance (signatures distinct : Nat) : Fintype (FewTimePattern signatures distinct) :=
  Fintype.ofEquiv _ (fewTimePatternEquiv signatures distinct).symm

theorem fewTimePattern_card (signatures distinct : Nat) :
    Fintype.card (FewTimePattern signatures distinct) =
      Nat.choose signatures distinct * distinct ^ (ftsTrees - 1) := by
  classical
  rw [Fintype.card_congr (fewTimePatternEquiv signatures distinct), Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_coe]
  have htreeCard : Fintype.card FtsTree = ftsTrees - 1 := Fintype.card_fin _
  simp_rw [htreeCard]
  have hselected : ∀ selected : {s : Finset (Fin signatures) // s.card = distinct},
      selected.1.card ^ (ftsTrees - 1) = distinct ^ (ftsTrees - 1) := by
    intro selected
    rw [selected.2]
  simp_rw [hselected]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset_len, Fintype.card_fin,
    nsmul_eq_mul]
  simp

theorem fewTimePattern_card_le_pow (signatures distinct : Nat) :
    Nat.factorial distinct * Fintype.card (FewTimePattern signatures distinct)
      ≤ signatures ^ distinct * distinct ^ (ftsTrees - 1) := by
  rw [fewTimePattern_card, ← Nat.mul_assoc]
  exact Nat.mul_le_mul_right _ (factorial_mul_choose_le_pow signatures distinct)

theorem fewTimePattern_card_scaled_le_signatureLimit {signatures distinct : Nat}
    (hsignatures : signatures ≤ signatureLimit) :
    Nat.factorial distinct * Fintype.card (FewTimePattern signatures distinct) ≤
      2 ^ (24 * distinct) * distinct ^ (ftsTrees - 1) := by
  calc
    Nat.factorial distinct * Fintype.card (FewTimePattern signatures distinct)
        ≤ signatures ^ distinct * distinct ^ (ftsTrees - 1) :=
      fewTimePattern_card_le_pow signatures distinct
    _ ≤ signatureLimit ^ distinct * distinct ^ (ftsTrees - 1) := by
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hsignatures distinct)
    _ = 2 ^ (24 * distinct) * distinct ^ (ftsTrees - 1) := by
      rw [signatureLimit, pow_mul]

theorem fewTimePattern_scaled_sum_le {signatures : Nat}
    (hsignatures : signatures ≤ signatureLimit) :
    Nat.factorial 14 *
        ∑ distinct ∈ Finset.Icc 1 14,
          Fintype.card (FewTimePattern signatures distinct) * 2 ^ (26 * (14 - distinct))
      ≤ Nat.factorial 14 * 2 ^ 382 := by
  rw [Finset.mul_sum]
  calc
    ∑ distinct ∈ Finset.Icc 1 14,
          Nat.factorial 14 *
            (Fintype.card (FewTimePattern signatures distinct) * 2 ^ (26 * (14 - distinct)))
        ≤ ∑ distinct ∈ Finset.Icc 1 14,
            (distinct + 1).ascFactorial (14 - distinct) * 2 ^ (24 * distinct) *
              distinct ^ 14 * 2 ^ (26 * (14 - distinct)) := by
          apply Finset.sum_le_sum
          intro distinct hdistinct
          have hle : distinct ≤ 14 := (Finset.mem_Icc.mp hdistinct).2
          have hfactorial : Nat.factorial distinct *
              (distinct + 1).ascFactorial (14 - distinct) = Nat.factorial 14 := by
            rw [Nat.factorial_mul_ascFactorial, Nat.add_sub_of_le hle]
          calc
            Nat.factorial 14 *
                (Fintype.card (FewTimePattern signatures distinct) *
                  2 ^ (26 * (14 - distinct))) =
              (distinct + 1).ascFactorial (14 - distinct) *
                (Nat.factorial distinct * Fintype.card (FewTimePattern signatures distinct)) *
                  2 ^ (26 * (14 - distinct)) := by rw [← hfactorial]; ring
            _ ≤ (distinct + 1).ascFactorial (14 - distinct) *
                (2 ^ (24 * distinct) * distinct ^ (ftsTrees - 1)) *
                  2 ^ (26 * (14 - distinct)) := by
              exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
                (fewTimePattern_card_scaled_le_signatureLimit
                  (signatures := signatures) (distinct := distinct) hsignatures))
            _ = (distinct + 1).ascFactorial (14 - distinct) * 2 ^ (24 * distinct) *
                distinct ^ 14 * 2 ^ (26 * (14 - distinct)) := by
              rw [show ftsTrees - 1 = 14 by decide]
              ring
    _ ≤ Nat.factorial 14 * 2 ^ 382 := by exact leak_union_bound_scaled_sum

theorem fewTimePattern_sum_le {signatures : Nat}
    (hsignatures : signatures ≤ signatureLimit) :
    (∑ distinct ∈ Finset.Icc 1 14,
        Fintype.card (FewTimePattern signatures distinct) * 2 ^ (26 * (14 - distinct)))
      ≤ 2 ^ 382 :=
  Nat.le_of_mul_le_mul_left (fewTimePattern_scaled_sum_le hsignatures)
    (Nat.factorial_pos 14)

noncomputable def FewTimeCover.pattern {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves) :
    FewTimePattern signingLog.length cover.entries.card where
  selected := cover.logIndices
  card_selected := cover.logIndices_card
  assignment := fun tree =>
    let entry : cover.entries := ⟨(cover.select tree).entry.flat, cover.entry_mem_entries tree⟩
    ⟨cover.logIndex entry, Finset.mem_image.2 ⟨entry, Finset.mem_univ _, rfl⟩⟩

end SphincsSecurity.Concrete
