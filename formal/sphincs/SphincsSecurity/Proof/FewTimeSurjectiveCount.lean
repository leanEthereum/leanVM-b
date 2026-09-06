import SphincsSecurity.Proof.FewTimeUsedPatterns
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

namespace SphincsSecurity.Concrete

open scoped Classical

noncomputable def avoidingAssignmentEquiv {α β : Type} (s : Finset β) :
    {f : α → β // ∀ a, f a ∉ s} ≃ (α → {b : β // b ∉ s}) where
  toFun f a := ⟨f.1 a, f.2 a⟩
  invFun f := ⟨fun a => (f a).1, fun a => (f a).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem avoidingAssignment_card {α β : Type} [Fintype α] [Fintype β]
    (s : Finset β) :
    Fintype.card {f : α → β // ∀ a, f a ∉ s} =
      (Fintype.card β - s.card) ^ Fintype.card α := by
  classical
  letI : DecidableEq α := Classical.decEq α
  letI : DecidableEq β := Classical.decEq β
  rw [Fintype.card_congr (avoidingAssignmentEquiv (α := α) s), Fintype.card_fun]
  congr 1
  simp

theorem surjectiveAssignment_card_inclusion_exclusion {α β : Type}
    [Fintype α] [Fintype β] :
    (Fintype.card {f : α → β // Function.Surjective f} : ℤ) =
      ∑ k ∈ Finset.range (Fintype.card β + 1),
        (Fintype.card β).choose k * (-1 : ℤ) ^ k *
          ((Fintype.card β - k) ^ Fintype.card α : Nat) := by
  classical
  letI : DecidableEq α := Classical.decEq α
  letI : DecidableEq β := Classical.decEq β
  let missing : β → Finset (α → β) := fun b => Finset.univ.filter (fun f => ∀ a, f a ≠ b)
  have hsurj : (Finset.univ.inf fun b => (missing b)ᶜ) =
      Finset.univ.filter (fun f : α → β => Function.Surjective f) := by
    ext f
    simp [missing, Function.Surjective, Finset.mem_inf]
  have hav : ∀ s : Finset β, s.inf missing =
      Finset.univ.filter (fun f : α → β => ∀ a, f a ∉ s) := by
    intro s
    ext f
    simp only [Finset.mem_inf, Finset.mem_filter, Finset.mem_univ, true_and, missing]
    aesop
  have h := Finset.inclusion_exclusion_card_inf_compl (Finset.univ : Finset β) missing
  rw [hsurj] at h
  simp_rw [hav] at h
  have hcard (s : Finset β) :
      (Finset.univ.filter (fun f : α → β => ∀ a, f a ∉ s)).card =
        (Fintype.card β - s.card) ^ Fintype.card α := by
    rw [← Fintype.card_subtype]
    exact avoidingAssignment_card s
  simp_rw [hcard] at h
  rw [← Fintype.card_subtype] at h
  rw [h, Finset.sum_powerset]
  simp only [Finset.card_univ]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = ∑ _s ∈ Finset.univ.powersetCard k,
        (-1 : ℤ) ^ k * ((Fintype.card β - k) ^ Fintype.card α : Nat) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [(Finset.mem_powersetCard.mp hs).2]
    _ = _ := by
      rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, nsmul_eq_mul]
      ring

def surjectiveAssignmentCount (domain codomain : Nat) : Nat :=
  (∑ k ∈ Finset.range (codomain + 1),
    (codomain.choose k : ℤ) * (-1 : ℤ) ^ k * ((codomain - k) ^ domain : Nat)).toNat

theorem surjectiveAssignment_card {α β : Type} [Fintype α] [Fintype β] :
    Fintype.card {f : α → β // Function.Surjective f} =
      surjectiveAssignmentCount (Fintype.card α) (Fintype.card β) := by
  unfold surjectiveAssignmentCount
  rw [← surjectiveAssignment_card_inclusion_exclusion (α := α) (β := β), Int.toNat_natCast]

theorem usedFewTimePattern_card_scaled_le_count {signatures distinct : Nat}
    (hsignatures : signatures ≤ signatureLimit) :
    Nat.factorial distinct * Fintype.card (UsedFewTimePattern signatures distinct) ≤
      2 ^ (24 * distinct) * surjectiveAssignmentCount 14 distinct := by
  have h := usedFewTimePattern_card_scaled_le_signatureLimit (distinct := distinct) hsignatures
  have hc := surjectiveAssignment_card (α := FtsTree) (β := Fin distinct)
  simp only [← Nat.card_eq_fintype_card] at h hc ⊢
  rw [hc] at h
  simpa only [Nat.card_fin, show ftsTrees - 1 = 14 by rfl] using h

end SphincsSecurity.Concrete
