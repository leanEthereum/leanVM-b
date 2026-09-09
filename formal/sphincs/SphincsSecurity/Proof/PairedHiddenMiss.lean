import SphincsSecurity.Proof.UniformTableRestriction

namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {ι α : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α]

def eraseTableValue (allowed : ι → Finset α) (coordinate : ι) (candidate : α) : ι → Finset α :=
  Function.update allowed coordinate ((allowed coordinate).erase candidate)

omit [Fintype ι] in
theorem eraseTableValue_nonempty (allowed : ι → Finset α)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (coordinate : ι) (candidate : α)
    (hne : ((allowed coordinate).erase candidate).Nonempty) :
    ∀ other, (eraseTableValue allowed coordinate candidate other).Nonempty := by
  intro other
  by_cases heq : other = coordinate <;> simp only [eraseTableValue, Function.update_apply, heq, if_true, if_false]
  · exact hne
  · exact ha other

theorem uniformTable_erase_restrict (allowed : ι → Finset α)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (coordinate : ι) (candidate : α)
    (hne : ((allowed coordinate).erase candidate).Nonempty) (table : ι → α) :
    (if table coordinate ≠ candidate then uniformTable allowed ha table else 0) =
      (((allowed coordinate).erase candidate).card : ENNReal) / (allowed coordinate).card *
        uniformTable (eraseTableValue allowed coordinate candidate)
          (eraseTableValue_nonempty allowed ha coordinate candidate hne) table := by
  classical
  have h := uniformTable_update_restrict allowed ha coordinate ((allowed coordinate).erase candidate)
    hne (Finset.erase_subset _ _) table
  change (if table coordinate ∈ (allowed coordinate).erase candidate then uniformTable allowed ha table else 0) = _ at h
  dsimp only [eraseTableValue]
  rw [← h]
  by_cases ht : table coordinate ∈ allowed coordinate
  · simp only [Finset.mem_erase, ht, and_true]
  · have hz : uniformTable allowed ha table = 0 := by
      rw [uniformTable_apply, if_neg (fun h => ht (h coordinate))]
    simp only [hz, ite_self]

def pairedMissAllowed (allowed : ι → Finset α) (child : ι) (candidate : α) (parent : ι) (answer : α) :
    ι → Finset α := eraseTableValue (eraseTableValue allowed child candidate) parent answer

omit [Fintype ι] in
theorem pairedMissAllowed_nonempty (allowed : ι → Finset α)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (child parent : ι) (hne : child ≠ parent)
    (candidate answer : α) (hc : ((allowed child).erase candidate).Nonempty)
    (hp : ((allowed parent).erase answer).Nonempty) :
    ∀ coordinate, (pairedMissAllowed allowed child candidate parent answer coordinate).Nonempty := by
  apply eraseTableValue_nonempty _ (eraseTableValue_nonempty allowed ha child candidate hc) parent answer
  simpa only [eraseTableValue, Function.update_of_ne hne.symm] using hp

theorem uniformTable_paired_miss_mass (allowed : ι → Finset α)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (child parent : ι) (hne : child ≠ parent)
    (candidate answer : α) (hc : ((allowed child).erase candidate).Nonempty)
    (hp : ((allowed parent).erase answer).Nonempty) (table : ι → α) :
    (if table child ≠ candidate ∧ table parent ≠ answer then uniformTable allowed ha table else 0) =
      ((((allowed child).erase candidate).card : ENNReal) / (allowed child).card *
        (((allowed parent).erase answer).card : ENNReal) / (allowed parent).card) *
          uniformTable (pairedMissAllowed allowed child candidate parent answer)
            (pairedMissAllowed_nonempty allowed ha child parent hne candidate answer hc hp) table := by
  have hc' := eraseTableValue_nonempty allowed ha child candidate hc
  have hp' : ((eraseTableValue allowed child candidate parent).erase answer).Nonempty := by
    simpa only [eraseTableValue, Function.update_of_ne hne.symm] using hp
  have hfirst := uniformTable_erase_restrict allowed ha child candidate hc table
  have hsecond := uniformTable_erase_restrict (eraseTableValue allowed child candidate) hc' parent answer hp' table
  simp only [eraseTableValue, Function.update_of_ne hne.symm] at hsecond
  calc
    _ = if table parent ≠ answer then (if table child ≠ candidate then uniformTable allowed ha table else 0) else 0 := by
      by_cases hchild : table child = candidate <;> by_cases hparent : table parent = answer <;> simp [hchild, hparent]
    _ = if table parent ≠ answer then
        (((allowed child).erase candidate).card : ENNReal) / (allowed child).card *
          uniformTable (eraseTableValue allowed child candidate) hc' table else 0 := by rw [hfirst]
    _ = (((allowed child).erase candidate).card : ENNReal) / (allowed child).card *
        (if table parent ≠ answer then uniformTable (eraseTableValue allowed child candidate) hc' table else 0) := by
      split <;> simp only [mul_zero]
    _ = _ := by
      dsimp only [eraseTableValue]
      rw [hsecond]
      simp only [pairedMissAllowed, eraseTableValue, Function.update_of_ne hne.symm, div_eq_mul_inv, mul_assoc]

omit [Fintype ι] in
theorem pairedMissAllowed_membership (allowed : ι → Finset α) (child parent : ι) (hne : child ≠ parent)
    (candidate answer : α) (table : ι → α) :
    (∀ coordinate, table coordinate ∈ pairedMissAllowed allowed child candidate parent answer coordinate) ↔
      (∀ coordinate, table coordinate ∈ allowed coordinate) ∧ table child ≠ candidate ∧ table parent ≠ answer := by
  constructor
  · intro h
    have hchild := h child
    have hparent := h parent
    simp only [pairedMissAllowed, eraseTableValue, Function.update_of_ne hne, Function.update_self,
      Function.update_of_ne hne.symm, Finset.mem_erase] at hchild hparent
    refine ⟨?_, hchild.1, hparent.1⟩
    intro coordinate
    by_cases hp : coordinate = parent
    · simpa only [hp] using hparent.2
    by_cases hc : coordinate = child
    · simpa only [hc] using hchild.2
    simpa only [pairedMissAllowed, eraseTableValue, Function.update_of_ne hp, Function.update_of_ne hc] using h coordinate
  · rintro ⟨h, hc, hp⟩ coordinate
    by_cases heqp : coordinate = parent
    · subst coordinate
      simp only [pairedMissAllowed, eraseTableValue, Function.update_self, Function.update_of_ne hne.symm,
        Finset.mem_erase]
      exact ⟨hp, h parent⟩
    by_cases heqc : coordinate = child
    · subst coordinate
      simp only [pairedMissAllowed, eraseTableValue, Function.update_of_ne hne, Function.update_self, Finset.mem_erase]
      exact ⟨hc, h child⟩
    simpa only [pairedMissAllowed, eraseTableValue, Function.update_of_ne heqp, Function.update_of_ne heqc] using h coordinate

omit [Fintype ι] in
theorem pairedMissAllowed_card_lower (allowed : ι → Finset α) (child parent : ι) (hne : child ≠ parent)
    (candidate answer : α) (coordinate : ι) :
    (allowed coordinate).card - 1 ≤ (pairedMissAllowed allowed child candidate parent answer coordinate).card := by
  by_cases hp : coordinate = parent
  · subst coordinate
    simpa only [pairedMissAllowed, eraseTableValue, Function.update_self, Function.update_of_ne hne.symm] using
      (Finset.pred_card_le_card_erase (s := allowed parent) (a := answer))
  by_cases hc : coordinate = child
  · subst coordinate
    simpa only [pairedMissAllowed, eraseTableValue, Function.update_of_ne hne, Function.update_self] using
      (Finset.pred_card_le_card_erase (s := allowed child) (a := candidate))
  simpa only [pairedMissAllowed, eraseTableValue, Function.update_of_ne hp, Function.update_of_ne hc] using
    Nat.sub_le (allowed coordinate).card 1

omit [Fintype ι] in
theorem pairedMissAllowed_card_ge (allowed : ι → Finset α) (child parent : ι) (hne : child ≠ parent)
    (candidate answer : α) (minimum : Nat) (hmin : ∀ coordinate, minimum ≤ (allowed coordinate).card) :
    ∀ coordinate, minimum - 1 ≤ (pairedMissAllowed allowed child candidate parent answer coordinate).card := by
  intro coordinate
  exact (Nat.sub_le_sub_right (hmin coordinate) 1).trans
    (pairedMissAllowed_card_lower allowed child parent hne candidate answer coordinate)

omit [Fintype ι] in
theorem pairedMissAllowed_card_active (allowed : ι → Finset α) (active : Finset ι)
    (child parent : ι) (hne : child ≠ parent) (candidate answer : α) (minimum : Nat)
    (hmin : ∀ coordinate ∈ active, minimum ≤ (allowed coordinate).card) :
    ∀ coordinate ∈ active, minimum - 1 ≤ (pairedMissAllowed allowed child candidate parent answer coordinate).card := by
  intro coordinate hcoordinate
  exact (Nat.sub_le_sub_right (hmin coordinate hcoordinate) 1).trans
    (pairedMissAllowed_card_lower allowed child parent hne candidate answer coordinate)

end SphincsSecurity.Concrete
