import SphincsSecurity.Proof.Sampling
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import VCVio.EvalDist.Defs.Instances

namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem uniformFinset_restrict_mass {α : Type} (source target : Finset α)
    (hs : source.Nonempty) (ht : target.Nonempty) (hsub : target ⊆ source) (value : α) :
    (if value ∈ target then PMF.uniformOfFinset source hs value else 0) =
      ((target.card : ENNReal) / source.card) * PMF.uniformOfFinset target ht value := by
  by_cases hv : value ∈ target
  · rw [if_pos hv, PMF.uniformOfFinset_apply_of_mem hs (hsub hv), PMF.uniformOfFinset_apply_of_mem ht hv]
    have ht0 : (target.card : ENNReal) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ht.card_pos
    rw [div_eq_mul_inv, mul_right_comm, ENNReal.mul_inv_cancel ht0 (by finiteness), one_mul]
  · simp only [hv, if_false, PMF.uniformOfFinset_apply_of_notMem ht hv, mul_zero]

theorem probEvent_uniformFinset_subset {α : Type} (source target : Finset α)
    (hs : source.Nonempty) (ht : target.Nonempty) (hsub : target ⊆ source) :
    Pr[fun value => value ∈ target | PMF.uniformOfFinset source hs] =
      (target.card : ENNReal) / source.card := by
  simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply,
    uniformFinset_restrict_mass source target hs ht hsub, ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

theorem uniformFinset_filter {α : Type} (source target : Finset α)
    (hs : source.Nonempty) (ht : target.Nonempty) (hsub : target ⊆ source) :
    (PMF.uniformOfFinset source hs).filter (target : Set α)
      (by obtain ⟨value, hv⟩ := ht; exact ⟨value, hv, (PMF.mem_support_uniformOfFinset_iff _ _).mpr (hsub hv)⟩) =
        PMF.uniformOfFinset target ht := by
  have hmass : (∑' value, (target : Set α).indicator (PMF.uniformOfFinset source hs) value) =
      (target.card : ENNReal) / source.card := by
    simpa only [Set.indicator_apply, Finset.mem_coe, probEvent_eq_tsum_ite, PMF.probOutput_eq_apply] using
      probEvent_uniformFinset_subset source target hs ht hsub
  have hzero : (target.card : ENNReal) / source.card ≠ 0 := by
    apply ENNReal.div_ne_zero.mpr
    exact ⟨by exact_mod_cast Nat.ne_of_gt ht.card_pos, by finiteness⟩
  have hfinite : (target.card : ENNReal) / source.card ≠ ⊤ := by
    apply ENNReal.div_ne_top
    · finiteness
    · exact_mod_cast Nat.ne_of_gt hs.card_pos
  apply PMF.ext
  intro value
  rw [PMF.filter_apply, hmass]
  simp only [Set.indicator_apply, Finset.mem_coe, uniformFinset_restrict_mass source target hs ht hsub]
  rw [mul_right_comm, ENNReal.mul_inv_cancel hzero hfinite, one_mul]

variable {ι α : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α]

noncomputable def uniformTable (allowed : ι → Finset α) (hallowed : ∀ coordinate, (allowed coordinate).Nonempty) :
    PMF (ι → α) := PMF.uniformOfFinset (Fintype.piFinset allowed) (Fintype.piFinset_nonempty.mpr hallowed)

theorem uniformTable_apply (allowed : ι → Finset α) (hallowed : ∀ coordinate, (allowed coordinate).Nonempty)
    (table : ι → α) :
    uniformTable allowed hallowed table =
      if ∀ coordinate, table coordinate ∈ allowed coordinate then
        ((∏ coordinate, (allowed coordinate).card : Nat) : ENNReal)⁻¹ else 0 := by
  simp only [uniformTable, PMF.uniformOfFinset_apply, Fintype.mem_piFinset, Fintype.card_piFinset]

theorem uniformTable_restrict (allowed reduced : ι → Finset α)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (hr : ∀ coordinate, (reduced coordinate).Nonempty)
    (hsub : ∀ coordinate, reduced coordinate ⊆ allowed coordinate) (table : ι → α) :
    (if ∀ coordinate, table coordinate ∈ reduced coordinate then uniformTable allowed ha table else 0) =
      (((∏ coordinate, (reduced coordinate).card : Nat) : ENNReal) /
        ((∏ coordinate, (allowed coordinate).card : Nat) : ENNReal)) * uniformTable reduced hr table := by
  simpa only [uniformTable, Fintype.mem_piFinset, Fintype.card_piFinset] using
    uniformFinset_restrict_mass (Fintype.piFinset allowed) (Fintype.piFinset reduced)
      (Fintype.piFinset_nonempty.mpr ha) (Fintype.piFinset_nonempty.mpr hr)
      (Fintype.piFinset_subset reduced allowed hsub) table

omit [DecidableEq α] in
theorem uniformTable_condition (allowed reduced : ι → Finset α)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (hr : ∀ coordinate, (reduced coordinate).Nonempty)
    (hsub : ∀ coordinate, reduced coordinate ⊆ allowed coordinate) :
    (uniformTable allowed ha).filter (Fintype.piFinset reduced : Set (ι → α))
      (by obtain ⟨table, ht⟩ := Fintype.piFinset_nonempty.mpr hr
          exact ⟨table, ht, (PMF.mem_support_uniformOfFinset_iff _ _).mpr
            (Fintype.piFinset_subset reduced allowed hsub ht)⟩) = uniformTable reduced hr :=
  uniformFinset_filter (Fintype.piFinset allowed) (Fintype.piFinset reduced)
    (Fintype.piFinset_nonempty.mpr ha) (Fintype.piFinset_nonempty.mpr hr)
    (Fintype.piFinset_subset reduced allowed hsub)

end SphincsSecurity.Concrete
