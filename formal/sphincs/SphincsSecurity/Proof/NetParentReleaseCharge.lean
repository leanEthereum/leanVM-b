import SphincsSecurity.Proof.StoppedParentReleaseBound

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition parentReserve directParentRelease
set_option backward.isDefEq.respectTransparency false

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
  (eligible : Position → Prop)

theorem directParentRelease_le_released
    {cache : QueryCache HashSpec} {input : HashInput} {answer : HashOutput} (hfresh : cache input = none) :
    directParentRelease parameter otsSecret ftsSecret eligible cache input ≤
      releasedParentReserve parameter otsSecret ftsSecret eligible cache (cache.cacheQuery input answer) := by
  unfold directParentRelease releasedParentReserve
  apply Finset.sum_le_sum
  intro parent _
  by_cases hr : ReadyParentRelease parameter otsSecret ftsSecret cache input parent
  · have hc := ReadyParentRelease.newly_settled_children parameter otsSecret ftsSecret (answer := answer) hfresh hr
    rw [if_pos hr, parentReserveContribution, releasedParentReserveAt]
    by_cases he : eligible parent
    · rw [if_pos ⟨he, hc.1⟩, if_pos ⟨he, hc.1, hc.2⟩]
    · rw [if_neg (fun h => he h.1), if_neg (fun h => he h.1)]
  · rw [if_neg hr]
    exact Nat.zero_le _

theorem directParentQueryCharge_le_released (cache : QueryCache HashSpec) (input : HashInput) :
    directParentQueryCharge parameter otsSecret ftsSecret eligible cache input ≤
      releasedParentQueryCharge parameter otsSecret ftsSecret eligible cache input := by
  by_cases hfresh : cache input = none
  · rw [directParentQueryCharge, if_pos hfresh, releasedParentQueryCharge, randomOracle,
      QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
    calc
      _ = ∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (directParentRelease parameter otsSecret ftsSecret eligible cache input : ENNReal) := by
        rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
      _ ≤ _ := ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl
        (Nat.cast_le.mpr (directParentRelease_le_released parameter otsSecret ftsSecret eligible (answer := answer) hfresh))
  · rw [directParentQueryCharge, if_neg hfresh]
    exact zero_le

theorem releasedParentReserve_add_discard_le_direct_add_remaining
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (hsub : ∀ cache input answer, exception cache input answer → ParentSettlement parameter otsSecret ftsSecret cache input answer)
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {input : HashInput} {answer : HashOutput} (hfresh : cache input = none) :
    releasedParentReserve parameter otsSecret ftsSecret eligible cache (cache.cacheQuery input answer) +
      (if exception cache input answer then parentReserve parameter otsSecret ftsSecret eligible (cache.cacheQuery input answer) else 0) ≤
      directParentRelease parameter otsSecret ftsSecret eligible cache input +
        if ParentSettlement parameter otsSecret ftsSecret cache input answer then
          parentReserve parameter otsSecret ftsSecret eligible cache - directParentRelease parameter otsSecret ftsSecret eligible cache input else 0 := by
  by_cases hp : ParentSettlement parameter otsSecret ftsSecret cache input answer
  · rw [if_pos hp, Nat.add_sub_of_le (directParentRelease_le_before parameter otsSecret ftsSecret eligible cache input)]
    by_cases he : exception cache input answer
    · obtain ⟨parent, hr⟩ := ParentSettlement.exists_ready_release parameter otsSecret ftsSecret hp
      have hz := freshParentReserveCharge_eq_zero_of_ready parameter otsSecret ftsSecret eligible hr
      rw [freshParentReserveCharge, if_pos hfresh, Nat.cast_eq_zero] at hz
      have hbalance := parentReserve_cacheQuery_add_released_eq parameter otsSecret ftsSecret eligible (answer := answer) hfinite hfresh
      rw [hz, Nat.add_zero] at hbalance
      rw [if_pos he, Nat.add_comm, hbalance]
    · rw [if_neg he, Nat.add_zero]
      exact releasedParentReserve_le_before parameter otsSecret ftsSecret eligible cache _
  · rw [if_neg hp, Nat.add_zero, if_neg (fun he => hp (hsub cache input answer he)), Nat.add_zero,
      releasedParentReserve_eq_direct_without_parent parameter otsSecret ftsSecret eligible hfresh hp]

noncomputable def localizedParentReleaseCharge (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  directParentQueryCharge parameter otsSecret ftsSecret eligible cache input +
    ((parentReserve parameter otsSecret ftsSecret eligible cache - directParentRelease parameter otsSecret ftsSecret eligible cache input : Nat) : ENNReal) *
      min 1 (directParentQueryCharge parameter otsSecret ftsSecret (fun _ => True) cache input * ((2 ^ digestBits : Nat) : ENNReal)⁻¹)

theorem localizedParentReleaseCharge_le_direct_add_scaled (cache : QueryCache HashSpec) (input : HashInput) :
    localizedParentReleaseCharge parameter otsSecret ftsSecret eligible cache input ≤
      directParentQueryCharge parameter otsSecret ftsSecret eligible cache input +
        (parentReserve parameter otsSecret ftsSecret eligible cache : ENNReal) *
          directParentQueryCharge parameter otsSecret ftsSecret (fun _ => True) cache input * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  unfold localizedParentReleaseCharge
  rw [mul_assoc]
  exact add_le_add le_rfl (mul_le_mul' (Nat.cast_le.mpr (Nat.sub_le _ _)) (min_le_right _ _))

theorem localizedParentReleaseCharge_le_before (cache : QueryCache HashSpec) (input : HashInput) :
    localizedParentReleaseCharge parameter otsSecret ftsSecret eligible cache input ≤
      (parentReserve parameter otsSecret ftsSecret eligible cache : ENNReal) := by
  unfold localizedParentReleaseCharge
  by_cases hfresh : cache input = none
  · rw [directParentQueryCharge, if_pos hfresh]
    apply (add_le_add le_rfl (mul_le_of_le_one_right' (min_le_left _ _))).trans_eq
    rw [← Nat.cast_add, Nat.add_sub_of_le (directParentRelease_le_before parameter otsSecret ftsSecret eligible cache input)]
  · simp only [directParentQueryCharge, if_neg hfresh, zero_mul, min_eq_right zero_le, mul_zero, add_zero, zero_le]

theorem releasedParentQueryCharge_add_discard_le_localized
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (hsub : ∀ cache input answer, exception cache input answer → ParentSettlement parameter otsSecret ftsSecret cache input answer)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) :
    releasedParentQueryCharge parameter otsSecret ftsSecret eligible cache input +
      exceptionDiscardCharge exception (fun current => (parentReserve parameter otsSecret ftsSecret eligible current : ENNReal)) cache input ≤
      localizedParentReleaseCharge parameter otsSecret ftsSecret eligible cache input := by
  rw [releasedParentQueryCharge, exceptionDiscardCharge, ← ENNReal.tsum_add]
  simp_rw [← mul_add]
  by_cases hfresh : cache input = none
  · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
    let remaining := parentReserve parameter otsSecret ftsSecret eligible cache - directParentRelease parameter otsSecret ftsSecret eligible cache input
    calc
      _ ≤ ∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
          ((directParentRelease parameter otsSecret ftsSecret eligible cache input : ENNReal) +
            if ParentSettlement parameter otsSecret ftsSecret cache input answer then (remaining : ENNReal) else 0) := by
        apply ENNReal.tsum_le_tsum
        intro answer
        apply mul_le_mul' le_rfl
        have h := Nat.cast_le (α := ENNReal).mpr
          (releasedParentReserve_add_discard_le_direct_add_remaining parameter otsSecret ftsSecret eligible exception hsub
            (answer := answer) hfinite hfresh)
        simpa only [queryException, hfresh, true_and, decide_eq_true_eq, Nat.cast_add, Nat.cast_ite, Nat.cast_zero] using h
      _ = (directParentRelease parameter otsSecret ftsSecret eligible cache input : ENNReal) +
          (remaining : ENNReal) * Pr[ParentSettlement parameter otsSecret ftsSecret cache input | ($ᵗ HashOutput : ProbComp HashOutput)] := by
        simp only [mul_add, ENNReal.tsum_add]
        rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
        congr 1
        apply tsum_congr
        intro answer
        split_ifs <;> simp [mul_comm]
      _ ≤ _ := by
        rw [localizedParentReleaseCharge, directParentQueryCharge, if_pos hfresh]
        apply add_le_add le_rfl
        apply mul_le_mul' le_rfl
        apply le_min probEvent_le_one
        simpa only [directParentQueryCharge, if_pos hfresh] using
          probEvent_parentSettlement_le_direct_release parameter otsSecret ftsSecret hfinite hfresh
  · obtain ⟨answer, ha⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [randomOracle, QueryImpl.withCaching_run_some _ ha, tsum_probOutput_pure_mul, releasedParentReserve_refl]
    simp only [Nat.cast_zero, queryException, hfresh, false_and, decide_false, Bool.false_eq_true, if_false,
      add_zero, localizedParentReleaseCharge, directParentQueryCharge, zero_mul, min_eq_right zero_le, mul_zero, le_refl]

theorem releasedParentQueryCharge_le_localized
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) :
    releasedParentQueryCharge parameter otsSecret ftsSecret eligible cache input ≤
      localizedParentReleaseCharge parameter otsSecret ftsSecret eligible cache input :=
  le_self_add.trans (releasedParentQueryCharge_add_discard_le_localized parameter otsSecret ftsSecret eligible
    (fun _ _ _ => False) (fun _ _ _ h => h.elim) cache hfinite input)

end SphincsSecurity
