import SphincsSecurity.Proof.ParentCrossReleaseBudget

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition parentReserve directParentRelease
set_option backward.isDefEq.respectTransparency false

theorem remainingParentReserve_eq_sum (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (eligible : Position → Prop)
    (cache : QueryCache HashSpec) (input : HashInput) :
    parentReserve parameter otsSecret ftsSecret eligible cache - directParentRelease parameter otsSecret ftsSecret eligible cache input =
      ∑ position : Position, if ReadyParentRelease parameter otsSecret ftsSecret cache input position then 0
        else parentReserveContribution parameter otsSecret ftsSecret eligible cache position := by
  have h : directParentRelease parameter otsSecret ftsSecret eligible cache input +
      (∑ position : Position, if ReadyParentRelease parameter otsSecret ftsSecret cache input position then 0
        else parentReserveContribution parameter otsSecret ftsSecret eligible cache position) =
      parentReserve parameter otsSecret ftsSecret eligible cache := by
    unfold directParentRelease parentReserve
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro position _
    split_ifs <;> simp
  omega

theorem remainingParentReserve_le_all (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (eligible : Position → Prop)
    (cache : QueryCache HashSpec) (input : HashInput) :
    parentReserve parameter otsSecret ftsSecret eligible cache - directParentRelease parameter otsSecret ftsSecret eligible cache input ≤
      parentReserve parameter otsSecret ftsSecret (fun _ => True) cache - directParentRelease parameter otsSecret ftsSecret (fun _ => True) cache input := by
  rw [remainingParentReserve_eq_sum, remainingParentReserve_eq_sum]
  apply Finset.sum_le_sum
  intro position _
  split_ifs
  · exact le_rfl
  · unfold parentReserveContribution
    split_ifs <;> simp_all

private theorem mul_add_choose_le_choose_add (a d : Nat) : a * d + a.choose 2 ≤ (a + d).choose 2 := by
  induction d with
  | zero => simp
  | succ d ih =>
      change a * (d + 1) + a.choose 2 ≤ ((a + d) + 1).choose (1 + 1)
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
      nlinarith

private theorem released_pairs_add_remaining_le (p d before after : Nat)
    (hp : p ≤ before) (hd : d ≤ p) (ha : after + d ≤ before) :
    (p - d) * d + after.choose 2 ≤ before.choose 2 := by
  calc
    _ ≤ (before - d) * d + (before - d).choose 2 :=
      Nat.add_le_add (Nat.mul_le_mul_right d (Nat.sub_le_sub_right hp d)) (Nat.choose_le_choose 2 (by omega))
    _ ≤ ((before - d) + d).choose 2 := mul_add_choose_le_choose_add _ _
    _ = _ := by rw [Nat.sub_add_cancel (hd.trans hp)]

namespace Concrete

noncomputable def parentCrossPairPotential (key : SecretKey) (cap : Nat) (cache : QueryCache HashSpec) : ENNReal :=
  (((cacheSlotCount cap cache + parentReserve key.parameter key.otsSecret key.ftsSecret (fun _ => True) cache).choose 2 : Nat) : ENNReal) *
    ((2 ^ digestBits : Nat) : ENNReal)⁻¹

theorem parentCrossPairPotential_le_choose (key : SecretKey) (cap : Nat) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (hcap : QueryCache.enncard cache ≤ cap) :
    parentCrossPairPotential key cap cache ≤ (cap.choose 2 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  have hp := (parentReserve_le_answerPotential key.parameter key.otsSecret key.ftsSecret (fun _ => True) cache).trans
    (answerPotential_le_cachedInputs key.parameter key.otsSecret key.ftsSecret hfinite)
  have hc : {input | cache input ≠ none}.ncard ≤ cap := by
    rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard] at hcap
    exact Nat.cast_le.mp hcap
  apply mul_le_mul' (Nat.cast_le.mpr (Nat.choose_le_choose 2 ?_)) le_rfl
  unfold cacheSlotCount
  omega

theorem crossFtsParentReleaseCharge_add_cacheQuery_pairPotential_le
    (key : SecretKey) (cap : Nat) (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (input : HashInput) (answer : HashOutput) (hfresh : cache input = none)
    (hcap : QueryCache.enncard (cache.cacheQuery input answer) ≤ cap) :
    crossFtsParentReleaseCharge key cache input + parentCrossPairPotential key cap (cache.cacheQuery input answer) ≤
      parentCrossPairPotential key cap cache := by
  have hslots := cacheSlotCount_cacheQuery_succ cap cache input answer hfresh
    (by rwa [enncard_cacheQuery_of_fresh cache input answer hfresh] at hcap)
  have hbalance := parentReserve_cacheQuery_add_released_eq key.parameter key.otsSecret key.ftsSecret (fun _ => True) hfinite hfresh (answer := answer)
  have hrelease := directParentRelease_le_released key.parameter key.otsSecret key.ftsSecret (fun _ => True) hfresh (answer := answer)
  have hcharge : parentReserveCharge key.parameter key.otsSecret key.ftsSecret (fun _ => True) cache input ≤ 1 := by
    unfold parentReserveCharge
    split_ifs <;> omega
  have hpair := released_pairs_add_remaining_le
    (parentReserve key.parameter key.otsSecret key.ftsSecret (fun _ => True) cache)
    (directParentRelease key.parameter key.otsSecret key.ftsSecret (fun _ => True) cache input)
    (cacheSlotCount cap cache + parentReserve key.parameter key.otsSecret key.ftsSecret (fun _ => True) cache)
    (cacheSlotCount cap (cache.cacheQuery input answer) + parentReserve key.parameter key.otsSecret key.ftsSecret (fun _ => True) (cache.cacheQuery input answer))
    (by omega) (directParentRelease_le_before key.parameter key.otsSecret key.ftsSecret (fun _ => True) cache input) (by omega)
  have hcross : crossFtsParentReleaseCharge key cache input ≤
      (((parentReserve key.parameter key.otsSecret key.ftsSecret (fun _ => True) cache -
        directParentRelease key.parameter key.otsSecret key.ftsSecret (fun _ => True) cache input) *
        directParentRelease key.parameter key.otsSecret key.ftsSecret (fun _ => True) cache input : Nat) : ENNReal) *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
    unfold crossFtsParentReleaseCharge
    rw [directParentQueryCharge, if_pos hfresh, Nat.cast_mul, mul_assoc]
    exact mul_le_mul' (Nat.cast_le.mpr (remainingParentReserve_le_all key.parameter key.otsSecret key.ftsSecret _ cache input)) (min_le_right _ _)
  apply (add_le_add hcross le_rfl).trans
  unfold parentCrossPairPotential
  rw [← add_mul, ← Nat.cast_add]
  exact mul_le_mul' (Nat.cast_le.mpr hpair) le_rfl

theorem crossFtsParentReleaseCharge_add_expected_pairPotential_le
    (key : SecretKey) (cap : Nat) (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput)
    (hcap : ∀ result ∈ support ((randomOracle input).run cache), QueryCache.enncard result.2 ≤ cap) :
    crossFtsParentReleaseCharge key cache input +
      (∑' result, Pr[= result | (randomOracle input).run cache] * parentCrossPairPotential key cap result.2) ≤
      parentCrossPairPotential key cap cache := by
  by_cases hfresh : cache input = none
  · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
    calc
      _ = ∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (crossFtsParentReleaseCharge key cache input + parentCrossPairPotential key cap (cache.cacheQuery input answer)) := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
        rfl
      _ ≤ ∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] * parentCrossPairPotential key cap cache := by
        apply ENNReal.tsum_le_tsum
        intro answer
        apply mul_le_mul' le_rfl
        apply crossFtsParentReleaseCharge_add_cacheQuery_pairPotential_le key cap cache hfinite input answer hfresh
        apply hcap (answer, cache.cacheQuery input answer)
        rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, support_map]
        exact ⟨answer, by simp [uniformSampleImpl], rfl⟩
      _ = _ := by rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
  · obtain ⟨answer, ha⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [randomOracle, QueryImpl.withCaching_run_some _ ha, tsum_probOutput_pure_mul]
    simp only [crossFtsParentReleaseCharge, directParentQueryCharge, if_neg hfresh, zero_mul, min_eq_right zero_le, mul_zero, zero_add, le_refl]

theorem hashQueryCharge_cross_add_expected_pairPotential_le
    (key : SecretKey) (cap : Nat) (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : OracleWorld.Domain)
    (hcap : ∀ result ∈ support ((romImpl input).run cache), QueryCache.enncard result.2 ≤ cap) :
    hashQueryCharge (crossFtsParentReleaseCharge key) cache input +
      (∑' result, Pr[= result | (romImpl input).run cache] * parentCrossPairPotential key cap result.2) ≤
      parentCrossPairPotential key cap cache := by
  cases input with
  | inl input =>
      have hrun : (unifFwdImpl HashSpec input).run cache =
          (fun sample => (sample, cache)) <$> (liftM (unifSpec.query input) : ProbComp (unifSpec.Range input)) := by
        simpa [simulateQ_query] using (unifFwdImpl.simulateQ_run
          (hashSpec := HashSpec) (liftM (unifSpec.query input) : ProbComp (unifSpec.Range input)) cache)
      change 0 + (∑' result, Pr[= result | (unifFwdImpl HashSpec input).run cache] * parentCrossPairPotential key cap result.2) ≤ _
      rw [zero_add, hrun, tsum_probOutput_map_mul]
      dsimp only
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one
  | inr input => exact crossFtsParentReleaseCharge_add_expected_pairPotential_le key cap cache hfinite input hcap

theorem expected_crossParentRelease_add_pairPotential_le
    (key : SecretKey) (cap : Nat) (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (hcap : ∀ result ∈ support ((simulateQ romImpl computation).run cache), QueryCache.enncard result.2 ≤ cap) :
    expectedQueryCharge (crossFtsParentReleaseCharge key) computation cache +
      (∑' result, Pr[= result | (simulateQ romImpl computation).run cache] * parentCrossPairPotential key cap result.2) ≤
      parentCrossPairPotential key cap cache := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul, expectedQueryCharge_pure, zero_add, le_refl]
  | query_bind input next ih =>
      have htail (middle : OracleWorld.Range input × QueryCache HashSpec)
          (hm : middle ∈ support ((romImpl input).run cache)) :
          ∀ result ∈ support ((simulateQ romImpl (next middle.1)).run middle.2), QueryCache.enncard result.2 ≤ cap := by
        intro result hr
        apply hcap result
        rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
        exact ⟨middle, hm, hr⟩
      have hstep := hashQueryCharge_cross_add_expected_pairPotential_le key cap cache hfinite input
        (fun middle hm => simulateQ_romImpl_initial_cache_bound cap (next middle.1) middle.2 (htail middle hm))
      rw [expectedQueryCharge_query_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul]
      calc
        _ = hashQueryCharge (crossFtsParentReleaseCharge key) cache input +
            ∑' middle, Pr[= middle | (romImpl input).run cache] *
              (expectedQueryCharge (crossFtsParentReleaseCharge key) (next middle.1) middle.2 +
                ∑' result, Pr[= result | (simulateQ romImpl (next middle.1)).run middle.2] * parentCrossPairPotential key cap result.2) := by
          simp only [mul_add, ENNReal.tsum_add, add_assoc]
        _ ≤ hashQueryCharge (crossFtsParentReleaseCharge key) cache input +
            ∑' middle, Pr[= middle | (romImpl input).run cache] * parentCrossPairPotential key cap middle.2 := by
          apply add_le_add le_rfl
          apply ENNReal.tsum_le_tsum
          intro middle
          by_cases hm : middle ∈ support ((romImpl input).run cache)
          · exact mul_le_mul' le_rfl (ih middle.1 middle.2 (finite_of_mem_support_romImpl hfinite hm) (htail middle hm))
          · rw [probOutput_eq_zero_of_not_mem_support hm, zero_mul, zero_mul]
        _ ≤ _ := hstep

theorem expected_crossParentRelease_le_pairs
    (key : SecretKey) (cap : Nat) (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (hcap : ∀ result ∈ support ((simulateQ romImpl computation).run cache), QueryCache.enncard result.2 ≤ cap) :
    expectedQueryCharge (crossFtsParentReleaseCharge key) computation cache ≤
      (cap.choose 2 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
  (le_self_add.trans (expected_crossParentRelease_add_pairPotential_le key cap computation cache hfinite hcap)).trans
    (parentCrossPairPotential_le_choose key cap cache hfinite (simulateQ_romImpl_initial_cache_bound cap computation cache hcap))

namespace FtsProbeSimulation.JointOriginal

theorem expectedBeforeFailureCrossParentCharge_le_pairs
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (key : SecretKey)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (hit failed : Bool) (cap : Nat)
    (hcap : ∀ result ∈ support (runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed),
      QueryCache.enncard result.1.2.1.2 ≤ cap) :
    expectedBeforeFailureCharge exception (crossFtsParentReleaseCharge key)
      parameter root otsTable ftsTable computation frame cache hit failed ≤ (cap.choose 2 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
  ((expectedBeforeFailureCharge_le_preExceptionCharge exception _ parameter root otsTable ftsTable computation frame cache hit failed).trans
    (expectedPreExceptionCharge_le_queryCharge exception _ _ cache hit)).trans
      (expected_crossParentRelease_le_pairs key cap
        (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation) cache hfinite
        (runWithFailure_original_cache_cap exception parameter root otsTable ftsTable computation frame cache hit failed cap hcap))

end FtsProbeSimulation.JointOriginal
end Concrete
end SphincsSecurity
