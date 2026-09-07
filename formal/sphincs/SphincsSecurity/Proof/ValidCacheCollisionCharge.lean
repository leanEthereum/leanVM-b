import SphincsSecurity.Proof.ValidCacheCollisionBound

namespace SphincsSecurity

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] validCacheEntries digestCollisionCount
set_option backward.isDefEq.respectTransparency false

theorem digestCollisionCount_insertValid_eq (entries : Finset (HashInput × Digest))
    (input : HashInput) (output : HashOutput) (hfresh : ∀ entry ∈ entries, entry.1 ≠ input)
    (hvalid : ∀ entry ∈ entries, TargetSum.ValidDigest entry.2) :
    digestCollisionCount (insertValidDigest entries input output) = digestCollisionCount entries +
      2 * ∑ entry ∈ entries, if entry.2 = truncateHash output then 1 else 0 := by
  unfold insertValidDigest
  split_ifs with hv
  · exact digestCollisionCount_insert entries input _ hfresh
  · have hm : (∑ entry ∈ entries, if entry.2 = truncateHash output then 1 else 0 : Nat) = 0 := by
      apply Finset.sum_eq_zero
      intro entry he
      apply if_neg
      intro hd
      exact hv (hd ▸ hvalid entry he)
    rw [hm, Nat.mul_zero, Nat.add_zero]

theorem uniform_digestCollisionCount_insertValid_eq (entries : Finset (HashInput × Digest))
    (input : HashInput) (hfresh : ∀ entry ∈ entries, entry.1 ≠ input)
    (hvalid : ∀ entry ∈ entries, TargetSum.ValidDigest entry.2) :
    (∑' output : HashOutput, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (digestCollisionCount (insertValidDigest entries input output) : ENNReal)) =
      (digestCollisionCount entries : ENNReal) + 2 * (entries.card : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ := by
  simp_rw [digestCollisionCount_insertValid_eq entries input _ hfresh hvalid]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  simp_rw [mul_add, mul_left_comm (Pr[= _ | _]) (2 : ENNReal)]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul,
    ENNReal.tsum_mul_left, uniform_digestMatchCount, mul_assoc]

noncomputable def validCachePairIncrementCharge (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  if cache input = none then 2 * (validCacheEntries cache).card * (Fintype.card Digest : ENNReal)⁻¹ else 0

theorem expected_randomOracle_validCache_pairs_eq (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) :
    (∑' result, Pr[= result | (randomOracle input).run cache] * (digestCollisionCount (validCacheEntries result.2) : ENNReal)) =
      (digestCollisionCount (validCacheEntries cache) : ENNReal) + validCachePairIncrementCharge cache input := by
  by_cases hfresh : cache input = none
  · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul,
      validCachePairIncrementCharge, if_pos hfresh]
    simp_rw [validCacheEntries_cacheQuery hfinite _ hfresh]
    apply uniform_digestCollisionCount_insertValid_eq _ input (validCacheEntries_fresh hfinite hfresh)
    rintro ⟨other, digest⟩ he
    obtain ⟨_, hv, hd⟩ := (mem_validCacheEntries_iff hfinite).mp he
    exact hd ▸ hv
  · obtain ⟨output, ho⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [randomOracle, QueryImpl.withCaching_run_some _ ho, tsum_probOutput_pure_mul,
      validCachePairIncrementCharge, if_neg hfresh, add_zero]

theorem expected_romImpl_validCache_pairs_eq (cache : QueryCache HashSpec) (hfinite : Finite cache) (query : OracleWorld.Domain) :
    (∑' result, Pr[= result | (romImpl query).run cache] * (digestCollisionCount (validCacheEntries result.2) : ENNReal)) =
      (digestCollisionCount (validCacheEntries cache) : ENNReal) + hashQueryCharge validCachePairIncrementCharge cache query := by
  cases query with
  | inl sample =>
      have hu : (romImpl (.inl sample)).run cache =
          (fun output => (output, cache)) <$> (liftM (unifSpec.query sample) : ProbComp _) := rfl
      rw [hu, tsum_probOutput_map_mul]
      dsimp only
      rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
      simp only [hashQueryCharge, Sum.elim_inl, add_zero]
  | inr input => exact expected_randomOracle_validCache_pairs_eq cache hfinite input

theorem expected_validCache_pairs_eq_queryCharge {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    (∑' result, Pr[= result | (simulateQ romImpl computation).run cache] *
      (digestCollisionCount (validCacheEntries result.2) : ENNReal)) =
      (digestCollisionCount (validCacheEntries cache) : ENNReal) +
        expectedQueryCharge validCachePairIncrementCharge computation cache := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp [simulateQ_pure]
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul,
        expectedQueryCharge_query_bind]
      calc
        _ = ∑' result, Pr[= result | (romImpl query).run cache] *
            ((digestCollisionCount (validCacheEntries result.2) : ENNReal) +
              expectedQueryCharge validCachePairIncrementCharge (next result.1) result.2) := by
          apply tsum_congr
          intro result
          by_cases hr : result ∈ support ((romImpl query).run cache)
          · rw [ih result.1 result.2 (finite_of_mem_support_romImpl hfinite hr)]
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
        _ = _ := by
          simp_rw [mul_add, ENNReal.tsum_add]
          rw [expected_romImpl_validCache_pairs_eq cache hfinite query, add_assoc]

theorem expected_validCache_pairs_empty_eq_queryCharge {α : Type} (computation : OracleComp OracleWorld α) :
    (∑' result, Pr[= result | (simulateQ romImpl computation).run ∅] *
      (digestCollisionCount (validCacheEntries result.2) : ENNReal)) =
        expectedQueryCharge validCachePairIncrementCharge computation ∅ := by
  simpa only [validCacheEntries_empty, digestCollisionCount, Finset.sum_empty, Nat.cast_zero, zero_add] using
    expected_validCache_pairs_eq_queryCharge computation ∅ finite_empty

theorem expected_validCachePairIncrementCharge_scaled_le_127 {α : Type} (computation : OracleComp OracleWorld α)
    (q : Nat) (hbound : computation.IsQueryBoundP (· matches Sum.inr _) q) (hq : q ≤ 2 ^ 127) :
    expectedQueryCharge validCachePairIncrementCharge computation ∅ * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (q : ENNReal) * (1 / 64) * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [← expected_validCache_pairs_empty_eq_queryCharge]
  exact expected_validCache_pairs_scaled_le_127 computation q hbound hq

end SphincsSecurity
