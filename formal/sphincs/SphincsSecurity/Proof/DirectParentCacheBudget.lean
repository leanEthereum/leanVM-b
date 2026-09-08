import SphincsSecurity.Proof.NetParentReleaseCharge
import SphincsSecurity.Proof.CacheGrowthCharge

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition parentReserve directParentRelease
set_option backward.isDefEq.respectTransparency false

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
  (eligible : Position → Prop)

theorem parentReserve_le_enncard (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    (parentReserve parameter otsSecret ftsSecret eligible cache : ENNReal) ≤ QueryCache.enncard cache := by
  rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
  exact Nat.cast_le.mpr ((parentReserve_le_answerPotential parameter otsSecret ftsSecret eligible cache).trans
    (answerPotential_le_cachedInputs parameter otsSecret ftsSecret hfinite))

theorem freshParentReserveCharge_le_freshCache (cache : QueryCache HashSpec) (input : HashInput) :
    freshParentReserveCharge parameter otsSecret ftsSecret eligible cache input ≤ Concrete.freshCacheCharge cache input := by
  unfold freshParentReserveCharge Concrete.freshCacheCharge parentReserveCharge
  split_ifs <;> simp

theorem expected_directParentQueryCharge_le_final_cache (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    expectedQueryCharge (directParentQueryCharge parameter otsSecret ftsSecret eligible) computation cache ≤
      ∑' result, Pr[= result | (simulateQ romImpl computation).run cache] * QueryCache.enncard result.2 := by
  calc
    _ ≤ expectedQueryCharge (releasedParentQueryCharge parameter otsSecret ftsSecret eligible) computation cache :=
      expectedQueryCharge_mono _ _ (directParentQueryCharge_le_released parameter otsSecret ftsSecret eligible) computation cache
    _ ≤ (parentReserve parameter otsSecret ftsSecret eligible cache : ENNReal) +
        expectedQueryCharge (freshParentReserveCharge parameter otsSecret ftsSecret eligible) computation cache :=
      le_add_self.trans_eq (expected_parentReserve_add_released_eq_queryCharge parameter otsSecret ftsSecret eligible computation cache hfinite)
    _ ≤ QueryCache.enncard cache + expectedQueryCharge Concrete.freshCacheCharge computation cache :=
      add_le_add (parentReserve_le_enncard parameter otsSecret ftsSecret eligible cache hfinite)
        (expectedQueryCharge_mono _ _ (freshParentReserveCharge_le_freshCache parameter otsSecret ftsSecret eligible) computation cache)
    _ = _ := (Concrete.expected_simulateQ_enncard computation cache).symm

theorem expected_directParentQueryCharge_le_cache_cap (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (cap : Nat)
    (hcap : ∀ result ∈ support ((simulateQ romImpl computation).run cache), QueryCache.enncard result.2 ≤ cap) :
    expectedQueryCharge (directParentQueryCharge parameter otsSecret ftsSecret eligible) computation cache ≤ cap := by
  apply (expected_directParentQueryCharge_le_final_cache parameter otsSecret ftsSecret eligible computation cache hfinite).trans
  calc
    _ ≤ ∑' result, Pr[= result | (simulateQ romImpl computation).run cache] * (cap : ENNReal) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support ((simulateQ romImpl computation).run cache)
      · exact mul_le_mul' le_rfl (hcap result hr)
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

end SphincsSecurity
