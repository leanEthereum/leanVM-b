import SphincsSecurity.Proof.CachedTargetEnvelope

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem expected_logTraced_sign_cachedTargetEnvelope_le (key : SecretKey) (q signatures : Nat) (hq : q ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (message : Message)
    (hcap : ∀ result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state), QueryCache.enncard result.2.1 ≤ q)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      cachedTargetEnvelope key q signatures result.2 groups remaining) ≤
      cachedTargetEnvelope key q (signatures + 1) state groups remaining +
        (Fintype.card Index : ENNReal)⁻¹ * rawIndexCacheEnvelope key q signatures state groups remaining := by
  have hold : (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      cacheMessageWeight key.parameter (fun input target => targetCacheEnvelope key q (payloadOf input) target signatures result.2 groups remaining) state.1) ≤
      cachedTargetEnvelope key q (signatures + 1) state groups remaining := by
    rw [expected_cacheMessageWeight]
    apply cacheMessageWeight_mono
    intro input target
    exact expected_logTraced_sign_targetCacheEnvelope_le key q (payloadOf input) target signatures hq state hsigned hcache message hcap groups remaining hvalid
  apply le_trans ?_ (add_le_add hold (expected_logTraced_sign_newCachedTargetEnvelope_le key q signatures state hsigned message hcap groups remaining hvalid))
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state)
  · rw [cachedTargetEnvelope_split key q signatures state.1 result.2
      (logTracedMappedAdversaryImpl_cache_le key (.inr message) state result hresult), mul_add]
  · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul, zero_mul, add_zero]

end SphincsSecurity.Concrete
