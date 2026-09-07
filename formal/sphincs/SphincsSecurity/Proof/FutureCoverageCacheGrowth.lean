import SphincsSecurity.Proof.CacheGrowthCharge
import SphincsSecurity.Proof.OccupancyCompletionGrowth
import SphincsSecurity.Proof.CachedFutureCoverage
import SphincsSecurity.Proof.OtsProbeNativeRootQueryCharge

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expected_futureCoverageCharge_le_cacheGrowth {α : Type} {n : Nat}
    (remaining : Nat) (parameter : PublicParameter) (views : HashInput → Fin n → Option FewTimeView)
    (bound : ENNReal) (hbound : ∀ input, coverageOccupancyCompletion (views input) remaining ≤ bound)
    (computation : OracleComp OracleWorld α) (before : QueryCache HashSpec) (hfinite : Finite before) :
    expectedQueryCharge (freshFutureCoverageCharge remaining parameter views) computation before ≤
      (∑' result, Pr[= result | (simulateQ romImpl computation).run before] *
        (QueryCache.enncard result.2 - QueryCache.enncard before)) * (bound * ((2 ^ 176 : Nat) : ENNReal)⁻¹) := by
  have hcharge (cache : QueryCache HashSpec) (input : HashInput) :
      freshFutureCoverageCharge remaining parameter views cache input ≤
        freshCacheCharge cache input * (bound * ((2 ^ 176 : Nat) : ENNReal)⁻¹) := by
    unfold freshFutureCoverageCharge freshCacheCharge
    by_cases hfresh : cache input = none
    · simp only [hfresh, true_and, if_true, one_mul]
      split_ifs
      · exact mul_le_mul' (hbound input) le_rfl
      · exact bot_le
    · simp only [hfresh, false_and, if_false, zero_mul, le_refl]
  apply (expectedQueryCharge_mono _ _ hcharge computation before).trans_eq
  rw [expectedQueryCharge_mul, expectedQueryCharge_fresh_eq_growth computation before hfinite]

theorem expected_newMessageFutureCoverage_le_cacheGrowth {α : Type} {n : Nat}
    (remaining : Nat) (parameter : PublicParameter) (views : HashInput → Fin n → Option FewTimeView)
    (bound : ENNReal) (hbound : ∀ input, coverageOccupancyCompletion (views input) remaining ≤ bound)
    (computation : OracleComp OracleWorld α) (before : QueryCache HashSpec) (hfinite : Finite before) :
    (∑' result, Pr[= result | (simulateQ romImpl computation).run before] *
      newMessageFutureCoverage remaining parameter views before result.2) ≤
      (∑' result, Pr[= result | (simulateQ romImpl computation).run before] *
        (QueryCache.enncard result.2 - QueryCache.enncard before)) * (bound * ((2 ^ 176 : Nat) : ENNReal)⁻¹) :=
  (expected_newMessageFutureCoverage_le remaining parameter views computation before hfinite).trans
    (expected_futureCoverageCharge_le_cacheGrowth remaining parameter views bound hbound computation before hfinite)

theorem expected_signWithView_cachedFutureCoverage_le_growth (remaining : Nat) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard before ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      cachedFutureCoverage remaining key.parameter key.root result.2 (log ++ [⟨message, result.1.1⟩])) ≤
      cachedFutureCoverage (remaining + 1) key.parameter key.root before log +
        (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
          (QueryCache.enncard result.2 - QueryCache.enncard before)) *
          (observedLogOccupancyCompletion remaining key (before, log) * ((2 ^ 176 : Nat) : ENNReal)⁻¹) +
        cachedFutureCoverageReuseCharge remaining key message before log q := by
  apply (expected_signWithView_cachedFutureCoverage_le remaining key message before (Finite.of_enncard_le hcache) log hsigned q hq hcache).trans
  apply add_le_add _ le_rfl
  apply add_le_add le_rfl
  exact expected_futureCoverageCharge_le_cacheGrowth remaining key.parameter
    (fixedSigningViews key.parameter before key.root log) _
    (fun input => eligibleSigningViews_completion_le _ _ _ _ remaining)
    (signWithView key message) before (Finite.of_enncard_le hcache)

end SphincsSecurity.Concrete
