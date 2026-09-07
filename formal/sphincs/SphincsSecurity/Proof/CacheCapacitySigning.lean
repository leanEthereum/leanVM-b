import SphincsSecurity.Proof.CacheCapacity
import SphincsSecurity.Proof.FutureCoverageCacheGrowth

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def cacheCapacityPotential (remaining : Nat) (key : SecretKey) (q : Nat) (state : CoverLogState) : ENNReal :=
  cachedFutureCoverage remaining key.parameter key.root state.1 state.2 +
    cacheCapacity q state.1 * (observedLogOccupancyCompletion remaining key state * ((2 ^ 176 : Nat) : ENNReal)⁻¹)

noncomputable def cacheCapacityReuseCharge (remaining : Nat) (key : SecretKey) (q : Nat)
    (state : CoverLogState) (message : Message) : ENNReal :=
  cachedFutureCoverageReuseCharge remaining key message state.1 state.2 q +
    cacheCapacity q state.1 * (occupancyCompletionReuseCharge remaining key q state message * ((2 ^ 176 : Nat) : ENNReal)⁻¹)

theorem expected_logTraced_sign_cachedFutureCoverage_le_growth (remaining : Nat) (key : SecretKey) (q : Nat)
    (hq : q ≤ 2 ^ 127) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (message : Message) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      cachedFutureCoverage remaining key.parameter key.root result.2.1 result.2.2) ≤
      cachedFutureCoverage (remaining + 1) key.parameter key.root state.1 state.2 +
        (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
          (QueryCache.enncard result.2.1 - QueryCache.enncard state.1)) *
          (observedLogOccupancyCompletion remaining key state * ((2 ^ 176 : Nat) : ENNReal)⁻¹) +
        cachedFutureCoverageReuseCharge remaining key message state.1 state.2 q := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul, tsum_probOutput_map_mul]
  have hrun : (unloggedMappedAdversaryImpl key (.inr message)).run state.1 =
      (fun result => (result.1.1, result.2)) <$> (simulateQ romImpl (signWithView key message)).run state.1 :=
    (simulateQ_signWithView_fst_run key message state.1).symm
  rw [hrun, tsum_probOutput_map_mul, tsum_probOutput_map_mul]
  exact expected_signWithView_cachedFutureCoverage_le_growth remaining key message state.1 state.2 hsigned q hq hcache

theorem expected_logTraced_sign_cacheCapacityPotential_le (remaining : Nat) (key : SecretKey) (q : Nat)
    (hq : q ≤ 2 ^ 127) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (message : Message)
    (hcap : ∀ result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state),
      QueryCache.enncard result.2.1 ≤ q) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      cacheCapacityPotential remaining key q result.2) ≤
      cacheCapacityPotential (remaining + 1) key q state + cacheCapacityReuseCharge remaining key q state message := by
  let computation := (logTracedMappedAdversaryImpl key (.inr message)).run state
  let rate : ENNReal := ((2 ^ 176 : Nat) : ENNReal)⁻¹
  let lower := observedLogOccupancyCompletion remaining key state * rate
  let weight := fun result : Option Signature × CoverLogState => observedLogOccupancyCompletion remaining key result.2 * rate
  have hreserve := expected_cacheCapacity_reserve_le computation q state.1 (fun result => result.2.1) lower weight
    (fun result hresult => logTracedMappedAdversaryImpl_cache_le key (.inr message) state result hresult) hcap
    (fun result hresult => mul_le_mul' (observedLogOccupancyCompletion_mono remaining key state result.2
      (logTracedMappedAdversaryImpl_cache_le key (.inr message) state result hresult)
      (logTracedMappedAdversaryImpl_log_prefix key (.inr message) state result hresult) hsigned) le_rfl)
  have hoccupancy : (∑' result, Pr[= result | computation] * weight result) ≤
      (observedLogOccupancyCompletion (remaining + 1) key state + occupancyCompletionReuseCharge remaining key q state message) * rate := by
    simp only [weight, ← mul_assoc, ENNReal.tsum_mul_right]
    exact mul_le_mul' (expected_logTraced_sign_occupancyCompletion_le remaining key q hq state hsigned hcache message) le_rfl
  simp only [cacheCapacityPotential, mul_add, ENNReal.tsum_add]
  calc
    _ ≤ (cachedFutureCoverage (remaining + 1) key.parameter key.root state.1 state.2 +
          (∑' result, Pr[= result | computation] * (QueryCache.enncard result.2.1 - QueryCache.enncard state.1)) * lower +
          cachedFutureCoverageReuseCharge remaining key message state.1 state.2 q) +
        (∑' result, Pr[= result | computation] * (cacheCapacity q result.2.1 * weight result)) :=
      add_le_add (expected_logTraced_sign_cachedFutureCoverage_le_growth remaining key q hq state hsigned hcache message) le_rfl
    _ = (cachedFutureCoverage (remaining + 1) key.parameter key.root state.1 state.2 +
          cachedFutureCoverageReuseCharge remaining key message state.1 state.2 q) +
        ((∑' result, Pr[= result | computation] * (QueryCache.enncard result.2.1 - QueryCache.enncard state.1)) * lower +
          (∑' result, Pr[= result | computation] * (cacheCapacity q result.2.1 * weight result))) := by ac_rfl
    _ ≤ (cachedFutureCoverage (remaining + 1) key.parameter key.root state.1 state.2 +
          cachedFutureCoverageReuseCharge remaining key message state.1 state.2 q) +
        cacheCapacity q state.1 * ((observedLogOccupancyCompletion (remaining + 1) key state +
          occupancyCompletionReuseCharge remaining key q state message) * rate) :=
      add_le_add le_rfl (hreserve.trans (mul_le_mul' le_rfl hoccupancy))
    _ = _ := by
      unfold cacheCapacityReuseCharge rate
      simp only [add_mul, mul_add]
      ac_rfl

end SphincsSecurity.Concrete
