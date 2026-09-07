import SphincsSecurity.Proof.CacheCapacitySigning

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
set_option backward.isDefEq.respectTransparency false

theorem expected_fixedLog_cacheCapacityPotential_le {α : Type} (remaining : Nat) (key : SecretKey) (q : Nat)
    (state : CoverLogState) (hfinite : Finite state.1)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (computation : OracleComp OracleWorld α)
    (hcap : ∀ result ∈ support ((simulateQ romImpl computation).run state.1), QueryCache.enncard result.2 ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl computation).run state.1] *
      cacheCapacityPotential remaining key q (result.2, state.2)) ≤ cacheCapacityPotential remaining key q state := by
  let run := (simulateQ romImpl computation).run state.1
  let rate : ENNReal := ((2 ^ 176 : Nat) : ENNReal)⁻¹
  let lower := observedLogOccupancyCompletion remaining key state * rate
  have hstable (result : α × QueryCache HashSpec) (hresult : result ∈ support run) :
      observedLogOccupancyCompletion remaining key (result.2, state.2) = observedLogOccupancyCompletion remaining key state := by
    unfold observedLogOccupancyCompletion
    rw [observedOptionalSigningViews_cache_stable key.parameter key.root state.1 result.2 state.2
      (simulateQ_romImpl_cache_le computation state.1 result hresult) hsigned]
  have hcover : (∑' result, Pr[= result | run] * cachedFutureCoverage remaining key.parameter key.root result.2 state.2) ≤
      cachedFutureCoverage remaining key.parameter key.root state.1 state.2 +
        (∑' result, Pr[= result | run] * (QueryCache.enncard result.2 - QueryCache.enncard state.1)) * lower :=
    (expected_cachedFutureCoverage_fixedLog_le remaining key.parameter key.root state.1 hfinite state.2 hsigned computation).trans
      (add_le_add le_rfl (expected_futureCoverageCharge_le_cacheGrowth remaining key.parameter
        (fixedSigningViews key.parameter state.1 key.root state.2) _
        (fun input => eligibleSigningViews_completion_le _ _ _ _ remaining) computation state.1 hfinite))
  have hreserve := expected_cacheCapacity_reserve_le run q state.1 Prod.snd lower (fun _ => lower)
    (fun result hresult => simulateQ_romImpl_cache_le computation state.1 result hresult) hcap (fun _ _ => le_rfl)
  have heq : (∑' result, Pr[= result | run] * cacheCapacityPotential remaining key q (result.2, state.2)) =
      (∑' result, Pr[= result | run] * cachedFutureCoverage remaining key.parameter key.root result.2 state.2) +
        (∑' result, Pr[= result | run] * (cacheCapacity q result.2 * lower)) := by
    rw [← ENNReal.tsum_add]
    apply tsum_congr
    intro result
    by_cases hresult : result ∈ support run
    · simp only [cacheCapacityPotential, hstable result hresult, mul_add]
      rfl
    · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul, zero_mul, add_zero]
  change _ ≤ cachedFutureCoverage remaining key.parameter key.root state.1 state.2 + cacheCapacity q state.1 * lower
  rw [heq]
  apply (add_le_add hcover le_rfl).trans
  rw [add_assoc]
  apply add_le_add le_rfl
  apply hreserve.trans
  rw [ENNReal.tsum_mul_right]
  exact mul_le_mul' le_rfl (mul_le_of_le_one_left' tsum_probOutput_le_one)

theorem expected_world_cacheCapacityPotential_le (remaining : Nat) (key : SecretKey) (q : Nat)
    (state : CoverLogState) (hfinite : Finite state.1)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) (input : OracleWorld.Domain)
    (hcap : ∀ result ∈ support ((logTracedMappedAdversaryImpl key (.inl input)).run state), QueryCache.enncard result.2.1 ≤ q) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl input)).run state] *
      cacheCapacityPotential remaining key q result.2) ≤ cacheCapacityPotential remaining key q state := by
  have hbase (result : OracleWorld.Range input × QueryCache HashSpec)
      (hresult : result ∈ support ((romImpl input).run state.1)) : QueryCache.enncard result.2 ≤ q := by
    apply hcap (result.1, (result.2, state.2))
    rw [logTracedMappedAdversaryImpl_run_map, support_map]
    refine ⟨result, ?_, ?_⟩
    · simpa only [unloggedMappedAdversaryImpl, OracleSpec.Range, OracleSpec.add_apply_inl] using hresult
    · simp only [signingLogFragment, List.append_nil]
  have hbound := expected_fixedLog_cacheCapacityPotential_le remaining key q state hfinite hsigned (OracleSpec.query input)
    (fun result hresult => hbase result (by simpa only [simulateQ_spec_query] using hresult))
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  simpa only [signingLogFragment, List.append_nil, simulateQ_spec_query, unloggedMappedAdversaryImpl,
    OracleSpec.Range, OracleSpec.add_apply_inl] using hbound

end SphincsSecurity.Concrete
