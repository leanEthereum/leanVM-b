import SphincsSecurity.Proof.WorldMixedMomentEnvelope

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem cacheSlotCount_antitone (q : Nat) (before after : QueryCache HashSpec)
    (hcache : before ≤ after) (hcap : QueryCache.enncard after ≤ q) : cacheSlotCount q after ≤ cacheSlotCount q before := by
  have hafter := Finite.of_enncard_le hcap
  have hbefore := Finite.of_enncard_le ((QueryCache.enncard_mono hcache).trans hcap)
  have h : (cacheSlotCount q after : ENNReal) ≤ (cacheSlotCount q before : ENNReal) := by
    rw [cacheSlotCount_cast q after hafter, cacheSlotCount_cast q before hbefore]
    exact tsub_le_tsub_left (QueryCache.enncard_mono hcache) _
  exact_mod_cast h

noncomputable def mixedCacheEnvelope (key : SecretKey) (q remaining signatures : Nat) (state : CoverLogState) : MixedMomentVector :=
  mixedRemainingEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal)) (cacheSlotCount q state.1) signatures
    (observedMixedDerivativeVector key remaining state)

theorem expected_randomOracle_mixedCacheEnvelope_le (key : SecretKey) (q remaining signatures : Nat)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hcap : ∀ result ∈ support ((randomOracle input).run before), QueryCache.enncard result.2 ≤ q) (power order : Nat) :
    (∑' result, Pr[= result | (randomOracle input).run before] *
      mixedCacheEnvelope key q remaining signatures (result.2, log) power order) ≤
      mixedCacheEnvelope key q remaining signatures (before, log) power order := by
  by_cases hfresh : before input = none
  · have hcap' : QueryCache.enncard before + 1 ≤ q := by
      have hdefault : (default : HashOutput) ∈ support ($ᵗ HashOutput : ProbComp HashOutput) := by simp
      have h := hcap (default, before.cacheQuery input default) (by
        rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, support_map]
        exact ⟨default, hdefault, rfl⟩)
      rwa [enncard_cacheQuery_of_fresh before input default hfresh] at h
    let slots := cacheSlotCount q (before.cacheQuery input default)
    have hbefore : cacheSlotCount q before = slots + 1 := cacheSlotCount_cacheQuery_succ q before input default hfresh hcap'
    have hslots (output : HashOutput) : cacheSlotCount q (before.cacheQuery input output) = slots := by
      have h := cacheSlotCount_cacheQuery_succ q before input output hfresh hcap'
      omega
    rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
    simp only [mixedCacheEnvelope, hslots, hbefore]
    exact expected_fresh_remainingEnvelope_le key q remaining slots signatures before log input hfresh hsigned power order
  · obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [randomOracle, QueryImpl.withCaching_run_some _ houtput, tsum_probOutput_pure_mul]

theorem expected_romImpl_mixedCacheEnvelope_le (key : SecretKey) (q remaining signatures : Nat)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : OracleWorld.Domain)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hcap : ∀ result ∈ support ((romImpl input).run before), QueryCache.enncard result.2 ≤ q) (power order : Nat) :
    (∑' result, Pr[= result | (romImpl input).run before] *
      mixedCacheEnvelope key q remaining signatures (result.2, log) power order) ≤
      mixedCacheEnvelope key q remaining signatures (before, log) power order := by
  cases input with
  | inl input =>
      have hrun : (unifFwdImpl HashSpec input).run before =
          (fun sample => (sample, before)) <$> (liftM (unifSpec.query input) : ProbComp (unifSpec.Range input)) := by
        simpa [simulateQ_query] using (unifFwdImpl.simulateQ_run
          (hashSpec := HashSpec) (liftM (unifSpec.query input) : ProbComp (unifSpec.Range input)) before)
      change (∑' result, Pr[= result | (unifFwdImpl HashSpec input).run before] *
        mixedCacheEnvelope key q remaining signatures (result.2, log) power order) ≤ _
      rw [hrun, tsum_probOutput_map_mul]
      dsimp only
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one
  | inr input => exact expected_randomOracle_mixedCacheEnvelope_le key q remaining signatures before log input hsigned hcap power order

theorem expected_logTraced_world_mixedCacheEnvelope_le (key : SecretKey) (q remaining signatures : Nat)
    (state : CoverLogState) (input : OracleWorld.Domain) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcap : ∀ result ∈ support ((logTracedMappedAdversaryImpl key (.inl input)).run state), QueryCache.enncard result.2.1 ≤ q)
    (power order : Nat) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl input)).run state] *
      mixedCacheEnvelope key q remaining signatures result.2 power order) ≤ mixedCacheEnvelope key q remaining signatures state power order := by
  have hbase (result : OracleWorld.Range input × QueryCache HashSpec)
      (hresult : result ∈ support ((romImpl input).run state.1)) : QueryCache.enncard result.2 ≤ q := by
    apply hcap (result.1, (result.2, state.2))
    rw [logTracedMappedAdversaryImpl_run_map, support_map]
    refine ⟨result, ?_, ?_⟩
    · simpa only [unloggedMappedAdversaryImpl, OracleSpec.Range, OracleSpec.add_apply_inl] using hresult
    · simp only [signingLogFragment, List.append_nil]
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  simpa only [signingLogFragment, List.append_nil, unloggedMappedAdversaryImpl, OracleSpec.Range, OracleSpec.add_apply_inl] using
    expected_romImpl_mixedCacheEnvelope_le key q remaining signatures state.1 state.2 input hsigned hbase power order

theorem expected_logTraced_sign_mixedCacheEnvelope_le (key : SecretKey) (q remaining signatures : Nat) (hq : q ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (message : Message)
    (hcap : ∀ result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state), QueryCache.enncard result.2.1 ≤ q)
    (power order : Nat) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      mixedCacheEnvelope key q remaining signatures result.2 power order) ≤
      mixedCacheEnvelope key q remaining (signatures + 1) state power order := by
  apply le_trans ?_ (expected_logTraced_sign_remainingEnvelope_le key q remaining (cacheSlotCount q state.1) signatures
    hq state hsigned hcache message power order)
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state)
  · apply mul_le_mul' le_rfl
    exact mixedRemainingEnvelope_queries_mono _ _ _ signatures _
      (cacheSlotCount_antitone q state.1 result.2.1 (logTracedMappedAdversaryImpl_cache_le key (.inr message) state result hresult)
        (hcap result hresult)) power order
  · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]

end SphincsSecurity.Concrete
