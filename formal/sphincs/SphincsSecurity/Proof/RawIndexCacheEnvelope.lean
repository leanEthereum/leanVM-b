import SphincsSecurity.Proof.WorldRawIndexEnvelope
import SphincsSecurity.Proof.MixedCacheEnvelope

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def rawIndexCacheEnvelope (key : SecretKey) (q : Nat) (signatures : Nat) (state : CoverLogState) : TargetShapeVector :=
  targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) (cacheSlotCount q state.1) signatures
    (observedRawIndexShapeVector key state)

theorem expected_randomOracle_rawIndexCacheEnvelope_le (key : SecretKey) (q : Nat) (signatures : Nat)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hcap : ∀ result ∈ support ((randomOracle input).run before), QueryCache.enncard result.2 ≤ q) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (randomOracle input).run before] *
      rawIndexCacheEnvelope key q signatures (result.2, log) groups remaining) ≤
      rawIndexCacheEnvelope key q signatures (before, log) groups remaining := by
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
    simp only [rawIndexCacheEnvelope, hslots, hbefore]
    exact expected_fresh_rawIndexEnvelope_le key q slots signatures before log input hfresh hsigned groups remaining hvalid
  · obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [randomOracle, QueryImpl.withCaching_run_some _ houtput, tsum_probOutput_pure_mul]

theorem expected_romImpl_rawIndexCacheEnvelope_le (key : SecretKey) (q : Nat) (signatures : Nat)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : OracleWorld.Domain)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hcap : ∀ result ∈ support ((romImpl input).run before), QueryCache.enncard result.2 ≤ q) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (romImpl input).run before] *
      rawIndexCacheEnvelope key q signatures (result.2, log) groups remaining) ≤
      rawIndexCacheEnvelope key q signatures (before, log) groups remaining := by
  cases input with
  | inl input =>
      have hrun : (unifFwdImpl HashSpec input).run before =
          (fun sample => (sample, before)) <$> (liftM (unifSpec.query input) : ProbComp (unifSpec.Range input)) := by
        simpa [simulateQ_query] using (unifFwdImpl.simulateQ_run
          (hashSpec := HashSpec) (liftM (unifSpec.query input) : ProbComp (unifSpec.Range input)) before)
      change (∑' result, Pr[= result | (unifFwdImpl HashSpec input).run before] *
        rawIndexCacheEnvelope key q signatures (result.2, log) groups remaining) ≤ _
      rw [hrun, tsum_probOutput_map_mul]
      dsimp only
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one
  | inr input => exact expected_randomOracle_rawIndexCacheEnvelope_le key q signatures before log input hsigned hcap groups remaining hvalid

theorem expected_logTraced_world_rawIndexCacheEnvelope_le (key : SecretKey) (q : Nat) (signatures : Nat)
    (state : CoverLogState) (input : OracleWorld.Domain) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcap : ∀ result ∈ support ((logTracedMappedAdversaryImpl key (.inl input)).run state), QueryCache.enncard result.2.1 ≤ q)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl input)).run state] *
      rawIndexCacheEnvelope key q signatures result.2 groups remaining) ≤ rawIndexCacheEnvelope key q signatures state groups remaining := by
  have hbase (result : OracleWorld.Range input × QueryCache HashSpec)
      (hresult : result ∈ support ((romImpl input).run state.1)) : QueryCache.enncard result.2 ≤ q := by
    apply hcap (result.1, (result.2, state.2))
    rw [logTracedMappedAdversaryImpl_run_map, support_map]
    refine ⟨result, ?_, ?_⟩
    · simpa only [unloggedMappedAdversaryImpl, OracleSpec.Range, OracleSpec.add_apply_inl] using hresult
    · simp only [signingLogFragment, List.append_nil]
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  simpa only [signingLogFragment, List.append_nil, unloggedMappedAdversaryImpl, OracleSpec.Range, OracleSpec.add_apply_inl] using
    expected_romImpl_rawIndexCacheEnvelope_le key q signatures state.1 state.2 input hsigned hbase groups remaining hvalid

theorem expected_logTraced_sign_rawIndexCacheEnvelope_le (key : SecretKey) (q : Nat) (signatures : Nat) (hq : q ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (message : Message)
    (hcap : ∀ result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state), QueryCache.enncard result.2.1 ≤ q)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      rawIndexCacheEnvelope key q signatures result.2 groups remaining) ≤
      rawIndexCacheEnvelope key q (signatures + 1) state groups remaining := by
  apply le_trans ?_ (expected_logTraced_sign_rawIndexEnvelope_le key q (cacheSlotCount q state.1) signatures
    hq state hsigned hcache message groups remaining hvalid)
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state)
  · apply mul_le_mul' le_rfl
    exact targetShapeEnvelope_queries_mono _ _ _ signatures _
      (cacheSlotCount_antitone q state.1 result.2.1 (logTracedMappedAdversaryImpl_cache_le key (.inr message) state result hresult)
        (hcap result hresult)) groups remaining hvalid
  · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]

end SphincsSecurity.Concrete
