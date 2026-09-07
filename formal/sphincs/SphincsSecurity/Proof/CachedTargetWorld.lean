import SphincsSecurity.Proof.NewTargetWorld

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

def worldTargetHashCost : OracleWorld.Domain → Nat
  | .inl _ => 0
  | .inr _ => 1

theorem expected_romImpl_newCachedTargetEnvelope_le (key : SecretKey) (q signatures : Nat)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : OracleWorld.Domain)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hcap : ∀ result ∈ support ((romImpl input).run before), QueryCache.enncard result.2 ≤ q)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (romImpl input).run before] *
      newCachedTargetEnvelope key q signatures before (result.2, log) groups remaining) ≤
      (worldTargetHashCost input : ENNReal) *
        ((((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
          rawIndexCacheEnvelope key q signatures (before, log) groups remaining) := by
  cases input with
  | inr input =>
      simp only [worldTargetHashCost, Nat.cast_one, one_mul]
      exact expected_randomOracle_newCachedTargetEnvelope_le key q signatures before log input hsigned hcap groups remaining hvalid
  | inl input =>
      have hrun : (unifFwdImpl HashSpec input).run before =
          (fun sample => (sample, before)) <$> (liftM (unifSpec.query input) : ProbComp (unifSpec.Range input)) := by
        simpa [simulateQ_query] using (unifFwdImpl.simulateQ_run
          (hashSpec := HashSpec) (liftM (unifSpec.query input) : ProbComp (unifSpec.Range input)) before)
      change (∑' result, Pr[= result | (unifFwdImpl HashSpec input).run before] *
        newCachedTargetEnvelope key q signatures before (result.2, log) groups remaining) ≤ _
      rw [hrun, tsum_probOutput_map_mul]
      simp only [newCachedTargetEnvelope, cacheMessageWeight_fresh_restriction, mul_zero, tsum_zero, zero_le]

theorem expected_logTraced_world_newCachedTargetEnvelope_le (key : SecretKey) (q signatures : Nat)
    (state : CoverLogState) (input : OracleWorld.Domain)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcap : ∀ result ∈ support ((logTracedMappedAdversaryImpl key (.inl input)).run state), QueryCache.enncard result.2.1 ≤ q)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl input)).run state] *
      newCachedTargetEnvelope key q signatures state.1 result.2 groups remaining) ≤
      (worldTargetHashCost input : ENNReal) *
        ((((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
          rawIndexCacheEnvelope key q signatures state groups remaining) := by
  have hbase (result : OracleWorld.Range input × QueryCache HashSpec)
      (hresult : result ∈ support ((romImpl input).run state.1)) : QueryCache.enncard result.2 ≤ q := by
    apply hcap (result.1, (result.2, state.2))
    rw [logTracedMappedAdversaryImpl_run_map, support_map]
    refine ⟨result, ?_, ?_⟩
    · simpa only [unloggedMappedAdversaryImpl, OracleSpec.Range, OracleSpec.add_apply_inl] using hresult
    · simp only [signingLogFragment, List.append_nil]
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  simpa only [signingLogFragment, List.append_nil, unloggedMappedAdversaryImpl, OracleSpec.Range, OracleSpec.add_apply_inl] using
    expected_romImpl_newCachedTargetEnvelope_le key q signatures state.1 state.2 input hsigned hbase groups remaining hvalid

theorem expected_logTraced_world_cachedTargetEnvelope_le (key : SecretKey) (q signatures : Nat)
    (state : CoverLogState) (input : OracleWorld.Domain)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcap : ∀ result ∈ support ((logTracedMappedAdversaryImpl key (.inl input)).run state), QueryCache.enncard result.2.1 ≤ q)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl input)).run state] *
      cachedTargetEnvelope key q signatures result.2 groups remaining) ≤
      cachedTargetEnvelope key q signatures state groups remaining +
        (worldTargetHashCost input : ENNReal) *
          ((((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
            rawIndexCacheEnvelope key q signatures state groups remaining) := by
  have hold : (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl input)).run state] *
      cacheMessageWeight key.parameter (fun query target => targetCacheEnvelope key q (payloadOf query) target signatures result.2 groups remaining) state.1) ≤
      cachedTargetEnvelope key q signatures state groups remaining := by
    rw [expected_cacheMessageWeight]
    apply cacheMessageWeight_mono
    intro query target
    exact expected_logTraced_world_targetCacheEnvelope_le key q (payloadOf query) target signatures state input hsigned hcap groups remaining hvalid
  apply le_trans ?_ (add_le_add hold (expected_logTraced_world_newCachedTargetEnvelope_le key q signatures state input hsigned hcap groups remaining hvalid))
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key (.inl input)).run state)
  · rw [cachedTargetEnvelope_split key q signatures state.1 result.2
      (logTracedMappedAdversaryImpl_cache_le key (.inl input) state result hresult), mul_add]
  · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul, zero_mul, add_zero]

end SphincsSecurity.Concrete
