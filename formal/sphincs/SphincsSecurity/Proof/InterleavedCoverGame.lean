import SphincsSecurity.Proof.ValidInterleavedCover
import SphincsSecurity.Proof.RetainedSigningTrace

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem simulateQ_signingTraceComputation_logTraced {α : Type} (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) :
    (fun result => (result.1.1, (result.2, result.1.2))) <$>
      (simulateQ (unloggedMappedAdversaryImpl key) (signingTraceComputation computation)).run cache =
        (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, []) := by
  rw [simulateQ_unloggedMapped_signingTraceComputation_run]
  have h := selectivelyLoggedMappedAdversaryImpl_run_eq_logTraced key computation cache []
  rw [selectivelyLoggedMappedAdversaryImpl_eq_mapped] at h
  simpa only [List.nil_append] using h

def interleavedRetainedProjection (result : (Forgery × Bool) × CoverLogState) :
    RetainedRestResult × QueryCache HashSpec :=
  (((result.1.1, result.2.2), result.1.2), result.2.1)

theorem retainedGameRestComputation_interleaved (adversary : Adversary) (key : SecretKey)
    (publicKey : PublicKey) (cache : QueryCache HashSpec) :
    (simulateQ (unloggedMappedAdversaryImpl key)
      (retainedGameRestComputation adversary publicKey)).run cache =
        interleavedRetainedProjection <$>
          (simulateQ (logTracedMappedAdversaryImpl key)
            (unloggedRetainedRestComputation adversary publicKey)).run (cache, []) := by
  rw [retainedGameRestComputation_eq_signingTrace, simulateQ_map, StateT.run_map,
    ← simulateQ_signingTraceComputation_logTraced, Functor.map_map]
  rfl

theorem actualRetainedGameAfterSecrets_cache_bound (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (table : Coordinate → Digest) (q : Nat)
    (hq : (gameAfterSecrets adversary parameter otsSecret
      (fun index tree leafIdx => table (index, tree, leafIdx))).IsQueryBoundP (· matches Sum.inr _) q)
    (result : RetainedGameResult × QueryCache HashSpec)
    (hresult : result ∈ support (actualRetainedGameAfterSecrets adversary parameter otsSecret table)) :
    QueryCache.enncard result.2 ≤ q := by
  have hlog : retainedGameLogProjection result ∈ support
      (retainedGameLogProjection <$> actualRetainedGameAfterSecrets adversary parameter otsSecret table) := by
    rw [support_map]
    exact ⟨result, hresult, rfl⟩
  rw [actualRetainedGameAfterSecrets_signing_projection, support_map] at hlog
  obtain ⟨traced, htraced, heq⟩ := hlog
  have hgame : (traced.1.2.2, traced.2.1) ∈ support
      ((simulateQ romImpl (gameAfterSecrets adversary parameter otsSecret
        (fun index tree leafIdx => table (index, tree, leafIdx)))).run ∅) := by
    rw [← gameAfterSecretsWithSigningTrace_projection, support_map]
    exact ⟨traced, htraced, rfl⟩
  have hcache : traced.2.1 = result.2 := congrArg (fun value => value.2.1) heq
  rw [← hcache]
  exact simulateQ_romImpl_enncard_le_queryBound _ q hq _ hgame

noncomputable def expectedRetainedCoverCharge (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (table : Coordinate → Digest) (q : Nat) : ENNReal :=
  ∑' rootResult, Pr[= rootResult | (simulateQ (randomOracle : QueryImpl HashSpec _)
      (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅] *
    expectedValidInterleavedCoverCharge
      ⟨parameter, rootResult.1, otsSecret, fun index tree leafIdx => table (index, tree, leafIdx)⟩ q
      (unloggedRetainedRestComputation adversary ⟨rootResult.1, parameter⟩) (rootResult.2, [])

theorem probEvent_actualRetained_validObservedCover_le_charge (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (table : Coordinate → Digest) (q : Nat) (hq : q ≤ 2 ^ 127)
    (hbudget : (gameAfterSecrets adversary parameter otsSecret
      (fun index tree leafIdx => table (index, tree, leafIdx))).IsQueryBoundP (· matches Sum.inr _) q) :
    Pr[fun result => SigningTranscript.Valid result.1.2.1.2 ∧
      ObservedFewTimeCover (messageAnswers parameter result.2)
      result.1.1 result.1.2.1.2 result.1.2.1.1 |
        actualRetainedGameAfterSecrets adversary parameter otsSecret table] ≤
      expectedRetainedCoverCharge adversary parameter otsSecret table q := by
  rw [actualRetainedGameAfterSecrets, probEvent_bind_eq_tsum, expectedRetainedCoverCharge]
  apply ENNReal.tsum_le_tsum
  intro rootResult
  by_cases hroot : rootResult ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _)
      (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅)
  · apply mul_le_mul' le_rfl
    simp only [bind_pure_comp, probEvent_map]
    rw [retainedGameRestComputation_interleaved, probEvent_map]
    apply probEvent_interleaved_validObservedCover_from_emptyLog_le_charge _ q hq _ _ Prod.fst
    intro result hresult
    apply actualRetainedGameAfterSecrets_cache_bound adversary parameter otsSecret table q hbudget
      ((rootResult.1, (interleavedRetainedProjection result).1), result.2.1)
    rw [actualRetainedGameAfterSecrets, mem_support_bind_iff]
    refine ⟨rootResult, hroot, ?_⟩
    rw [mem_support_bind_iff]
    refine ⟨interleavedRetainedProjection result, ?_, ?_⟩
    · rw [retainedGameRestComputation_interleaved, support_map]
      exact ⟨result, hresult, rfl⟩
    · simp only [support_pure, Set.mem_singleton_iff]
      rfl
  · rw [probOutput_eq_zero_of_not_mem_support hroot, zero_mul, zero_mul]

theorem probEvent_actualRetained_validObservedCover_le_charge_of_hashQueryBound (adversary : Adversary)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (table : Coordinate → Digest)
    (hfts : (fun index tree leafIdx => table (index, tree, leafIdx)) ∈ support sampleFtsSecrets)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hbudget : HasHashQueryBound scheme adversary q) :
    Pr[fun result => SigningTranscript.Valid result.1.2.1.2 ∧
      ObservedFewTimeCover (messageAnswers parameter result.2)
      result.1.1 result.1.2.1.2 result.1.2.1.1 |
        actualRetainedGameAfterSecrets adversary parameter otsSecret table] ≤
      expectedRetainedCoverCharge adversary parameter otsSecret table q :=
  probEvent_actualRetained_validObservedCover_le_charge adversary parameter otsSecret table q hq
    (isQueryBoundP_gameAfterSecrets adversary q hbudget hparameter hots hfts)

end SphincsSecurity.Concrete.FtsProbeSimulation
