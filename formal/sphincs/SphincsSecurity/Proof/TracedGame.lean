import SphincsSecurity.Proof.SigningTrace
import SphincsSecurity.Proof.OneTimeEvents

/-!
# The game with signer cache intervals retained

This is an observational refinement of the original game. Projecting away the forgery and signing
trace gives exactly the original verdict and final random-oracle cache.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

noncomputable def gameRestWithSigningTrace (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey) (initialCache : QueryCache HashSpec) :
    ProbComp ((Forgery × Bool) × (QueryCache HashSpec × SigningCacheTrace)) := do
  let (forgery, adversaryCache, trace) ←
    (simulateQ (cacheTracedMappedAdversaryImpl secretKey)
      (adversary.main publicKey)).run (initialCache, [])
  let (verified, finalCache) ←
    (simulateQ romImpl (Concrete.scheme.verify publicKey forgery.message forgery.signature)).run
      adversaryCache
  let log := trace.toSigningLog
  let verdict := decide (SigningTranscript.Valid log ∧
    ¬ SigningTranscript.Contains log forgery) && verified
  pure ((forgery, verdict), (finalCache, trace))

theorem gameRestWithSigningTrace_projection (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey) (initialCache : QueryCache HashSpec) :
    (fun result => (result.1.2, result.2.1)) <$>
        gameRestWithSigningTrace adversary publicKey secretKey initialCache =
      (simulateQ romImpl (gameRest Concrete.scheme adversary publicKey secretKey)).run
        initialCache := by
  let finish : Forgery × (QueryCache HashSpec × QueryLog SigningSpec) →
      ProbComp (Bool × QueryCache HashSpec) := fun result => do
    let (verified, finalCache) ←
      (simulateQ romImpl
        (Concrete.scheme.verify publicKey result.1.message result.1.signature)).run result.2.1
    pure (decide (SigningTranscript.Valid result.2.2 ∧
      ¬ SigningTranscript.Contains result.2.2 result.1) && verified, finalCache)
  let traceRun := (simulateQ (cacheTracedMappedAdversaryImpl secretKey)
    (adversary.main publicKey)).run (initialCache, [])
  let mappedRun := (((simulateQ (mappedAdversaryImpl secretKey)
    (adversary.main publicKey)).run).run initialCache)
  have hprojection :
      Prod.map id (fun state => (state.1, state.2.toSigningLog)) <$> traceRun =
        (fun result => (result.1.1, (result.2, result.1.2))) <$> mappedRun :=
    cacheTracedMappedAdversaryImpl_log_projection_eq_mapped secretKey
      (adversary.main publicKey) initialCache
  calc
    (fun result => (result.1.2, result.2.1)) <$>
        gameRestWithSigningTrace adversary publicKey secretKey initialCache =
      (Prod.map id (fun state => (state.1, state.2.toSigningLog)) <$> traceRun) >>= finish := by
        simp [gameRestWithSigningTrace, traceRun, finish, bind_map_left, map_bind, Prod.map]
        rfl
    _ = ((fun result => (result.1.1, (result.2, result.1.2))) <$> mappedRun) >>= finish := by
      rw [hprojection]
    _ = (simulateQ romImpl (gameRest Concrete.scheme adversary publicKey secretKey)).run
        initialCache := by
      simp [gameRest, mappedRun, mappedAdversaryImpl, finish, bind_map_left,
        QueryImpl.simulateQ_writerTMapBase_run]

theorem gameRestWithSigningTrace_support_invariants (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey) (initialCache : QueryCache HashSpec)
    (result : (Forgery × Bool) × (QueryCache HashSpec × SigningCacheTrace))
    (hmem : result ∈ support
      (gameRestWithSigningTrace adversary publicKey secretKey initialCache)) :
    result.2.2.ValidRuns secretKey ∧ result.2.2.CachesLe result.2.1
      ∧ result.2.2.Chronological := by
  rw [gameRestWithSigningTrace, mem_support_bind_iff] at hmem
  obtain ⟨⟨forgery, adversaryCache, trace⟩, hadversary, hfinish⟩ := hmem
  rw [mem_support_bind_iff] at hfinish
  obtain ⟨⟨verified, finalCache⟩, hverify, hpure⟩ := hfinish
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  have hvalid := cacheTracedMappedAdversaryImpl_validRuns secretKey
    (adversary.main publicKey) initialCache [] (forgery, adversaryCache, trace)
    (by simp [SigningCacheTrace.ValidRuns]) hadversary
  have hcachesChronological := cacheTracedMappedAdversaryImpl_cachesLe_chronological secretKey
    (adversary.main publicKey) initialCache [] (forgery, adversaryCache, trace)
    (by simp [SigningCacheTrace.CachesLe]) (by simp [SigningCacheTrace.Chronological]) hadversary
  exact ⟨hvalid, hcachesChronological.1.mono
      (simulateQ_romImpl_cache_le
        (Concrete.scheme.verify publicKey forgery.message forgery.signature)
        adversaryCache (verified, finalCache) hverify),
    hcachesChronological.2⟩

namespace Concrete

noncomputable def gameAfterSecretsWithSigningTrace (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    ProbComp ((Digest × Forgery × Bool) × (QueryCache HashSpec × SigningCacheTrace)) := do
  let (root, rootCache) ← (simulateQ romImpl
    (liftM ((treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) :
      OracleComp HashSpec Digest)) :
      OracleComp OracleWorld Digest)).run ∅
  let result ← gameRestWithSigningTrace adversary ⟨root, parameter⟩
    ⟨parameter, root, otsSecret, ftsSecret⟩ rootCache
  pure ((root, result.1.1, result.1.2), result.2)

theorem gameAfterSecretsWithSigningTrace_projection (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    (fun result => (result.1.2.2, result.2.1)) <$>
        gameAfterSecretsWithSigningTrace adversary parameter otsSecret ftsSecret =
      (simulateQ romImpl (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run ∅ := by
  rw [gameAfterSecretsWithSigningTrace, gameAfterSecrets, simulateQ_bind, StateT.run_bind]
  simp only [map_bind]
  apply bind_congr
  intro rootResult
  rw [← gameRestWithSigningTrace_projection adversary
    (⟨rootResult.1, parameter⟩ : PublicKey)
    (⟨parameter, rootResult.1, otsSecret, ftsSecret⟩ : SecretKey) rootResult.2]
  simp

theorem gameAfterSecretsWithSigningTrace_support_invariants (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × (QueryCache HashSpec × SigningCacheTrace))
    (hmem : result ∈ support
      (gameAfterSecretsWithSigningTrace adversary parameter otsSecret ftsSecret)) :
    let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
    result.2.2.ValidRuns secretKey ∧ result.2.2.CachesLe result.2.1
      ∧ result.2.2.Chronological := by
  rw [gameAfterSecretsWithSigningTrace, mem_support_bind_iff] at hmem
  obtain ⟨⟨root, rootCache⟩, _, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨restResult, hrest, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  simpa using gameRestWithSigningTrace_support_invariants adversary
    (⟨root, parameter⟩ : PublicKey)
    (⟨parameter, root, otsSecret, ftsSecret⟩ : SecretKey) rootCache restResult hrest

end Concrete

end SphincsSecurity
