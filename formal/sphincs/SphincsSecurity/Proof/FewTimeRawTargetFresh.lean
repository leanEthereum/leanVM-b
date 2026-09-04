import SphincsSecurity.Proof.FewTimeRawVerifierTarget

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem probEvent_gameRestWithViewTrace_fresh_honest_leak_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 125)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (root : Digest) (rootCache : QueryCache HashSpec)
    (hroot : (root, rootCache) ∈ support
      ((simulateQ romImpl
        (liftM ((treeRoot parameter topLayer rootTree
          (otsSecret topLayer rootTree) : OracleComp HashSpec Digest)) :
            OracleComp OracleWorld Digest)).run ∅)) :
    Pr[fun rest =>
        let result : (Digest × Forgery × Bool) × ViewedFullTraceState :=
          ((root, rest.1.1, rest.1.2), rest.2)
        ViewedHonestProperFewTimeLeakWitness parameter otsSecret ftsSecret result
          ∧ VerifierFreshTarget parameter result |
      gameRestWithViewTrace adversary ⟨root, parameter⟩
        ⟨parameter, root, otsSecret, ftsSecret⟩ rootCache] ≤
      ((q + 1 : Nat) : ℝ≥0∞) * rawTargetOriginUnionBound signatureLimit q := by
  classical
  let secretKey : SecretKey := ⟨parameter, root, otsSecret, ftsSecret⟩
  let publicKey : PublicKey := ⟨root, parameter⟩
  let initialState : ViewedFullTraceState :=
    ⟨rootCache, ⟨[], [], []⟩, [], none⟩
  let run := (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
    (adversary.main publicKey)).run initialState
  let finish : Forgery × ViewedFullTraceState →
      ProbComp ((Forgery × Bool) × ViewedFullTraceState) := fun prior => do
    let ((verified, targetView), finalCache) ←
      (simulateQ romImpl
        (liftM (verifyWithView publicKey prior.1.message prior.1.signature) :
          OracleComp OracleWorld (Bool × FewTimeView))).run prior.2.cache
    let log := prior.2.trace.signing.toSigningLog
    let verdict := decide (SigningTranscript.Valid log ∧
      ¬SigningTranscript.Contains log prior.1) && verified
    pure ((prior.1, verdict),
      ⟨finalCache, prior.2.trace, prior.2.views, some targetView⟩)
  let freshEvent := fun rest : (Forgery × Bool) × ViewedFullTraceState =>
    let result : (Digest × Forgery × Bool) × ViewedFullTraceState :=
      ((root, rest.1.1, rest.1.2), rest.2)
    ViewedHonestProperFewTimeLeakWitness parameter otsSecret ftsSecret result ∧
      VerifierFreshTarget parameter result
  have hrootNone : ∀ payload,
      rootCache (tweakableHashInput parameter .message payload) = none := by
    have hroot' : (root, rootCache) ∈ support
        ((simulateQ (randomOracle : QueryImpl HashSpec _)
          (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅) := by
      simpa only [simulateQ_romImpl_liftM] using hroot
    exact fun payload => treeRoot_cache_message_none parameter topLayer rootTree
      (otsSecret topLayer rootTree) root rootCache hroot' payload
  have hrootCache : QueryCache.enncard rootCache ≤ q := by
    have hgameBound := isQueryBoundP_gameAfterSecrets adversary q hq
      hparameter hots hfts
    rw [gameAfterSecrets] at hgameBound
    have hrootBound := OracleComp.IsQueryBoundP.of_bind_left
      (p := fun input : OracleWorld.Domain => input matches Sum.inr _) hgameBound
    exact simulateQ_romImpl_enncard_le_queryBound
      (liftM ((treeRoot parameter topLayer rootTree
        (otsSecret topLayer rootTree) : OracleComp HashSpec Digest)) :
          OracleComp OracleWorld Digest) q hrootBound (root, rootCache) hroot
  have hprefixBound :=
    probEvent_exists_fixedRawTargetViewedTerminal_le_idealOrigin_of_candidates
      (α := Forgery × HashOutput) (secretKey := secretKey)
      (computation := adversaryWithTargetQuery adversary publicKey)
      (initialCache := rootCache) (signatures := signatureLimit) (sources := q)
      (q := q) (hq := hqMax) (hcache := hrootCache) (candidates := q + 1)
  have hgame : gameRestWithViewTrace adversary publicKey secretKey rootCache =
      run >>= finish := rfl
  rw [show ⟨root, parameter⟩ = publicKey from rfl,
    show ⟨parameter, root, otsSecret, ftsSecret⟩ = secretKey from rfl, hgame]
  change Pr[freshEvent | run >>= finish] ≤ _
  have hfirst : Pr[freshEvent | run >>= finish] ≤
      Pr[SomeFixedRawTargetViewedTerminal secretKey
        (adversaryWithTargetQuery adversary publicKey) rootCache signatureLimit q q (q + 1) |
          (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
            (adversaryWithTargetQuery adversary publicKey)).run
              ⟨rootCache, ⟨[], [], []⟩, [], none⟩] := by
    rw [adversaryWithTargetQuery_viewed_run]
    change Pr[_ | run >>= _] ≤
      Pr[SomeFixedRawTargetViewedTerminal secretKey
        (adversaryWithTargetQuery adversary publicKey) rootCache signatureLimit q q (q + 1) |
          run >>= _]
    apply probEvent_bind_le_bind_of_forall_le
    rintro ⟨forgery, state⟩ hprior
    let input := tweakableHashInput parameter .message
      (messageDigestPayload root forgery.message forgery.signature.randomness)
    change Pr[_ |
      (simulateQ romImpl
        (liftM (verifyWithView publicKey forgery.message forgery.signature) :
          OracleComp OracleWorld (Bool × FewTimeView))).run state.cache >>= _] ≤ _
    rw [verifyWithView_split_run]
    simp only [bind_assoc]
    rw [show tweakableHashInput publicKey.parameter .message
      (messageDigestPayload publicKey.root forgery.message
        forgery.signature.randomness) = input from rfl]
    change _ ≤ Pr[SomeFixedRawTargetViewedTerminal secretKey
      (adversaryWithTargetQuery adversary publicKey) rootCache signatureLimit q q (q + 1) |
      (randomOracle input).run state.cache >>= pure ∘ fun source =>
        ((forgery, source.1), appendDirectTargetViewedState input state.cache
          source.1 source.2 state)]
    rw [probEvent_bind_pure_comp]
    change Pr[_ | (randomOracle input).run state.cache >>= _] ≤
      Pr[fun source => SomeFixedRawTargetViewedTerminal secretKey
        (adversaryWithTargetQuery adversary publicKey) rootCache signatureLimit q q (q + 1)
          ((forgery, source.1),
        appendDirectTargetViewedState input state.cache source.1 source.2 state) |
          (randomOracle input).run state.cache]
    apply probEvent_bind_le_probEvent
    rintro ⟨output, digestCache⟩ hquery hnotPrefix
    apply probEvent_eq_zero
    intro rest hrest hevent
    rw [mem_support_bind_iff] at hrest
    obtain ⟨⟨⟨verified, targetView⟩, finalCache⟩, hverifyRest, hpure⟩ := hrest
    simp only [support_pure, Set.mem_singleton_iff] at hpure
    subst rest
    let result : (Digest × Forgery × Bool) × ViewedFullTraceState :=
      ((root, forgery,
        decide (SigningTranscript.Valid state.trace.signing.toSigningLog ∧
          ¬SigningTranscript.Contains state.trace.signing.toSigningLog forgery) &&
            verified),
        ⟨finalCache, state.trace, state.views, some targetView⟩)
    change ViewedHonestProperFewTimeLeakWitness parameter otsSecret ftsSecret result ∧
      VerifierFreshTarget parameter result at hevent
    have hverify : ((verified, targetView), finalCache) ∈ support
        ((simulateQ romImpl
          (liftM (verifyWithView publicKey forgery.message forgery.signature) :
            OracleComp OracleWorld (Bool × FewTimeView))).run state.cache) := by
      rw [verifyWithView_split_run, mem_support_bind_iff]
      exact ⟨(output, digestCache), by simpa only [input, publicKey] using hquery,
        hverifyRest⟩
    have hrestSupport :
        ((forgery,
            decide (SigningTranscript.Valid state.trace.signing.toSigningLog ∧
              ¬SigningTranscript.Contains state.trace.signing.toSigningLog forgery) &&
                verified),
          ⟨finalCache, state.trace, state.views, some targetView⟩) ∈
          support (gameRestWithViewTrace adversary publicKey secretKey rootCache) := by
      rw [gameRestWithViewTrace, mem_support_bind_iff]
      refine ⟨(forgery, state), hprior, ?_⟩
      rw [mem_support_bind_iff]
      exact ⟨((verified, targetView), finalCache), hverify,
        by simp only [support_pure, Set.mem_singleton_iff]⟩
    have hresult : result ∈ support
        (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret) := by
      rw [gameAfterSecretsWithViewTrace, mem_support_bind_iff]
      refine ⟨(root, rootCache), hroot, ?_⟩
      rw [mem_support_bind_iff]
      exact ⟨_, hrestSupport, by simp [result]⟩
    obtain ⟨f, digest, hf, hvalid, _, hdigest, hadmissible, hproper, _hfull⟩ := hevent.1
    obtain ⟨otherRootCache, adversaryCache, _, _, hotherRootNone,
      hotherChain, hadversaryMiss, _, _, _⟩ := hevent.2
    have hbase : (forgery, state.base) ∈ support
        ((simulateQ (fullTracedMappedAdversaryImpl secretKey)
          (adversary.main publicKey)).run initialState.base) := by
      rw [← viewedFullTracedMappedAdversaryImpl_projection secretKey
        (adversary.main publicKey) initialState, support_map]
      exact ⟨(forgery, state), hprior, rfl⟩
    have hchain : FullAdversaryTrace.CacheChain rootCache state.trace.intervals
        state.cache :=
      fullTracedMappedAdversaryImpl_cacheChain secretKey (adversary.main publicKey)
        rootCache rootCache ⟨[], [], []⟩ (forgery, state.base) (by rfl) hbase
    have hmiss : state.cache input = none := by
      have hrootInput : rootCache input = none := by
        simpa only [input] using hrootNone
          (messageDigestPayload root forgery.message forgery.signature.randomness)
      have hotherRootInput : otherRootCache input = none := by
        simpa only [input, result] using hotherRootNone
          (messageDigestPayload root forgery.message forgery.signature.randomness)
      have hlookup := FullAdversaryTrace.CacheChain.finish_lookup_eq input
        (hrootInput.trans hotherRootInput.symm) hchain
        (by simpa only [result] using hotherChain)
      exact hlookup.trans hadversaryMiss
    have hdigestLe : digestCache ≤ finalCache :=
      simulateQ_romImpl_cache_le
        (liftM (verifyWithViewAfterOutput publicKey forgery.signature output) :
          OracleComp OracleWorld (Bool × FewTimeView)) digestCache
            ((verified, targetView), finalCache) hverifyRest
    have hcachedDigest : digestCache input = some output :=
      randomOracle_output_cached input state.cache digestCache output (by
        have hquerySim : simulateQ (randomOracle : QueryImpl HashSpec _)
            (oracleHash input) = randomOracle input := by
          change simulateQ (randomOracle : QueryImpl HashSpec _)
            (liftM (HashSpec.query input)) = randomOracle input
          rw [simulateQ_spec_query]
        rw [hquerySim]
        exact hquery)
    have hcachedFinal : finalCache input = some output := hdigestLe hcachedDigest
    have hanswer : f input = output := hf (by simpa only [result] using hcachedFinal)
    have hdigestOutput : truncateMessageDigest output = digest := by
      have hdigest' : truncateMessageDigest (f input) = digest := by
        simpa only [messageDigest, oracleHash, evalWithAnswerFn_bind,
          evalWithAnswerFn_query, evalWithAnswerFn_pure, result, input] using hdigest
      rwa [hanswer] at hdigest'
    have htargetOutput : hashOutputFewTimeView output =
        fewTimeTargetView (digestIndex digest) (digestLeaves digest) := by
      simp [hashOutputFewTimeView, fewTimeTargetView, hdigestOutput]
    have hfullBase : (result.1, result.2.base) ∈ support
        (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret) := by
      rw [← gameAfterSecretsWithViewTrace_projection adversary parameter otsSecret
        ftsSecret, support_map]
      exact ⟨result, hresult, rfl⟩
    obtain ⟨configuration, hrealized⟩ :=
      hproper.1.cover.exists_paddedRealized_originConfiguration_of_queryBudget
        adversary q hq parameter hparameter otsSecret hots ftsSecret hfts
          (result.1, result.2.base) hfullBase f hf (digestIndex digest)
            (digestLeaves digest) signatureLimit hvalid
    have hfinalCache : QueryCache.enncard finalCache ≤ q := by
      have hbound := gameAfterSecretsWithFullTrace_support_enncard_le adversary q hq
        parameter hparameter otsSecret hots ftsSecret hfts
          (result.1, result.2.base) hfullBase
      change QueryCache.enncard result.2.cache ≤ q at hbound
      simpa only [result] using hbound
    have hdigestCard : QueryCache.enncard digestCache ≤ q :=
      (QueryCache.enncard_mono hdigestLe).trans hfinalCache
    have hcountLe : (rawTargetCandidateViews state.trace.intervals).length ≤ q := by
      apply (rawTargetCandidateViews_length_le_directIntervalCount state.trace.intervals).trans
      exact gameAfterSecretsWithViewTrace_directIntervalCount_le adversary q hq parameter
        hparameter otsSecret hots ftsSecret hfts result hresult
    let candidate : Fin (q + 1) :=
      ⟨(rawTargetCandidateViews state.trace.intervals).length, by omega⟩
    unfold SomeFixedRawTargetViewedTerminal at hnotPrefix
    apply hnotPrefix
    refine ⟨hproper.1.cover.entries.card,
      Finset.mem_Icc.2 ⟨hproper.1.cover.entries_card_pos,
        hproper.1.cover.entries_card_le_trees⟩,
      hproper.1.cover.pattern.pad hvalid, configuration, candidate, ?_⟩
    exact configuration.raw_verifierTarget_fixedTerminal adversary parameter otsSecret
      ftsSecret result hresult f hf digest hproper hvalid hrealized
        rootCache state hprior rfl rfl input output digestCache rfl hmiss
          (by simpa only [input] using hquery) hdigestLe htargetOutput
            (by simp [signAttemptResultOfOutput, hdigestOutput, hadmissible]) q hdigestCard
  calc
    Pr[freshEvent | run >>= finish] ≤
        Pr[SomeFixedRawTargetViewedTerminal secretKey
          (adversaryWithTargetQuery adversary publicKey) rootCache signatureLimit q q (q + 1) |
            (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
              (adversaryWithTargetQuery adversary publicKey)).run
                ⟨rootCache, ⟨[], [], []⟩, [], none⟩] := hfirst
    _ ≤ ((q + 1 : Nat) : ℝ≥0∞) * rawTargetOriginUnionBound signatureLimit q :=
      hprefixBound

theorem probEvent_gameAfterSecretsWithViewTrace_fresh_honest_leak_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 125)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[fun result =>
        ViewedHonestProperFewTimeLeakWitness parameter otsSecret ftsSecret result
          ∧ VerifierFreshTarget parameter result |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      ((q + 1 : Nat) : ℝ≥0∞) * rawTargetOriginUnionBound signatureLimit q := by
  rw [gameAfterSecretsWithViewTrace]
  apply probEvent_bind_le_of_forall_le
  rintro ⟨root, rootCache⟩ hroot
  let attach := fun rest : (Forgery × Bool) × ViewedFullTraceState =>
    ((root, rest.1.1, rest.1.2), rest.2)
  change Pr[fun result =>
      ViewedHonestProperFewTimeLeakWitness parameter otsSecret ftsSecret result ∧
        VerifierFreshTarget parameter result |
    gameRestWithViewTrace adversary ⟨root, parameter⟩
      ⟨parameter, root, otsSecret, ftsSecret⟩ rootCache >>= pure ∘ attach] ≤ _
  rw [probEvent_bind_pure_comp]
  exact probEvent_gameRestWithViewTrace_fresh_honest_leak_le adversary q hq hqMax
    parameter hparameter otsSecret hots ftsSecret hfts root rootCache hroot

end SphincsSecurity.Concrete
