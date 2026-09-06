import SphincsSecurity.Proof.MessageCollisionWeightedCount

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem probEvent_gameRestWithViewTrace_nonfresh_messageCollision_le_weighted
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 127)
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
        ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
          ¬VerifierFreshTarget parameter result |
      gameRestWithViewTrace adversary ⟨root, parameter⟩
        ⟨parameter, root, otsSecret, ftsSecret⟩ rootCache] ≤
      q * weightedSingletonOriginUnionBound signatureLimit q (digestReuseWeight q) := by
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
  let prefixEvent := fun prior : Forgery × ViewedFullTraceState =>
    SomeFixedSingletonOriginTargetViewedTerminal secretKey
      (adversary.main publicKey) rootCache signatureLimit q q q prior
  have hgame : gameRestWithViewTrace adversary publicKey secretKey rootCache =
      run >>= finish := by
    rfl
  rw [show ⟨root, parameter⟩ = publicKey from rfl,
    show ⟨parameter, root, otsSecret, ftsSecret⟩ = secretKey from rfl, hgame]
  calc
    _ ≤ Pr[prefixEvent | run] := by
      apply probEvent_bind_le_probEvent
      intro prior hprior hnotPrefix
      rcases prior with ⟨forgery, state⟩
      apply probEvent_eq_zero
      intro rest hrest hevent
      rw [mem_support_bind_iff] at hrest
      obtain ⟨⟨⟨verified, targetView⟩, finalCache⟩, hverify, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst rest
      let result : (Digest × Forgery × Bool) × ViewedFullTraceState :=
        ((root, forgery,
          decide (SigningTranscript.Valid state.trace.signing.toSigningLog ∧
            ¬SigningTranscript.Contains state.trace.signing.toSigningLog forgery) &&
              verified),
          ⟨finalCache, state.trace, state.views, some targetView⟩)
      have hrestSupport :
          ((forgery,
              decide (SigningTranscript.Valid state.trace.signing.toSigningLog ∧
                ¬SigningTranscript.Contains state.trace.signing.toSigningLog forgery) &&
                  verified),
            ⟨finalCache, state.trace, state.views, some targetView⟩) ∈
            support (gameRestWithViewTrace adversary publicKey secretKey rootCache) := by
        rw [hgame, mem_support_bind_iff]
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
      obtain ⟨f, digest, hf, hvalid, _, hdigest, hadmissible,
        hcollision, _⟩ := hevent.1
      obtain ⟨cover, hcard, hne⟩ :=
        hcollision.exists_singletonFewTimeCover digest hdigest
      have hcacheLe : state.cache ≤ finalCache :=
        simulateQ_romImpl_cache_le
          (liftM (verifyWithView publicKey forgery.message forgery.signature) :
            OracleComp OracleWorld (Bool × FewTimeView)) state.cache
              ((verified, targetView), finalCache) hverify
      rcases gameAfterSecretsWithViewTrace_singletonCover_target_classified_at_adversary_state
          adversary q hq parameter hparameter otsSecret hots ftsSecret hfts result hresult
          f hf digest hdigest hadmissible cover hcard hne hvalid rootCache state rfl rfl
          hcacheLe with hfresh | hclassified
      · exact hevent.2 hfresh
      · obtain ⟨distinct, hdistinct, pattern, configuration, candidate, hterminal⟩ :=
          hclassified
        subst distinct
        apply hnotPrefix
        unfold prefixEvent SomeFixedSingletonOriginTargetViewedTerminal
        exact ⟨pattern, configuration, candidate, hterminal⟩
    _ ≤ _ := probEvent_someFixedSingletonOriginTargetViewedTerminal_le_weighted
      secretKey (adversary.main publicKey) rootCache signatureLimit q q hqMax
        (by
          have hroot' : QueryCache.enncard rootCache ≤ q := by
            have hprojected : (root, rootCache) ∈ support
                ((simulateQ romImpl
                  (liftM ((treeRoot parameter topLayer rootTree
                    (otsSecret topLayer rootTree) : OracleComp HashSpec Digest)) :
                      OracleComp OracleWorld Digest)).run ∅) := hroot
            have hgameBound := isQueryBoundP_gameAfterSecrets adversary q hq
              hparameter hots hfts
            rw [gameAfterSecrets] at hgameBound
            have hrootBound := OracleComp.IsQueryBoundP.of_bind_left
              (p := fun input : OracleWorld.Domain => input matches Sum.inr _) hgameBound
            have hbound := simulateQ_romImpl_enncard_le_queryBound
              (liftM ((treeRoot parameter topLayer rootTree
                (otsSecret topLayer rootTree) : OracleComp HashSpec Digest)) :
                  OracleComp OracleWorld Digest) q hrootBound
              (root, rootCache) hprojected
            exact hbound
          exact hroot') q

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in

theorem probEvent_gameRestWithViewTrace_fresh_messageCollision_le_weighted
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 127)
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
        ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
          VerifierFreshTarget parameter result |
      gameRestWithViewTrace adversary ⟨root, parameter⟩
        ⟨parameter, root, otsSecret, ftsSecret⟩ rootCache] ≤
      ((q + 1 : Nat) : ℝ≥0∞) * weightedSingletonOriginUnionBound signatureLimit q (digestReuseWeight q) := by
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
    ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
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
    probEvent_someFixedOneOriginTargetViewedTerminal_le_weighted
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
      Pr[SomeFixedOneOriginTargetViewedTerminal secretKey
        (adversaryWithTargetQuery adversary publicKey) rootCache signatureLimit q q (q + 1) |
          (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
            (adversaryWithTargetQuery adversary publicKey)).run
              ⟨rootCache, ⟨[], [], []⟩, [], none⟩] := by
    rw [adversaryWithTargetQuery_viewed_run]
    change Pr[_ | run >>= _] ≤
      Pr[SomeFixedOneOriginTargetViewedTerminal secretKey
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
    change _ ≤ Pr[SomeFixedOneOriginTargetViewedTerminal secretKey
      (adversaryWithTargetQuery adversary publicKey) rootCache signatureLimit q q (q + 1) |
      (randomOracle input).run state.cache >>= pure ∘ fun source =>
        ((forgery, source.1), appendDirectTargetViewedState input state.cache
          source.1 source.2 state)]
    rw [probEvent_bind_pure_comp]
    change Pr[_ | (randomOracle input).run state.cache >>= _] ≤
      Pr[fun source => SomeFixedOneOriginTargetViewedTerminal secretKey
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
    change ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
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
    obtain ⟨f, digest, hf, hvalid, _, hdigest, _, hcollision, _⟩ := hevent.1
    obtain ⟨cover, hcard, _⟩ :=
      hcollision.exists_singletonFewTimeCover digest hdigest
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
      cover.exists_paddedRealized_originConfiguration_of_queryBudget
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
    have hcountLe : freshTargetCandidateCount secretKey state.trace ≤ q := by
      rw [freshTargetCandidateCount_eq_card]
      have hbound := gameAfterSecretsWithViewTrace_freshTargetCandidatePositions_card_le
        adversary q hq parameter hparameter otsSecret hots ftsSecret hfts result hresult
      simp only [result] at hbound
      exact_mod_cast hbound
    let candidate : Fin (q + 1) :=
      ⟨freshTargetCandidateCount secretKey state.trace, by omega⟩
    unfold SomeFixedOneOriginTargetViewedTerminal at hnotPrefix
    apply hnotPrefix
    refine ⟨cover.entries.card, hcard, cover.pattern.pad hvalid,
      configuration, candidate, ?_⟩
    exact configuration.verifierTarget_fixedTerminal_for_cover adversary parameter otsSecret
      ftsSecret result hresult f hf digest cover hvalid hrealized
        rootCache state hprior rfl rfl input output digestCache rfl hmiss
          (by simpa only [input] using hquery) hdigestLe htargetOutput q hdigestCard
  calc
    Pr[freshEvent | run >>= finish] ≤
        Pr[SomeFixedOneOriginTargetViewedTerminal secretKey
          (adversaryWithTargetQuery adversary publicKey) rootCache signatureLimit q q (q + 1) |
            (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
              (adversaryWithTargetQuery adversary publicKey)).run
                ⟨rootCache, ⟨[], [], []⟩, [], none⟩] := hfirst
    _ ≤ ((q + 1 : Nat) : ℝ≥0∞) * weightedSingletonOriginUnionBound signatureLimit q (digestReuseWeight q) :=
      hprefixBound

theorem probEvent_gameAfterSecretsWithViewTrace_nonfresh_messageCollision_le_weighted
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[fun result =>
        ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
          ¬VerifierFreshTarget parameter result |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      q * weightedSingletonOriginUnionBound signatureLimit q (digestReuseWeight q) := by
  rw [gameAfterSecretsWithViewTrace]
  apply probEvent_bind_le_of_forall_le
  rintro ⟨root, rootCache⟩ hroot
  let attach := fun rest : (Forgery × Bool) × ViewedFullTraceState =>
    ((root, rest.1.1, rest.1.2), rest.2)
  change Pr[fun result =>
      ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
        ¬VerifierFreshTarget parameter result |
    gameRestWithViewTrace adversary ⟨root, parameter⟩
      ⟨parameter, root, otsSecret, ftsSecret⟩ rootCache >>= pure ∘ attach] ≤ _
  rw [probEvent_bind_pure_comp]
  exact probEvent_gameRestWithViewTrace_nonfresh_messageCollision_le_weighted adversary q hq hqMax
    parameter hparameter otsSecret hots ftsSecret hfts root rootCache hroot

theorem probEvent_gameAfterSecretsWithViewTrace_fresh_messageCollision_le_weighted
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[fun result =>
        ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
          VerifierFreshTarget parameter result |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      ((q + 1 : Nat) : ℝ≥0∞) * weightedSingletonOriginUnionBound signatureLimit q (digestReuseWeight q) := by
  rw [gameAfterSecretsWithViewTrace]
  apply probEvent_bind_le_of_forall_le
  rintro ⟨root, rootCache⟩ hroot
  let attach := fun rest : (Forgery × Bool) × ViewedFullTraceState =>
    ((root, rest.1.1, rest.1.2), rest.2)
  change Pr[fun result =>
      ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
        VerifierFreshTarget parameter result |
    gameRestWithViewTrace adversary ⟨root, parameter⟩
      ⟨parameter, root, otsSecret, ftsSecret⟩ rootCache >>= pure ∘ attach] ≤ _
  rw [probEvent_bind_pure_comp]
  exact probEvent_gameRestWithViewTrace_fresh_messageCollision_le_weighted adversary q hq hqMax
    parameter hparameter otsSecret hots ftsSecret hfts root rootCache hroot

theorem probEvent_gameAfterSecretsWithViewTrace_messageCollision_le_weighted
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      q * weightedSingletonOriginUnionBound signatureLimit q (digestReuseWeight q) +
        ((q + 1 : Nat) : ℝ≥0∞) * weightedSingletonOriginUnionBound signatureLimit q (digestReuseWeight q) := by
  classical
  calc
    _ ≤ Pr[fun result =>
        (ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
          ¬VerifierFreshTarget parameter result) ∨
        (ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
          VerifierFreshTarget parameter result) |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] := by
        apply probEvent_mono
        intro result _ hcollision
        by_cases hfresh : VerifierFreshTarget parameter result
        · exact Or.inr ⟨hcollision, hfresh⟩
        · exact Or.inl ⟨hcollision, hfresh⟩
    _ ≤ _ := (probEvent_or_le _ _ _).trans (add_le_add
      (probEvent_gameAfterSecretsWithViewTrace_nonfresh_messageCollision_le_weighted adversary q hq
        hqMax parameter hparameter otsSecret hots ftsSecret hfts)
      (probEvent_gameAfterSecretsWithViewTrace_fresh_messageCollision_le_weighted adversary q hq
        hqMax parameter hparameter otsSecret hots ftsSecret hfts))

end SphincsSecurity.Concrete
