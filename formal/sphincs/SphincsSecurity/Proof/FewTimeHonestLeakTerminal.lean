import SphincsSecurity.Proof.TerminalView
import SphincsSecurity.Proof.FewTimeSignerCompletion

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

def HonestLeakTerminalForgeryEvent (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec) (forgery : Forgery)
    (index : Index) (leaves : DigestTree → FtsLeaf) : Prop :=
  SettledForgedFreshLayerOpening f cache secretKey signingLog index leaves forgery.signature
    ∨ EncodingCollision f cache secretKey signingLog
    ∨ SettledForgedBackwardChainOpening f cache secretKey signingLog index leaves
      forgery.signature
    ∨ (MessageDigestCollision f cache secretKey signingLog forgery ∧
      FewTimeLeak f cache secretKey signingLog index leaves)
    ∨ (ProperFewTimeLeak f cache secretKey signingLog index leaves ∧
      FullyHonestOpening f cache secretKey index leaves forgery.signature)
    ∨ UncoveredFtsSecret f cache secretKey signingLog index leaves forgery.signature.ftsSecret

theorem gameAfterSecretsWithViewTrace_winning_honestLeakTerminal_classify
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hresult : result ∈ support
      (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret))
    (hwin : result.1.2.2 = true) :
    Bad parameter otsSecret ftsSecret result.2.cache ∨
      ViewedWinningTerminalWitnessFor parameter otsSecret ftsSecret
        HonestLeakTerminalForgeryEvent result := by
  rw [gameAfterSecretsWithViewTrace, mem_support_bind_iff] at hresult
  obtain ⟨⟨root, rootCache⟩, hroot, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨restResult, hrest, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  rw [gameRestWithViewTrace, mem_support_bind_iff] at hrest
  obtain ⟨⟨forgery, state⟩, hadversary, hfinish⟩ := hrest
  rw [mem_support_bind_iff] at hfinish
  obtain ⟨⟨⟨verified, targetView⟩, finalCache⟩, hverifyView, hpure⟩ := hfinish
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst restResult
  have hverified : verified = true := by
    cases verified <;> simp_all
  subst verified
  have htranscript : SigningTranscript.Valid state.trace.signing.toSigningLog ∧
      ¬SigningTranscript.Contains state.trace.signing.toSigningLog forgery := by
    have h := (show (SigningTranscript.Valid state.trace.signing.toSigningLog ∧
        ¬SigningTranscript.Contains state.trace.signing.toSigningLog forgery) ∧ True by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using hwin)
    exact h.1
  have hverify : (true, finalCache) ∈ support
      ((simulateQ romImpl
        (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)).run state.cache) := by
    rw [← simulateQ_verifyWithView_fst_run ⟨root, parameter⟩ forgery.message
      forgery.signature state.cache, support_map]
    exact ⟨((true, targetView), finalCache), hverifyView, rfl⟩
  obtain ⟨hverifyLe, f, hf, heval, hqueries⟩ := exists_answerFn_replay_of_mem_support
    (verify ⟨root, parameter⟩ forgery.message forgery.signature) state.cache true finalCache
      (by simpa only [scheme, simulateQ_romImpl_liftM] using hverify)
  have hroot' : (root, rootCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅) := by
    simpa only [simulateQ_romImpl_liftM] using hroot
  have hbaseAdversary : (forgery, state.base) ∈ support
      ((simulateQ (fullTracedMappedAdversaryImpl
        ⟨parameter, root, otsSecret, ftsSecret⟩)
        (adversary.main ⟨root, parameter⟩)).run
          (rootCache, ⟨[], [], []⟩)) := by
    let initialState : ViewedFullTraceState :=
      ⟨rootCache, ⟨[], [], []⟩, [], none⟩
    have hprojection := viewedFullTracedMappedAdversaryImpl_projection
      ⟨parameter, root, otsSecret, ftsSecret⟩ (adversary.main ⟨root, parameter⟩)
        initialState
    have hmapped : (forgery, state.base) ∈ support
        (Prod.map id ViewedFullTraceState.base <$>
          (simulateQ (viewedFullTracedMappedAdversaryImpl
            ⟨parameter, root, otsSecret, ftsSecret⟩)
              (adversary.main ⟨root, parameter⟩)).run initialState) := by
      rw [support_map]
      exact ⟨(forgery, state), by simpa only [initialState] using hadversary, rfl⟩
    rw [hprojection] at hmapped
    simpa only [initialState, ViewedFullTraceState.base] using hmapped
  have hchain : FullAdversaryTrace.CacheChain rootCache state.trace.intervals state.cache :=
    fullTracedMappedAdversaryImpl_cacheChain
      ⟨parameter, root, otsSecret, ftsSecret⟩ (adversary.main ⟨root, parameter⟩)
        rootCache rootCache ⟨[], [], []⟩ (forgery, state.base) rfl hbaseAdversary
  have hvalidIntervals : state.trace.ValidIntervals
      ⟨parameter, root, otsSecret, ftsSecret⟩ :=
    fullTracedMappedAdversaryImpl_validIntervals
      ⟨parameter, root, otsSecret, ftsSecret⟩ (adversary.main ⟨root, parameter⟩)
        rootCache ⟨[], [], []⟩ (forgery, state.base)
          (by simp [FullAdversaryTrace.ValidIntervals]) hbaseAdversary
  have hrootLe : rootCache ≤ finalCache :=
    (hchain.start_le_finish hvalidIntervals).trans hverifyLe
  obtain ⟨hrootEval, hrootQueries⟩ := replay_of_mem_support_of_le
    (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree)) ∅ root rootCache finalCache
      hroot' hrootLe f hf
  have hrootSettled := settled_treeRoot_of_cachedRun
    (otsSecret := otsSecret) (ftsSecret := ftsSecret) hf topLayer rootTree hrootQueries
  obtain ⟨digest, hdigest, hdigestRun, hadmissible, hlayers, hftsRun, hlayersRun⟩ :=
    verify_extract ⟨root, parameter⟩ forgery.message forgery.signature heval hqueries
  let index := digestIndex digest
  let leaves := digestLeaves digest
  let ftsPublicKey := evalWithAnswerFn f
    (ftsRecover parameter index leaves forgery.signature.ftsSecret forgery.signature.ftsPath)
  have hhypertree : HypertreeRun f finalCache parameter index forgery.signature
      ftsPublicKey root :=
    hypertreeRun_of_verify index forgery.signature ftsPublicKey root hlayers hlayersRun
  have htarget : root = honestNode f parameter topLayer rootTree
      (otsSecret topLayer rootTree) (layerHeight topLayer) 0 := by
    rw [← hrootEval]
    rfl
  have htop := hypertree_top_extract_or_bad hf index forgery.signature ftsPublicKey root
    hhypertree htarget (by simpa using hrootSettled)
  rcases htop with hbad | htop
  · exact Or.inl hbad
  · let secretKey : SecretKey := ⟨parameter, root, otsSecret, ftsSecret⟩
    have hclassified := accepted_forgery_classify f finalCache secretKey
      state.trace.signing.toSigningLog index forgery.signature leaves ftsPublicKey root hf rfl
        htop (by
          have htree : treeIndexAt index topLayer = rootTree := by
            apply Fin.ext
            exact treeIndexAt_topLayer index
          unfold LayerRootSettled
          rw [htree]
          simpa using hrootSettled) hftsRun
    rcases hclassified with hbad | hobstacle | hfull
    · exact Or.inl hbad
    · rcases settledForgedLayerObstacle_classify f finalCache secretKey
          state.trace.signing.toSigningLog index leaves forgery.signature hobstacle with
        hfresh | hencoding | hbackward
      · exact Or.inr ⟨f, digest, hf, htranscript.1, htranscript.2, hdigest,
          hadmissible, heval, Or.inl hfresh⟩
      · exact Or.inr ⟨f, digest, hf, htranscript.1, htranscript.2, hdigest,
          hadmissible, heval, Or.inr (Or.inl hencoding)⟩
      · exact Or.inr ⟨f, digest, hf, htranscript.1, htranscript.2, hdigest,
          hadmissible, heval, Or.inr (Or.inr (Or.inl hbackward))⟩
    · rcases fewTimeLeak_or_uncovered f finalCache secretKey state.trace.signing.toSigningLog
          index leaves with hleak | ⟨tree, huncovered⟩
      · rcases fullyHonest_leak_classify f finalCache secretKey
            state.trace.signing.toSigningLog forgery digest index leaves hdigest hdigestRun rfl rfl
              hfull.1 htranscript.2 hleak with hcollision | hobstacle | hproper
        · exact Or.inr ⟨f, digest, hf, htranscript.1, htranscript.2, hdigest,
            hadmissible, heval, Or.inr (Or.inr (Or.inr (Or.inl ⟨hcollision, hleak⟩)))⟩
        · rcases settledForgedLayerObstacle_classify f finalCache secretKey
              state.trace.signing.toSigningLog index leaves forgery.signature
                (hfull.settleObstacle hobstacle) with
            hfresh | hencoding | hbackward
          · exact Or.inr ⟨f, digest, hf, htranscript.1, htranscript.2, hdigest,
              hadmissible, heval, Or.inl hfresh⟩
          · exact Or.inr ⟨f, digest, hf, htranscript.1, htranscript.2, hdigest,
              hadmissible, heval, Or.inr (Or.inl hencoding)⟩
          · exact Or.inr ⟨f, digest, hf, htranscript.1, htranscript.2, hdigest,
              hadmissible, heval, Or.inr (Or.inr (Or.inl hbackward))⟩
        · exact Or.inr ⟨f, digest, hf, htranscript.1, htranscript.2, hdigest,
            hadmissible, heval, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hproper, hfull.1⟩))))⟩
      · exact Or.inr ⟨f, digest, hf, htranscript.1, htranscript.2, hdigest,
          hadmissible, heval, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨tree, huncovered, (hfull.1.2.1 tree).1, by
              apply hftsRun
              exact ftsRecover_leaf_query_mem f parameter index leaves
                forgery.signature.ftsSecret forgery.signature.ftsPath tree⟩))))⟩

theorem gameAfterSecretsWithViewTrace_fullyHonest_target_source_direct
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hresult : result ∈ support
      (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret))
    (f : QueryImpl HashSpec Id) (hf : result.2.cache.AgreesWithFn f)
    (digest : MessageDigest)
    (hdigest : evalWithAnswerFn f
      (messageDigest parameter result.1.1 result.1.2.1.message
        result.1.2.1.signature.randomness) = digest)
    (hadmissible : Admissible digest)
    (hproper : ProperFewTimeLeak f result.2.cache
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
      result.2.trace.signing.toSigningLog (digestIndex digest) (digestLeaves digest))
    (hfull : FullyHonestOpening f result.2.cache
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
      (digestIndex digest) (digestLeaves digest) result.1.2.1.signature)
    (source : Fin result.2.trace.intervals.length)
    (hbefore : (result.2.trace.intervals.get source).initialCache
      (tweakableHashInput parameter .message
        (messageDigestPayload result.1.1 result.1.2.1.message
          result.1.2.1.signature.randomness)) = none)
    (hafter : (result.2.trace.intervals.get source).finalCache
      (tweakableHashInput parameter .message
        (messageDigestPayload result.1.1 result.1.2.1.message
          result.1.2.1.signature.randomness)) ≠ none)
    (hkind : (result.2.trace.intervals.get source).input = .inl (.inr
        (tweakableHashInput parameter .message
          (messageDigestPayload result.1.1 result.1.2.1.message
            result.1.2.1.signature.randomness))) ∨
      ∃ request, (result.2.trace.intervals.get source).input = .inr request) :
    (result.2.trace.intervals.get source).input = .inl (.inr
      (tweakableHashInput parameter .message
        (messageDigestPayload result.1.1 result.1.2.1.message
          result.1.2.1.signature.randomness))) := by
  obtain ⟨output, _, _, houtput, hattempt⟩ :=
    gameAfterSecretsWithViewTrace_target_source_candidate adversary parameter otsSecret
      ftsSecret result hresult f hf digest hdigest hadmissible source hbefore hafter hkind
  rcases hkind with hdirect | ⟨request, hsigner⟩
  · exact hdirect
  · exfalso
    have hbase : (result.1, result.2.base) ∈ support
        (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret) := by
      rw [← gameAfterSecretsWithViewTrace_projection adversary parameter otsSecret ftsSecret,
        support_map]
      exact ⟨result, hresult, rfl⟩
    have hinvariants := gameAfterSecretsWithFullTrace_support_invariants adversary
      parameter otsSecret ftsSecret (result.1, result.2.base) hbase
    have hintervals := gameAfterSecretsWithFullTrace_support_interval_invariants adversary
      parameter otsSecret ftsSecret (result.1, result.2.base) hbase
    have hvalidViews := gameAfterSecretsWithViewTrace_support_validViews adversary parameter
      otsSecret ftsSecret result hresult
    generalize hentry : result.2.trace.intervals.get source = entry at hsigner hbefore houtput
    rcases entry with ⟨entryInput, entryOutput, initialCache, finalCache⟩
    rcases entryInput with worldInput | sourceRequest
    · simp at hsigner
    · simp only [Sum.inr.injEq] at hsigner
      subst sourceRequest
      exact hproper.no_signer_target_of_fullyHonest hfull result.2 rfl hvalidViews
        hintervals.1 hinvariants.1 hinvariants.2.1 hf source request entryOutput
        initialCache finalCache hentry
        (messageDigestPayload result.1.1 result.1.2.1.message
          result.1.2.1.signature.randomness) output hbefore houtput hattempt

end SphincsSecurity.Concrete
