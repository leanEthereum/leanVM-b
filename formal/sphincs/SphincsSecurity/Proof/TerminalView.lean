import SphincsSecurity.Proof.FewTimeTargetTerminal
import SphincsSecurity.Proof.TerminalDecomposition

/-!
# Terminal events on the observational game

The final probability bounds use the game that retains the actual forgery, signing transcript and
cache intervals. This prevents an existential terminal witness from choosing a transcript unrelated
to the supported execution.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

theorem FullAdversaryTrace.CacheChain.start_le_finish
    {secretKey : SecretKey} {start finish : QueryCache HashSpec}
    {intervals : List AdversaryCacheEntry}
    (hchain : FullAdversaryTrace.CacheChain start intervals finish)
    (hvalid : ∀ entry ∈ intervals,
      (entry.output, entry.finalCache) ∈ support
        ((unloggedMappedAdversaryImpl secretKey entry.input).run entry.initialCache)) :
    start ≤ finish := by
  induction intervals generalizing start finish with
  | nil =>
      change finish = start at hchain
      exact le_of_eq hchain.symm
  | cons head rest ih =>
      obtain ⟨hstart, hrest⟩ := hchain
      have hhead : head.initialCache ≤ head.finalCache :=
        unloggedMappedAdversaryImpl_cache_le secretKey head.input head.initialCache
          (head.output, head.finalCache) (hvalid head (by simp))
      rw [← hstart]
      exact hhead.trans (ih hrest fun entry hentry => hvalid entry (by simp [hentry]))

namespace Concrete

def ViewedTerminalWitnessFor (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (event : QueryImpl HashSpec Id → QueryCache HashSpec → SecretKey →
      QueryLog SigningSpec → Forgery → Index → (DigestTree → FtsLeaf) → Prop)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState) : Prop :=
  ∃ (f : QueryImpl HashSpec Id) (digest : MessageDigest),
    result.2.cache.AgreesWithFn f
      ∧ SigningTranscript.Valid result.2.trace.signing.toSigningLog
      ∧ ¬SigningTranscript.Contains result.2.trace.signing.toSigningLog result.1.2.1
      ∧ evalWithAnswerFn f
          (messageDigest parameter result.1.1 result.1.2.1.message
            result.1.2.1.signature.randomness) = digest
      ∧ Admissible digest
      ∧ event f result.2.cache ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
        result.2.trace.signing.toSigningLog result.1.2.1
          (digestIndex digest) (digestLeaves digest)

def ViewedTerminalWitness (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :=
  ViewedTerminalWitnessFor parameter otsSecret ftsSecret TerminalForgeryEvent

def ViewedFreshLayerOpeningWitness (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :=
  ViewedTerminalWitnessFor parameter otsSecret ftsSecret
    fun f cache secretKey signingLog forgery index _ =>
      ForgedFreshLayerOpening f cache secretKey signingLog index forgery.signature

def ViewedEncodingCollisionWitness (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :=
  ViewedTerminalWitnessFor parameter otsSecret ftsSecret
    fun f cache secretKey signingLog _ _ _ =>
      EncodingCollision f cache secretKey signingLog

def ViewedBackwardChainOpeningWitness (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :=
  ViewedTerminalWitnessFor parameter otsSecret ftsSecret
    fun f cache secretKey signingLog forgery index _ =>
      ForgedBackwardChainOpening f cache secretKey signingLog index forgery.signature

def ViewedMessageDigestCollisionWitness (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :=
  ViewedTerminalWitnessFor parameter otsSecret ftsSecret
    fun f cache secretKey signingLog forgery index leaves =>
      MessageDigestCollision f cache secretKey signingLog forgery ∧
        FewTimeLeak f cache secretKey signingLog index leaves

def ViewedUncoveredFtsSecretWitness (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :=
  ViewedTerminalWitnessFor parameter otsSecret ftsSecret
    fun f cache secretKey signingLog forgery index leaves =>
      UncoveredFtsSecret f cache secretKey signingLog index leaves forgery.signature.ftsSecret

noncomputable instance (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    DecidablePred (ViewedTerminalWitness parameter otsSecret ftsSecret) :=
  fun result => Classical.propDecidable
    (ViewedTerminalWitness parameter otsSecret ftsSecret result)

theorem gameAfterSecretsWithViewTrace_winning_terminal_classify
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hresult : result ∈ support
      (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret))
    (hwin : result.1.2.2 = true) :
    Bad parameter otsSecret ftsSecret result.2.cache ∨
      ViewedTerminalWitness parameter otsSecret ftsSecret result := by
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
        htop hftsRun
    rcases hclassified with hbad | hobstacle | hfull
    · exact Or.inl hbad
    · rcases forgedLayerObstacle_classify f finalCache secretKey
          state.trace.signing.toSigningLog index forgery.signature hobstacle with
        hfresh | hencoding | hbackward
      · exact Or.inr ⟨f, digest, hf, htranscript.1, htranscript.2, hdigest,
          hadmissible, Or.inl hfresh⟩
      · exact Or.inr ⟨f, digest, hf, htranscript.1, htranscript.2, hdigest,
          hadmissible, Or.inr (Or.inl hencoding)⟩
      · exact Or.inr ⟨f, digest, hf, htranscript.1, htranscript.2, hdigest,
          hadmissible, Or.inr (Or.inr (Or.inl hbackward))⟩
    · rcases fewTimeLeak_or_uncovered f finalCache secretKey state.trace.signing.toSigningLog
          index leaves with hleak | ⟨tree, huncovered⟩
      · rcases fullyHonest_leak_classify f finalCache secretKey
            state.trace.signing.toSigningLog forgery digest index leaves hdigest hdigestRun rfl rfl
              hfull htranscript.2 hleak with hcollision | hobstacle | hproper
        · exact Or.inr ⟨f, digest, hf, htranscript.1, htranscript.2, hdigest,
            hadmissible, Or.inr (Or.inr (Or.inr (Or.inl ⟨hcollision, hleak⟩)))⟩
        · rcases forgedLayerObstacle_classify f finalCache secretKey
              state.trace.signing.toSigningLog index forgery.signature hobstacle with
            hfresh | hencoding | hbackward
          · exact Or.inr ⟨f, digest, hf, htranscript.1, htranscript.2, hdigest,
              hadmissible, Or.inl hfresh⟩
          · exact Or.inr ⟨f, digest, hf, htranscript.1, htranscript.2, hdigest,
              hadmissible, Or.inr (Or.inl hencoding)⟩
          · exact Or.inr ⟨f, digest, hf, htranscript.1, htranscript.2, hdigest,
              hadmissible, Or.inr (Or.inr (Or.inl hbackward))⟩
        · exact Or.inr ⟨f, digest, hf, htranscript.1, htranscript.2, hdigest,
            hadmissible, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hproper))))⟩
      · exact Or.inr ⟨f, digest, hf, htranscript.1, htranscript.2, hdigest,
          hadmissible, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨tree, huncovered, (hfull.2.1 tree).1, by
              apply hftsRun
              exact ftsRecover_leaf_query_mem f parameter index leaves
                forgery.signature.ftsSecret forgery.signature.ftsPath tree⟩))))⟩

theorem viewedTerminalWitness_cases (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hwitness : ViewedTerminalWitness parameter otsSecret ftsSecret result) :
    ViewedFreshLayerOpeningWitness parameter otsSecret ftsSecret result
      ∨ ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result
      ∨ ViewedBackwardChainOpeningWitness parameter otsSecret ftsSecret result
      ∨ ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result
      ∨ ViewedProperFewTimeLeakWitness parameter otsSecret ftsSecret result
      ∨ ViewedUncoveredFtsSecretWitness parameter otsSecret ftsSecret result := by
  obtain ⟨f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, hterminal⟩ := hwitness
  rcases hterminal with hfresh | hencoding | hbackward | hmessage | hfewTime | huncovered
  · exact Or.inl ⟨f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, hfresh⟩
  · exact Or.inr (Or.inl
      ⟨f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, hencoding⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, hbackward⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, hmessage⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, hfewTime⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, huncovered⟩))))

theorem probEvent_viewedTerminalWitness_le (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (run : ProbComp ((Digest × Forgery × Bool) × ViewedFullTraceState)) :
    Pr[ViewedTerminalWitness parameter otsSecret ftsSecret | run] ≤
      Pr[ViewedFreshLayerOpeningWitness parameter otsSecret ftsSecret | run] +
      (Pr[ViewedEncodingCollisionWitness parameter otsSecret ftsSecret | run] +
      (Pr[ViewedBackwardChainOpeningWitness parameter otsSecret ftsSecret | run] +
      (Pr[ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret | run] +
      (Pr[ViewedProperFewTimeLeakWitness parameter otsSecret ftsSecret | run] +
        Pr[ViewedUncoveredFtsSecretWitness parameter otsSecret ftsSecret | run])))) := by
  classical
  calc
    _ ≤ Pr[fun result =>
        ViewedFreshLayerOpeningWitness parameter otsSecret ftsSecret result
          ∨ ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result
          ∨ ViewedBackwardChainOpeningWitness parameter otsSecret ftsSecret result
          ∨ ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result
          ∨ ViewedProperFewTimeLeakWitness parameter otsSecret ftsSecret result
          ∨ ViewedUncoveredFtsSecretWitness parameter otsSecret ftsSecret result | run] := by
      apply probEvent_mono
      intro result _ hwitness
      exact viewedTerminalWitness_cases parameter otsSecret ftsSecret result hwitness
    _ ≤ Pr[ViewedFreshLayerOpeningWitness parameter otsSecret ftsSecret | run] +
        Pr[fun result => ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result
          ∨ ViewedBackwardChainOpeningWitness parameter otsSecret ftsSecret result
          ∨ ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result
          ∨ ViewedProperFewTimeLeakWitness parameter otsSecret ftsSecret result
          ∨ ViewedUncoveredFtsSecretWitness parameter otsSecret ftsSecret result | run] :=
      probEvent_or_le _ _ _
    _ ≤ Pr[ViewedFreshLayerOpeningWitness parameter otsSecret ftsSecret | run] +
        (Pr[ViewedEncodingCollisionWitness parameter otsSecret ftsSecret | run] +
        Pr[fun result => ViewedBackwardChainOpeningWitness parameter otsSecret ftsSecret result
          ∨ ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result
          ∨ ViewedProperFewTimeLeakWitness parameter otsSecret ftsSecret result
          ∨ ViewedUncoveredFtsSecretWitness parameter otsSecret ftsSecret result | run]) := by
      gcongr
      exact probEvent_or_le _ _ _
    _ ≤ Pr[ViewedFreshLayerOpeningWitness parameter otsSecret ftsSecret | run] +
        (Pr[ViewedEncodingCollisionWitness parameter otsSecret ftsSecret | run] +
        (Pr[ViewedBackwardChainOpeningWitness parameter otsSecret ftsSecret | run] +
        Pr[fun result => ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result
          ∨ ViewedProperFewTimeLeakWitness parameter otsSecret ftsSecret result
          ∨ ViewedUncoveredFtsSecretWitness parameter otsSecret ftsSecret result | run])) := by
      gcongr
      exact probEvent_or_le _ _ _
    _ ≤ Pr[ViewedFreshLayerOpeningWitness parameter otsSecret ftsSecret | run] +
        (Pr[ViewedEncodingCollisionWitness parameter otsSecret ftsSecret | run] +
        (Pr[ViewedBackwardChainOpeningWitness parameter otsSecret ftsSecret | run] +
        (Pr[ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret | run] +
        Pr[fun result => ViewedProperFewTimeLeakWitness parameter otsSecret ftsSecret result
          ∨ ViewedUncoveredFtsSecretWitness parameter otsSecret ftsSecret result | run]))) := by
      gcongr
      exact probEvent_or_le _ _ _
    _ ≤ _ := by
      gcongr
      exact probEvent_or_le _ _ _

theorem probEvent_clean_viewedTerminalWitness_le (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (run : ProbComp ((Digest × Forgery × Bool) × ViewedFullTraceState)) :
    Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
        ViewedTerminalWitness parameter otsSecret ftsSecret result | run] ≤
      Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
        ViewedFreshLayerOpeningWitness parameter otsSecret ftsSecret result | run] +
      (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
        ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result | run] +
      (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
        ViewedBackwardChainOpeningWitness parameter otsSecret ftsSecret result | run] +
      (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
        ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result | run] +
      (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
        ViewedProperFewTimeLeakWitness parameter otsSecret ftsSecret result | run] +
      Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
        ViewedUncoveredFtsSecretWitness parameter otsSecret ftsSecret result | run])))) := by
  classical
  calc
    _ ≤ Pr[fun result =>
        (¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedFreshLayerOpeningWitness parameter otsSecret ftsSecret result) ∨
        (¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result) ∨
        (¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedBackwardChainOpeningWitness parameter otsSecret ftsSecret result) ∨
        (¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result) ∨
        (¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedProperFewTimeLeakWitness parameter otsSecret ftsSecret result) ∨
        (¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedUncoveredFtsSecretWitness parameter otsSecret ftsSecret result) | run] := by
      apply probEvent_mono
      intro result _ hwitness
      obtain ⟨hclean, hterminal⟩ := hwitness
      rcases viewedTerminalWitness_cases parameter otsSecret ftsSecret result hterminal with
        hfresh | hencoding | hbackward | hmessage | hproper | huncovered
      · exact Or.inl ⟨hclean, hfresh⟩
      · exact Or.inr (Or.inl ⟨hclean, hencoding⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hclean, hbackward⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hclean, hmessage⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hclean, hproper⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hclean, huncovered⟩))))
    _ ≤ _ := by
      calc
        _ ≤ Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
              ViewedFreshLayerOpeningWitness parameter otsSecret ftsSecret result | run] +
            Pr[fun result =>
              (¬Bad parameter otsSecret ftsSecret result.2.cache ∧
                ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result) ∨
              (¬Bad parameter otsSecret ftsSecret result.2.cache ∧
                ViewedBackwardChainOpeningWitness parameter otsSecret ftsSecret result) ∨
              (¬Bad parameter otsSecret ftsSecret result.2.cache ∧
                ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result) ∨
              (¬Bad parameter otsSecret ftsSecret result.2.cache ∧
                ViewedProperFewTimeLeakWitness parameter otsSecret ftsSecret result) ∨
              (¬Bad parameter otsSecret ftsSecret result.2.cache ∧
                ViewedUncoveredFtsSecretWitness parameter otsSecret ftsSecret result) | run] :=
          probEvent_or_le _ _ _
        _ ≤ _ := by
          gcongr
          calc
            _ ≤ Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
                  ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result | run] +
                Pr[fun result =>
                  (¬Bad parameter otsSecret ftsSecret result.2.cache ∧
                    ViewedBackwardChainOpeningWitness parameter otsSecret ftsSecret result) ∨
                  (¬Bad parameter otsSecret ftsSecret result.2.cache ∧
                    ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result) ∨
                  (¬Bad parameter otsSecret ftsSecret result.2.cache ∧
                    ViewedProperFewTimeLeakWitness parameter otsSecret ftsSecret result) ∨
                  (¬Bad parameter otsSecret ftsSecret result.2.cache ∧
                    ViewedUncoveredFtsSecretWitness parameter otsSecret ftsSecret result) | run] :=
              probEvent_or_le _ _ _
            _ ≤ _ := by
              gcongr
              calc
                _ ≤ Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
                      ViewedBackwardChainOpeningWitness parameter otsSecret ftsSecret result | run] +
                    Pr[fun result =>
                      (¬Bad parameter otsSecret ftsSecret result.2.cache ∧
                        ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result) ∨
                      (¬Bad parameter otsSecret ftsSecret result.2.cache ∧
                        ViewedProperFewTimeLeakWitness parameter otsSecret ftsSecret result) ∨
                      (¬Bad parameter otsSecret ftsSecret result.2.cache ∧
                        ViewedUncoveredFtsSecretWitness parameter otsSecret ftsSecret result) | run] :=
                  probEvent_or_le _ _ _
                _ ≤ _ := by
                  gcongr
                  calc
                    _ ≤ Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
                          ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result |
                            run] +
                        Pr[fun result =>
                          (¬Bad parameter otsSecret ftsSecret result.2.cache ∧
                            ViewedProperFewTimeLeakWitness parameter otsSecret ftsSecret result) ∨
                          (¬Bad parameter otsSecret ftsSecret result.2.cache ∧
                            ViewedUncoveredFtsSecretWitness parameter otsSecret ftsSecret result) |
                              run] := probEvent_or_le _ _ _
                    _ ≤ _ := by
                      gcongr
                      exact probEvent_or_le _ _ _
theorem gameAfterSecretsWithViewTrace_verdictCache_projection (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    (fun result => (result.1.2.2, result.2.cache)) <$>
        gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret =
      (simulateQ romImpl (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run ∅ := by
  calc
    _ = (fun result : (Digest × Forgery × Bool) ×
          (QueryCache HashSpec × FullAdversaryTrace) => (result.1.2.2, result.2.1)) <$>
        ((fun result => (result.1, result.2.base)) <$>
          gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret) := by
      simp only [Functor.map_map, ViewedFullTraceState.base]
    _ = (fun result : (Digest × Forgery × Bool) ×
          (QueryCache HashSpec × FullAdversaryTrace) => (result.1.2.2, result.2.1)) <$>
        gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret := by
      rw [gameAfterSecretsWithViewTrace_projection]
    _ = _ := gameAfterSecretsWithFullTrace_projection adversary parameter otsSecret ftsSecret

theorem probEvent_bad_gameAfterSecretsWithViewTrace_le (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hq : (gameAfterSecrets adversary parameter otsSecret ftsSecret).IsQueryBoundP
      (· matches Sum.inr _) q) :
    Pr[fun result => Bad parameter otsSecret ftsSecret result.2.cache |
        gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      ((44 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    _ = Pr[fun result : Bool × QueryCache HashSpec =>
          Bad parameter otsSecret ftsSecret result.2 |
        (fun result => (result.1.2.2, result.2.cache)) <$>
          gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] := by
      rw [probEvent_map]
      rfl
    _ = Pr[fun result => Bad parameter otsSecret ftsSecret result.2 |
        (simulateQ romImpl
          (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run ∅] := by
      rw [gameAfterSecretsWithViewTrace_verdictCache_projection]
    _ ≤ _ := probEvent_bad_gameAfterSecrets_le adversary parameter otsSecret ftsSecret q hq

theorem probEvent_clean_properFewTimeLeak_le_nine_mul_inv
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 120)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
        ViewedProperFewTimeLeakWitness parameter otsSecret ftsSecret result |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      ((2 * q + 1 : Nat) : ℝ≥0∞) *
        (9 * ((2 ^ 125 : Nat) : ℝ≥0∞)⁻¹) := by
  apply le_trans (probEvent_mono fun _ _ event => event.2)
  exact probEvent_gameAfterSecretsWithViewTrace_proper_leak_le_nine_mul_inv adversary q hq
    hqMax parameter hparameter otsSecret hots ftsSecret hfts

theorem viewedMessageDigestCollisionWitness_patternHit
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hresult : result ∈ support
      (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret))
    (hwitness : ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result) :
    SomeFewTimePatternHit result.2.trace.signing.toSigningLog.length
      ((gameAfterSecretsWithViewTrace_support_validViews adversary parameter otsSecret ftsSecret
          result hresult).signingViewsForLog rfl,
        result.2.targetView.getD default) := by
  obtain ⟨f, digest, hf, _, _, hdigest, _, _, hleak⟩ := hwitness
  exact gameAfterSecretsWithViewTrace_fewTimeLeak_patternHit adversary parameter otsSecret
    ftsSecret result hresult f hf digest hdigest hleak

theorem probEvent_win_le_viewed_bad_add_terminal_cases (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    let run := gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret
    Pr[= true | (simulateQ romImpl
        (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run' ∅] ≤
      Pr[fun result => Bad parameter otsSecret ftsSecret result.2.cache | run] +
      (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
        ViewedFreshLayerOpeningWitness parameter otsSecret ftsSecret result | run] +
      (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
        ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result | run] +
      (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
        ViewedBackwardChainOpeningWitness parameter otsSecret ftsSecret result | run] +
      (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
        ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result | run] +
      (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
        ViewedProperFewTimeLeakWitness parameter otsSecret ftsSecret result | run] +
      Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
        ViewedUncoveredFtsSecretWitness parameter otsSecret ftsSecret result | run]))))) := by
  classical
  dsimp only
  let run := gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret
  calc
    Pr[= true | (simulateQ romImpl
        (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run' ∅] =
        Pr[fun result => result.1.2.2 = true | run] := by
      rw [StateT.run'_eq, ← probEvent_eq_eq_probOutput,
        ← gameAfterSecretsWithViewTrace_verdictCache_projection adversary parameter otsSecret
          ftsSecret, probEvent_map]
      rw [probEvent_map]
      rfl
    _ ≤ Pr[fun result => Bad parameter otsSecret ftsSecret result.2.cache ∨
          (¬Bad parameter otsSecret ftsSecret result.2.cache ∧
            ViewedTerminalWitness parameter otsSecret ftsSecret result) | run] := by
      apply probEvent_mono
      intro result hresult hwin
      rcases gameAfterSecretsWithViewTrace_winning_terminal_classify adversary parameter
          otsSecret ftsSecret result hresult hwin with hbad | hterminal
      · exact Or.inl hbad
      · by_cases hbad : Bad parameter otsSecret ftsSecret result.2.cache
        · exact Or.inl hbad
        · exact Or.inr ⟨hbad, hterminal⟩
    _ ≤ Pr[fun result => Bad parameter otsSecret ftsSecret result.2.cache | run] +
        Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedTerminalWitness parameter otsSecret ftsSecret result | run] :=
      probEvent_or_le _ _ _
    _ ≤ _ := by
      gcongr
      exact probEvent_clean_viewedTerminalWitness_le parameter otsSecret ftsSecret run

end Concrete

end SphincsSecurity
