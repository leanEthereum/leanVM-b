import SphincsSecurity.Proof.RetainedForgeryClassify
import SphincsSecurity.Proof.FewTimeHonestLeakTerminal

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

def ViewedVerifierStructuralCollision (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState) : Prop :=
  result.1.2.2 = true ∧ ∃ f : QueryImpl HashSpec Id,
    result.2.cache.AgreesWithFn f ∧
      evalWithAnswerFn f
        (verify ⟨result.1.1, parameter⟩ result.1.2.1.message result.1.2.1.signature) = true ∧
      CachedRun result.2.cache f
        (verify ⟨result.1.1, parameter⟩ result.1.2.1.message result.1.2.1.signature) ∧
      BadOnInputs ⟨parameter, result.1.1, otsSecret, ftsSecret⟩ result.2.cache
        {input | input ∈ queriedInputs f
          (verify ⟨result.1.1, parameter⟩ result.1.2.1.message result.1.2.1.signature)}

theorem ViewedVerifierStructuralCollision.bad
    {parameter : PublicParameter}
    {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {result : (Digest × Forgery × Bool) × ViewedFullTraceState}
    (hcollision : ViewedVerifierStructuralCollision parameter otsSecret ftsSecret result) :
    Bad parameter otsSecret ftsSecret result.2.cache := by
  obtain ⟨_, _, _, _, _, hbad⟩ := hcollision
  exact hbad.bad

theorem viewedVerifierStructuralCollision_iff_fromCache
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState) :
    ViewedVerifierStructuralCollision parameter otsSecret ftsSecret result ↔
      result.1.2.2 = true ∧
        evalWithAnswerFn (fromCache result.2.cache)
          (verify ⟨result.1.1, parameter⟩ result.1.2.1.message result.1.2.1.signature) = true ∧
        CachedRun result.2.cache (fromCache result.2.cache)
          (verify ⟨result.1.1, parameter⟩ result.1.2.1.message result.1.2.1.signature) ∧
        BadOnInputs ⟨parameter, result.1.1, otsSecret, ftsSecret⟩ result.2.cache
          {input | input ∈ queriedInputs (fromCache result.2.cache)
            (verify ⟨result.1.1, parameter⟩ result.1.2.1.message result.1.2.1.signature)} := by
  have hg := agreesWithFn_fromCache result.2.cache
  constructor
  · rintro ⟨hwin, f, hf, heval, hrun, hbad⟩
    refine ⟨hwin, (hrun.eval_eq hf hg).symm.trans heval, hrun.changeAnswerFn hf hg, ?_⟩
    simpa only [hrun.queriedInputs_eq hf hg] using hbad
  · rintro ⟨hwin, heval, hrun, hbad⟩
    exact ⟨hwin, fromCache result.2.cache, hg, heval, hrun, hbad⟩

theorem gameAfterSecretsWithViewTrace_winning_usedCollision_classify
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hresult : result ∈ support
      (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret))
    (hwin : result.1.2.2 = true) :
    ViewedVerifierStructuralCollision parameter otsSecret ftsSecret result ∨
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
  let secretKey : SecretKey := ⟨parameter, root, otsSecret, ftsSecret⟩
  let inputs : Set HashInput := {input | input ∈ queriedInputs f
    (verify ⟨root, parameter⟩ forgery.message forgery.signature)}
  let retained := retainHonestCache secretKey finalCache inputs
  have hretainedLe : retained ≤ finalCache := retainHonestCache_le secretKey finalCache inputs
  have hfRetained : retained.AgreesWithFn f :=
    retainHonestCache_agreesWithFn secretKey finalCache inputs f hf
  have hpreserved := settled_retainHonestCache secretKey finalCache inputs
  have hqueriesRetained : CachedRun retained f
      (verify ⟨root, parameter⟩ forgery.message forgery.signature) :=
    cachedRun_retainHonestCache secretKey finalCache inputs f _ hqueries (fun _ h => h)
  obtain ⟨digest, hdigest, hdigestRunSmall, hadmissible, hlayers, hftsRunSmall, hlayersRunSmall⟩ :=
    verify_extract ⟨root, parameter⟩ forgery.message forgery.signature heval hqueriesRetained
  have hdigestRun := hdigestRunSmall.mono hretainedLe
  have hftsRun := hftsRunSmall.mono hretainedLe
  let index := digestIndex digest
  let leaves := digestLeaves digest
  let ftsPublicKey := evalWithAnswerFn f
    (ftsRecover parameter index leaves forgery.signature.ftsSecret forgery.signature.ftsPath)
  have hhypertree : HypertreeRun f retained parameter index forgery.signature
      ftsPublicKey root :=
    hypertreeRun_of_verify index forgery.signature ftsPublicKey root hlayers hlayersRunSmall
  have htarget : root = honestNode f parameter topLayer rootTree
      (otsSecret topLayer rootTree) (layerHeight topLayer) 0 := by
    rw [← hrootEval]
    rfl
  have htop := hypertree_top_extract_or_bad hfRetained index forgery.signature ftsPublicKey root
    hhypertree htarget (by simpa using hpreserved _ hrootSettled)
  rcases htop with hbad | htop
  · apply Or.inl
    exact ⟨hwin, f, hf, heval, hqueries,
      (bad_retainHonestCache_iff secretKey finalCache inputs).mp hbad⟩
  · have hclassified := accepted_forgery_classify_retained f finalCache retained secretKey
      state.trace.signing.toSigningLog index forgery.signature leaves ftsPublicKey root hf
        hretainedLe hpreserved rfl
        htop (by
          have htree : treeIndexAt index topLayer = rootTree := by
            apply Fin.ext
            exact treeIndexAt_topLayer index
          unfold LayerRootSettled
          rw [htree]
          simpa using hrootSettled) hftsRunSmall
    rcases hclassified with hbad | hobstacle | hfull
    · apply Or.inl
      exact ⟨hwin, f, hf, heval, hqueries,
        (bad_retainHonestCache_iff secretKey finalCache inputs).mp hbad⟩
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

end SphincsSecurity.Concrete
