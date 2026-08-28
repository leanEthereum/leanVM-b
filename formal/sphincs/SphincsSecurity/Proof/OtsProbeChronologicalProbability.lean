import SphincsSecurity.Proof.OtsProbeChronologicalTerminal

/-!
# Probability boundary for chronological one-time probes

The resolved coupling supplies a concrete cache that agrees with every clean deferred completion.
This file first packages that support-level fact into the exact terminal contradiction, before
relating failed completion to the lazy-probe probability bound.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedChronologicalRetainedGameAfterFtsSecrets
  actualRetainedGameAfterTable

theorem VerifierLayerMessage.changeAnswerFn_of_cachedVerify
    {f g : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {publicKey : PublicKey} {forgedMessage : Message} {signature : Signature}
    {digest : MessageDigest} {lay : Layer} {layerMessage : Digest}
    (hmessage : VerifierLayerMessage f publicKey.parameter (digestIndex digest)
      (digestLeaves digest) signature lay layerMessage)
    (hdigest : evalWithAnswerFn f
      (messageDigest publicKey.parameter publicKey.root forgedMessage signature.randomness) =
        digest)
    (hadmissible : Admissible digest)
    (hrun : CachedRun cache f (verify publicKey forgedMessage signature))
    (hf : cache.AgreesWithFn f) (hg : cache.AgreesWithFn g) :
    VerifierLayerMessage g publicKey.parameter (digestIndex digest)
      (digestLeaves digest) signature lay layerMessage := by
  simp only [VerifierLayerMessage] at hmessage ⊢
  obtain ⟨bottomLeaf, hbottom, middleLeaf, hmiddle, hposition⟩ := hmessage
  have hftsRun : CachedRun cache f
      (ftsRecover publicKey.parameter (digestIndex digest) (digestLeaves digest)
        signature.ftsSecret signature.ftsPath) := by
    intro input hquery
    exact hrun input (ftsRecover_query_mem_verify hdigest hadmissible hquery)
  have hftsEq := hftsRun.eval_eq hf hg
  have hbottomRun : CachedRun cache f
      (otsLeaf publicKey.parameter bottomLayer
        (treeIndexAt (digestIndex digest) bottomLayer)
        (leafIndexAt (digestIndex digest) bottomLayer)
        (evalWithAnswerFn f
          (ftsRecover publicKey.parameter (digestIndex digest) (digestLeaves digest)
            signature.ftsSecret signature.ftsPath))
        (signature.counter bottomLayer) (signature.chainValue bottomLayer)) := by
    intro input hquery
    exact hrun input (bottomOts_query_mem_verify hdigest hadmissible hquery)
  have hbottomEq := hbottomRun.eval_eq hf hg
  have hbottomFoldRun : CachedRun cache f
      (treeFold publicKey.parameter bottomLayer
        (treeIndexAt (digestIndex digest) bottomLayer)
        (leafIndexAt (digestIndex digest) bottomLayer)
        (signaturePath signature bottomLayer) (layerHeight bottomLayer) bottomLeaf) := by
    intro input hquery
    exact hrun input (bottomFold_query_mem_verify hdigest hadmissible hbottom hquery)
  have hbottomFoldEq :
      foldValue f publicKey.parameter bottomLayer
          (treeIndexAt (digestIndex digest) bottomLayer)
          (leafIndexAt (digestIndex digest) bottomLayer)
          (signaturePath signature bottomLayer) bottomLeaf (layerHeight bottomLayer) =
        foldValue g publicKey.parameter bottomLayer
          (treeIndexAt (digestIndex digest) bottomLayer)
          (leafIndexAt (digestIndex digest) bottomLayer)
          (signaturePath signature bottomLayer) bottomLeaf (layerHeight bottomLayer) := by
    exact hbottomFoldRun.eval_eq hf hg
  have hmiddleRun : CachedRun cache f
      (otsLeaf publicKey.parameter middleLayer
        (treeIndexAt (digestIndex digest) middleLayer)
        (leafIndexAt (digestIndex digest) middleLayer)
        (foldValue f publicKey.parameter bottomLayer
          (treeIndexAt (digestIndex digest) bottomLayer)
          (leafIndexAt (digestIndex digest) bottomLayer)
          (signaturePath signature bottomLayer) bottomLeaf (layerHeight bottomLayer))
        (signature.counter middleLayer) (signature.chainValue middleLayer)) := by
    intro input hquery
    exact hrun input (middleOts_query_mem_verify hdigest hadmissible hbottom hquery)
  have hmiddleEq := hmiddleRun.eval_eq hf hg
  have hmiddleFoldRun : CachedRun cache f
      (treeFold publicKey.parameter middleLayer
        (treeIndexAt (digestIndex digest) middleLayer)
        (leafIndexAt (digestIndex digest) middleLayer)
        (signaturePath signature middleLayer) (layerHeight middleLayer) middleLeaf) := by
    intro input hquery
    exact hrun input
      (middleFold_query_mem_verify hdigest hadmissible hbottom hmiddle hquery)
  have hmiddleFoldEq :
      foldValue f publicKey.parameter middleLayer
          (treeIndexAt (digestIndex digest) middleLayer)
          (leafIndexAt (digestIndex digest) middleLayer)
          (signaturePath signature middleLayer) middleLeaf (layerHeight middleLayer) =
        foldValue g publicKey.parameter middleLayer
          (treeIndexAt (digestIndex digest) middleLayer)
          (leafIndexAt (digestIndex digest) middleLayer)
          (signaturePath signature middleLayer) middleLeaf (layerHeight middleLayer) := by
    exact hmiddleFoldRun.eval_eq hf hg
  refine ⟨bottomLeaf, ?_, middleLeaf, ?_, ?_⟩
  · rw [← hftsEq, ← hbottomEq]
    exact hbottom
  · rw [← hbottomFoldEq, ← hmiddleEq]
    exact hmiddle
  · rcases hposition with hbottomPosition | hmiddlePosition | htopPosition
    · exact Or.inl ⟨hbottomPosition.1, hbottomPosition.2.trans hftsEq⟩
    · exact Or.inr (Or.inl
        ⟨hmiddlePosition.1, hmiddlePosition.2.trans hbottomFoldEq⟩)
    · exact Or.inr (Or.inr ⟨htopPosition.1, htopPosition.2.trans hmiddleFoldEq⟩)

set_option maxHeartbeats 2000000 in
theorem VerifyProbeWitnessAt.changeAnswerFn
    {f g : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {signingLog : QueryLog SigningSpec}
    {forgedMessage : Message} {signature : Signature} {lay : Layer}
    (hprobe : VerifyProbeWitnessAt f cache secretKey signingLog forgedMessage signature lay)
    (hrun : CachedRun cache f
      (verify ⟨secretKey.root, secretKey.parameter⟩ forgedMessage signature))
    (hf : cache.AgreesWithFn f) (hg : cache.AgreesWithFn g) :
    VerifyProbeWitnessAt g cache secretKey signingLog forgedMessage signature lay := by
  obtain ⟨digest, layerMessage, codeword, chainIdx, hdigit, probe, input,
    hinput, hdigest, hadmissible, hencode, hverifierMessage, hhits, hmatches, hquery,
    hcached, hnotCovered, hsourceSettled⟩ := hprobe
  have hdigestRun : CachedRun cache f
      (messageDigest secretKey.parameter secretKey.root forgedMessage signature.randomness) := by
    intro query hquery
    exact hrun query (messageDigest_query_mem_verify hquery)
  have hdigest' : evalWithAnswerFn g
      (messageDigest secretKey.parameter secretKey.root forgedMessage signature.randomness) =
        digest := by
    rw [← hdigestRun.eval_eq hf hg]
    exact hdigest
  have hotsRun : CachedRun cache f
      (otsLeaf secretKey.parameter lay (treeIndexAt (digestIndex digest) lay)
        (leafIndexAt (digestIndex digest) lay) layerMessage (signature.counter lay)
        (signature.chainValue lay)) := by
    intro query hquery
    exact hrun query
      (VerifierLayerMessage.otsLeaf_query_mem_verify hdigest hadmissible
        hverifierMessage hquery)
  have hencodeRun : CachedRun cache f
      (encode secretKey.parameter lay (treeIndexAt (digestIndex digest) lay)
        (leafIndexAt (digestIndex digest) lay) layerMessage (signature.counter lay)) :=
    hotsRun.bind_left
  have hencode' : evalWithAnswerFn g
      (encode secretKey.parameter lay (treeIndexAt (digestIndex digest) lay)
        (leafIndexAt (digestIndex digest) lay) layerMessage (signature.counter lay)) =
        some codeword := by
    rw [← hencodeRun.eval_eq hf hg]
    exact hencode
  have hverifierMessage' : VerifierLayerMessage g secretKey.parameter
      (digestIndex digest) (digestLeaves digest) signature lay layerMessage := by
    exact VerifierLayerMessage.changeAnswerFn_of_cachedVerify
      (f := f) (g := g) (cache := cache)
      (publicKey := ⟨secretKey.root, secretKey.parameter⟩)
      (forgedMessage := forgedMessage) (signature := signature) (digest := digest)
      (lay := lay) (layerMessage := layerMessage) hverifierMessage hdigest hadmissible
      hrun hf hg
  have hhits' : probe.Hits g secretKey.parameter secretKey.otsSecret secretKey.ftsSecret := by
    unfold Probe.Hits at hhits ⊢
    rw [← probe.target_eq_of_sourceSettled hf hg hsourceSettled]
    exact hhits
  have hquery' : input ∈ queriedInputs g
      (verify ⟨secretKey.root, secretKey.parameter⟩ forgedMessage signature) := by
    rw [← hrun.queriedInputs_eq hf hg]
    exact hquery
  have hnotCovered' :
      ¬CoveredChainCoordinate g cache secretKey signingLog probe.coordinate := by
    intro hcovered
    exact hnotCovered (hcovered.changeAnswerFn hg hf)
  refine ⟨digest, layerMessage, codeword, chainIdx, hdigit, probe, input, hinput, ?_⟩
  refine ⟨hdigest', ?_⟩
  refine ⟨hadmissible, ?_⟩
  refine ⟨hencode', ?_⟩
  refine ⟨hverifierMessage', ?_⟩
  refine ⟨hhits', ?_⟩
  refine ⟨hmatches, ?_⟩
  refine ⟨hquery', ?_⟩
  refine ⟨hcached, ?_⟩
  exact ⟨hnotCovered', hsourceSettled⟩

theorem VerifyProbeWitness.changeAnswerFn
    {f g : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {signingLog : QueryLog SigningSpec}
    {forgedMessage : Message} {signature : Signature}
    (hprobe : VerifyProbeWitness f cache secretKey signingLog forgedMessage signature)
    (hrun : CachedRun cache f
      (verify ⟨secretKey.root, secretKey.parameter⟩ forgedMessage signature))
    (hf : cache.AgreesWithFn f) (hg : cache.AgreesWithFn g) :
    VerifyProbeWitness g cache secretKey signingLog forgedMessage signature := by
  obtain ⟨lay, hprobe⟩ := hprobe
  exact ⟨lay, hprobe.changeAnswerFn hrun hf hg⟩

def ResolvedCompletionVerifyProbe (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : ResolvedRunResult (RetainedGameResult × SplitHashCache))
    (actualValue : RetainedGameResult) (actualCache : QueryCache HashSpec) : Prop :=
  ∃ completion : Coordinate → HashOutput,
    DeferredCompletion table result.context completion ∧
      VerifyProbeWitness
        (tableAnswer parameter completion (fromCache (ordinaryQueryCache result.value.2)))
        actualCache
        (⟨parameter, actualValue.1,
          fun lay tree leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
          ftsSecret⟩ : SecretKey)
        actualValue.2.1.2 actualValue.2.1.1.message actualValue.2.1.1.signature

set_option maxHeartbeats 2000000 in
theorem resolvedCompletionVerifyProbe_of_winning_of_deferredCompletable
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : ResolvedRunResult (RetainedGameResult × SplitHashCache))
    (actualValue : RetainedGameResult) (actualCache : QueryCache HashSpec)
    (hactual : (actualValue, actualCache) ∈ support
      (actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table)))
    (hrelation : ReachableResolvedRunRel parameter table (some result)
      (actualValue, actualCache))
    (hcompletable : DeferredCompletable table result.context)
    (hwitness : WinningRetainedVerifyProbeWitness parameter (extendStartTable table)
      ftsSecret (actualValue, actualCache)) :
    ResolvedCompletionVerifyProbe parameter table ftsSecret result actualValue actualCache := by
  rcases hrelation with hclean | hdoomed
  · obtain ⟨_, _, hinvariant, _, _⟩ := hclean
    obtain ⟨completion, hcompletion⟩ := hcompletable
    have hexecuted := winningRetainedVerifyProbe_imp_executed adversary parameter
      (extendStartTable table) ftsSecret (actualValue, actualCache) hactual hwitness
    obtain ⟨_, f, _, hf, _, _, _, _, _, _, hprobe, hrun⟩ := hexecuted
    let fallback : QueryImpl HashSpec Id :=
      fromCache (ordinaryQueryCache result.value.2)
    have hfallback : CacheAgreesWithFnOffTable parameter completion
        (ordinaryQueryCache result.value.2) fallback :=
      CacheAgreesWithFnOffTable.of_agrees
        (agreesWithFn_fromCache (ordinaryQueryCache result.value.2))
    have hagrees : actualCache.AgreesWithFn
        (tableAnswer parameter completion fallback) :=
      hinvariant.concreteCache_agreesWith_tableAnswer_of_fallback completion hcompletion
        fallback hfallback
    refine ⟨completion, hcompletion, ?_⟩
    exact hprobe.changeAnswerFn hrun hf hagrees
  · exact False.elim (hdoomed.2.2.2 hcompletable)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem not_completionVerifyProbe_of_reachableResolvedRunRel
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (result : ResolvedRunResult (RetainedGameResult × SplitHashCache))
    (actualValue : RetainedGameResult) (actualCache : QueryCache HashSpec)
    (hresult : some result ∈ support
      (runResolvedFromTable
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues }
        fuel table
        ((maskedChronologicalRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run
          emptySplitHashCache)))
    (hactual : (actualValue, actualCache) ∈ support
      (actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table)))
    (hrelation : ReachableResolvedRunRel parameter table (some result)
      (actualValue, actualCache))
    (completion : Coordinate → HashOutput)
    (hcompletion : DeferredCompletion table result.context completion)
    (hprobe : VerifyProbeWitness
      (tableAnswer parameter completion (fromCache (ordinaryQueryCache result.value.2)))
      actualCache
      (⟨parameter, actualValue.1,
        fun lay tree leafIdx chainIdx =>
          truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
        ftsSecret⟩ : SecretKey)
      actualValue.2.1.2 actualValue.2.1.1.message actualValue.2.1.1.signature) : False := by
  rcases hrelation with hclean | hdoomed
  · obtain ⟨htable, hvalue, hinvariant, _hclosed, _hpublished⟩ := hclean
    have hactual' : (result.value.1, actualCache) ∈ support
        (actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table)) := by
      rw [hvalue]
      exact hactual
    have hprobe' : VerifyProbeWitness
        (tableAnswer parameter completion (fromCache (ordinaryQueryCache result.value.2)))
        actualCache
        (⟨parameter, result.value.1.1,
          fun lay tree leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
          ftsSecret⟩ : SecretKey)
        result.value.1.2.1.2 result.value.1.2.1.1.message
          result.value.1.2.1.1.signature := by
      rw [hvalue]
      exact hprobe
    let fallback : QueryImpl HashSpec Id := fromCache (ordinaryQueryCache result.value.2)
    have hfallback : CacheAgreesWithFnOffTable parameter completion
        (ordinaryQueryCache result.value.2) fallback :=
      CacheAgreesWithFnOffTable.of_agrees
        (agreesWithFn_fromCache (ordinaryQueryCache result.value.2))
    have hagrees : actualCache.AgreesWithFn
        (tableAnswer parameter completion fallback) :=
      hinvariant.concreteCache_agreesWith_tableAnswer_of_fallback completion hcompletion
        fallback hfallback
    have hlogRuns := successfulSignRuns_of_mem_support_actualRetainedGameAfterTable adversary
      (tableAnswer parameter completion fallback) parameter table ftsSecret result.value.1.1
        result.value.1.2.1.1 result.value.1.2.1.2 result.value.1.2.2 actualCache hactual' hagrees
    exact not_verifyProbe_of_mem_runResolved_maskedChronologicalRetainedGame adversary parameter
      table ftsSecret actualCache completion fallback fuel result hresult hcompletion hfallback
        hlogRuns hprobe'
  · exact hdoomed.2.2.2 ⟨completion, hcompletion⟩

theorem not_resolvedCompletionVerifyProbe_of_reachableResolvedRunRel
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (result : ResolvedRunResult (RetainedGameResult × SplitHashCache))
    (actualValue : RetainedGameResult) (actualCache : QueryCache HashSpec)
    (hresult : some result ∈ support
      (runResolvedFromTable
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues }
        fuel table
        ((maskedChronologicalRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run
          emptySplitHashCache)))
    (hactual : (actualValue, actualCache) ∈ support
      (actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table)))
    (hrelation : ReachableResolvedRunRel parameter table (some result)
      (actualValue, actualCache)) :
    ¬ResolvedCompletionVerifyProbe parameter table ftsSecret result actualValue actualCache := by
  rintro ⟨completion, hcompletion, hprobe⟩
  exact not_completionVerifyProbe_of_reachableResolvedRunRel adversary parameter table ftsSecret
    fuel result actualValue actualCache hresult hactual hrelation completion hcompletion hprobe

theorem not_deferredCompletable_of_winningRetainedVerifyProbe
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (result : ResolvedRunResult (RetainedGameResult × SplitHashCache))
    (actualValue : RetainedGameResult) (actualCache : QueryCache HashSpec)
    (hresult : some result ∈ support
      (runResolvedFromTable
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues }
        fuel table
        ((maskedChronologicalRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run
          emptySplitHashCache)))
    (hactual : (actualValue, actualCache) ∈ support
      (actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table)))
    (hrelation : ReachableResolvedRunRel parameter table (some result)
      (actualValue, actualCache))
    (hwitness : WinningRetainedVerifyProbeWitness parameter (extendStartTable table)
      ftsSecret (actualValue, actualCache)) :
    ¬DeferredCompletable table result.context := by
  intro hcompletable
  have hcompletionProbe :=
    resolvedCompletionVerifyProbe_of_winning_of_deferredCompletable adversary parameter table
      ftsSecret result actualValue actualCache hactual hrelation hcompletable hwitness
  exact (not_resolvedCompletionVerifyProbe_of_reachableResolvedRunRel adversary parameter table
    ftsSecret fuel result actualValue actualCache hresult hactual hrelation) hcompletionProbe

def ResolvedCompletionFailure (table : OtsSecretIndex → HashOutput) :
    Option (ResolvedRunResult (RetainedGameResult × SplitHashCache)) → Prop
  | none => True
  | some result => ¬DeferredCompletable table result.context

theorem probEvent_winningRetainedVerifyProbe_le_resolvedCompletionFailure
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[WinningRetainedVerifyProbeWitness parameter (extendStartTable table) ftsSecret |
        actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table)] ≤
      Pr[ResolvedCompletionFailure table |
        runResolvedFromTable
          { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
            values := emptyDeferredStructuralValues }
          fuel table
          ((maskedChronologicalRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run
            emptySplitHashCache)] := by
  let resolvedRun := runResolvedFromTable
    { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      values := emptyDeferredStructuralValues }
    fuel table
    ((maskedChronologicalRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run
      emptySplitHashCache)
  let actualRun :=
    actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table)
  have hrel := relTriple_runResolvedFromTable_maskedChronologicalRetainedGame adversary parameter
    table ftsSecret fuel
  have hleft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hrel
      (fun result => result ∈ support resolvedRun) (fun result hresult => hresult)
  have hboth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
  apply probEvent_le_of_relTriple (relTriple_symm hboth)
  intro actualResult resolvedResult hrelation hwitness
  cases resolvedResult with
  | none => trivial
  | some result =>
      exact not_deferredCompletable_of_winningRetainedVerifyProbe adversary parameter table
        ftsSecret fuel result actualResult.1 actualResult.2 hrelation.1.2 hrelation.2
          hrelation.1.1 hwitness

theorem probEvent_resolvedCompletionFailure_le_finishResolvedRun_none
    (table : OtsSecretIndex → HashOutput)
    (run : ProbComp
      (Option (ResolvedRunResult (RetainedGameResult × SplitHashCache))))
    (htable : ∀ result, some result ∈ support run → result.table = table) :
    Pr[ResolvedCompletionFailure table | run] ≤
      Pr[fun result => result = none | run >>= finishResolvedRun] := by
  classical
  calc
    Pr[ResolvedCompletionFailure table | run] =
        Pr[ResolvedCompletionFailure table | run >>= pure] := by rw [bind_pure]
    _ ≤ Pr[fun result => result = none | run >>= finishResolvedRun] := by
      apply probEvent_bind_le_bind_of_forall_le
      intro result _hresult
      cases result with
      | none => simp [ResolvedCompletionFailure, finishResolvedRun]
      | some result =>
          have hresultTable := htable result _hresult
          by_cases hcompletable : DeferredCompletable table result.context
          · have hfailure : ¬ResolvedCompletionFailure table (some result) := by
              simpa [ResolvedCompletionFailure] using hcompletable
            rw [probEvent_pure]
            simp [hfailure]
          · have hdoomed : ¬DeferredCompletable result.table result.context := by
              rwa [hresultTable]
            rw [finishResolvedRun_of_not_deferredCompletable result hdoomed]
            simp [ResolvedCompletionFailure, hcompletable]

theorem probEvent_winningRetainedVerifyProbe_le_finishedResolvedRun_none
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[WinningRetainedVerifyProbeWitness parameter (extendStartTable table) ftsSecret |
        actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table)] ≤
      Pr[fun result => result = none |
        runResolvedFromTable
          { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
            values := emptyDeferredStructuralValues }
          fuel table
          ((maskedChronologicalRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run
            emptySplitHashCache) >>= finishResolvedRun] := by
  exact (probEvent_winningRetainedVerifyProbe_le_resolvedCompletionFailure adversary parameter
    table ftsSecret fuel).trans
      (probEvent_resolvedCompletionFailure_le_finishResolvedRun_none table _ (by
        intro result hresult
        exact (resolvedCore_of_mem_runResolvedFromTable
          ((maskedChronologicalRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run
            emptySplitHashCache)
          { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
            values := emptyDeferredStructuralValues }
          fuel table result DeferredContext.valid_empty.valuesConsistent
          (startTableAgrees_empty table)
          hresult).1))

end SphincsSecurity.Concrete.OtsProbeSimulation
