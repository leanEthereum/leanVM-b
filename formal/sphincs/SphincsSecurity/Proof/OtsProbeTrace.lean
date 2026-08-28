import SphincsSecurity.Proof.OtsProbeSampling

/-!
# Retained verifier trace alignment

The digest and few-time recovery prefix of verification uses only stable hash domains. This module
first packages that replay fact, then connects the three concrete one-time verifier layers to the
ordinary entries produced by the probing handler.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

theorem queriesStable_ftsFold
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (tree : FtsTree) (leafIdx : FtsLeaf)
    (path : Fin ftsTreeHeight → Digest) :
    ∀ levels value, levels ≤ ftsTreeHeight →
      QueriesStable parameter f
        (ftsFold parameter index tree leafIdx path levels value)
  | 0, value, _ => QueriesStable.pure parameter f value
  | levels + 1, value, hlevels => by
      rw [ftsFold_succ_eq]
      exact (queriesStable_ftsFold f parameter index tree leafIdx path levels value
        (by omega)).bind <| by
        split <;> split <;>
          exact queriesStable_tweakableHash f parameter
            (.ftsNode index tree (levels + 1) (leafIdx.val / 2 ^ (levels + 1))) _
              (by
                show levels + 1 < 2 ^ 32 ∧ leafIdx.val / 2 ^ (levels + 1) < 2 ^ 32
                constructor
                · have hheight : ftsTreeHeight < 2 ^ 32 := by
                    norm_num [ftsTreeHeight]
                  omega
                · have hleaf : leafIdx.val < 2 ^ 32 := by
                    exact lt_of_lt_of_le leafIdx.isLt (by norm_num [ftsTreeHeight])
                  have hdiv := Nat.div_le_self leafIdx.val (2 ^ (levels + 1))
                  omega)
              (by simp) (by simp) (by simp)

theorem queriesStable_ftsRecover
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (leaves : DigestTree → FtsLeaf)
    (secrets : FtsTree → Digest) (paths : FtsTree → Fin ftsTreeHeight → Digest) :
    QueriesStable parameter f
      (ftsRecover parameter index leaves secrets paths) := by
  unfold ftsRecover
  apply (QueriesStable.sequenceFin _ fun tree => ?_).bind
  · exact queriesStable_tweakableHash f parameter (.ftsRoots index) _ (by trivial)
      (by simp) (by simp) (by simp)
  · exact (queriesStable_ftsLeafHash f parameter index tree
      (leaves (ftsIndexOf tree)) (secrets tree)).bind
        (queriesStable_ftsFold f parameter index tree (leaves (ftsIndexOf tree))
          (paths tree) ftsTreeHeight _ le_rfl)

theorem simulateQ_probingRom_scheme_verify
    (parameter : PublicParameter) (publicKey : PublicKey)
    (message : Message) (signature : Signature) :
    simulateQ (probingRomImpl parameter)
        (scheme.verify publicKey message signature) =
      simulateQ (probingHashImpl parameter)
        (verify publicKey message signature) := by
  rw [show scheme.verify publicKey message signature =
      liftM (verify publicKey message signature : OracleComp HashSpec Bool) by rfl]
  exact QueryImpl.simulateQ_add_liftM_right _ _ _

theorem simulateQ_verifierRom_scheme_verify
    (parameter : PublicParameter) (publicKey : PublicKey)
    (message : Message) (signature : Signature) :
    simulateQ (verifierRomImpl parameter)
        (scheme.verify publicKey message signature) =
      simulateQ (verifierHashImpl parameter)
        (verify publicKey message signature) := by
  rw [show scheme.verify publicKey message signature =
      liftM (verify publicKey message signature : OracleComp HashSpec Bool) by rfl]
  exact QueryImpl.simulateQ_add_liftM_right _ _ _

theorem replay_of_mem_runRaw_verifierRom_scheme_verify
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (publicKey : PublicKey) (message : Message) (signature : Signature)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (verified : Bool)
    (hf : (ordinaryQueryCache finalCache).AgreesWithFn f)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        (verified, finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((simulateQ (verifierRomImpl parameter)
          (scheme.verify publicKey message signature)).run cache))) :
    evalWithAnswerFn f (verify publicKey message signature) = verified ∧
      CachedRun (ordinaryQueryCache finalCache) f
        (verify publicKey message signature) := by
  rw [simulateQ_verifierRom_scheme_verify] at hresult
  exact replay_of_mem_runRaw_verifierHashImpl f parameter
    (verify publicKey message signature) state finalState cache finalCache fuel remaining verified
      hf hresult

theorem rawCachesVerifierTrace_of_mem_runRaw_verifierRom
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (publicKey : PublicKey) (message : Message) (signature : Signature)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (verified : Bool)
    (hf : (ordinaryQueryCache finalCache).AgreesWithFn f)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        (verified, finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((simulateQ (verifierRomImpl parameter)
          (scheme.verify publicKey message signature)).run cache))) :
    ∀ input, input ∈ queriedInputs f (verify publicKey message signature) →
      finalCache (.ordinary input) ≠ none := by
  exact (replay_of_mem_runRaw_verifierRom_scheme_verify f parameter publicKey message signature
    state finalState cache finalCache fuel remaining verified hf hresult).2

set_option maxRecDepth 10000 in
theorem cached_bottom_probe_of_mem_runRaw_verify
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (root : Digest) (message : Message) (signature : Signature)
    (digest : MessageDigest) (codeword : Encoding) (chainIdx : ChainIndex)
    (hdigit : (codeword chainIdx).val < chainLength - 1)
    (hdigest : evalWithAnswerFn f
      (messageDigest parameter root message signature.randomness) = digest)
    (hadmissible : Admissible digest)
    (hencode : evalWithAnswerFn f
      (encode parameter bottomLayer (treeIndexAt (digestIndex digest) bottomLayer)
        (leafIndexAt (digestIndex digest) bottomLayer)
        (evalWithAnswerFn f
          (ftsRecover parameter (digestIndex digest) (digestLeaves digest)
            signature.ftsSecret signature.ftsPath))
        (signature.counter bottomLayer)) = some codeword)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (verified : Bool)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        (verified, finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((simulateQ (probingRomImpl parameter)
          (scheme.verify ⟨root, parameter⟩ message signature)).run cache))) :
    finalCache (.ordinary (tweakableHashInput parameter
      (.chain bottomLayer (treeIndexAt (digestIndex digest) bottomLayer)
        (leafIndexAt (digestIndex digest) bottomLayer) chainIdx
          ⟨(codeword chainIdx).val, hdigit⟩)
      (digestBytes (signature.chainValue bottomLayer chainIdx)))) ≠ none := by
  rw [simulateQ_probingRom_scheme_verify, verify_eq, simulateQ_bind,
    StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨digestRaw, hdigestRaw, hafterDigest⟩ := hresult
  cases digestRaw with
  | stopped hit => simp at hafterDigest
  | done digestState digestRemaining digestResult =>
      rcases digestResult with ⟨sampledDigest, digestCache⟩
      have hfDigest : StableCacheAgreesWithFn parameter digestCache f :=
        StableCacheAgreesWithFn.of_run
          (fun input hstable =>
            (ordinaryEntryPreservingImpl_probingHashImpl parameter input hstable).simulateQ _)
          digestState finalState digestCache finalCache digestRemaining remaining verified hf
            hafterDigest
      have hdigestEval := (replay_of_mem_runRaw_probingHashImpl_of_stable f parameter
        (messageDigest parameter root message signature.randomness) state digestState cache
          digestCache fuel digestRemaining sampledDigest hfDigest
            (queriesStable_messageDigest f parameter root message signature.randomness)
              hdigestRaw).1
      rw [hdigest] at hdigestEval
      subst sampledDigest
      simp only [hadmissible, not_true_eq_false, ↓reduceIte] at hafterDigest
      rw [simulateQ_bind, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hafterDigest
      obtain ⟨ftsRaw, hftsRaw, hafterFts⟩ := hafterDigest
      cases ftsRaw with
      | stopped hit => simp at hafterFts
      | done ftsState ftsRemaining ftsResult =>
          rcases ftsResult with ⟨ftsPublicKey, ftsCache⟩
          have hfFts : StableCacheAgreesWithFn parameter ftsCache f :=
            StableCacheAgreesWithFn.of_run
              (fun input hstable =>
                (ordinaryEntryPreservingImpl_probingHashImpl parameter input hstable).simulateQ _)
              ftsState finalState ftsCache finalCache ftsRemaining remaining verified hf hafterFts
          have hftsEval := (replay_of_mem_runRaw_probingHashImpl_of_stable f parameter
            (ftsRecover parameter (digestIndex digest) (digestLeaves digest)
              signature.ftsSecret signature.ftsPath)
            digestState ftsState digestCache ftsCache digestRemaining ftsRemaining ftsPublicKey
              hfFts (queriesStable_ftsRecover f parameter (digestIndex digest)
                (digestLeaves digest) signature.ftsSecret signature.ftsPath) hftsRaw).1
          subst ftsPublicKey
          simp only at hafterFts
          rw [simulateQ_bind, StateT.run_bind, LazyRevealProbe.runRaw_bind,
            mem_support_bind_iff] at hafterFts
          obtain ⟨layersRaw, hlayersRaw, hafterLayers⟩ := hafterFts
          cases layersRaw with
          | stopped hit => simp at hafterLayers
          | done layersState layersRemaining layersResult =>
              rcases layersResult with ⟨verifiedRoot, layersCache⟩
              have hfLayers : StableCacheAgreesWithFn parameter layersCache f :=
                StableCacheAgreesWithFn.of_run
                  (fun input hstable =>
                    (ordinaryEntryPreservingImpl_probingHashImpl parameter input
                      hstable).simulateQ _)
                  layersState finalState layersCache finalCache layersRemaining remaining
                    verified hf hafterLayers
              rw [show numLayers = bottomLayer.val + 1 by rfl, verifyLayers_succ_eq,
                dif_pos bottomLayer.isLt, simulateQ_bind, StateT.run_bind,
                LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hlayersRaw
              obtain ⟨otsRaw, hotsRaw, hafterOts⟩ := hlayersRaw
              cases otsRaw with
              | stopped hit => simp at hafterOts
              | done otsState otsRemaining otsResult =>
                  rcases otsResult with ⟨leafResult, otsCache⟩
                  have hfOts : StableCacheAgreesWithFn parameter otsCache f :=
                    StableCacheAgreesWithFn.of_run
                      (fun input hstable =>
                        (ordinaryEntryPreservingImpl_probingHashImpl parameter input
                          hstable).simulateQ _)
                      otsState layersState otsCache layersCache otsRemaining layersRemaining
                        verifiedRoot hfLayers hafterOts
                  have hcached := cached_forged_chain_query_of_mem_runRaw_otsLeaf f parameter
                    bottomLayer (treeIndexAt (digestIndex digest) bottomLayer)
                      (leafIndexAt (digestIndex digest) bottomLayer)
                      (evalWithAnswerFn f
                        (ftsRecover parameter (digestIndex digest) (digestLeaves digest)
                          signature.ftsSecret signature.ftsPath))
                      (signature.counter bottomLayer) (signature.chainValue bottomLayer)
                      codeword hencode chainIdx hdigit ftsState otsState ftsCache otsCache
                        ftsRemaining otsRemaining leafResult hfOts hotsRaw
                  have hcachedLayers :=
                    (preservesOrdinaryPresenceImpl_probingHashImpl parameter _).simulateQ _
                      otsState otsCache otsRemaining layersState layersRemaining verifiedRoot
                        layersCache hcached hafterOts
                  exact (preservesOrdinaryPresenceImpl_probingHashImpl parameter _).simulateQ _
                    layersState layersCache layersRemaining finalState remaining verified
                      finalCache hcachedLayers hafterLayers

theorem VerifierLayerMessage.bottom_message
    {f : QueryImpl HashSpec Id} {parameter : PublicParameter} {index : Index}
    {leaves : DigestTree → FtsLeaf} {signature : Signature} {message : Digest}
    (hmessage : VerifierLayerMessage f parameter index leaves signature bottomLayer message) :
    message = evalWithAnswerFn f
      (ftsRecover parameter index leaves signature.ftsSecret signature.ftsPath) := by
  simp only [VerifierLayerMessage] at hmessage
  obtain ⟨bottomLeaf, hbottom, middleLeaf, hmiddle, hposition⟩ := hmessage
  rcases hposition with hbottomPosition | hrest
  · exact hbottomPosition.2
  · rcases hrest with hmiddlePosition | htopPosition
    · have : bottomLayer ≠ middleLayer := by
        intro heq
        have hval := congrArg Fin.val heq
        norm_num [bottomLayer, middleLayer, numLayers] at hval
      exact (this hmiddlePosition.1).elim
    · have : bottomLayer ≠ topLayer := by
        intro heq
        have hval := congrArg Fin.val heq
        norm_num [bottomLayer, topLayer, numLayers] at hval
      exact (this htopPosition.1).elim

theorem VerifierLayerMessage.middle_data
    {f : QueryImpl HashSpec Id} {parameter : PublicParameter} {index : Index}
    {leaves : DigestTree → FtsLeaf} {signature : Signature} {message : Digest}
    (hmessage : VerifierLayerMessage f parameter index leaves signature middleLayer message) :
    ∃ bottomLeaf,
      evalWithAnswerFn f
          (otsLeaf parameter bottomLayer (treeIndexAt index bottomLayer)
            (leafIndexAt index bottomLayer)
            (evalWithAnswerFn f
              (ftsRecover parameter index leaves signature.ftsSecret signature.ftsPath))
            (signature.counter bottomLayer) (signature.chainValue bottomLayer)) =
        some bottomLeaf
      ∧ message = foldValue f parameter bottomLayer (treeIndexAt index bottomLayer)
        (leafIndexAt index bottomLayer) (signaturePath signature bottomLayer) bottomLeaf
          (layerHeight bottomLayer) := by
  simp only [VerifierLayerMessage] at hmessage
  obtain ⟨bottomLeaf, hbottom, middleLeaf, hmiddle, hposition⟩ := hmessage
  refine ⟨bottomLeaf, hbottom, ?_⟩
  rcases hposition with hbottomPosition | hrest
  · have : middleLayer ≠ bottomLayer := by
      intro heq
      have hval := congrArg Fin.val heq
      norm_num [middleLayer, bottomLayer, numLayers] at hval
    exact (this hbottomPosition.1).elim
  · rcases hrest with hmiddlePosition | htopPosition
    · exact hmiddlePosition.2
    · have : middleLayer ≠ topLayer := by
        intro heq
        have hval := congrArg Fin.val heq
        norm_num [middleLayer, topLayer, numLayers] at hval
      exact (this htopPosition.1).elim

theorem VerifierLayerMessage.top_data
    {f : QueryImpl HashSpec Id} {parameter : PublicParameter} {index : Index}
    {leaves : DigestTree → FtsLeaf} {signature : Signature} {message : Digest}
    (hmessage : VerifierLayerMessage f parameter index leaves signature topLayer message) :
    ∃ bottomLeaf middleLeaf,
      evalWithAnswerFn f
          (otsLeaf parameter bottomLayer (treeIndexAt index bottomLayer)
            (leafIndexAt index bottomLayer)
            (evalWithAnswerFn f
              (ftsRecover parameter index leaves signature.ftsSecret signature.ftsPath))
            (signature.counter bottomLayer) (signature.chainValue bottomLayer)) =
        some bottomLeaf
      ∧ evalWithAnswerFn f
          (otsLeaf parameter middleLayer (treeIndexAt index middleLayer)
            (leafIndexAt index middleLayer)
            (foldValue f parameter bottomLayer (treeIndexAt index bottomLayer)
              (leafIndexAt index bottomLayer) (signaturePath signature bottomLayer)
                bottomLeaf (layerHeight bottomLayer))
            (signature.counter middleLayer) (signature.chainValue middleLayer)) =
        some middleLeaf
      ∧ message = foldValue f parameter middleLayer (treeIndexAt index middleLayer)
        (leafIndexAt index middleLayer) (signaturePath signature middleLayer) middleLeaf
          (layerHeight middleLayer) := by
  simp only [VerifierLayerMessage] at hmessage
  obtain ⟨bottomLeaf, hbottom, middleLeaf, hmiddle, hposition⟩ := hmessage
  refine ⟨bottomLeaf, middleLeaf, hbottom, hmiddle, ?_⟩
  rcases hposition with hbottomPosition | hrest
  · have : topLayer ≠ bottomLayer := by
      intro heq
      have hval := congrArg Fin.val heq
      norm_num [topLayer, bottomLayer, numLayers] at hval
    exact (this hbottomPosition.1).elim
  · rcases hrest with hmiddlePosition | htopPosition
    · have : topLayer ≠ middleLayer := by
        intro heq
        have hval := congrArg Fin.val heq
        norm_num [topLayer, middleLayer, numLayers] at hval
      exact (this hmiddlePosition.1).elim
    · exact htopPosition.2

theorem VerifyProbeWitness.at_bottom_or_middle_or_top
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {signingLog : QueryLog SigningSpec}
    {forgedMessage : Message} {signature : Signature}
    (hprobe : VerifyProbeWitness f cache secretKey signingLog forgedMessage signature) :
    VerifyProbeWitnessAt f cache secretKey signingLog forgedMessage signature bottomLayer
      ∨ VerifyProbeWitnessAt f cache secretKey signingLog forgedMessage signature middleLayer
      ∨ VerifyProbeWitnessAt f cache secretKey signingLog forgedMessage signature topLayer := by
  obtain ⟨lay, hprobe⟩ := hprobe
  fin_cases lay
  · exact Or.inr (Or.inr hprobe)
  · exact Or.inr (Or.inl hprobe)
  · exact Or.inl hprobe

theorem ChainInvariant.not_finalized_false_of_bottom_verifyProbe
    {f : QueryImpl HashSpec Id} {parameter : PublicParameter}
    {table : Coordinate → HashOutput}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {targetCache : QueryCache HashSpec}
    {initialState rawState completedState : LazyRevealProbe.State Coordinate}
    {initialCache rawCache : SplitHashCache} {root : Digest} {forgery : Forgery}
    {signingLog : QueryLog SigningSpec} {fuel remaining : Nat} {verified : Bool}
    (hinvariant : ChainInvariant parameter
      (CoveredChainCoordinate f targetCache
        (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) signingLog)
      rawState rawCache)
    (hf : StableCacheAgreesWithFn parameter rawCache f)
    (hcompletedTable : ∀ coordinate output,
      completedState.values coordinate = some output → output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hfinalize : (false, completedState) ∈ support
      (LazyRevealProbe.finalizeDetailed rawState))
    (hverify : LazyRevealProbe.RawResult.done rawState remaining
        (verified, rawCache) ∈ support
      (LazyRevealProbe.runRaw initialState fuel
        ((simulateQ (probingRomImpl parameter)
          (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)).run
            initialCache)))
    (hprobe : VerifyProbeWitnessAt f targetCache
      (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
      signingLog forgery.message forgery.signature bottomLayer) : False := by
  obtain ⟨digest, layerMessage, codeword, chainIdx, hdigit, probe, input, hinput,
    hdigest, hadmissible, hencode, hverifierMessage, hhits, hmatches, hquery,
    htargetCached, hnotCovered, _hsourceSettled⟩ := hprobe
  have hlayerMessage := VerifierLayerMessage.bottom_message hverifierMessage
  rw [hlayerMessage] at hencode
  have hcached := cached_bottom_probe_of_mem_runRaw_verify f parameter root forgery.message
    forgery.signature digest codeword chainIdx hdigit hdigest hadmissible hencode
      initialState rawState initialCache rawCache fuel remaining verified hf hverify
  have hcachedInput : rawCache (.ordinary input) ≠ none := by
    rw [hinput]
    exact hcached
  exact hinvariant.not_finalized_false_of_uncovered_probe probe input hhits hmatches
    hcachedInput hnotCovered (hcompletedTable probe.coordinate) hrealizes hfinalize

theorem ChainInvariant.not_finalized_false_of_verifyProbe_of_cachedBefore
    {f : QueryImpl HashSpec Id} {parameter : PublicParameter}
    {table : Coordinate → HashOutput}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {targetCache : QueryCache HashSpec}
    {initialState rawState completedState : LazyRevealProbe.State Coordinate}
    {initialCache rawCache : SplitHashCache} {root : Digest} {forgery : Forgery}
    {signingLog : QueryLog SigningSpec} {fuel remaining : Nat} {verified : Bool}
    (hinvariant : ChainInvariant parameter
      (CoveredChainCoordinate f targetCache
        (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) signingLog)
      initialState initialCache)
    (hcompletedTable : ∀ coordinate output,
      completedState.values coordinate = some output → output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hfinalize : (false, completedState) ∈ support
      (LazyRevealProbe.finalizeDetailed rawState))
    (hverify : LazyRevealProbe.RawResult.done rawState remaining
        (verified, rawCache) ∈ support
      (LazyRevealProbe.runRaw initialState fuel
        ((simulateQ (verifierRomImpl parameter)
          (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)).run
            initialCache)))
    (hqueriesBefore : ∀ input,
      input ∈ queriedInputs f
        (verify ⟨root, parameter⟩ forgery.message forgery.signature) →
      initialCache (.ordinary input) ≠ none)
    (hprobe : VerifyProbeWitness f targetCache
      (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
      signingLog forgery.message forgery.signature) : False := by
  obtain ⟨lay, digest, layerMessage, codeword, chainIdx, hdigit, probe, input,
    hinput, hdigest, hadmissible, hencode, hverifierMessage, hhits, hmatches, hquery,
    _, hnotCovered, _hsourceSettled⟩ := hprobe
  exact hinvariant.not_finalized_false_of_uncovered_probe_through probe input hhits hmatches
    (hqueriesBefore input hquery) hnotCovered (hcompletedTable probe.coordinate) hrealizes
      hverify hfinalize

end SphincsSecurity.Concrete.OtsProbeSimulation
