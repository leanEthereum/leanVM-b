import SphincsSecurity.Proof.SecretProbe
import SphincsSecurity.Proof.TerminalSampling

/-!
# Few-time terminal witnesses expose an exact secret probe

The uncovered-secret terminal branch already retains the exact few-time leaf-hash input used by
verification. This module packages that input as one coordinate-and-candidate probe into the sampled
few-time table.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

theorem UncoveredFtsSecret.exists_hit_probe
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index} {leaves : DigestTree → FtsLeaf}
    {secrets : FtsTree → Digest}
    (huncovered : UncoveredFtsSecret f cache secretKey signingLog index leaves secrets) :
    ∃ probe : FtsSecretProbe,
      probe.Hits secretKey.ftsSecret
        ∧ cache (probe.input secretKey.parameter) ≠ none
        ∧ ¬ SignedFtsLeaf f cache secretKey signingLog probe.index probe.tree probe.leafIdx := by
  obtain ⟨tree, hnotSigned, hsecret, hcached⟩ := huncovered
  let probe : FtsSecretProbe :=
    ⟨index, tree, leaves (ftsIndexOf tree), secrets tree⟩
  exact ⟨probe, hsecret.symm, hcached, hnotSigned⟩

theorem ViewedUncoveredFtsSecretWitness.exists_hit_probe
    {parameter : PublicParameter}
    {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {result : (Digest × Forgery × Bool) × ViewedFullTraceState}
    (hwitness : ViewedUncoveredFtsSecretWitness parameter otsSecret ftsSecret result) :
    ∃ probe : FtsSecretProbe,
      probe.Hits ftsSecret ∧ result.2.cache (probe.input parameter) ≠ none := by
  obtain ⟨f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, huncovered⟩ := hwitness
  obtain ⟨probe, hhit, hcached, _⟩ := huncovered.exists_hit_probe
  exact ⟨probe, hhit, hcached⟩

theorem cleanUncoveredEvent_exists_hit_probe
    {parameter : PublicParameter}
    {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {result : (Digest × Forgery × Bool) × ViewedFullTraceState}
    (hevent : cleanUncoveredEvent parameter otsSecret ftsSecret result) :
    ∃ probe : FtsSecretProbe,
      probe.Hits ftsSecret ∧ result.2.cache (probe.input parameter) ≠ none :=
  hevent.2.exists_hit_probe

theorem FreshLayerOpening.exists_hit_probe
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec}
    (hfresh : FreshLayerOpening f cache secretKey signingLog) :
    ∃ probe : OtsValueProbe,
      probe.Hits f secretKey.parameter secretKey.otsSecret
        ∧ ¬ SignedLayerAt f cache secretKey signingLog probe.lay probe.tree probe.leafIdx := by
  obtain ⟨lay, tree, leafIdx, message, counter, values, path, hopening, hcached,
      hnotSigned⟩ := hfresh
  obtain ⟨codeword, hencode, hvalues, hpath⟩ := hopening
  let chainIdx : ChainIndex := ⟨0, by decide⟩
  let probe : OtsValueProbe :=
    ⟨lay, tree, leafIdx, chainIdx, codeword chainIdx, values chainIdx⟩
  exact ⟨probe, hvalues chainIdx, hnotSigned⟩

theorem BackwardChainOpening.exists_hit_probe
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec}
    (hbackward : BackwardChainOpening f cache secretKey signingLog) :
    ∃ (probe : OtsValueProbe) (signedDigit : Digit),
      probe.Hits f secretKey.parameter secretKey.otsSecret
        ∧ probe.digit.val < signedDigit.val := by
  obtain ⟨lay, tree, leafIdx, forgedMessage, forgedCounter, forgedValues, forgedPath,
      entry, signature, index, leaves, signedCodeword, forgedCodeword, hforgedOpening,
      hforgedRun, hentry, hresponse, hsignRun, hdigest, htree, hleaf, hmessage,
      hsignedOpening, hsignedCached, hsigned, hforged, chainIdx, hlt⟩ := hbackward
  obtain ⟨openingCodeword, hopeningEncode, hforgedValues, _⟩ := hforgedOpening
  have hcodeword : openingCodeword = forgedCodeword :=
    Option.some.inj (hopeningEncode.symm.trans hforged)
  let probe : OtsValueProbe :=
    ⟨lay, tree, leafIdx, chainIdx, forgedCodeword chainIdx, forgedValues chainIdx⟩
  refine ⟨probe, signedCodeword chainIdx, ?_, hlt⟩
  simpa only [OtsValueProbe.Hits, OtsValueProbe.target, probe, hcodeword] using
    hforgedValues chainIdx

theorem slotDigest_leafPayload_zero (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (endpoints : ChainIndex → Digest) (chainIdx : ChainIndex) (hzero : chainIdx.val = 0) :
    slotDigest 0 (tweakableHashInput parameter (.leaf lay tree leafIdx)
      (leafPayload endpoints)) = endpoints chainIdx := by
  unfold leafPayload
  rw [slotDigest_flatMap parameter (.leaf lay tree leafIdx) (List.ofFn endpoints) 0
    (by norm_num [numChains])]
  simp only [List.getElem_ofFn]
  congr 1
  exact Fin.ext (by simpa using hzero.symm)

theorem FreshLayerOpening.exists_hit_probe_cached
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec}
    (hfresh : FreshLayerOpening f cache secretKey signingLog) :
    ∃ (probe : OtsValueProbe) (input : HashInput),
      probe.Hits f secretKey.parameter secretKey.otsSecret ∧
        ¬ SignedLayerAt f cache secretKey signingLog probe.lay probe.tree probe.leafIdx ∧
        probe.MatchesInput secretKey.parameter input ∧ cache input ≠ none := by
  obtain ⟨lay, tree, leafIdx, message, counter, values, path, hopening, hcached,
      hnotSigned⟩ := hfresh
  obtain ⟨codeword, hencode, hvalues, hpath⟩ := hopening
  let chainIdx : ChainIndex := ⟨0, by decide⟩
  let probe : OtsValueProbe :=
    ⟨lay, tree, leafIdx, chainIdx, codeword chainIdx, values chainIdx⟩
  have hhit : probe.Hits f secretKey.parameter secretKey.otsSecret := hvalues chainIdx
  by_cases hdigit : (codeword chainIdx).val < chainLength - 1
  · let step : ChainStep := ⟨(codeword chainIdx).val, hdigit⟩
    let input := tweakableHashInput secretKey.parameter
      (.chain lay tree leafIdx chainIdx step) (digestBytes (values chainIdx))
    have hquery : input ∈ queriedInputs f
        (otsLeaf secretKey.parameter lay tree leafIdx message counter values) := by
      simpa only [input, step, Nat.add_zero, walkValue, chainWalk,
        evalWithAnswerFn_pure] using
        otsLeaf_chain_query_mem f secretKey.parameter lay tree leafIdx message counter values
          codeword hencode chainIdx 0 (by omega) hdigit
    refine ⟨probe, input, hhit, hnotSigned, Or.inl ⟨step, rfl, rfl⟩, hcached input hquery⟩
  · have hdigitLast : (codeword chainIdx).val = chainLength - 1 := by
      have := (codeword chainIdx).isLt
      omega
    let endpoints := fun otherChain : ChainIndex =>
      walkValue f secretKey.parameter lay tree leafIdx otherChain
        (codeword otherChain).val (values otherChain)
        (chainLength - 1 - (codeword otherChain).val)
    let input := tweakableHashInput secretKey.parameter (.leaf lay tree leafIdx)
      (leafPayload endpoints)
    have hquery : input ∈ queriedInputs f
        (otsLeaf secretKey.parameter lay tree leafIdx message counter values) := by
      exact otsLeaf_leaf_query_mem f secretKey.parameter lay tree leafIdx message counter values
        codeword hencode
    have hslot : slotDigest 0 input = probe.candidate := by
      rw [show slotDigest 0 input = endpoints chainIdx from
        slotDigest_leafPayload_zero secretKey.parameter lay tree leafIdx endpoints chainIdx rfl]
      simp only [endpoints, probe, chainIdx, hdigitLast, Nat.sub_self, walkValue, chainWalk,
        evalWithAnswerFn_pure]
    refine ⟨probe, input, hhit, hnotSigned, Or.inr ⟨hdigitLast, rfl, ?_⟩,
      hcached input hquery⟩
    exact ⟨leafPayload endpoints, rfl, hslot⟩

theorem BackwardChainOpening.exists_hit_probe_cached
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec}
    (hbackward : BackwardChainOpening f cache secretKey signingLog) :
    ∃ (probe : OtsValueProbe) (signedDigit : Digit) (input : HashInput),
      probe.Hits f secretKey.parameter secretKey.otsSecret ∧
        probe.digit.val < signedDigit.val ∧
        probe.MatchesInput secretKey.parameter input ∧ cache input ≠ none := by
  obtain ⟨lay, tree, leafIdx, forgedMessage, forgedCounter, forgedValues, forgedPath,
      entry, signature, index, leaves, signedCodeword, forgedCodeword, hforgedOpening,
      hforgedRun, hentry, hresponse, hsignRun, hdigest, htree, hleaf, hmessage,
      hsignedOpening, hsignedCached, hsigned, hforged, chainIdx, hlt⟩ := hbackward
  obtain ⟨openingCodeword, hopeningEncode, hforgedValues, hpath⟩ := hforgedOpening
  have hcodeword : openingCodeword = forgedCodeword :=
    Option.some.inj (hopeningEncode.symm.trans hforged)
  let probe : OtsValueProbe :=
    ⟨lay, tree, leafIdx, chainIdx, forgedCodeword chainIdx, forgedValues chainIdx⟩
  have hhit : probe.Hits f secretKey.parameter secretKey.otsSecret := by
    simpa only [OtsValueProbe.Hits, OtsValueProbe.target, probe, hcodeword] using
      hforgedValues chainIdx
  have hdigit : (forgedCodeword chainIdx).val < chainLength - 1 := by
    have hsignedLt := (signedCodeword chainIdx).isLt
    omega
  have hdigitOpening : (openingCodeword chainIdx).val < chainLength - 1 := by
    rw [hcodeword]
    exact hdigit
  let step : ChainStep := ⟨(openingCodeword chainIdx).val, hdigitOpening⟩
  let input := tweakableHashInput secretKey.parameter
    (.chain lay tree leafIdx chainIdx step) (digestBytes (forgedValues chainIdx))
  have hquery : input ∈ queriedInputs f
      (otsLeaf secretKey.parameter lay tree leafIdx forgedMessage forgedCounter forgedValues) := by
    simpa only [input, step, Nat.add_zero, walkValue, chainWalk,
      evalWithAnswerFn_pure] using
      otsLeaf_chain_query_mem f secretKey.parameter lay tree leafIdx forgedMessage forgedCounter
        forgedValues openingCodeword hopeningEncode chainIdx 0 (by omega) hdigitOpening
  exact ⟨probe, signedCodeword chainIdx, input, hhit, hlt,
    Or.inl ⟨step, by simp [probe, step, hcodeword], rfl⟩, hforgedRun input hquery⟩

theorem ViewedFreshLayerOpeningWitness.exists_hit_probe
    {parameter : PublicParameter}
    {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {result : (Digest × Forgery × Bool) × ViewedFullTraceState}
    (hwitness : ViewedFreshLayerOpeningWitness parameter otsSecret ftsSecret result) :
    ∃ (f : QueryImpl HashSpec Id) (probe : OtsValueProbe),
      result.2.cache.AgreesWithFn f ∧ probe.Hits f parameter otsSecret := by
  obtain ⟨f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, hfresh⟩ := hwitness
  obtain ⟨probe, hhit, _⟩ := hfresh.toFreshLayerOpening.exists_hit_probe
  exact ⟨f, probe, hf, hhit⟩

theorem ViewedBackwardChainOpeningWitness.exists_hit_probe
    {parameter : PublicParameter}
    {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {result : (Digest × Forgery × Bool) × ViewedFullTraceState}
    (hwitness : ViewedBackwardChainOpeningWitness parameter otsSecret ftsSecret result) :
    ∃ (f : QueryImpl HashSpec Id) (probe : OtsValueProbe) (signedDigit : Digit),
      result.2.cache.AgreesWithFn f ∧ probe.Hits f parameter otsSecret
        ∧ probe.digit.val < signedDigit.val := by
  obtain ⟨f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, hbackward⟩ := hwitness
  obtain ⟨probe, signedDigit, hhit, hlt⟩ :=
    hbackward.toBackwardChainOpening.exists_hit_probe
  exact ⟨f, probe, signedDigit, hf, hhit, hlt⟩

theorem cleanFreshEvent_exists_hit_probe
    {parameter : PublicParameter}
    {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {result : (Digest × Forgery × Bool) × ViewedFullTraceState}
    (hevent : cleanFreshEvent parameter otsSecret ftsSecret result) :
    ∃ (f : QueryImpl HashSpec Id) (probe : OtsValueProbe),
      result.2.cache.AgreesWithFn f ∧ probe.Hits f parameter otsSecret :=
  ViewedFreshLayerOpeningWitness.exists_hit_probe hevent.2.toViewed

theorem cleanBackwardEvent_exists_hit_probe
    {parameter : PublicParameter}
    {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {result : (Digest × Forgery × Bool) × ViewedFullTraceState}
    (hevent : cleanBackwardEvent parameter otsSecret ftsSecret result) :
    ∃ (f : QueryImpl HashSpec Id) (probe : OtsValueProbe) (signedDigit : Digit),
      result.2.cache.AgreesWithFn f ∧ probe.Hits f parameter otsSecret
        ∧ probe.digit.val < signedDigit.val :=
  ViewedBackwardChainOpeningWitness.exists_hit_probe hevent.2.toViewed

end SphincsSecurity.Concrete
