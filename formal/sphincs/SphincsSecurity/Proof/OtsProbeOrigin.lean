import SphincsSecurity.Proof.OtsProbeRetained

/-!
# Origins of published one-time chain values

Every chain value published by the masked signer belongs to one successful signing-log entry. This
module packages that semantic endpoint and proves the incompatibilities needed by the exact forged
opening events.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

def PublishedChainCoordinate (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec) (coordinate : Coordinate) : Prop :=
  ∃ (entry : (request : SignRequest) × SigningSpec.Range request) (signature : Signature)
      (index : Index) (leaves : DigestTree → FtsLeaf) (lay : Layer) (chainIdx : ChainIndex)
      (codeword : Encoding),
    entry ∈ signingLog
      ∧ entry.2 = some signature
      ∧ SuccessfulSignRun f cache secretKey entry.1 signature
      ∧ SuccessfulDigestRun f cache secretKey entry.1 signature.randomness index leaves
      ∧ evalWithAnswerFn f (encode secretKey.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) (evalWithAnswerFn f (layerMessage secretKey index lay))
        (signature.counter lay)) = some codeword
      ∧ coordinate = chainValueCoordinate lay (treeIndexAt index lay)
        (leafIndexAt index lay) chainIdx (codeword chainIdx)

def CoveredChainCoordinate (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec) (coordinate : Coordinate) : Prop :=
  ∃ (entry : (request : SignRequest) × SigningSpec.Range request) (signature : Signature)
      (index : Index) (leaves : DigestTree → FtsLeaf) (lay : Layer) (chainIdx : ChainIndex)
      (codeword : Encoding) (targetDigit : Digit),
    entry ∈ signingLog
      ∧ entry.2 = some signature
      ∧ SuccessfulSignRun f cache secretKey entry.1 signature
      ∧ SuccessfulDigestRun f cache secretKey entry.1 signature.randomness index leaves
      ∧ evalWithAnswerFn f (encode secretKey.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) (evalWithAnswerFn f (layerMessage secretKey index lay))
        (signature.counter lay)) = some codeword
      ∧ (codeword chainIdx).val ≤ targetDigit.val
      ∧ coordinate = chainValueCoordinate lay (treeIndexAt index lay)
        (leafIndexAt index lay) chainIdx targetDigit

theorem PublishedChainCoordinate.signedLayerAt
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {coordinate : Coordinate}
    (hpublished : PublishedChainCoordinate f cache secretKey signingLog coordinate) :
    ∃ lay tree leafIdx, SignedLayerAt f cache secretKey signingLog lay tree leafIdx := by
  obtain ⟨entry, signature, index, leaves, lay, chainIdx, codeword, hentry, hresponse,
    hrun, hdigest, hencode, hcoordinate⟩ := hpublished
  obtain ⟨hmessage, hopening⟩ := hrun.honest_layer_at_of_digest hdigest lay
  have hcached := hrun.signed_encode_cached_of_digest hdigest lay
  exact ⟨lay, treeIndexAt index lay, leafIndexAt index lay, entry, signature, index, leaves,
    hentry, hresponse, hrun, hdigest, rfl, rfl, hmessage, hcached, hopening⟩

theorem ForgedFreshLayerOpening.exists_uncovered_matching_probe
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index} {signature : Signature}
    (hfresh : ForgedFreshLayerOpening f cache secretKey signingLog index signature) :
    ∃ (probe : Probe) (input : HashInput),
      probe.Hits f secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
        ∧ probe.MatchesInput secretKey.parameter input
        ∧ cache input ≠ none
        ∧ ¬CoveredChainCoordinate f cache secretKey signingLog probe.coordinate := by
  obtain ⟨valueProbe, input, hhit, hnotSigned, hmatch, hcached⟩ :=
    hfresh.toFreshLayerOpening.exists_hit_probe_cached
  refine ⟨toProbe valueProbe, input, toProbe_hits hhit,
    toProbe_matchesInput secretKey.parameter valueProbe input hmatch, hcached, ?_⟩
  intro hcovered
  obtain ⟨entry, publishedSignature, publishedIndex, leaves, publishedLay, chainIdx,
    codeword, targetDigit, hentry, hresponse, hrun, hdigest, hencode, hle,
    hcoordinate⟩ := hcovered
  obtain ⟨hmessage, hopening⟩ := hrun.honest_layer_at_of_digest hdigest publishedLay
  have hcachedEncode := hrun.signed_encode_cached_of_digest hdigest publishedLay
  have hsigned : SignedLayerAt f cache secretKey signingLog publishedLay
      (treeIndexAt publishedIndex publishedLay) (leafIndexAt publishedIndex publishedLay) :=
    ⟨entry, publishedSignature, publishedIndex, leaves, hentry, hresponse, hrun, hdigest,
      rfl, rfl, hmessage, hcachedEncode, hopening⟩
  have hparts := chainValueCoordinate_injective
    (hcoordinate.symm.trans (toProbe_coordinate valueProbe))
  exact hnotSigned (hparts.1 ▸ hparts.2.1 ▸ hparts.2.2.1 ▸ hsigned)

theorem ForgedBackwardChainOpening.exists_uncovered_matching_probe
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {forgedIndex : Index}
    {forgedSignature : Signature}
    (hbackward : ForgedBackwardChainOpening f cache secretKey signingLog forgedIndex
      forgedSignature) :
    ∃ (probe : Probe) (input : HashInput),
      probe.Hits f secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
        ∧ probe.MatchesInput secretKey.parameter input
        ∧ cache input ≠ none
        ∧ ¬CoveredChainCoordinate f cache secretKey signingLog probe.coordinate := by
  obtain ⟨lay, forgedMessage, entry, signedSignature, signedIndex, leaves, signedCodeword,
    forgedCodeword, hforgedOpening, hforgedRun, hentry, hresponse, hsignRun, hdigest,
    htree, hleaf, hmessage, hsignedOpening, hsignedCached, hsigned, hforged,
    chainIdx, hlt⟩ := hbackward
  obtain ⟨openingCodeword, hopeningEncode, hforgedValues, hpath⟩ := hforgedOpening
  have hopeningCodeword : openingCodeword = forgedCodeword :=
    Option.some.inj (hopeningEncode.symm.trans hforged)
  let valueProbe : OtsValueProbe :=
    ⟨lay, treeIndexAt forgedIndex lay, leafIndexAt forgedIndex lay, chainIdx,
      forgedCodeword chainIdx, forgedSignature.chainValue lay chainIdx⟩
  have hhit : valueProbe.Hits f secretKey.parameter secretKey.otsSecret := by
    simpa only [OtsValueProbe.Hits, OtsValueProbe.target, valueProbe,
      hopeningCodeword] using hforgedValues chainIdx
  have hdigit : (forgedCodeword chainIdx).val < chainLength - 1 := by
    have hsignedLt := (signedCodeword chainIdx).isLt
    omega
  have hopeningDigit : (openingCodeword chainIdx).val < chainLength - 1 := by
    rw [hopeningCodeword]
    exact hdigit
  let step : ChainStep := ⟨(openingCodeword chainIdx).val, hopeningDigit⟩
  let input := tweakableHashInput secretKey.parameter
    (.chain lay (treeIndexAt forgedIndex lay) (leafIndexAt forgedIndex lay) chainIdx step)
    (digestBytes (forgedSignature.chainValue lay chainIdx))
  have hquery : input ∈ queriedInputs f
      (otsLeaf secretKey.parameter lay (treeIndexAt forgedIndex lay)
        (leafIndexAt forgedIndex lay) forgedMessage (forgedSignature.counter lay)
        (forgedSignature.chainValue lay)) := by
    simpa only [input, step, Nat.add_zero, walkValue, chainWalk,
      evalWithAnswerFn_pure] using
      otsLeaf_chain_query_mem f secretKey.parameter lay (treeIndexAt forgedIndex lay)
        (leafIndexAt forgedIndex lay) forgedMessage (forgedSignature.counter lay)
        (forgedSignature.chainValue lay) openingCodeword hopeningEncode chainIdx 0
        (by omega) hopeningDigit
  have hmatch : (toProbe valueProbe).MatchesInput secretKey.parameter input := by
    apply toProbe_matchesInput secretKey.parameter valueProbe input
    exact Or.inl ⟨step, by simp [valueProbe, step, hopeningCodeword], rfl⟩
  refine ⟨toProbe valueProbe, input, toProbe_hits hhit, hmatch, hforgedRun input hquery, ?_⟩
  intro hcovered
  obtain ⟨publishedEntry, publishedSignature, publishedIndex, publishedLeaves, publishedLay,
    publishedChain, publishedCodeword, targetDigit, hpublishedEntry, hpublishedResponse,
    hpublishedRun, hpublishedDigest, hpublishedEncode, hcoveredDigit, hcoordinate⟩ := hcovered
  have hparts := chainValueCoordinate_injective
    (hcoordinate.symm.trans (toProbe_coordinate valueProbe))
  dsimp only [valueProbe] at hparts
  obtain ⟨hlay, htreePublished, hleafPublished, hchainPublished, htargetDigit⟩ := hparts
  subst publishedLay
  have htreeSame : treeIndexAt publishedIndex lay = treeIndexAt signedIndex lay :=
    htreePublished.trans htree.symm
  have hleafSame : leafIndexAt publishedIndex lay = leafIndexAt signedIndex lay :=
    hleafPublished.trans hleaf.symm
  have hpartsSame := successfulSignRun_layer_ots_eq_of_position_eq hpublishedRun hsignRun
    hpublishedDigest hdigest lay htreeSame hleafSame
  have hlayerMessage := congrArg (evalWithAnswerFn f)
    (layerMessage_eq_of_position_eq secretKey publishedIndex signedIndex lay
      htreeSame hleafSame)
  have hpublishedEncode' := hpublishedEncode
  rw [htreePublished, hleafPublished, hlayerMessage, hpartsSame.1] at hpublishedEncode'
  have hcodeword : publishedCodeword = signedCodeword :=
    Option.some.inj (hpublishedEncode'.symm.trans hsigned)
  subst publishedChain
  rw [hcodeword] at hcoveredDigit
  have hdigitValue := congrArg Fin.val htargetDigit
  omega

end SphincsSecurity.Concrete.OtsProbeSimulation
