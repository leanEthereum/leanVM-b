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

theorem ViewedFreshLayerOpeningWitness.exists_hit_probe
    {parameter : PublicParameter}
    {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {result : (Digest × Forgery × Bool) × ViewedFullTraceState}
    (hwitness : ViewedFreshLayerOpeningWitness parameter otsSecret ftsSecret result) :
    ∃ (f : QueryImpl HashSpec Id) (probe : OtsValueProbe),
      result.2.cache.AgreesWithFn f ∧ probe.Hits f parameter otsSecret := by
  obtain ⟨f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, hfresh⟩ := hwitness
  obtain ⟨probe, hhit, _⟩ := hfresh.exists_hit_probe
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
  obtain ⟨probe, signedDigit, hhit, hlt⟩ := hbackward.exists_hit_probe
  exact ⟨f, probe, signedDigit, hf, hhit, hlt⟩

theorem cleanFreshEvent_exists_hit_probe
    {parameter : PublicParameter}
    {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {result : (Digest × Forgery × Bool) × ViewedFullTraceState}
    (hevent : cleanFreshEvent parameter otsSecret ftsSecret result) :
    ∃ (f : QueryImpl HashSpec Id) (probe : OtsValueProbe),
      result.2.cache.AgreesWithFn f ∧ probe.Hits f parameter otsSecret :=
  hevent.2.exists_hit_probe

theorem cleanBackwardEvent_exists_hit_probe
    {parameter : PublicParameter}
    {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {result : (Digest × Forgery × Bool) × ViewedFullTraceState}
    (hevent : cleanBackwardEvent parameter otsSecret ftsSecret result) :
    ∃ (f : QueryImpl HashSpec Id) (probe : OtsValueProbe) (signedDigit : Digit),
      result.2.cache.AgreesWithFn f ∧ probe.Hits f parameter otsSecret
        ∧ probe.digit.val < signedDigit.val :=
  hevent.2.exists_hit_probe

end SphincsSecurity.Concrete
