import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.ForgeryClassify

/-!
# One-time terminal events

A layer obstacle is either an honest opening at a position the transcript never used, an encoding
collision at a used position, or a codeword that moves backward on at least one used chain.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

def EncodingCollision (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec) : Prop :=
  ∃ (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (forgedMessage : Digest)
      (forgedCounter : Counter) (forgedValues : ChainIndex → Digest)
      (forgedPath : Nat → Digest)
      (entry : (request : SignRequest) × SigningSpec.Range request) (signature : Signature)
      (index : Index) (leaves : DigestTree → FtsLeaf),
    CachedRun cache f (otsLeaf secretKey.parameter lay tree leafIdx forgedMessage forgedCounter
        forgedValues)
      ∧ HonestLayerOpening f secretKey.parameter secretKey.otsSecret lay tree leafIdx
          forgedMessage forgedCounter forgedValues forgedPath
      ∧ entry ∈ signingLog
      ∧ entry.2 = some signature
      ∧ SuccessfulSignRun f cache secretKey entry.1 signature
      ∧ SuccessfulDigestRun f cache secretKey entry.1 signature.randomness index leaves
      ∧ treeIndexAt index lay = tree
      ∧ leafIndexAt index lay = leafIdx
      ∧ CachedRun cache f (layerMessage secretKey index lay)
      ∧ HonestLayerOpening f secretKey.parameter secretKey.otsSecret lay tree leafIdx
          (evalWithAnswerFn f (layerMessage secretKey index lay)) (signature.counter lay)
          (signature.chainValue lay) (signaturePath signature lay)
      ∧ cache (tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx)
        (digestBytes (evalWithAnswerFn f (layerMessage secretKey index lay)) ++
          counterBytes (signature.counter lay))) ≠ none
      ∧ EncodingHit f secretKey.parameter lay tree leafIdx
        (evalWithAnswerFn f (layerMessage secretKey index lay)) forgedMessage
        (signature.counter lay) forgedCounter

def SettledForgedFreshLayerOpening (f : QueryImpl HashSpec Id)
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (signingLog : QueryLog SigningSpec) (index : Index)
    (leaves : DigestTree → FtsLeaf) (signature : Signature) : Prop :=
  ∃ (lay : Layer) (message : Digest),
    LayerRootSettled cache secretKey lay (treeIndexAt index lay)
      ∧ VerifierLayerMessage f secretKey.parameter index leaves signature lay message
      ∧ HonestLayerOpening f secretKey.parameter secretKey.otsSecret lay
        (treeIndexAt index lay) (leafIndexAt index lay) message (signature.counter lay)
        (signature.chainValue lay) (signaturePath signature lay)
      ∧ CachedRun cache f (otsLeaf secretKey.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) message (signature.counter lay) (signature.chainValue lay))
      ∧ ¬SignedLayerAt f cache secretKey signingLog lay
        (treeIndexAt index lay) (leafIndexAt index lay)

def SettledForgedBackwardChainOpening (f : QueryImpl HashSpec Id)
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (signingLog : QueryLog SigningSpec) (forgedIndex : Index)
    (forgedLeaves : DigestTree → FtsLeaf) (forgedSignature : Signature) : Prop :=
  ∃ (lay : Layer) (forgedMessage : Digest)
      (entry : (request : SignRequest) × SigningSpec.Range request) (signature : Signature)
      (index : Index) (leaves : DigestTree → FtsLeaf)
      (signedCodeword forgedCodeword : Encoding),
    LayerRootSettled cache secretKey lay (treeIndexAt forgedIndex lay)
      ∧ VerifierLayerMessage f secretKey.parameter forgedIndex forgedLeaves forgedSignature lay
        forgedMessage
      ∧ HonestLayerOpening f secretKey.parameter secretKey.otsSecret lay
        (treeIndexAt forgedIndex lay) (leafIndexAt forgedIndex lay) forgedMessage
        (forgedSignature.counter lay) (forgedSignature.chainValue lay)
        (signaturePath forgedSignature lay)
      ∧ CachedRun cache f (otsLeaf secretKey.parameter lay (treeIndexAt forgedIndex lay)
        (leafIndexAt forgedIndex lay) forgedMessage (forgedSignature.counter lay)
        (forgedSignature.chainValue lay))
      ∧ entry ∈ signingLog
      ∧ entry.2 = some signature
      ∧ SuccessfulSignRun f cache secretKey entry.1 signature
      ∧ SuccessfulDigestRun f cache secretKey entry.1 signature.randomness index leaves
      ∧ treeIndexAt index lay = treeIndexAt forgedIndex lay
      ∧ leafIndexAt index lay = leafIndexAt forgedIndex lay
      ∧ CachedRun cache f (layerMessage secretKey index lay)
      ∧ HonestLayerOpening f secretKey.parameter secretKey.otsSecret lay
          (treeIndexAt forgedIndex lay) (leafIndexAt forgedIndex lay)
          (evalWithAnswerFn f (layerMessage secretKey index lay)) (signature.counter lay)
          (signature.chainValue lay) (signaturePath signature lay)
      ∧ cache (tweakableHashInput secretKey.parameter
        (.encoding lay (treeIndexAt forgedIndex lay) (leafIndexAt forgedIndex lay))
        (digestBytes (evalWithAnswerFn f (layerMessage secretKey index lay)) ++
          counterBytes (signature.counter lay))) ≠ none
      ∧ evalWithAnswerFn f (encode secretKey.parameter lay (treeIndexAt forgedIndex lay)
          (leafIndexAt forgedIndex lay) (evalWithAnswerFn f (layerMessage secretKey index lay))
          (signature.counter lay)) = some signedCodeword
      ∧ evalWithAnswerFn f (encode secretKey.parameter lay (treeIndexAt forgedIndex lay)
          (leafIndexAt forgedIndex lay) forgedMessage (forgedSignature.counter lay)) =
        some forgedCodeword
      ∧ ∃ chainIdx, (forgedCodeword chainIdx).val < (signedCodeword chainIdx).val

theorem settledForgedLayerObstacle_classify (f : QueryImpl HashSpec Id)
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (signingLog : QueryLog SigningSpec) (index : Index) (leaves : DigestTree → FtsLeaf)
    (signature : Signature)
    (hobstacle : SettledForgedLayerObstacle f cache secretKey signingLog index leaves signature) :
    SettledForgedFreshLayerOpening f cache secretKey signingLog index leaves signature
      ∨ EncodingCollision f cache secretKey signingLog
      ∨ SettledForgedBackwardChainOpening f cache secretKey signingLog index leaves
        signature := by
  obtain ⟨lay, message, hsettled, hverifierMessage, hopening, hcached,
      hfresh | hfailure⟩ := hobstacle
  · exact Or.inl ⟨lay, message, hsettled, hverifierMessage, hopening, hcached, hfresh⟩
  · obtain ⟨entry, signedSignature, signedIndex, signedLeaves, hentry, hresponse, hsignRun,
        hdigest, htree, hleaf, hmessage, hsignedOpening, hsignedCached,
        hencoding | hbackward⟩ := hfailure
    · exact Or.inr (Or.inl ⟨lay, treeIndexAt index lay, leafIndexAt index lay, message,
        signature.counter lay, signature.chainValue lay, signaturePath signature lay,
        entry, signedSignature, signedIndex, signedLeaves, hcached, hopening, hentry, hresponse,
        hsignRun, hdigest, htree, hleaf, hmessage, hsignedOpening, hsignedCached, hencoding⟩)
    · obtain ⟨signedCodeword, forgedCodeword, hsigned, hforged, hlt⟩ := hbackward
      exact Or.inr (Or.inr ⟨lay, message, entry, signedSignature, signedIndex, signedLeaves,
        signedCodeword, forgedCodeword, hsettled, hverifierMessage, hopening, hcached, hentry,
        hresponse, hsignRun, hdigest, htree, hleaf, hmessage, hsignedOpening, hsignedCached,
        hsigned, hforged, hlt⟩)

end SphincsSecurity.Concrete
