import SphincsSecurity.Proof.FrontierInitialization
import SphincsSecurity.Proof.ReferenceEncodingGame

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] boundaryEval canonicalGraphGameInputs

noncomputable def causalFrontierAdversaryImpl (parameter : PublicParameter) (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) :
    QueryImpl (OracleWorld + SigningSpec) (WriterT SigningBoundaryTrace ProbComp)
  | .inl input => (fixedHashWorld external).withTrace (signingBoundaryTrace parameter) input
  | .inr message => WriterT.mk
      (frontierSigningRun parameter root (maskOtsPrefixes parameter words external) ftsSecret words frontier message)

theorem causalFrontierAdversaryImpl_eq (parameter : PublicParameter) (root : Digest)
    (f : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) :
    causalFrontierAdversaryImpl parameter root f ftsSecret words frontier =
      frontierAdversaryImpl parameter root f ftsSecret words frontier := by
  funext input
  cases input with
  | inl input => rfl
  | inr message =>
      change (WriterT.mk
        (frontierSigningRun parameter root (maskOtsPrefixes parameter words f) ftsSecret words frontier message) :
          WriterT SigningBoundaryTrace ProbComp (Option Signature)) =
        WriterT.mk (frontierSigningRun parameter root f ftsSecret words frontier message)
      rw [← frontierSigningRun_eq_of_agree parameter words f (maskOtsPrefixes parameter words f)
        (maskOtsPrefixes_agrees parameter words f)]

noncomputable def causalFrontierAdversaryRun {α : Type} (parameter : PublicParameter) (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ProbComp ((α × QueryLog SigningSpec) × SigningBoundaryTrace) :=
  ((simulateQ ((causalFrontierAdversaryImpl parameter root external ftsSecret words frontier).withTraceAppend signingLogFragment)
    computation).run).run

theorem causalFrontierAdversaryRun_eq {α : Type} (parameter : PublicParameter) (root : Digest)
    (f : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    causalFrontierAdversaryRun parameter root f ftsSecret words frontier computation =
      frontierAdversaryRun parameter root f ftsSecret words frontier computation := by
  rw [causalFrontierAdversaryRun, frontierAdversaryRun, causalFrontierAdversaryImpl_eq]

noncomputable def causalFrontierGameRest (parameter : PublicParameter) (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (adversary : Adversary) :
    ProbComp (Bool × SigningBoundaryTrace) := do
  let result ← causalFrontierAdversaryRun parameter root external ftsSecret words frontier
    (adversary.main ⟨root, parameter⟩)
  let checked := boundaryEval parameter external (verify ⟨root, parameter⟩ result.1.1.message result.1.1.signature)
  pure (decide (SigningTranscript.Valid result.1.2 ∧ ¬SigningTranscript.Contains result.1.2 result.1.1) && checked.1,
    result.2 * checked.2)

theorem causalFrontierGameRest_eq (parameter : PublicParameter) (root : Digest)
    (f : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (adversary : Adversary) :
    causalFrontierGameRest parameter root f ftsSecret words frontier adversary =
      frontierGameRest parameter root f ftsSecret words frontier adversary := by
  rw [causalFrontierGameRest, frontierGameRest, causalFrontierAdversaryRun_eq]

noncomputable def causalFrontierGame (parameter : PublicParameter) (external : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (adversary : Adversary) : ProbComp (Bool × SigningBoundaryTrace) :=
  (fun result => (result.1, (FreeMonoid.of none) ^ 1212415 * result.2)) <$>
    causalFrontierGameRest parameter (frontierRoot parameter (maskOtsPrefixes parameter words external) words frontier)
      external ftsSecret words frontier adversary

theorem causalFrontierGame_eq (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (adversary : Adversary) :
    causalFrontierGame parameter f ftsSecret words frontier adversary =
      frontierGame parameter f ftsSecret words frontier adversary := by
  rw [causalFrontierGame, frontierGame, causalFrontierGameRest_eq,
    ← frontierRoot_eq_of_agree parameter words f (maskOtsPrefixes parameter words f)
      (maskOtsPrefixes_agrees parameter words f)]

def endpointWords : OtsReferenceWords := fun _ _ _ _ => ⟨chainLength - 1, by decide⟩

theorem maskOtsPrefixes_endpoint_chain (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex) (step : ChainStep)
    (payload : HashInput) :
    maskOtsPrefixes parameter endpointWords f
      (tweakableHashInput parameter (.chain lay tree leaf chainIdx step) payload) = 0 := by
  apply maskOtsPrefixes_private
  rw [privateOtsPrefixInput_chain_iff]
  exact step.isLt

def canonicalGraphEndpoints (labels : CanonicalGraphLabels) : OtsFrontierValues :=
  fun lay tree leaf chainIdx => truncateHash (labels (.chain lay tree leaf chainIdx Position.lastChainStep))

theorem canonicalGraphFrontier_endpoints
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels) :
    canonicalGraphFrontier otsSecret labels endpointWords = canonicalGraphEndpoints labels := by
  funext lay tree leaf chainIdx
  rfl

noncomputable def causalGraphFrontierGameRest (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (labels : CanonicalGraphLabels)
    (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords) (adversary : Adversary) :
    ProbComp (Bool × SigningBoundaryTrace) := do
  let words := frontierReferenceWords parameter (maskOtsPrefixes parameter endpointWords f)
    ftsSecret endpointWords (canonicalGraphEndpoints labels) dummy
  causalFrontierGame parameter f ftsSecret words (canonicalGraphFrontier otsSecret labels words) adversary

theorem causalGraphFrontierGameRest_canonical (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords) (adversary : Adversary) :
    causalGraphFrontierGameRest parameter otsSecret ftsSecret
        (canonicalGraphLabels parameter otsSecret ftsSecret f) f dummy adversary =
      graphFrontierGameRest parameter otsSecret ftsSecret
        (canonicalGraphLabels parameter otsSecret ftsSecret f) f dummy adversary := by
  let labels := canonicalGraphLabels parameter otsSecret ftsSecret f
  let key : SecretKey := ⟨parameter, canonicalGraphRoot labels, otsSecret, ftsSecret⟩
  have hcut : IsSigningFrontier key f endpointWords (canonicalGraphEndpoints labels) := by
    rw [← canonicalGraphFrontier_endpoints otsSecret labels,
      canonicalGraphLabels_frontier parameter otsSecret ftsSecret f endpointWords key.root]
    exact isSigningFrontier_canonical key f endpointWords
  have hwords := canonicalReferenceWords_eq_masked_frontier key f endpointWords
    (canonicalGraphEndpoints labels) hcut dummy
  unfold causalGraphFrontierGameRest graphFrontierGameRest
  change causalFrontierGame parameter f ftsSecret
      (frontierReferenceWords parameter (maskOtsPrefixes parameter endpointWords f)
        ftsSecret endpointWords (canonicalGraphEndpoints labels) dummy)
      (canonicalGraphFrontier otsSecret labels
        (frontierReferenceWords parameter (maskOtsPrefixes parameter endpointWords f)
          ftsSecret endpointWords (canonicalGraphEndpoints labels) dummy)) adversary =
    frontierGame parameter f ftsSecret (canonicalReferenceWords key f dummy)
      (canonicalGraphFrontier otsSecret labels (canonicalReferenceWords key f dummy)) adversary
  rw [← hwords, causalFrontierGame_eq]

noncomputable def causalReferenceEncodingGame (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (position : EncodingPosition) (dummy : OtsReferenceWords) (adversary : Adversary) :
    SPMF (ReferenceSelection × (Bool × SigningBoundaryTrace)) := do
  let parameter ← 𝒟[sampleParameter]
  let otsSecret ← 𝒟[sampleOtsSecrets]
  let ftsSecret ← 𝒟[sampleFtsSecrets]
  let reference ← 𝒟[referenceOracleSample ⟨parameter, 0, otsSecret, ftsSecret⟩ inputs (hencoding parameter) position]
  let f := finiteHashAnswer ∅ inputs reference.2
  let result ← 𝒟[causalGraphFrontierGameRest parameter otsSecret ftsSecret
    (canonicalGraphLabels parameter otsSecret ftsSecret f) f dummy adversary]
  pure (reference.1, result)

theorem causalReferenceEncodingGame_eq (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (position : EncodingPosition) (dummy : OtsReferenceWords) (adversary : Adversary) :
    causalReferenceEncodingGame inputs hencoding position dummy adversary =
      referenceEncodingGame inputs hencoding position dummy adversary := by
  simp only [causalReferenceEncodingGame, referenceEncodingGame, causalGraphFrontierGameRest_canonical]

theorem forgeAdvantage_eq_causalReferenceEncoding (position : EncodingPosition)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    forgeAdvantage scheme adversary =
      Pr[fun result => result.2.1 = true |
        causalReferenceEncodingGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) position dummy adversary] := by
  rw [causalReferenceEncodingGame_eq]
  exact forgeAdvantage_eq_referenceEncoding position dummy adversary

theorem causalReferenceEncodingGame_hashCalls_le (position : EncodingPosition)
    (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (result : ReferenceSelection × (Bool × SigningBoundaryTrace))
    (hresult : result ∈ support (causalReferenceEncodingGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) position dummy adversary)) :
    result.2.2.hashCalls ≤ q := by
  rw [causalReferenceEncodingGame_eq] at hresult
  exact referenceEncodingGame_hashCalls_le position dummy adversary q hbound result hresult

end SphincsSecurity.Concrete
