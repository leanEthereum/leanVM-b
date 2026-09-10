import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.CheckedByteExecution
import SphincsSecurity.Proof.PrefixByteAction
import SphincsSecurity.Proof.PublicEncodingMatch

namespace SphincsSecurity.Concrete.ResidualByteFrontend

open _root_.OracleComp OracleSpec CanonicalProbeRouting HiddenLabelObservation ResidualByteAction
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev prefixEnvironment (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows) :=
  environment parameter inputs words disclosed known
    (freshPrefix parameter inputs hencoding words disclosed known publicReplies selections rows)

noncomputable abbrev prefixByteRun {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (actual : Labels) (seed : inputs → HashOutput)
    (computation : OracleComp OracleWorld Result) (state : State inputs) :=
  checkedByteRun parameter inputs words disclosed known
    (freshPrefix parameter inputs hencoding words disclosed known publicReplies selections rows)
    (PublicEncodingMatch.Match parameter (knownEncodingMessage known) words selections) actual seed computation state

theorem prefixByteRun_eq_original {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (graph : CanonicalGraphLabels)
    (hagrees : PublicAgreement words disclosed known (CanonicalCoordinate.value otsSecret ftsSecret graph))
    (hreplies : ∀ position, ¬CanonicalCoordinate.Hidden words disclosed (.graph position) → publicReplies position = graph position)
    (seed : inputs → HashOutput) (computation : OracleComp OracleWorld Result) (hinputs : hashInputs computation ⊆ inputs)
    (state : State inputs) (hcovered : RowsCovered inputs state)
    (hmatches : CacheMatches (programmedHash parameter otsSecret ftsSecret graph
      (finiteHashAnswer ∅ inputs (canonicalPrefixResidual parameter inputs hencoding graph selections rows seed))) state.memory.cache)
    (hclean : CacheClean parameter words disclosed (CanonicalCoordinate.value otsSecret ftsSecret graph) state.memory.cache) :
    let actual := CanonicalCoordinate.value otsSecret ftsSecret graph
    let oracle := programmedHash parameter otsSecret ftsSecret graph
      (finiteHashAnswer ∅ inputs (canonicalPrefixResidual parameter inputs hencoding graph selections rows seed))
    forget <$> prefixByteRun parameter inputs hencoding words disclosed known publicReplies selections rows actual seed computation state =
      externalRun (fun input memory => pure (checkedResult
        (PublicEncodingMatch.Match parameter (canonicalGraphMessage graph) words selections) input
        (fixedStep parameter words disclosed known actual oracle input memory))) computation state.memory := by
  dsimp only
  rw [← PublicEncodingMatch.known_eq_original parameter words disclosed known otsSecret ftsSecret graph hagrees selections]
  apply checkedByteRun_eq_fixed parameter inputs words disclosed known
    (freshPrefix parameter inputs hencoding words disclosed known publicReplies selections rows)
    _ _ seed _ (freshPrefix_local parameter inputs hencoding words disclosed known publicReplies selections rows)
    _ computation hinputs state hcovered hmatches hclean
  intro input
  exact freshPrefix_eq_original parameter inputs hencoding words disclosed known otsSecret ftsSecret graph publicReplies
    hagrees hreplies selections rows seed input

end SphincsSecurity.Concrete.ResidualByteFrontend
