import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.RetainedResidualProgram

namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs
set_option backward.isDefEq.respectTransparency false

def forget {Result : Type} {inputs : Finset HashInput} (result : Option Result × State inputs) :
    Option Result × ExternalMemory := (result.1, result.2.memory.external)

theorem observedRun_externalProgram_project {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (actual : Labels) (seed : inputs → HashOutput) (computation : OracleComp OracleWorld Result) (state : State inputs) :
    projectResult <$> observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
      (externalProgram inputs parameter words selections computation) state =
      ResidualByteFrontend.prefixByteRun parameter inputs hencoding words state.memory.routing.disclosed state.memory.routing.known
        publicReplies selections rows actual seed computation (project state) := by
  rw [externalProgram, observedRun_routing_bind, observedRun_embed]
  rfl

theorem observedRun_externalProgram_original {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (graph : CanonicalGraphLabels)
    (seed : inputs → HashOutput) (computation : OracleComp OracleWorld Result)
    (hinputs : hashInputs computation ⊆ inputs) (state : State inputs)
    (hagrees : PublicAgreement words state.memory.routing.disclosed state.memory.routing.known
      (CanonicalCoordinate.value otsSecret ftsSecret graph))
    (hreplies : ∀ position, ¬CanonicalCoordinate.Hidden words state.memory.routing.disclosed (.graph position) → publicReplies position = graph position)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hmatches : ResidualByteFrontend.CacheMatches (programmedHash parameter otsSecret ftsSecret graph
      (finiteHashAnswer ∅ inputs (canonicalPrefixResidual parameter inputs hencoding graph selections rows seed))) state.memory.external.cache)
    (hclean : CacheClean parameter words state.memory.routing.disclosed (CanonicalCoordinate.value otsSecret ftsSecret graph) state.memory.external.cache) :
    let actual := CanonicalCoordinate.value otsSecret ftsSecret graph
    let oracle := programmedHash parameter otsSecret ftsSecret graph
      (finiteHashAnswer ∅ inputs (canonicalPrefixResidual parameter inputs hencoding graph selections rows seed))
    forget <$> observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
      (externalProgram inputs parameter words selections computation) state =
      externalRun (fun input memory => pure (ResidualByteFrontend.checkedResult
        (PublicEncodingMatch.Match parameter (canonicalGraphMessage graph) words selections) input
        (ResidualByteFrontend.fixedStep parameter words state.memory.routing.disclosed state.memory.routing.known actual oracle input memory)))
        computation state.memory.external := by
  dsimp only
  have h := congrArg (ResidualByteFrontend.forget <$> ·)
    (observedRun_externalProgram_project parameter inputs hencoding words publicReplies selections rows
      (CanonicalCoordinate.value otsSecret ftsSecret graph) seed computation state)
  simp only [Functor.map_map] at h
  exact h.trans (ResidualByteFrontend.prefixByteRun_eq_original parameter inputs hencoding words state.memory.routing.disclosed
    state.memory.routing.known publicReplies selections rows otsSecret ftsSecret graph hagrees hreplies seed computation hinputs
    (project state) hcovered hmatches hclean)

theorem observedRun_signingProgram_original (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (graph : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (message : Message)
    (hinputs : hashInputs (signWithView key message) ⊆ inputs) (state : State inputs)
    (hagrees : PublicAgreement (referenceFamilyWords auxiliary.selections dummy) state.memory.routing.disclosed state.memory.routing.known
      (CanonicalCoordinate.value key.otsSecret key.ftsSecret graph))
    (hreplies : ∀ position, ¬CanonicalCoordinate.Hidden (referenceFamilyWords auxiliary.selections dummy) state.memory.routing.disclosed (.graph position) →
      publicReplies position = graph position)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hmatches : ResidualByteFrontend.CacheMatches (programmedHash key.parameter key.otsSecret key.ftsSecret graph
      (finiteHashAnswer ∅ inputs (canonicalPrefixResidual key.parameter inputs hencoding graph auxiliary.selections auxiliary.rows auxiliary.seed)))
      state.memory.external.cache)
    (hclean : CacheClean key.parameter (referenceFamilyWords auxiliary.selections dummy) state.memory.routing.disclosed
      (CanonicalCoordinate.value key.otsSecret key.ftsSecret graph) state.memory.external.cache) :
    let words := referenceFamilyWords auxiliary.selections dummy
    let actual := CanonicalCoordinate.value key.otsSecret key.ftsSecret graph
    let oracle := programmedHash key.parameter key.otsSecret key.ftsSecret graph
      (finiteHashAnswer ∅ inputs (canonicalPrefixResidual key.parameter inputs hencoding graph auxiliary.selections auxiliary.rows auxiliary.seed))
    forget <$> observedRun (environment key.parameter inputs hencoding words publicReplies auxiliary.selections auxiliary.rows) actual auxiliary.seed
      (signingProgram inputs key.parameter key.root words auxiliary.selections message) state =
      (fun record => (some record.1.1, ResidualByteFrontend.applyBoundary state.memory.external record.2)) <$>
        𝒟[fixedBoundaryRun key.parameter oracle (signWithView key message)] := by
  dsimp only
  have hproject := congrArg (ResidualByteFrontend.forget <$> ·)
    (observedRun_signingProgram_project key.parameter inputs hencoding (referenceFamilyWords auxiliary.selections dummy)
      publicReplies auxiliary.selections auxiliary.rows (CanonicalCoordinate.value key.otsSecret key.ftsSecret graph)
      auxiliary.seed key.root message state)
  have horiginal := congrArg ((fun result : Option SigningRecord × ExternalMemory =>
      (result.1.map (fun record => record.1.1), result.2)) <$> ·)
    (ResidualByteFrontend.observedRun_jointSigningProgram_original key inputs hencoding graph auxiliary hauxiliary dummy
      state.memory.routing.disclosed state.memory.routing.known publicReplies hagrees hreplies message hinputs
      (project state) hcovered hmatches hclean)
  simp only [Functor.map_map, ResidualByteFrontend.forget, projectResult, project] at hproject
  simp only [Functor.map_map, ResidualByteFrontend.forget, Option.map_some, project] at horiginal
  exact hproject.trans horiginal

end SphincsSecurity.Concrete.RetainedResidual
