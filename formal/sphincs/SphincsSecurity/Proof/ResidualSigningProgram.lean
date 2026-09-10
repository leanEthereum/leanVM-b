import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.ReferencePrefixSigning
import SphincsSecurity.Proof.ResidualSigningDisclosure

namespace SphincsSecurity.Concrete.ResidualByteFrontend

open _root_.OracleComp OracleSpec CanonicalProbeRouting ResidualByteAction
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

noncomputable def jointSigningProgram (inputs : Finset HashInput) (parameter : PublicParameter) (root : Digest)
    (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily) (message : Message) :
    OracleComp (World inputs) ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) := do
  let work ← simulateQ (checkedTranslate inputs (PublicEncodingMatch.Match parameter (knownEncodingMessage known) words selections))
    (publicSigningWork parameter root known words selections message)
  jointCompleteSigningWork work

def completeSigningResult (actual : Labels) (result : Option PublicSigningRecord × ExternalMemory) :
    Option ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) × ExternalMemory :=
  (result.1.map (completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf))), result.2)

theorem observedRun_jointSigningProgram_project (parameter : PublicParameter) (inputs : Finset HashInput)
    (words : OtsReferenceWords) (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels)
    (actions : inputs → Action inputs) (actual : Labels) (seed : inputs → HashOutput)
    (root : Digest) (selections : ReferenceFamily) (message : Message) (state : State inputs) :
    forget <$> AdaptiveResidualLabels.observedRun (environment parameter inputs words disclosed known actions) actual seed
      (jointSigningProgram inputs parameter root known words selections message) state =
    completeSigningResult actual <$> (accountSigningResult <$> (forget <$>
      checkedByteRun parameter inputs words disclosed known actions
        (PublicEncodingMatch.Match parameter (knownEncodingMessage known) words selections) actual seed
        (publicSigningWork parameter root known words selections message) state)) := by
  rw [jointSigningProgram, observedRun_bind, map_bind]
  simp only [checkedByteRun, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  apply congrArg ((AdaptiveResidualLabels.observedRun (environment parameter inputs words disclosed known actions) actual seed
    (simulateQ (checkedTranslate inputs (PublicEncodingMatch.Match parameter (knownEncodingMessage known) words selections))
      (publicSigningWork parameter root known words selections message)) state) >>= ·)
  funext result
  rcases result with ⟨work, after⟩
  cases work with
  | none =>
      simp only [Option.elim_none, pure_bind, forget, accountSigningResult, completeSigningResult, Option.map_none]
  | some work =>
      change forget <$> AdaptiveResidualLabels.observedRun (environment parameter inputs words disclosed known actions) actual seed
        (jointCompleteSigningWork work) after = _
      rw [observedRun_jointCompleteSigningWork_memory]
      rfl

theorem observedRun_jointSigningProgram_prefix (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (root : Digest) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (graph : CanonicalGraphLabels)
    (hagrees : PublicAgreement words disclosed known (CanonicalCoordinate.value otsSecret ftsSecret graph))
    (hreplies : ∀ position, ¬CanonicalCoordinate.Hidden words disclosed (.graph position) → publicReplies position = graph position)
    (seed : inputs → HashOutput) (message : Message)
    (hinputs : hashInputs (publicSigningWork parameter root known words selections message) ⊆ inputs)
    (state : State inputs) (hcovered : RowsCovered inputs state)
    (hmatches : CacheMatches (programmedHash parameter otsSecret ftsSecret graph
      (finiteHashAnswer ∅ inputs (canonicalPrefixResidual parameter inputs hencoding graph selections rows seed))) state.memory.cache)
    (hclean : CacheClean parameter words disclosed (CanonicalCoordinate.value otsSecret ftsSecret graph) state.memory.cache) :
    let actual := CanonicalCoordinate.value otsSecret ftsSecret graph
    let oracle := programmedHash parameter otsSecret ftsSecret graph
      (finiteHashAnswer ∅ inputs (canonicalPrefixResidual parameter inputs hencoding graph selections rows seed))
    forget <$> AdaptiveResidualLabels.observedRun
      (prefixEnvironment parameter inputs hencoding words disclosed known publicReplies selections rows) actual seed
      (jointSigningProgram inputs parameter root known words selections message) state =
      (fun record => (some (completePublicSigningRecord ftsSecret record), applyBoundary state.memory record.2)) <$>
        𝒟[publicSigningRecord parameter root oracle known words selections message] := by
  dsimp only
  rw [observedRun_jointSigningProgram_project]
  have h := prefixByteRun_eq_original parameter inputs hencoding words disclosed known publicReplies selections rows
    otsSecret ftsSecret graph hagrees hreplies seed (publicSigningWork parameter root known words selections message) hinputs state hcovered hmatches hclean
  rw [h, checkedPublicSigningWork_record]
  simp only [Functor.map_map, completeSigningResult, Option.map_some, CanonicalCoordinate.value]

theorem observedRun_jointSigningProgram_original (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (graph : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (publicReplies : CanonicalGraphLabels)
    (hagrees : PublicAgreement (referenceFamilyWords auxiliary.selections dummy) disclosed known
      (CanonicalCoordinate.value key.otsSecret key.ftsSecret graph))
    (hreplies : ∀ position, ¬CanonicalCoordinate.Hidden (referenceFamilyWords auxiliary.selections dummy) disclosed (.graph position) →
      publicReplies position = graph position)
    (message : Message)
    (hinputs : hashInputs (signWithView key message) ⊆ inputs)
    (state : State inputs) (hcovered : RowsCovered inputs state)
    (hmatches : CacheMatches (programmedHash key.parameter key.otsSecret key.ftsSecret graph
      (finiteHashAnswer ∅ inputs (canonicalPrefixResidual key.parameter inputs hencoding graph auxiliary.selections auxiliary.rows auxiliary.seed)))
      state.memory.cache)
    (hclean : CacheClean key.parameter (referenceFamilyWords auxiliary.selections dummy) disclosed
      (CanonicalCoordinate.value key.otsSecret key.ftsSecret graph) state.memory.cache) :
    let words := referenceFamilyWords auxiliary.selections dummy
    let actual := CanonicalCoordinate.value key.otsSecret key.ftsSecret graph
    let oracle := programmedHash key.parameter key.otsSecret key.ftsSecret graph
      (finiteHashAnswer ∅ inputs (canonicalPrefixResidual key.parameter inputs hencoding graph auxiliary.selections auxiliary.rows auxiliary.seed))
    forget <$> AdaptiveResidualLabels.observedRun
      (prefixEnvironment key.parameter inputs hencoding words disclosed known publicReplies auxiliary.selections auxiliary.rows) actual auxiliary.seed
      (jointSigningProgram inputs key.parameter key.root known words auxiliary.selections message) state =
    (fun record => (some record, applyBoundary state.memory record.2)) <$>
      𝒟[fixedBoundaryRun key.parameter oracle (signWithView key message)] := by
  dsimp only
  rw [observedRun_jointSigningProgram_prefix key.parameter inputs hencoding key.root _ disclosed known publicReplies
    auxiliary.selections auxiliary.rows key.otsSecret key.ftsSecret graph hagrees hreplies auxiliary.seed message
    ((hashInputs_publicSigningWork_subset_signWithView key known _ auxiliary.selections message).trans hinputs) state hcovered hmatches hclean]
  have hmessage (randomness : Randomness) := programmedPrefixResidual_outside key.parameter inputs hencoding _ disclosed known
    key.otsSecret key.ftsSecret graph hagrees auxiliary.selections auxiliary.rows auxiliary.seed _
    (decodePosition_message key.parameter (messageDigestPayload key.root message randomness))
  have hpublic := fixedBoundaryRun_publicDigestLoop_eq_of_message key.parameter key.root message _ _ hmessage digestAttemptLimit
  have hrecord := fixedBoundaryRun_signWithView_prefix_public key inputs hencoding graph auxiliary hauxiliary dummy disclosed known hagrees message
  have h := congrArg (fun computation =>
    (fun record => (some record, applyBoundary state.memory record.2)) <$> 𝒟[computation]) hrecord
  simp only [evalDist_map, Functor.map_map, completePublicSigningRecord_trace] at h
  rw [publicSigningRecord, hpublic]
  exact h.symm

theorem jointSigningProgram_posterior (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (root : Digest) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (message : Message) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty) :
    (UniformTableCompletion.complete state.candidates >>= fun labels => ResidualTableCompletion.completeRows state.rows >>= fun seed =>
      AdaptiveResidualLabels.retain labels seed <$> AdaptiveResidualLabels.observedRun
        (prefixEnvironment parameter inputs hencoding words disclosed known publicReplies selections rows) labels seed
        (jointSigningProgram inputs parameter root known words selections message) state) =
      (AdaptiveResidualLabels.lazyRun
        (prefixEnvironment parameter inputs hencoding words disclosed known publicReplies selections rows)
        (jointSigningProgram inputs parameter root known words selections message) state >>= AdaptiveResidualLabels.finish) :=
  AdaptiveResidualLabels.run_posterior _ _ state ha

theorem jointSigningProgram_erasure (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (root : Digest) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (message : Message) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty) :
    (UniformTableCompletion.complete state.candidates >>= fun labels => ResidualTableCompletion.completeRows state.rows >>= fun seed =>
      AdaptiveResidualLabels.observedRun
        (prefixEnvironment parameter inputs hencoding words disclosed known publicReplies selections rows) labels seed
        (jointSigningProgram inputs parameter root known words selections message) state) =
      AdaptiveResidualLabels.lazyRun
        (prefixEnvironment parameter inputs hencoding words disclosed known publicReplies selections rows)
        (jointSigningProgram inputs parameter root known words selections message) state :=
  AdaptiveResidualLabels.run_erasure _ _ state ha

end SphincsSecurity.Concrete.ResidualByteFrontend
