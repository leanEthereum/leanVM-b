import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.PublicSigningDisclosure
import SphincsSecurity.Proof.ReferenceAuxiliarySigning

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec CanonicalProbeRouting AdaptiveHiddenLabels
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition

variable {AuxIndex Memory : Type} {auxSpec : OracleSpec AuxIndex}

noncomputable def nativePublicSigningRun (environment : Environment auxSpec CanonicalCoordinate Memory)
    (labels : Labels) (state : ObservationState CanonicalCoordinate Memory)
    (parameter : PublicParameter) (root : Digest) (outside : QueryImpl HashSpec Id)
    (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily) (message : Message) :
    SPMF (Option ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) × ObservationState CanonicalCoordinate Memory) :=
  𝒟[publicSigningRecord parameter root outside known words selections message] >>= fun record =>
    observedRun environment labels (nativeCompleteSigningRecord record) state

theorem nativePublicSigningRun_eq (environment : Environment auxSpec CanonicalCoordinate Memory)
    (labels : Labels) (state : ObservationState CanonicalCoordinate Memory)
    (parameter : PublicParameter) (root : Digest) (outside : QueryImpl HashSpec Id)
    (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily) (message : Message) :
    nativePublicSigningRun environment labels state parameter root outside known words selections message =
      (𝒟[publicSigningRecord parameter root outside known words selections message] >>= fun record =>
        pure (some (completePublicSigningRecord (fun index tree leaf => labels (.ftsStart index tree leaf)) record),
          completedSigningState environment labels record state)) := by
  simp only [nativePublicSigningRun, observedRun_nativeCompleteSigningRecord]

theorem nativePublicSigningRun_erasure (environment : Environment auxSpec CanonicalCoordinate Memory)
    (labels : Labels) (state : ObservationState CanonicalCoordinate Memory)
    (parameter : PublicParameter) (root : Digest) (outside : QueryImpl HashSpec Id)
    (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily) (message : Message) :
    Prod.fst <$> nativePublicSigningRun environment labels state parameter root outside known words selections message =
      𝒟[(some ∘ completePublicSigningRecord (fun index tree leaf => labels (.ftsStart index tree leaf))) <$>
        publicSigningRecord parameter root outside known words selections message] := by
  simp only [nativePublicSigningRun_eq, map_eq_bind_pure_comp, evalDist_bind, evalDist_pure,
    bind_assoc, pure_bind, Function.comp_def]

theorem nativePublicSigningRun_original (environment : Environment auxSpec CanonicalCoordinate Memory)
    (state : ObservationState CanonicalCoordinate Memory) (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels)
    (hagrees : PublicAgreement (referenceFamilyWords auxiliary.selections dummy) disclosed known
      (CanonicalCoordinate.value key.otsSecret key.ftsSecret labels)) (message : Message) :
    Prod.fst <$> nativePublicSigningRun environment (CanonicalCoordinate.value key.otsSecret key.ftsSecret labels) state
        key.parameter key.root
        (finiteHashAnswer ∅ inputs (knownReferenceResidual key.parameter inputs hencoding known auxiliary.rows auxiliary.seed))
        known (referenceFamilyWords auxiliary.selections dummy) auxiliary.selections message =
      some <$> 𝒟[fixedBoundaryRun key.parameter
        (programmedHash key.parameter key.otsSecret key.ftsSecret labels
          (finiteHashAnswer ∅ inputs (canonicalReferenceResidual key.parameter inputs hencoding labels auxiliary.rows auxiliary.seed)))
        (signWithView key message)] := by
  rw [nativePublicSigningRun_erasure,
    fixedBoundaryRun_signWithView_auxiliary_public key inputs hencoding labels auxiliary hauxiliary dummy disclosed known hagrees message]
  simp only [evalDist_map, LawfulFunctor.comp_map, CanonicalCoordinate.value]

noncomputable def lazyPublicSigningRun (environment : Environment auxSpec CanonicalCoordinate Memory)
    (state : ObservationState CanonicalCoordinate Memory)
    (parameter : PublicParameter) (root : Digest) (outside : QueryImpl HashSpec Id)
    (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily) (message : Message) :
    SPMF (Option ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) × ObservationState CanonicalCoordinate Memory) :=
  𝒟[publicSigningRecord parameter root outside known words selections message] >>= fun record =>
    lazyRun environment (nativeCompleteSigningRecord record) state

theorem publicSigningRun_posterior (environment : Environment auxSpec CanonicalCoordinate Memory)
    (state : ObservationState CanonicalCoordinate Memory) (ha : ∀ coordinate, (state.allowed coordinate).Nonempty)
    (parameter : PublicParameter) (root : Digest) (outside : QueryImpl HashSpec Id)
    (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily) (message : Message) :
    (UniformTableCompletion.complete state.allowed >>= fun labels =>
      retain labels <$> nativePublicSigningRun environment labels state parameter root outside known words selections message) =
        (lazyPublicSigningRun environment state parameter root outside known words selections message >>= AdaptiveHiddenLabels.finish) := by
  simp only [nativePublicSigningRun, lazyPublicSigningRun, map_bind, bind_assoc]
  rw [RetainedObservation.bind_comm]
  apply congrArg (𝒟[publicSigningRecord parameter root outside known words selections message] >>= ·)
  funext record
  exact run_posterior environment (nativeCompleteSigningRecord record) state ha

theorem publicSigningRun_erasure (environment : Environment auxSpec CanonicalCoordinate Memory)
    (state : ObservationState CanonicalCoordinate Memory) (ha : ∀ coordinate, (state.allowed coordinate).Nonempty)
    (parameter : PublicParameter) (root : Digest) (outside : QueryImpl HashSpec Id)
    (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily) (message : Message) :
    (UniformTableCompletion.complete state.allowed >>= fun labels =>
      nativePublicSigningRun environment labels state parameter root outside known words selections message) =
        lazyPublicSigningRun environment state parameter root outside known words selections message := by
  simp only [nativePublicSigningRun, lazyPublicSigningRun]
  rw [RetainedObservation.bind_comm]
  apply congrArg (𝒟[publicSigningRecord parameter root outside known words selections message] >>= ·)
  funext record
  exact run_erasure environment (nativeCompleteSigningRecord record) state ha

end SphincsSecurity.Concrete
