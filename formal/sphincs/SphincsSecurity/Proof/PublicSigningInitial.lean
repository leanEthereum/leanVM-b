import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.CanonicalPublicPrior
import SphincsSecurity.Proof.PublicSigningNative

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec CanonicalProbeRouting AdaptiveHiddenLabels UniformTableCompletion
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem initialKnown_root (words : OtsReferenceWords) (exposedValues : InitialPublicLabels words)
    (labels : Labels) (hlabels : complete (initialAllowed words exposedValues) labels ≠ 0)
    (high : CanonicalGraphHighHalves) :
    knownRoot (initialKnown words exposedValues) = canonicalGraphRoot (coordinateGraphLabels labels high) := by
  apply knownRoot_eq (coordinateOtsSecrets labels) (coordinateFtsSecrets labels)
    (coordinateGraphLabels labels high) words (fun _ _ _ => False)
  rw [coordinateGraphLabels_value]
  exact initialKnown_agrees words exposedValues labels hlabels

variable {AuxIndex Memory : Type} {auxSpec : OracleSpec AuxIndex}

noncomputable def initialSigningState (words : OtsReferenceWords) (exposedValues : InitialPublicLabels words)
    (memory : Memory) : ObservationState CanonicalCoordinate Memory :=
  ⟨initialAllowed words exposedValues, memory⟩

variable (environment : Environment auxSpec CanonicalCoordinate Memory) (memory : Memory)
    (parameter : PublicParameter) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) (exposedValues : InitialPublicLabels (referenceFamilyWords auxiliary.selections dummy))
    (high : CanonicalGraphHighHalves) (message : Message)

include hauxiliary in
theorem initialPublicSigning_original (labels : Labels)
    (hlabels : complete (initialAllowed (referenceFamilyWords auxiliary.selections dummy) exposedValues) labels ≠ 0) :
    let words := referenceFamilyWords auxiliary.selections dummy
    let known := initialKnown words exposedValues
    let key : SecretKey := ⟨parameter, knownRoot known, coordinateOtsSecrets labels, coordinateFtsSecrets labels⟩
    Prod.fst <$> nativePublicSigningRun environment labels (initialSigningState words exposedValues memory)
      parameter (knownRoot known)
      (finiteHashAnswer ∅ inputs (knownReferenceResidual parameter inputs hencoding known auxiliary.rows auxiliary.seed))
      known words auxiliary.selections message =
        some <$> 𝒟[fixedBoundaryRun parameter
          (programmedHash parameter key.otsSecret key.ftsSecret (coordinateGraphLabels labels high)
            (finiteHashAnswer ∅ inputs (canonicalReferenceResidual parameter inputs hencoding
              (coordinateGraphLabels labels high) auxiliary.rows auxiliary.seed)))
          (signWithView key message)] := by
  dsimp only
  have hagrees : PublicAgreement (referenceFamilyWords auxiliary.selections dummy) (fun _ _ _ => False)
      (initialKnown (referenceFamilyWords auxiliary.selections dummy) exposedValues)
      (CanonicalCoordinate.value (coordinateOtsSecrets labels) (coordinateFtsSecrets labels) (coordinateGraphLabels labels high)) := by
    rw [coordinateGraphLabels_value]
    exact initialKnown_agrees _ exposedValues labels hlabels
  have h := nativePublicSigningRun_original environment
    (initialSigningState (referenceFamilyWords auxiliary.selections dummy) exposedValues memory)
    ⟨parameter, knownRoot (initialKnown (referenceFamilyWords auxiliary.selections dummy) exposedValues),
      coordinateOtsSecrets labels, coordinateFtsSecrets labels⟩
    inputs hencoding (coordinateGraphLabels labels high) auxiliary hauxiliary dummy (fun _ _ _ => False)
    (initialKnown (referenceFamilyWords auxiliary.selections dummy) exposedValues) hagrees message
  simpa only [coordinateGraphLabels_value] using h

include hauxiliary in
theorem initialPublicSigning_erasure :
    let words := referenceFamilyWords auxiliary.selections dummy
    let known := initialKnown words exposedValues
    (complete (initialAllowed words exposedValues) >>= fun labels =>
      let key : SecretKey := ⟨parameter, knownRoot known, coordinateOtsSecrets labels, coordinateFtsSecrets labels⟩
      some <$> 𝒟[fixedBoundaryRun parameter
        (programmedHash parameter key.otsSecret key.ftsSecret (coordinateGraphLabels labels high)
          (finiteHashAnswer ∅ inputs (canonicalReferenceResidual parameter inputs hencoding
            (coordinateGraphLabels labels high) auxiliary.rows auxiliary.seed)))
        (signWithView key message)]) =
      Prod.fst <$> lazyPublicSigningRun environment (initialSigningState words exposedValues memory)
        parameter (knownRoot known)
        (finiteHashAnswer ∅ inputs (knownReferenceResidual parameter inputs hencoding known auxiliary.rows auxiliary.seed))
        known words auxiliary.selections message := by
  dsimp only
  rw [← publicSigningRun_erasure environment
    (initialSigningState (referenceFamilyWords auxiliary.selections dummy) exposedValues memory)
    (initialAllowed_nonempty _ exposedValues)]
  rw [map_bind]
  dsimp only [initialSigningState]
  apply evalDist_bind_congr (m := SPMF)
  intro labels hlabels
  exact (initialPublicSigning_original environment memory parameter inputs hencoding auxiliary hauxiliary
    dummy exposedValues high message labels hlabels).symm

end SphincsSecurity.Concrete
