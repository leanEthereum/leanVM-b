import SphincsSecurity.Proof.ReferenceCoordinateGame
import SphincsSecurity.Proof.AdaptiveResidualErasure

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec UniformTableCompletion ResidualTableCompletion
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

structure ReferenceEncodingAuxiliary where
  selections : ReferenceFamily
  rows : CanonicalEncodingRows

noncomputable def referenceEncodingAuxiliarySample : PMF ReferenceEncodingAuxiliary :=
  (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).bind (fun selections =>
    (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit decodeEncodingOutput_invalid_nonempty selections).map
      (fun rows => ⟨selections, Function.uncurry rows⟩))

theorem referenceEncodingAuxiliarySample_select (auxiliary : ReferenceEncodingAuxiliary)
    (hauxiliary : auxiliary ∈ referenceEncodingAuxiliarySample.support) (position : EncodingPosition) :
    FirstSuccessTable.select decodeEncodingOutput (fun counter => auxiliary.rows (position, counter)) =
      auxiliary.selections position := by
  rw [referenceEncodingAuxiliarySample, PMF.mem_support_bind_iff] at hauxiliary
  obtain ⟨selections, hselections, hauxiliary⟩ := hauxiliary
  rw [PMF.mem_support_map_iff] at hauxiliary
  obtain ⟨rows, hrows, rfl⟩ := hauxiliary
  have hselected : FirstSuccessFamily.select decodeEncodingOutput encodingAttemptLimit rows = selections := by
    by_contra hne
    have hmass := FirstSuccessFamily.selected_mul_afterSelect decodeEncodingOutput encodingAttemptLimit
      decodeEncodingOutput_invalid_nonempty selections rows
    rw [if_neg hne] at hmass
    exact mul_ne_zero ((PMF.mem_support_iff _ _).mp hselections) ((PMF.mem_support_iff _ _).mp hrows) hmass
  exact congrFun hselected position

theorem referenceAuxiliarySample_bind_seed {Result : Type} (inputs : Finset HashInput)
    (next : ReferenceAuxiliary inputs → SPMF Result) :
    (𝒟[referenceAuxiliarySample inputs] >>= next) =
      (𝒟[referenceEncodingAuxiliarySample] >>= fun encoding =>
        completeRows (fun _ : inputs => none) >>= fun seed => next ⟨encoding.selections, encoding.rows, seed⟩) := by
  rw [completeRows_empty]
  simp only [referenceAuxiliarySample, referenceEncodingAuxiliarySample,
    ← PMF.monad_bind_eq_bind, ← PMF.monad_map_eq_map, evalDist_bind,
    map_eq_bind_pure_comp, Function.comp_def, evalDist_pure, bind_assoc, pure_bind]

noncomputable def referenceJointPriorGame (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF (ReferenceFamily × (Bool × SigningBoundaryTrace)) := do
  let parameter ← 𝒟[sampleParameter]
  let encoding ← 𝒟[referenceEncodingAuxiliarySample]
  let words := referenceFamilyWords encoding.selections dummy
  let high ← 𝒟[PMF.uniformOfFintype CanonicalGraphHighHalves]
  let exposedValues ← 𝒟[PMF.uniformOfFintype (InitialPublicLabels words)]
  let labels ← complete (initialAllowed words exposedValues)
  let seed ← completeRows (fun _ : inputs => none)
  let ots := coordinateOtsSecrets labels
  let fts := coordinateFtsSecrets labels
  let graph := coordinateGraphLabels labels high
  let f := programmedHash parameter ots fts graph
    (finiteHashAnswer ∅ inputs (canonicalReferenceResidual parameter inputs (hencoding parameter) graph encoding.rows seed))
  let result ← 𝒟[referenceFamilyFrontierRest ⟨parameter, 0, ots, fts⟩ f graph encoding.selections dummy adversary]
  pure (encoding.selections, result)

theorem referenceCoordinateGame_eq_jointPrior (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    referenceCoordinateGame inputs hencoding dummy adversary = referenceJointPriorGame inputs hencoding dummy adversary := by
  rw [referenceCoordinateGame, referenceJointPriorGame]
  apply congrArg (𝒟[sampleParameter] >>= ·)
  funext parameter
  rw [referenceAuxiliarySample_bind_seed]
  apply congrArg (𝒟[referenceEncodingAuxiliarySample] >>= ·)
  funext encoding
  dsimp only
  rw [RetainedObservation.bind_comm (completeRows (fun _ : inputs => none))]
  apply congrArg (𝒟[PMF.uniformOfFintype CanonicalGraphHighHalves] >>= ·)
  funext high
  rw [RetainedObservation.bind_comm (completeRows (fun _ : inputs => none))
    𝒟[PMF.uniformOfFintype (InitialPublicLabels (referenceFamilyWords encoding.selections dummy))]]
  apply congrArg (𝒟[PMF.uniformOfFintype (InitialPublicLabels (referenceFamilyWords encoding.selections dummy))] >>= ·)
  funext exposedValues
  rw [RetainedObservation.bind_comm (completeRows (fun _ : inputs => none))
    (complete (initialAllowed (referenceFamilyWords encoding.selections dummy) exposedValues))]

theorem forgeAdvantage_eq_referenceJointPrior (dummy : OtsReferenceWords) (adversary : Adversary) :
    forgeAdvantage scheme adversary =
      Pr[fun result => result.2.1 = true | referenceJointPriorGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] := by
  rw [← referenceCoordinateGame_eq_jointPrior]
  exact forgeAdvantage_eq_referenceCoordinates dummy adversary

theorem referenceJointPriorGame_hashCalls_le (dummy : OtsReferenceWords) (adversary : Adversary)
    (q : Nat) (hbound : HasHashQueryBound scheme adversary q) (result : ReferenceFamily × (Bool × SigningBoundaryTrace))
    (hresult : result ∈ support (referenceJointPriorGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary)) :
    result.2.2.hashCalls ≤ q := by
  rw [← referenceCoordinateGame_eq_jointPrior] at hresult
  exact referenceCoordinateGame_hashCalls_le dummy adversary q hbound result hresult

theorem referenceJointPrior_posterior {AuxIndex Memory Result : Type} {auxSpec : OracleSpec AuxIndex}
    (inputs : Finset HashInput)
    (environment : AdaptiveResidualLabels.Environment auxSpec CanonicalCoordinate inputs Memory)
    (words : OtsReferenceWords) (exposedValues : InitialPublicLabels words) (memory : Memory)
    (computation : OracleComp (AdaptiveResidualLabels.World auxSpec CanonicalCoordinate inputs) Result) :
    let state : AdaptiveResidualLabels.State CanonicalCoordinate inputs Memory :=
      ⟨initialAllowed words exposedValues, fun _ => none, memory⟩
    (complete state.candidates >>= fun labels => completeRows state.rows >>= fun table =>
      AdaptiveResidualLabels.retain labels table <$>
        AdaptiveResidualLabels.observedRun environment labels table computation state) =
      (AdaptiveResidualLabels.lazyRun environment computation state >>= AdaptiveResidualLabels.finish) := by
  exact AdaptiveResidualLabels.run_posterior environment computation _ (initialAllowed_nonempty words exposedValues)

theorem referenceJointPrior_erasure {AuxIndex Memory Result : Type} {auxSpec : OracleSpec AuxIndex}
    (inputs : Finset HashInput)
    (environment : AdaptiveResidualLabels.Environment auxSpec CanonicalCoordinate inputs Memory)
    (words : OtsReferenceWords) (exposedValues : InitialPublicLabels words) (memory : Memory)
    (computation : OracleComp (AdaptiveResidualLabels.World auxSpec CanonicalCoordinate inputs) Result) :
    let state : AdaptiveResidualLabels.State CanonicalCoordinate inputs Memory :=
      ⟨initialAllowed words exposedValues, fun _ => none, memory⟩
    (complete state.candidates >>= fun labels => completeRows state.rows >>= fun table =>
      AdaptiveResidualLabels.observedRun environment labels table computation state) =
      AdaptiveResidualLabels.lazyRun environment computation state := by
  exact AdaptiveResidualLabels.run_erasure environment computation _ (initialAllowed_nonempty words exposedValues)

end SphincsSecurity.Concrete
