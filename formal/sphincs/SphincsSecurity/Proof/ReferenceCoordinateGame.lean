import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.CanonicalPublicPrior
import SphincsSecurity.Proof.ReferenceResidualSeeds

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec UniformTableCompletion
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

noncomputable def referenceCoordinateGame (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF (ReferenceFamily × (Bool × SigningBoundaryTrace)) := do
  let parameter ← 𝒟[sampleParameter]
  let auxiliary ← 𝒟[referenceAuxiliarySample inputs]
  let words := referenceFamilyWords auxiliary.selections dummy
  let high ← 𝒟[PMF.uniformOfFintype CanonicalGraphHighHalves]
  let exposedValues ← 𝒟[PMF.uniformOfFintype (InitialPublicLabels words)]
  let labels ← complete (initialAllowed words exposedValues)
  let ots := coordinateOtsSecrets labels
  let fts := coordinateFtsSecrets labels
  let graph := coordinateGraphLabels labels high
  let f := programmedHash parameter ots fts graph
    (finiteHashAnswer ∅ inputs (canonicalReferenceResidual parameter inputs (hencoding parameter) graph auxiliary.rows auxiliary.seed))
  let result ← 𝒟[referenceFamilyFrontierRest ⟨parameter, 0, ots, fts⟩ f graph auxiliary.selections dummy adversary]
  pure (auxiliary.selections, result)

theorem referenceResidualGame_eq_coordinates (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    referenceResidualGame inputs hencoding dummy adversary = referenceCoordinateGame inputs hencoding dummy adversary := by
  rw [referenceResidualGame_eq_auxiliary, referenceCoordinateGame]
  apply congrArg (𝒟[sampleParameter] >>= ·)
  funext parameter
  conv_lhs =>
    enter [2, ots]
    rw [RetainedObservation.bind_comm 𝒟[sampleFtsSecrets] 𝒟[referenceAuxiliarySample inputs]]
  rw [RetainedObservation.bind_comm 𝒟[sampleOtsSecrets] 𝒟[referenceAuxiliarySample inputs]]
  apply congrArg (𝒟[referenceAuxiliarySample inputs] >>= ·)
  funext auxiliary
  exact sampleSecretGraph_bind_public (referenceFamilyWords auxiliary.selections dummy)
    (fun _ _ ots fts graph => do
      let f := programmedHash parameter ots fts graph
        (finiteHashAnswer ∅ inputs (canonicalReferenceResidual parameter inputs (hencoding parameter) graph auxiliary.rows auxiliary.seed))
      let result ← 𝒟[referenceFamilyFrontierRest ⟨parameter, 0, ots, fts⟩ f graph auxiliary.selections dummy adversary]
      pure (auxiliary.selections, result))

theorem referenceCoordinateGame_erased (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    Prod.snd <$> referenceCoordinateGame inputs hencoding dummy adversary =
      𝒟[residualGraphOracleGame inputs dummy adversary] := by
  rw [← referenceResidualGame_eq_coordinates]
  exact referenceResidualGame_erased inputs hencoding dummy adversary

theorem forgeAdvantage_eq_referenceCoordinates (dummy : OtsReferenceWords) (adversary : Adversary) :
    forgeAdvantage scheme adversary =
      Pr[fun result => result.2.1 = true | referenceCoordinateGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] := by
  rw [← referenceResidualGame_eq_coordinates]
  exact forgeAdvantage_eq_referenceResidual dummy adversary

theorem referenceCoordinateGame_hashCalls_le (dummy : OtsReferenceWords) (adversary : Adversary)
    (q : Nat) (hbound : HasHashQueryBound scheme adversary q) (result : ReferenceFamily × (Bool × SigningBoundaryTrace))
    (hresult : result ∈ support (referenceCoordinateGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary)) :
    result.2.2.hashCalls ≤ q := by
  rw [← referenceResidualGame_eq_coordinates] at hresult
  exact referenceResidualGame_hashCalls_le dummy adversary q hbound result hresult

end SphincsSecurity.Concrete
