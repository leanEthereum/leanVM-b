import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.CanonicalGraphGame
import SphincsSecurity.Proof.CanonicalResidualQuery

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec OracleComp.DeferredSampling
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphInputs canonicalPayloadInputs canonicalGraphOrder instFintypePosition

noncomputable local instance residualGameLabelsSampleable : SampleableType CanonicalGraphLabels :=
  SampleableType.ofFintype CanonicalGraphLabels

noncomputable def residualGraphOracleGame (inputs : Finset HashInput) (dummy : OtsReferenceWords) (adversary : Adversary) :
    ProbComp (Bool × SigningBoundaryTrace) := do
  let parameter ← sampleParameter
  let otsSecret ← sampleOtsSecrets
  let ftsSecret ← sampleFtsSecrets
  let labels ← ($ᵗ CanonicalGraphLabels : ProbComp _)
  let residual ← sampleHashTable inputs
  graphFrontierGameRest parameter otsSecret ftsSecret labels
    (programmedHash parameter otsSecret ftsSecret labels (finiteHashAnswer ∅ inputs residual)) dummy adversary

theorem evalDist_canonicalGraph_eq_residualGraph (inputs : Finset HashInput)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    𝒟[canonicalGraphOracleGame inputs hgraph dummy adversary] =
      𝒟[residualGraphOracleGame inputs dummy adversary] := by
  rw [canonicalGraphOracleGame, residualGraphOracleGame]
  apply evalDist_bind_congr_left
  intro parameter
  apply evalDist_bind_congr_left
  intro otsSecret
  apply evalDist_bind_congr_left
  intro ftsSecret
  have h := evalDist_plantCanonicalGraph_bind_eq_residual parameter otsSecret ftsSecret inputs (hgraph parameter)
    (fun labels table => graphFrontierGameRest parameter otsSecret ftsSecret labels
      (finiteHashAnswer ∅ inputs table) dummy adversary)
  simpa only [finiteHashAnswer_program_eq] using h

theorem evalDist_boundaryGameCore_residualGraph (inputs : Finset HashInput)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary)
    (hinputs : hashInputs (boundaryGameCore adversary) ⊆ inputs) :
    𝒟[(simulateQ romImpl (boundaryGameCore adversary)).run' ∅] =
      𝒟[residualGraphOracleGame inputs dummy adversary] :=
  (evalDist_boundaryGameCore_canonicalGraph inputs hgraph dummy adversary hinputs).trans
    (evalDist_canonicalGraph_eq_residualGraph inputs hgraph dummy adversary)

theorem forgeAdvantage_eq_residualGraph (dummy : OtsReferenceWords) (adversary : Adversary) :
    forgeAdvantage scheme adversary =
      Pr[fun result => result.1 = true | residualGraphOracleGame (canonicalGraphGameInputs adversary) dummy adversary] := by
  rw [forgeAdvantage_eq_canonicalGraph dummy adversary]
  exact probEvent_congr' (fun _ _ => Iff.rfl)
    (evalDist_canonicalGraph_eq_residualGraph (canonicalGraphGameInputs adversary)
      (canonicalGraphInputs_subset_gameInputs adversary) dummy adversary)

end SphincsSecurity.Concrete
