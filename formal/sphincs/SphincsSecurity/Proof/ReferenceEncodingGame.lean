import SphincsSecurity.Proof.ReferenceOracleConditioning

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec OracleComp.DeferredSampling
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs
set_option backward.isDefEq.respectTransparency false

noncomputable def referenceEncodingGame (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (position : EncodingPosition) (dummy : OtsReferenceWords) (adversary : Adversary) :
    SPMF (ReferenceSelection × (Bool × SigningBoundaryTrace)) := do
  let parameter ← 𝒟[sampleParameter]
  let otsSecret ← 𝒟[sampleOtsSecrets]
  let ftsSecret ← 𝒟[sampleFtsSecrets]
  let reference ← 𝒟[referenceOracleSample ⟨parameter, 0, otsSecret, ftsSecret⟩ inputs (hencoding parameter) position]
  let f := finiteHashAnswer ∅ inputs reference.2
  let result ← 𝒟[graphFrontierGameRest parameter otsSecret ftsSecret
    (canonicalGraphLabels parameter otsSecret ftsSecret f) f dummy adversary]
  pure (reference.1, result)

theorem referenceEncodingGame_erased (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (position : EncodingPosition) (dummy : OtsReferenceWords) (adversary : Adversary) :
    Prod.snd <$> referenceEncodingGame inputs hencoding position dummy adversary =
      𝒟[frontierOracleGame inputs dummy adversary] := by
  rw [referenceEncodingGame, frontierOracleGame]
  simp_rw [← fixedGraphGame_eq_frontier]
  simp only [fixedGraphGame, map_bind, map_pure, bind_pure]
  rw [evalDist_bind_comm]
  rw [evalDist_bind]
  apply congrArg (𝒟[sampleParameter] >>= ·)
  funext parameter
  rw [evalDist_bind_comm, evalDist_bind]
  apply congrArg (𝒟[sampleOtsSecrets] >>= ·)
  funext otsSecret
  rw [evalDist_bind_comm, evalDist_bind]
  apply congrArg (𝒟[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  exact referenceOracleSample_bind ⟨parameter, 0, otsSecret, ftsSecret⟩ inputs
    (hencoding parameter) (hgraph parameter) position
    (fun table => graphFrontierGameRest parameter otsSecret ftsSecret
      (canonicalGraphLabels parameter otsSecret ftsSecret (finiteHashAnswer ∅ inputs table))
      (finiteHashAnswer ∅ inputs table) dummy adversary)

theorem evalDist_boundaryGameCore_referenceEncoding (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (position : EncodingPosition) (dummy : OtsReferenceWords) (adversary : Adversary)
    (hinputs : hashInputs (boundaryGameCore adversary) ⊆ inputs) :
    𝒟[(simulateQ romImpl (boundaryGameCore adversary)).run' ∅] =
      Prod.snd <$> referenceEncodingGame inputs hencoding position dummy adversary := by
  exact (evalDist_boundaryGameCore_frontier inputs dummy adversary hinputs).trans
    (referenceEncodingGame_erased inputs hencoding hgraph position dummy adversary).symm

theorem forgeAdvantage_eq_referenceEncoding (position : EncodingPosition)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    forgeAdvantage scheme adversary =
      Pr[fun result => result.2.1 = true |
        referenceEncodingGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) position dummy adversary] := by
  rw [forgeAdvantage, probOutput_def,
    evalDist_gameCore_frontier (canonicalGraphGameInputs adversary) dummy adversary
      (hashInputs_subset_canonicalGraphGameInputs adversary), evalDist_map,
    ← referenceEncodingGame_erased (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary)
      (canonicalGraphInputs_subset_gameInputs adversary) position dummy adversary,
    ← LawfulFunctor.comp_map]
  change Pr[= true | (Prod.fst ∘ Prod.snd) <$>
    referenceEncodingGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) position dummy adversary] = _
  rw [probOutput_map]
  rfl

theorem referenceEncodingGame_hashCalls_le (position : EncodingPosition)
    (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (result : ReferenceSelection × (Bool × SigningBoundaryTrace))
    (hresult : result ∈ support (referenceEncodingGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) position dummy adversary)) :
    result.2.2.hashCalls ≤ q := by
  apply boundaryGameCore_hashCalls_le adversary q hbound result.2
  apply (mem_support_iff_of_evalDist_eq
    (mx' := Prod.snd <$> referenceEncodingGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) position dummy adversary)
    (evalDist_boundaryGameCore_referenceEncoding (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary)
      (canonicalGraphInputs_subset_gameInputs adversary) position dummy adversary
      (hashInputs_subset_canonicalGraphGameInputs adversary)) result.2).mpr
  rw [support_map]
  exact ⟨result, hresult, rfl⟩

end SphincsSecurity.Concrete
