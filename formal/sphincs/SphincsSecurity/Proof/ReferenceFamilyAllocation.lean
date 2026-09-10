import SphincsSecurity.Proof.OtsPrefixAllocation
import SphincsSecurity.Proof.ReferenceFamilyGame

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs

noncomputable def referenceRecordedRest (key : SecretKey) (f : QueryImpl HashSpec Id)
    (labels : CanonicalGraphLabels) (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) :
    ProbComp ((Bool × SigningBoundaryTrace) × List OracleWorld.Domain) :=
  let words := referenceFamilyWords selections dummy
  simulateQ (fixedHashWorld f) (QueryCap.recorded (CausalFrontierProgram.game key.parameter f key.ftsSecret words
    (canonicalGraphFrontier key.otsSecret labels words) adversary))

theorem referenceRecordedRest_erased (key : SecretKey) (f : QueryImpl HashSpec Id)
    (labels : CanonicalGraphLabels) (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) :
    Prod.fst <$> referenceRecordedRest key f labels selections dummy adversary =
      referenceFamilyFrontierRest key f labels selections dummy adversary := by
  rw [referenceRecordedRest, ← simulateQ_map, QueryCap.recorded_forget, CausalFrontierProgram.fixed_game,
    referenceFamilyFrontierRest, causalFrontierGame_eq]

theorem referenceRecordedRest_calls_le (key : SecretKey) (f : QueryImpl HashSpec Id)
    (labels : CanonicalGraphLabels) (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary)
    (result : (Bool × SigningBoundaryTrace) × List OracleWorld.Domain)
    (hresult : result ∈ support (referenceRecordedRest key f labels selections dummy adversary)) :
    QueryCap.calls CausalFrontierProgram.IsHash result.2 ≤ result.1.2.hashCalls :=
  CausalFrontierProgram.game_recorded_le _ _ _ _ _ _ result (QueryCap.simulate_oracle_mem_support _ _ result hresult)

abbrev ReferenceRecordedResult := PublicParameter × ReferenceFamily × ((Bool × SigningBoundaryTrace) × List OracleWorld.Domain)

def ReferenceRecordedResult.erase (result : ReferenceRecordedResult) : ReferenceFamily × (Bool × SigningBoundaryTrace) :=
  (result.2.1, result.2.2.1)

noncomputable def referenceRecordedGame (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF ReferenceRecordedResult := do
  let parameter ← 𝒟[sampleParameter]
  let otsSecret ← 𝒟[sampleOtsSecrets]
  let ftsSecret ← 𝒟[sampleFtsSecrets]
  let key : SecretKey := ⟨parameter, 0, otsSecret, ftsSecret⟩
  let reference ← 𝒟[referenceFamilyOracleSample key inputs (hencoding parameter)]
  let f := finiteHashAnswer ∅ inputs reference.2
  let result ← 𝒟[referenceRecordedRest key f
    (canonicalGraphLabels parameter otsSecret ftsSecret f) reference.1 dummy adversary]
  pure (parameter, reference.1, result)

theorem referenceRecordedGame_erased (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary) :
    ReferenceRecordedResult.erase <$> referenceRecordedGame inputs hencoding dummy adversary =
      referenceFamilyGame inputs hencoding dummy adversary := by
  unfold referenceRecordedGame referenceFamilyGame
  simp only [map_bind, map_pure, ReferenceRecordedResult.erase]
  apply congrArg (𝒟[sampleParameter] >>= ·)
  funext parameter
  apply congrArg (𝒟[sampleOtsSecrets] >>= ·)
  funext otsSecret
  apply congrArg (𝒟[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  apply congrArg (𝒟[referenceFamilyOracleSample _ inputs (hencoding parameter)] >>= ·)
  funext reference
  rw [← referenceRecordedRest_erased, evalDist_map, bind_map_left]

private theorem probComp_mem_of_evalDist {Result : Type} (computation : ProbComp Result) (result : Result)
    (hresult : result ∈ support 𝒟[computation]) : result ∈ support computation :=
  (mem_support_iff_of_evalDist_eq (mx := computation) (mx' := 𝒟[computation]) rfl result).mpr hresult

theorem referenceRecordedGame_calls_le (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) (result : ReferenceRecordedResult)
    (hresult : result ∈ support (referenceRecordedGame inputs hencoding dummy adversary)) :
    QueryCap.calls CausalFrontierProgram.IsHash result.2.2.2 ≤ result.2.2.1.2.hashCalls := by
  simp only [referenceRecordedGame, mem_support_bind_iff] at hresult
  obtain ⟨parameter, _, otsSecret, _, ftsSecret, _, reference, _, output, houtput, hresult⟩ := hresult
  rw [mem_support_pure_iff] at hresult
  subst result
  exact referenceRecordedRest_calls_le _ _ _ _ dummy adversary output (probComp_mem_of_evalDist _ output houtput)

theorem referenceRecordedGame_hashCalls_le (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (result : ReferenceRecordedResult)
    (hresult : result ∈ support (referenceRecordedGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary)) : result.2.2.1.2.hashCalls ≤ q := by
  apply referenceFamilyGame_hashCalls_le dummy adversary q hbound result.erase
  rw [← referenceRecordedGame_erased, support_map]
  exact ⟨result, hresult, rfl⟩

theorem referenceRecordedGame_allocation_le (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (result : ReferenceRecordedResult)
    (hresult : result ∈ support (referenceRecordedGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary)) :
    (∑ address : OtsPrefix.ChainAddress,
      QueryCap.calls (OtsPrefix.atAddress result.1 (referenceFamilyWords result.2.1 dummy) address).Selects result.2.2.2) ≤ q := by
  exact (OtsPrefix.allocation_le result.1 (referenceFamilyWords result.2.1 dummy) Finset.univ result.2.2.2).trans
    ((referenceRecordedGame_calls_le _ _ dummy adversary result hresult).trans
      (referenceRecordedGame_hashCalls_le dummy adversary q hbound result hresult))

theorem referenceRecordedGame_expected_allocation_le (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) :
    (∑ address : OtsPrefix.ChainAddress, ∑' result : ReferenceRecordedResult,
      Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] *
      (QueryCap.calls (OtsPrefix.atAddress result.1 (referenceFamilyWords result.2.1 dummy) address).Selects
        result.2.2.2 : ENNReal)) ≤ q := by
  let law := referenceRecordedGame (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary
  calc
    _ = ∑' result : ReferenceRecordedResult, Pr[= result | law] *
        ((∑ address : OtsPrefix.ChainAddress,
          QueryCap.calls (OtsPrefix.atAddress result.1 (referenceFamilyWords result.2.1 dummy) address).Selects
            result.2.2.2 : Nat) : ENNReal) := by
      rw [← tsum_fintype (L := SummationFilter.unconditional OtsPrefix.ChainAddress), ENNReal.tsum_comm]
      simp only [tsum_fintype, Nat.cast_sum, Finset.mul_sum, law]
    _ ≤ ∑' result : ReferenceRecordedResult, Pr[= result | law] * (q : ENNReal) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support law
      · exact mul_le_mul' le_rfl (Nat.cast_le.mpr (referenceRecordedGame_allocation_le dummy adversary q hbound result hresult))
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ ≤ q := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem forgeAdvantage_eq_referenceRecorded (dummy : OtsReferenceWords) (adversary : Adversary) :
    forgeAdvantage scheme adversary =
      Pr[fun result => result.2.2.1.1 = true | referenceRecordedGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] := by
  rw [forgeAdvantage_eq_referenceFamily dummy adversary, ← referenceRecordedGame_erased, probEvent_map]
  rfl

end SphincsSecurity.Concrete
