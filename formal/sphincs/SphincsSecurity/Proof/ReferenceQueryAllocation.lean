import SphincsSecurity.Proof.QueryClassAllocation
import SphincsSecurity.Proof.OtsPrefixIdealAllocation

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs

theorem referenceRecordedRest_nonmessage_le (key : SecretKey) (f : QueryImpl HashSpec Id)
    (labels : CanonicalGraphLabels) (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary)
    (result : (Bool × SigningBoundaryTrace) × List OracleWorld.Domain)
    (hresult : result ∈ support (referenceRecordedRest key f labels selections dummy adversary)) :
    QueryCap.calls (CausalFrontierProgram.NonmessageHash key.parameter) result.2 + result.1.2.messageCalls.length ≤
      result.1.2.hashCalls :=
  CausalFrontierProgram.game_nonmessage_recorded_le _ _ _ _ _ _ result (QueryCap.simulate_oracle_mem_support _ _ result hresult)

private theorem probComp_mem_of_evalDist {Result : Type} (computation : ProbComp Result) (result : Result)
    (hresult : result ∈ support 𝒟[computation]) : result ∈ support computation :=
  (mem_support_iff_of_evalDist_eq (mx := computation) (mx' := 𝒟[computation]) rfl result).mpr hresult

theorem referenceRecordedGame_nonmessage_le (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) (result : ReferenceRecordedResult)
    (hresult : result ∈ support (referenceRecordedGame inputs hencoding dummy adversary)) :
    QueryCap.calls (CausalFrontierProgram.NonmessageHash result.1) result.2.2.2 + result.2.2.1.2.messageCalls.length ≤
      result.2.2.1.2.hashCalls := by
  simp only [referenceRecordedGame, mem_support_bind_iff] at hresult
  obtain ⟨parameter, _, otsSecret, _, ftsSecret, _, reference, _, output, houtput, hresult⟩ := hresult
  rw [mem_support_pure_iff] at hresult
  subst result
  exact referenceRecordedRest_nonmessage_le ⟨parameter, 0, otsSecret, ftsSecret⟩ (finiteHashAnswer ∅ inputs reference.2)
    (canonicalGraphLabels parameter otsSecret ftsSecret (finiteHashAnswer ∅ inputs reference.2)) reference.1 dummy adversary output
    (probComp_mem_of_evalDist _ output houtput)

noncomputable def ReferenceRecordedResult.prefixCalls (dummy : OtsReferenceWords) (result : ReferenceRecordedResult) : Nat :=
  ∑ address : OtsPrefix.ChainAddress,
    QueryCap.calls (OtsPrefix.atAddress result.1 (referenceFamilyWords result.2.1 dummy) address).Selects result.2.2.2

noncomputable def ReferenceRecordedResult.encodingCalls (result : ReferenceRecordedResult) : Nat :=
  QueryCap.calls (QueryClass.EncodingHash result.1) result.2.2.2

noncomputable def ReferenceRecordedResult.otherCalls (dummy : OtsReferenceWords) (result : ReferenceRecordedResult) : Nat :=
  QueryCap.calls (QueryClass.OtherHash result.1 (referenceFamilyWords result.2.1 dummy)) result.2.2.2

def ReferenceRecordedResult.messageCalls (result : ReferenceRecordedResult) : Nat := result.2.2.1.2.messageCalls.length

noncomputable def ReferenceRecordedResult.remainingCalls (dummy : OtsReferenceWords) (result : ReferenceRecordedResult) : Nat :=
  result.encodingCalls + result.otherCalls dummy + result.messageCalls

theorem referenceRecordedGame_joint_budget (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (result : ReferenceRecordedResult)
    (hresult : result ∈ support (referenceRecordedGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary)) :
    result.prefixCalls dummy + result.remainingCalls dummy ≤ q := by
  have hpartition := QueryClass.allocation_calls result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.2
  have hslots := referenceRecordedGame_nonmessage_le _ _ dummy adversary result hresult
  have hbudget := referenceRecordedGame_hashCalls_le dummy adversary q hbound result hresult
  dsimp only [ReferenceRecordedResult.prefixCalls, ReferenceRecordedResult.remainingCalls,
    ReferenceRecordedResult.encodingCalls, ReferenceRecordedResult.otherCalls, ReferenceRecordedResult.messageCalls]
  omega

theorem referenceRecordedGame_expected_joint_budget (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) :
    (∑ address : OtsPrefix.ChainAddress, ∑' result : ReferenceRecordedResult,
      Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] *
      (QueryCap.calls (OtsPrefix.atAddress result.1 (referenceFamilyWords result.2.1 dummy) address).Selects
        result.2.2.2 : ENNReal)) +
      (∑' result : ReferenceRecordedResult, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.remainingCalls dummy : ENNReal)) ≤ q := by
  let law := referenceRecordedGame (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary
  calc
    _ = ∑' result : ReferenceRecordedResult, Pr[= result | law] *
        ((result.prefixCalls dummy + result.remainingCalls dummy : Nat) : ENNReal) := by
      rw [← tsum_fintype (L := SummationFilter.unconditional OtsPrefix.ChainAddress), ENNReal.tsum_comm, ← ENNReal.tsum_add]
      simp only [tsum_fintype, ReferenceRecordedResult.prefixCalls, Nat.cast_add, Nat.cast_sum, Finset.mul_sum, mul_add, law]
    _ ≤ ∑' result : ReferenceRecordedResult, Pr[= result | law] * (q : ENNReal) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support law
      · exact mul_le_mul' le_rfl (Nat.cast_le.mpr (referenceRecordedGame_joint_budget dummy adversary q hbound result hresult))
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ ≤ q := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem prefixIdealCostGame_joint_budget (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) :
    (1 - (q : ENNReal) / Fintype.card Digest) *
        (∑ address : OtsPrefix.ChainAddress, ∑' count, Pr[= count | prefixIdealCostGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) (canonicalGraphInputs_subset_gameInputs adversary)
          address dummy adversary q] * (count : ENNReal)) +
      (∑' result : ReferenceRecordedResult, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.remainingCalls dummy : ENNReal)) ≤ q := by
  refine le_trans ?_ (referenceRecordedGame_expected_joint_budget dummy adversary q hbound)
  refine add_le_add ?_ le_rfl
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro address _
  have h := prefixIdealCostGame_lower address dummy adversary q hbound
  simpa only [prefixCountedObservedGame_original, tsum_probOutput_map_mul, ReferenceRecordedResult.prefixCounted] using h

end SphincsSecurity.Concrete
