import SphincsSecurity.Proof.RawIndexSigningGrowth
import SphincsSecurity.Proof.RawIndexMomentAlgebra

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expected_signWithView_rawIndexGrowth_le_uniform (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (power degree : Nat)
    (hsigned : SigningDigestsCached key.parameter before key.root log) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      rawIndexSigningGrowth key before power (result.2, log ++ [⟨message, result.1.1⟩]) degree) ≤
      ∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * newRawIndexWeight key before log power source degree := by
  apply le_trans ?_ (expected_newAdmissibleSignerView_weight_le key message before (fun source => newRawIndexWeight key before log power source degree))
  calc
    _ ≤ ∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
        ∑' source, if NewAdmissibleSignerView before key (· = source) result then newRawIndexWeight key before log power source degree else 0 := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)
      · exact mul_le_mul' le_rfl (signWithView_rawIndexGrowth_le_newEvents key message before log power degree hsigned result hresult)
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ = _ := by
      simp only [← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro source
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro result
      split_ifs <;> simp

theorem expected_newRawIndexWeight (key : SecretKey) (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (power degree : Nat) :
    (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * newRawIndexWeight key before log power source degree) =
      (Fintype.card Index : ENNReal)⁻¹ *
        (targetIndexCacheLower (targetIndexMoments key before log) power degree +
          targetIndexCacheLower (targetIndexTreeLower (targetIndexMoments key before log)) power degree) := by
  unfold newRawIndexWeight
  rw [uniform_view_index_weight_expectation (fun index => cachePowerArrival power (cachedIndexMultiplicity key.parameter before index) *
    (((signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) index).card + 1 : Nat) : ENNReal) ^ degree),
    weighted_cachePowerArrival_sum]
  simp only [targetIndexMoments_raised, mul_add, Finset.sum_add_distrib, targetIndexCacheLower, div_eq_mul_inv]
  ring

end SphincsSecurity.Concrete
