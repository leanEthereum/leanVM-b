import SphincsSecurity.Proof.NormalizedTargetLogSigning
import SphincsSecurity.Proof.ExactSignerReuse

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

theorem expected_signWithView_normalizedTargetLogProduct_le_of_exactReuse (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset FtsTree)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (reuse : ENNReal) (hreuse : exactDigestReuseWeight key message before ≤ reuse) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      normalizedTargetLogProduct key result.2 (log ++ [⟨message, result.1.1⟩]) payload target required) ≤
      normalizedTargetLogProduct key before log payload target required +
        (Fintype.card Index : ENNReal)⁻¹ * (∑ selected ∈ required.powerset.erase ∅, normalizedTargetLogProduct key before log payload target (required \ selected)) +
        (∑ selected ∈ required.powerset.erase ∅,
          normalizedCachedTargetSubsetMatch key.parameter before (tweakableHashInput key.parameter .message payload) target selected *
            normalizedTargetLogProduct key before log payload target (required \ selected)) * reuse := by
  let weight := fun input source => if input = tweakableHashInput key.parameter .message payload then 0
    else normalizedTargetLogIncrement key before log payload target required source
  have hweight (input : HashInput) (source : FewTimeView) : weight input source ≤ normalizedTargetLogIncrement key before log payload target required source := by
    unfold weight
    split_ifs; exact bot_le; exact le_rfl
  calc
    _ ≤ ∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
        (normalizedTargetLogProduct key before log payload target required + successfulSignerInputWeight key message weight result) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)
      · exact mul_le_mul' le_rfl (signWithView_normalizedTargetLogProduct_le_input key message before log payload target required hsigned result hresult)
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ ≤ normalizedTargetLogProduct key before log payload target required +
        (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] * successfulSignerInputWeight key message weight result) := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
      exact add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) le_rfl
    _ ≤ _ := by
      have hbound := (expected_successfulSignerInputWeight_le_allMessage_of_reuseWeight key message before weight _ hweight reuse
        (fun input => (probEvent_signWithView_fixedPrehit_le_exactWeight key message before input (fun _ => True)).trans hreuse)).trans
          (add_le_add (mul_le_of_le_one_left' (freshDigestSelectionProbability_le_one key message before)) le_rfl)
      simp only [weight, expected_normalizedTargetLogIncrement, cached_normalizedTargetLogIncrement] at hbound
      simpa only [add_assoc, weight] using add_le_add (le_refl (normalizedTargetLogProduct key before log payload target required)) hbound

end SphincsSecurity.Concrete
