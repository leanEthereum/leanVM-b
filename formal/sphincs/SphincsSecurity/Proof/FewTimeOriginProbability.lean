import SphincsSecurity.Proof.FewTimeOriginRealization
import SphincsSecurity.Proof.FewTimeFixedPrehit

/-!
# Probability composition for a direct few-time origin

A realized prehit has a fresh direct random-oracle source. If the rest of the execution can satisfy
an event only after that source returns an admissible answer with a selected view, its probability
is the source probability multiplied by the conditional bound for the rest of the execution.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

theorem probEvent_bind_le_gated_mul
    {First Second : Type} {firstComp : ProbComp First}
    {continuation : First → ProbComp Second} {gate : First → Prop}
    {event : Second → Prop} {epsilon : ℝ≥0∞}
    (hoff : ∀ result ∈ support firstComp, ¬ gate result →
      Pr[event | continuation result] = 0)
    (hon : ∀ result ∈ support firstComp, gate result →
      Pr[event | continuation result] ≤ epsilon) :
    Pr[event | firstComp >>= continuation] ≤ Pr[gate | firstComp] * epsilon := by
  classical
  rw [probEvent_bind_eq_tsum]
  calc
    ∑' result, Pr[= result | firstComp] * Pr[event | continuation result] ≤
        ∑' result, {result | gate result}.indicator
          (fun value => Pr[= value | firstComp] * epsilon) result := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support firstComp
      · by_cases hgate : gate result
        · simpa [hgate] using mul_le_mul' le_rfl (hon result hresult hgate)
        · rw [hoff result hresult hgate]
          simp [hgate]
      · rw [probOutput_eq_zero_of_not_mem_support hresult]
        simp
    _ = (∑' result, {result | gate result}.indicator
          (fun value => Pr[= value | firstComp]) result) * epsilon := by
      rw [← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro result
      by_cases hgate : gate result <;> simp [hgate]
    _ = Pr[gate | firstComp] * epsilon := by
      rw [probEvent_eq_tsum_indicator]

theorem Concrete.probEvent_randomOracle_fresh_bind_admissible_view_le_mul
    {Result : Type} (input : HashInput) (cache : QueryCache HashSpec)
    (hcache : cache input = none) (P : FewTimeView → Prop)
    (continuation : HashOutput × QueryCache HashSpec → ProbComp Result)
    (event : Result → Prop) (epsilon : ℝ≥0∞)
    (hoff : ∀ source ∈ support ((randomOracle input).run cache),
      ¬ (signAttemptResultOfOutput source.1 ≠ none ∧
        P (hashOutputFewTimeView source.1)) →
      Pr[event | continuation source] = 0)
    (hon : ∀ source ∈ support ((randomOracle input).run cache),
      signAttemptResultOfOutput source.1 ≠ none ∧
        P (hashOutputFewTimeView source.1) →
      Pr[event | continuation source] ≤ epsilon) :
    Pr[event | (randomOracle input).run cache >>= continuation] ≤
      (((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
        Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)]) * epsilon := by
  refine (probEvent_bind_le_gated_mul hoff hon).trans_eq ?_
  rw [probEvent_randomOracle_fresh_admissible_view input cache hcache P]

theorem Concrete.probEvent_randomOracle_fresh_bind_fixedPrehit_le
    {Result : Type} (input : HashInput) (cache : QueryCache HashSpec)
    (hcache : cache input = none) (P : FewTimeView → Prop)
    (continuation : HashOutput × QueryCache HashSpec → ProbComp Result)
    (event : Result → Prop)
    (hoff : ∀ source ∈ support ((randomOracle input).run cache),
      ¬ (signAttemptResultOfOutput source.1 ≠ none ∧
        P (hashOutputFewTimeView source.1)) →
      Pr[event | continuation source] = 0)
    (hon : ∀ source ∈ support ((randomOracle input).run cache),
      signAttemptResultOfOutput source.1 ≠ none ∧
        P (hashOutputFewTimeView source.1) →
      Pr[event | continuation source] ≤
        ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹) :
    Pr[event | (randomOracle input).run cache >>= continuation] ≤
      Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
        ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    Pr[event | (randomOracle input).run cache >>= continuation] ≤
        (((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
          Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)]) *
            ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹ :=
      probEvent_randomOracle_fresh_bind_admissible_view_le_mul input cache hcache P
        continuation event _ hoff hon
    _ = Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
          (((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹ *
            ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹) := by
      ac_rfl
    _ = Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
        ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ := by
      rw [prehit_race_source_weight]

end SphincsSecurity
