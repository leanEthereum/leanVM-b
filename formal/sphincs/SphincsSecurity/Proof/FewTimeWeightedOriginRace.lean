import SphincsSecurity.Proof.FewTimeParametricSignerRace
import SphincsSecurity.Proof.FewTimeOriginProbability

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

namespace Concrete

noncomputable def digestReuseWeight (q : Nat) : ℝ≥0∞ :=
  ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ /
    ((1 - ((q + digestAttemptLimit : Nat) : ℝ≥0∞) *
      ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹) *
      ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹)

theorem digestReuseWeight_ne_top (q : Nat) (hq : q ≤ 2 ^ 127) :
    digestReuseWeight q ≠ ∞ := by
  apply ENNReal.div_ne_top (by finiteness)
  apply digestRaceSuccessRate_ne_zero_of_budget_lt
  norm_num [digestAttemptLimit, randomnessBits] at *
  omega

theorem digestReuseWeight_source (q : Nat) :
    ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * digestReuseWeight q =
      (((2 ^ randomnessBits : Nat) : ℝ≥0∞) - (q + digestAttemptLimit : Nat))⁻¹ := by
  let space : ℝ≥0∞ := (2 ^ randomnessBits : Nat)
  let admissibility : ℝ≥0∞ := ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹
  let budget : ℝ≥0∞ := (q + digestAttemptLimit : Nat)
  have hspace : space ≠ 0 := by dsimp [space]; positivity
  have hspaceTop : space ≠ ∞ := by dsimp [space]; finiteness
  have hadmissibility : admissibility ≠ 0 := by
    apply ENNReal.inv_ne_zero.mpr
    finiteness
  have hadmissibilityTop : admissibility ≠ ∞ := by dsimp [admissibility]; finiteness
  change admissibility * (space⁻¹ / ((1 - budget * space⁻¹) * admissibility)) =
    (space - budget)⁻¹
  rw [← mul_div_assoc, mul_comm admissibility,
    ENNReal.mul_div_mul_right _ _ hadmissibility hadmissibilityTop]
  have hfraction : (space - budget) / space = 1 - budget * space⁻¹ := by
    rw [ENNReal.sub_div (fun _ _ => hspace), ENNReal.div_self hspace hspaceTop,
      div_eq_mul_inv]
  rw [← hfraction, div_eq_mul_inv, ENNReal.inv_div (Or.inl hspaceTop) (Or.inl hspace),
    ← mul_div_assoc, ENNReal.inv_mul_cancel hspace hspaceTop, one_div]

set_option linter.constructorNameAsVariable false in
theorem probEvent_signWithView_fixedPrehit_le_digestReuseWeight
    (secretKey : SecretKey) (message : Message) (initialCache : QueryCache HashSpec)
    (target : HashInput) (P : FewTimeView → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard initialCache ≤ q) :
    Pr[PrehitSuccessfulSignerView (onlyInputCache initialCache target) secretKey message P |
      (simulateQ romImpl (signWithView secretKey message)).run initialCache] ≤
      digestReuseWeight q := by
  calc
    _ ≤ cachedMessageEntryCountWhere (onlyInputCache initialCache target)
        secretKey.parameter secretKey.root message P * digestReuseWeight q :=
      probEvent_signWithView_prehitSuccessful_le_queryBudget127 secretKey message
        (onlyInputCache initialCache target) initialCache P
        (onlyInputCache_le initialCache target) q hq hcache
    _ ≤ 1 * digestReuseWeight q := mul_le_mul'
      (cachedMessageEntryCountWhere_onlyInput_le_one initialCache target
        secretKey.parameter secretKey.root message P) le_rfl
    _ = _ := one_mul _

theorem tsum_probOutput_signWithView_fixedPrehit_mul_le_of_weight
    (secretKey : SecretKey) (message : Message)
    (initialCache : QueryCache HashSpec) (target : HashInput) (P : FewTimeView → Prop)
    (reuseWeight : ℝ≥0∞)
    (hreuse : Pr[PrehitSuccessfulSignerView (onlyInputCache initialCache target)
      secretKey message P |
      (simulateQ romImpl (signWithView secretKey message)).run initialCache] ≤ reuseWeight)
    (cost : ((Option Signature × Option FewTimeView) × QueryCache HashSpec) → ℝ≥0∞)
    (epsilon : ℝ≥0∞)
    (hoff : ∀ signerResult ∈ support
        ((simulateQ romImpl (signWithView secretKey message)).run initialCache),
      ¬ PrehitSuccessfulSignerView (onlyInputCache initialCache target)
        secretKey message P signerResult → cost signerResult = 0)
    (hon : ∀ signerResult ∈ support
        ((simulateQ romImpl (signWithView secretKey message)).run initialCache),
      PrehitSuccessfulSignerView (onlyInputCache initialCache target)
        secretKey message P signerResult → cost signerResult ≤ epsilon) :
    (∑' signerResult,
      Pr[= signerResult |
        (simulateQ romImpl (signWithView secretKey message)).run initialCache] *
          cost signerResult) ≤ reuseWeight * epsilon :=
  (tsum_probOutput_mul_le_gated _ _ _ _ hoff hon).trans (mul_le_mul' hreuse le_rfl)

end Concrete

end SphincsSecurity
