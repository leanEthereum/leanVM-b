import SphincsSecurity.Proof.AdaptiveCompletion

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem uniformCoverageCompletion_le_power (remaining : Nat) :
    uniformCoverageCompletion remaining ≤
      ∑ degree ∈ Finset.range 14, (coverageFactorialCoefficient (degree + 1) : ENNReal) *
        ((remaining : ENNReal) / (Fintype.card Index : ENNReal)) ^ (degree + 1) * (Fintype.card Index : ENNReal) := by
  unfold uniformCoverageCompletion
  apply Finset.sum_le_sum
  intro degree _
  have hchoose : ((degree + 1).factorial * remaining.choose (degree + 1) : Nat) ≤ remaining ^ (degree + 1) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow _ _
  have hcast : ((degree + 1).factorial : ENNReal) * (remaining.choose (degree + 1) : ENNReal) ≤
      (remaining : ENNReal) ^ (degree + 1) := by exact_mod_cast hchoose
  simp only [Nat.cast_mul]
  calc
    _ = (coverageFactorialCoefficient (degree + 1) : ENNReal) *
        ((degree + 1).factorial * (remaining.choose (degree + 1) : ENNReal)) *
          (Fintype.card Index : ENNReal)⁻¹ ^ (degree + 1) * (Fintype.card Index : ENNReal) := by ring
    _ ≤ (coverageFactorialCoefficient (degree + 1) : ENNReal) * (remaining : ENNReal) ^ (degree + 1) *
          (Fintype.card Index : ENNReal)⁻¹ ^ (degree + 1) * (Fintype.card Index : ENNReal) :=
      mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hcast) le_rfl) le_rfl
    _ = _ := by rw [div_eq_mul_inv, mul_pow]; ring

theorem uniformCoverageCompletion_signatureLimit_le :
    uniformCoverageCompletion signatureLimit ≤ 7 * (2 : ENNReal) ^ 40 := by
  apply (uniformCoverageCompletion_le_power signatureLimit).trans
  have hratio : ((signatureLimit : ENNReal) / (Fintype.card Index : ENNReal)) ≠ ∞ := by
    apply ENNReal.div_ne_top (by finiteness)
    norm_num [Index, totalHeight]
  have hfinite (degree : Nat) : (coverageFactorialCoefficient (degree + 1) : ENNReal) *
      ((signatureLimit : ENNReal) / (Fintype.card Index : ENNReal)) ^ (degree + 1) * (Fintype.card Index : ENNReal) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by finiteness) (ENNReal.pow_ne_top hratio)) (by finiteness)
  apply (ENNReal.toReal_le_toReal (ENNReal.sum_ne_top.mpr (fun degree _ => hfinite degree)) (by finiteness)).mp
  rw [ENNReal.toReal_sum (fun degree _ => hfinite degree)]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div,
    signatureLimit, Index, totalHeight, Finset.sum_range_succ, coverageFactorialCoefficient, List.getD]

theorem expected_adaptive_validOccupancy_le_seven_add_reuse {α : Type}
    (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])] *
      (if SigningTranscript.Valid result.2.2 then observedLogOccupancy key result.2 else 0)) ≤
        7 * (2 : ENNReal) ^ 40 +
          ∑ degree ∈ Finset.range 14, (coverageFactorialCoefficient (degree + 1) * (degree + 1).factorial : Nat) *
            expectedCompletionReuseCharge key q (degree + 1) computation (cache, []) :=
  (expected_adaptive_validOccupancy_le_uniform_add_reuse key q hq computation cache hbudget).trans
    (add_le_add uniformCoverageCompletion_signatureLimit_le le_rfl)

end SphincsSecurity.Concrete
