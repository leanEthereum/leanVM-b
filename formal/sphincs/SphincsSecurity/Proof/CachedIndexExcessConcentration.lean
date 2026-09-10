import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.CachedIndexHashMoments
import SphincsSecurity.Proof.ExceptionBudgetPotential

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

noncomputable def cachedIndexExcessMoment (parameter : PublicParameter) (cache : QueryCache HashSpec) : ENNReal :=
  ∑ index : Index, positiveScoreMoment (cachedIndexExcessScore parameter cache index) 2

theorem cachedIndexExcessExceptional_moment_ge (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (hbad : CachedIndexExcessExceptional parameter cache) :
    (2 ^ 160 : ENNReal) ≤ cachedIndexExcessMoment parameter cache := by
  obtain ⟨index, hindex⟩ := hbad
  have hpower : (2 ^ 160 : ℝ) ≤ max (cachedIndexExcessScore parameter cache index) 0 ^ 2 := by
    calc
      _ = (2 ^ 80 : ℝ) ^ 2 := by rw [← pow_mul]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (hindex.le.trans (le_max_left _ _)) 2
  have hreal := ENNReal.ofReal_le_ofReal hpower
  rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_ofNat] at hreal
  exact hreal.trans (Finset.single_le_sum (s := Finset.univ)
    (f := fun index => positiveScoreMoment (cachedIndexExcessScore parameter cache index) 2)
    (fun _ _ => zero_le) (Finset.mem_univ index))

theorem cachedIndexExcessMoment_zero_of_no_message (parameter : PublicParameter)
    (cache : QueryCache HashSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput parameter input → cache input = none) :
    cachedIndexExcessMoment parameter cache = 0 := by
  apply Finset.sum_eq_zero
  intro index _
  exact positiveScoreMoment_zero_of_nonpos _
    (cachedIndexExcessScore_nonpos_of_no_message parameter cache hnone index) 2 (by decide)

theorem expected_cachedIndexExcessMoment_le (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) (hfresh : cache input = none) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      cachedIndexExcessMoment parameter (cache.cacheQuery input output)) ≤
        cachedIndexExcessMoment parameter cache + (2 ^ 10 : ENNReal)⁻¹ := by
  calc
    _ = ∑ index : Index, ∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
        positiveScoreMoment (cachedIndexExcessScore parameter (cache.cacheQuery input output) index) 2 := by
      simp only [cachedIndexExcessMoment, Finset.mul_sum]
      exact Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
    _ ≤ ∑ index : Index, (positiveScoreMoment (cachedIndexExcessScore parameter cache index) 2 +
        ((2 ^ 36 : Nat) : ENNReal)⁻¹) :=
      Finset.sum_le_sum (fun index _ => expected_cachedIndexScore_second_le parameter cache hfinite input hfresh index)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      congr 1
      have hcard : Fintype.card Index = 2 ^ 26 := Fintype.card_fin _
      rw [hcard]
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv]

theorem probEvent_cachedIndexExcessExceptional_le (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (q : Nat)
    (hbound : computation.IsQueryBoundP (· matches Sum.inr _) q)
    (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput parameter input → cache input = none) :
    Pr[fun result => result.2 = true |
      runExceptionMonitor (cacheEntryException (CachedIndexExcessExceptional parameter)) computation cache false] ≤
        (q : ENNReal) / 2 ^ 170 := by
  apply le_trans (b := (cachedIndexExcessMoment parameter cache + (q : ENNReal) * (2 ^ 10 : ENNReal)⁻¹) / 2 ^ 160)
  · apply probEvent_cacheEntryException_le_budgetPotential (CachedIndexExcessExceptional parameter)
      (fun remaining current =>
        (cachedIndexExcessMoment parameter current + (remaining : ENNReal) * (2 ^ 10 : ENNReal)⁻¹) / 2 ^ 160)
      ?_ ?_ ?_ computation q hbound cache hfinite
    · intro remaining current _ hbad
      calc
        1 = (2 ^ 160 : ENNReal) / 2 ^ 160 := (ENNReal.div_self (by positivity) (by finiteness)).symm
        _ ≤ _ := ENNReal.div_le_div_right
          ((cachedIndexExcessExceptional_moment_ge parameter current hbad).trans le_self_add) _
    · intro remaining current _
      apply ENNReal.div_le_div_right
      simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ← add_assoc]
      exact le_self_add
    · intro remaining current hcurrent input hnew
      simp only [div_eq_mul_inv, mul_add, ← mul_assoc, ENNReal.tsum_add, ENNReal.tsum_mul_right,
        tsum_probOutput_of_liftM_PMF, one_mul]
      have hstep := expected_cachedIndexExcessMoment_le parameter current hcurrent input hnew
      calc
        _ ≤ (cachedIndexExcessMoment parameter current + (2 ^ 10 : ENNReal)⁻¹ +
            (remaining : ENNReal) * (2 ^ 10 : ENNReal)⁻¹) * (2 ^ 160 : ENNReal)⁻¹ :=
          mul_le_mul' (add_le_add hstep le_rfl) le_rfl
        _ = _ := by push_cast; ring
  · rw [cachedIndexExcessMoment_zero_of_no_message parameter cache hnone, zero_add]
    apply le_of_eq
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv]
    ring

end SphincsSecurity.Concrete
