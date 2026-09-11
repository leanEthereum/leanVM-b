import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.PoissonCertificateGame
import SphincsSecurity.Proof.Fts.TerminalProposalEnvelope

namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal
open scoped NNReal

theorem poissonMeasure_descFactorial_shift (rate : NNReal) (count degree : Nat) :
    (ProbabilityTheory.poissonMeasure rate).toPMF (count + degree) *
      ((count + degree).descFactorial degree : ENNReal) =
        (rate : ENNReal) ^ degree * (ProbabilityTheory.poissonMeasure rate).toPMF count := by
  have hfactorial : ((count + degree).factorial : ℝ) =
      (count.factorial : ℝ) * ((count + degree).descFactorial degree : ℝ) := by
    exact_mod_cast (by simpa only [Nat.add_sub_cancel_right] using
      (Nat.factorial_mul_descFactorial (Nat.le_add_left degree count)).symm)
  have hreal : (Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ (count + degree) /
      (count + degree).factorial) * (count + degree).descFactorial degree =
        (rate : ℝ) ^ degree * (Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ count / count.factorial) := by
    rw [pow_add]
    field_simp
    rw [hfactorial]
    ring
  simp only [MeasureTheory.Measure.toPMF_apply, ProbabilityTheory.poissonMeasure_singleton]
  calc
    _ = ENNReal.ofReal ((Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ (count + degree) /
        (count + degree).factorial) * (count + degree).descFactorial degree) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal ((rate : ℝ) ^ degree *
        (Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ count / count.factorial)) := congrArg ENNReal.ofReal hreal
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow rate.coe_nonneg, ENNReal.ofReal_coe_nnreal]

theorem expected_poisson_descFactorial (rate : NNReal) (degree : Nat) :
    (∑' count, (ProbabilityTheory.poissonMeasure rate).toPMF count * (count.descFactorial degree : ENNReal)) =
      (rate : ENNReal) ^ degree := by
  rw [← Summable.sum_add_tsum_nat_add' (k := degree)
    (f := fun count => (ProbabilityTheory.poissonMeasure rate).toPMF count * (count.descFactorial degree : ENNReal))
    ENNReal.summable]
  have hzero : (∑ count ∈ Finset.range degree,
      (ProbabilityTheory.poissonMeasure rate).toPMF count * (count.descFactorial degree : ENNReal)) = 0 := by
    apply Finset.sum_eq_zero
    intro count hc
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr (Finset.mem_range.mp hc), Nat.cast_zero, mul_zero]
  rw [hzero, zero_add]
  simp_rw [poissonMeasure_descFactorial_shift, ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

theorem expected_poisson_binomial_power (rate : NNReal) (selection : ENNReal)
    (hselection : selection ≤ 1) (degree : Nat) :
    (∑' total, (ProbabilityTheory.poissonMeasure rate).toPMF total *
      binomialAverage selection total (fun count => (count : ENNReal) ^ degree)) =
        ∑ order ∈ Finset.range (degree + 1),
          (Nat.stirlingSecond degree order : ENNReal) * ((rate : ENNReal) * selection) ^ order := by
  simp_rw [binomialAverage_power hselection, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro order _
  calc
    _ = (Nat.stirlingSecond degree order : ENNReal) *
        (∑' total, (ProbabilityTheory.poissonMeasure rate).toPMF total * (total.descFactorial order : ENNReal)) *
          selection ^ order := by
      rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro total
      ring
    _ = _ := by rw [expected_poisson_descFactorial, mul_pow]; ring

theorem expected_independentProposalWord_count_power {α : Type}
    [SampleableType α] [Fintype α] [Nonempty α] [DecidableEq α]
    (index : α) (total degree : Nat) :
    (∑' word, Pr[= word | independentProposalWord (PMF.uniformOfFintype α) total] *
      (word.count index : ENNReal) ^ degree) =
        binomialAverage (Fintype.card α : ENNReal)⁻¹ total (fun count => (count : ENNReal) ^ degree) := by
  have h := expected_uniformProposalWord_count index total (fun count => (count : ENNReal) ^ degree)
  simpa only [probOutput_def, evalDist_sampleUniformProposalWord, PMF.evalDist_eq] using h

theorem expected_poissonProposal_count_power {α : Type}
    [SampleableType α] [Fintype α] [Nonempty α] [DecidableEq α]
    (rate : NNReal) (index : α) (degree : Nat) :
    (∑' total, (ProbabilityTheory.poissonMeasure (rate * (Fintype.card α : NNReal))).toPMF total *
      ∑' word, Pr[= word | independentProposalWord (PMF.uniformOfFintype α) total] *
        (word.count index : ENNReal) ^ degree) =
          ∑ order ∈ Finset.range (degree + 1),
            (Nat.stirlingSecond degree order : ENNReal) * (rate : ENNReal) ^ order := by
  simp_rw [expected_independentProposalWord_count_power]
  have hcard : (Fintype.card α : ENNReal) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [expected_poisson_binomial_power _ _ (ENNReal.inv_le_one.mpr (by exact_mod_cast Fintype.card_pos))]
  simp only [ENNReal.coe_mul, ENNReal.coe_natCast, mul_assoc, ENNReal.mul_inv_cancel hcard (by finiteness), mul_one]

noncomputable def poissonPowerMoment (rate : ENNReal) (degree : Nat) : ENNReal :=
  ∑ order ∈ Finset.range (degree + 1), (Nat.stirlingSecond degree order : ENNReal) * rate ^ order

noncomputable def terminalProposalAverage (payoff : List Index → ENNReal) : ENNReal :=
  ∑' total, Pr[= total | targetProposalPool] *
    ∑' word, Pr[= word | independentProposalWord (PMF.uniformOfFintype Index) total] * payoff word

theorem terminalProposalAverage_scale (payoff : List Index → ENNReal) (left right : ENNReal) :
    terminalProposalAverage (fun word => left * payoff word * right) =
      left * terminalProposalAverage payoff * right := by
  unfold terminalProposalAverage
  simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro total
  apply tsum_congr
  intro word
  ring

theorem terminalProposalAverage_count_power (index : Index) (degree : Nat) :
    terminalProposalAverage (fun word => (word.count index : ENNReal) ^ degree) =
      poissonPowerMoment (19 / 50) degree := by
  have hcard : Fintype.card Index = 2 ^ totalHeight := by simp [Index]
  have hrate : ((19 / 50 : NNReal) : ENNReal) = 19 / 50 := by norm_num
  simpa only [terminalProposalAverage, targetProposalPool, PMF.probOutput_eq_apply, hcard,
    poissonPowerMoment, hrate] using
      expected_poissonProposal_count_power (19 / 50 : NNReal) index degree

theorem terminalProposalAverage_power_sum (degree : Nat) :
    terminalProposalAverage (fun word => ∑ index : Index, (word.count index : ENNReal) ^ degree) =
      (Fintype.card Index : ENNReal) * poissonPowerMoment (19 / 50) degree := by
  unfold terminalProposalAverage
  simp_rw [Finset.mul_sum, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  change (∑ index : Index, terminalProposalAverage (fun word => (word.count index : ENNReal) ^ degree)) = _
  simp only [terminalProposalAverage_count_power, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem terminalProposalAverage_certificatePrice (required : Finset FtsTree) :
    terminalProposalAverage (terminalCertificatePrice required) =
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * poissonPowerMoment (19 / 50) required.card) *
        targetCertificateScale required := by
  unfold terminalCertificatePrice
  rw [terminalProposalAverage_scale, terminalProposalAverage_power_sum]
  have hcard : (Fintype.card Index : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [mul_assoc (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹),
    ← mul_assoc (Fintype.card Index : ENNReal)⁻¹,
    ENNReal.inv_mul_cancel hcard (by finiteness), one_mul]

end SphincsSecurity.Concrete
