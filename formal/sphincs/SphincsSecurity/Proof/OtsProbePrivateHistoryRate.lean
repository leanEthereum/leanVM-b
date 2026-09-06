import SphincsSecurity.Proof.OtsProbePrivateValueHistoryRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def privateHistoryGuessRate (excluded : Nat) : ENNReal :=
  ((Fintype.card Digest - excluded : Nat) : ENNReal)⁻¹

theorem privateHistoryGuessRate_mono {a b : Nat} (hle : a ≤ b) :
    privateHistoryGuessRate a ≤ privateHistoryGuessRate b := by
  apply ENNReal.inv_le_inv.mpr
  exact Nat.cast_le.mpr (Nat.sub_le_sub_left hle _)

theorem privateHistoryGuessRate_ne_top {excluded : Nat} (hsmall : excluded < Fintype.card Digest) :
    privateHistoryGuessRate excluded ≠ ⊤ := by
  apply ENNReal.inv_ne_top.mpr
  exact_mod_cast Nat.sub_ne_zero_of_lt hsmall

theorem privateHistoryGuessRate_le_four_thirds {excluded : Nat} (hsmall : excluded ≤ 2 ^ 126) :
    privateHistoryGuessRate excluded ≤ (4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  apply (privateHistoryGuessRate_mono hsmall).trans_eq
  apply (ENNReal.toReal_eq_toReal_iff'
    (privateHistoryGuessRate_ne_top (by norm_num [digestBits])) (by finiteness)).mp
  norm_num [privateHistoryGuessRate, digestBits, ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_div]

theorem privateHistoryGuessRate_le_two {excluded : Nat} (hsmall : excluded ≤ 2 ^ 127) :
    privateHistoryGuessRate excluded ≤ (2 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  apply (privateHistoryGuessRate_mono hsmall).trans_eq
  apply (ENNReal.toReal_eq_toReal_iff'
    (privateHistoryGuessRate_ne_top (by norm_num [digestBits])) (by finiteness)).mp
  norm_num [privateHistoryGuessRate, digestBits, ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_div]

theorem probEvent_uniform_avoids_private_history_eq (history : Finset Digest) :
    Pr[fun output => truncateHash output ∉ history | LazyRevealProbe.sampleHashOutput] =
      ((Fintype.card Digest - history.card : Nat) : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ := by
  simpa only [LazyRevealProbe.sampleHashOutput, Finset.mem_compl, Finset.card_compl, div_eq_mul_inv] using
    SphincsSecurity.probEvent_uniform_truncateHash_mem historyᶜ

theorem privateValue_history_row_hit_le_historyRate
    (history : Finset Digest) (weight : ENNReal) (likelihood : HashOutput → ENNReal) (candidate : Digest)
    (hrow : ∀ output, likelihood output = if truncateHash output ∉ history then weight else 0)
    (hcard : history.card < Fintype.card Digest) :
    (∑' output, if truncateHash output = candidate then
      Pr[= output | LazyRevealProbe.sampleHashOutput] * likelihood output else 0) ≤
      (∑' output, Pr[= output | LazyRevealProbe.sampleHashOutput] * likelihood output) *
        privateHistoryGuessRate history.card := by
  have hhit : (∑' output, if truncateHash output = candidate then
      Pr[= output | LazyRevealProbe.sampleHashOutput] * likelihood output else 0) ≤
      (Fintype.card Digest : ENNReal)⁻¹ * weight := by
    calc
      _ ≤ ∑' output, if truncateHash output = candidate then
          Pr[= output | LazyRevealProbe.sampleHashOutput] * weight else 0 := by
        apply ENNReal.tsum_le_tsum
        intro output
        have hle : likelihood output ≤ weight := by rw [hrow]; split_ifs <;> simp
        split_ifs
        · exact mul_le_mul' le_rfl hle
        · rfl
      _ = Pr[fun output => truncateHash output = candidate | LazyRevealProbe.sampleHashOutput] * weight := by
        rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
        apply tsum_congr
        intro output
        split_ifs <;> simp
      _ = _ := by
        rw [show Pr[fun output => truncateHash output = candidate | LazyRevealProbe.sampleHashOutput] =
          (Fintype.card Digest : ENNReal)⁻¹ by
            simpa only [LazyRevealProbe.sampleHashOutput] using
              SphincsSecurity.probEvent_uniform_truncateHash_eq candidate]
  rw [privateValue_compatible_row_mass (fun output => truncateHash output ∉ history) weight likelihood
    (fun output => by
      by_cases hclean : truncateHash output ∉ history <;>
        simpa only [if_pos hclean, if_neg hclean] using hrow output),
    probEvent_uniform_avoids_private_history_eq]
  apply hhit.trans_eq
  have hnonzero : ((Fintype.card Digest - history.card : Nat) : ENNReal) ≠ 0 := by
    exact_mod_cast Nat.sub_ne_zero_of_lt hcard
  have hcancel := ENNReal.mul_inv_cancel hnonzero (by simp)
  unfold privateHistoryGuessRate
  calc
    _ = (((Fintype.card Digest - history.card : Nat) : ENNReal) *
        ((Fintype.card Digest - history.card : Nat) : ENNReal)⁻¹) *
        ((Fintype.card Digest : ENNReal)⁻¹ * weight) := by rw [hcancel, one_mul]
    _ = _ := by ring

theorem privateValue_history_row_hit_le_historyRate_of_compatible
    (history : Finset Digest) (likelihood : HashOutput → ENNReal) (candidate : Digest)
    (hcompatible : ∀ before after, truncateHash before ∉ history → truncateHash after ∉ history →
      likelihood before = likelihood after)
    (hreject : ∀ output, truncateHash output ∈ history → likelihood output = 0)
    (hcard : history.card < Fintype.card Digest) :
    (∑' output, if truncateHash output = candidate then
      Pr[= output | LazyRevealProbe.sampleHashOutput] * likelihood output else 0) ≤
      (∑' output, Pr[= output | LazyRevealProbe.sampleHashOutput] * likelihood output) *
        privateHistoryGuessRate history.card := by
  obtain ⟨digest, hmiss⟩ : ∃ digest : Digest, digest ∉ history := by
    by_contra hnone
    push Not at hnone
    have huniv := Finset.eq_univ_iff_forall.mpr hnone
    simp only [huniv, Finset.card_univ, lt_self_iff_false] at hcard
  let reference := hashOutputOfDigest digest
  apply privateValue_history_row_hit_le_historyRate history (likelihood reference) likelihood candidate _ hcard
  intro output
  by_cases hclean : truncateHash output ∉ history
  · rw [if_pos hclean]
    exact hcompatible output reference hclean (by simpa only [reference, truncateHash_hashOutputOfDigest] using hmiss)
  · rw [if_neg hclean]
    exact hreject output (not_not.mp hclean)

noncomputable def privateHistoryWeightedOccurrence
    (run : HashOutput → ProbComp (Option α)) (candidate : α → Option Digest)
    (history : α → Finset Digest) : ENNReal :=
  ∑' record : α, if candidate record ≠ none then
    (∑' output, Pr[= output | LazyRevealProbe.sampleHashOutput] * Pr[= some record | run output]) *
      privateHistoryGuessRate (history record).card else 0

theorem probEvent_samplePrivateHistoryGuess_hit_le_weighted
    (run : HashOutput → ProbComp (Option α)) (candidate : α → Option Digest) (history : α → Finset Digest)
    (hcompatible : ∀ before after record, truncateHash before ∉ history record → truncateHash after ∉ history record →
      Pr[= some record | run before] = Pr[= some record | run after])
    (hreject : ∀ output record, truncateHash output ∈ history record → Pr[= some record | run output] = 0)
    (hcard : ∀ output record, some record ∈ support (run output) → (history record).card < Fintype.card Digest) :
    Pr[fun pair => pair.2 = some (truncateHash pair.1) | samplePrivateHistoryGuess run candidate] ≤
      privateHistoryWeightedOccurrence run candidate history := by
  rw [probEvent_samplePrivateHistoryGuess_eq_rows, tsum_option (hf := ENNReal.summable)]
  simp only [Option.bind_none, reduceCtorEq, if_false, tsum_zero, zero_add]
  unfold privateHistoryWeightedOccurrence
  apply ENNReal.tsum_le_tsum
  intro record
  cases hcandidate : candidate record with
  | none => simp [hcandidate]
  | some digest =>
      simp only [Option.bind_some, hcandidate]
      by_cases hsmall : (history record).card < Fintype.card Digest
      · simpa only [Option.some.injEq, eq_comm, ne_eq, reduceCtorEq, not_false_eq_true, if_true] using
          privateValue_history_row_hit_le_historyRate_of_compatible (history record)
            (fun output => Pr[= some record | run output]) digest
            (fun before after => hcompatible before after record) (fun output => hreject output record) hsmall
      · have hzero : ∀ output, Pr[= some record | run output] = 0 := by
          intro output
          apply probOutput_eq_zero_of_not_mem_support
          intro hsupport
          exact hsmall (hcard output record hsupport)
        simp [hzero]

theorem privateHistoryWeightedOccurrence_le_budget
    (run : HashOutput → ProbComp (Option α)) (candidate : α → Option Digest) (history : α → Finset Digest)
    (budget : Nat)
    (hcard : ∀ output record, some record ∈ support (run output) → (history record).card ≤ budget) :
    privateHistoryWeightedOccurrence run candidate history ≤
      Pr[fun pair => pair.2 ≠ none | samplePrivateHistoryGuess run candidate] * privateHistoryGuessRate budget := by
  rw [probEvent_samplePrivateHistoryGuess_eq_rows, tsum_option (hf := ENNReal.summable)]
  simp only [Option.bind_none, ne_eq, not_true_eq_false, if_false, tsum_zero, zero_add]
  rw [← ENNReal.tsum_mul_right]
  unfold privateHistoryWeightedOccurrence
  apply ENNReal.tsum_le_tsum
  intro record
  by_cases hcandidate : candidate record = none
  · simp [hcandidate]
  · simp only [Option.bind_some, hcandidate, not_false_eq_true, if_true, if_pos hcandidate]
    by_cases hsmall : (history record).card ≤ budget
    · exact mul_le_mul' le_rfl (privateHistoryGuessRate_mono hsmall)
    · have hzero : ∀ output, Pr[= some record | run output] = 0 := by
        intro output
        apply probOutput_eq_zero_of_not_mem_support
        intro hsupport
        exact hsmall (hcard output record hsupport)
      simp [hzero]

end SphincsSecurity.Concrete.OtsProbeSimulation
