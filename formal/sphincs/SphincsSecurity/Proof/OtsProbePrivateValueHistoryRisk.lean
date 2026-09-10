import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.EncodingProbability
import SphincsSecurity.Proof.OtsProbeCompletionSampling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem privateValue_compatible_row_mass
    (allowed : HashOutput → Prop) (weight : ENNReal) (likelihood : HashOutput → ENNReal)
    (hrow : ∀ output, likelihood output = if allowed output then weight else 0) :
    (∑' output, Pr[= output | LazyRevealProbe.sampleHashOutput] * likelihood output) =
      Pr[allowed | LazyRevealProbe.sampleHashOutput] * weight := by
  rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro output
  rw [hrow]
  by_cases hallowed : allowed output <;> simp [hallowed]

theorem privateValue_compatible_row_hit_le
    (allowed : HashOutput → Prop) (weight : ENNReal) (likelihood : HashOutput → ENNReal) (candidate : Digest)
    (hrow : ∀ output, likelihood output = if allowed output then weight else 0)
    (hallowed : (3 / 4 : ENNReal) ≤ Pr[allowed | LazyRevealProbe.sampleHashOutput]) :
    (∑' output, if truncateHash output = candidate then
      Pr[= output | LazyRevealProbe.sampleHashOutput] * likelihood output else 0) ≤
      (∑' output, Pr[= output | LazyRevealProbe.sampleHashOutput] * likelihood output) *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  have hhit : (∑' output, if truncateHash output = candidate then
      Pr[= output | LazyRevealProbe.sampleHashOutput] * likelihood output else 0) ≤
      weight * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
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
          ((2 ^ digestBits : Nat) : ENNReal)⁻¹ by
            simpa only [LazyRevealProbe.sampleHashOutput, show Fintype.card Digest = 2 ^ digestBits by simp] using
              SphincsSecurity.probEvent_uniform_truncateHash_eq candidate]
        exact mul_comm _ _
  rw [privateValue_compatible_row_mass allowed weight likelihood hrow]
  apply hhit.trans
  have hfactor : (3 / 4 : ENNReal) * (4 / 3) = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
  calc
    _ = ((3 / 4 : ENNReal) * weight) * ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
      calc
        _ = ((3 / 4 : ENNReal) * (4 / 3)) * (weight * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by rw [hfactor, one_mul]
        _ = _ := by ring
    _ ≤ _ := mul_le_mul' (mul_le_mul' hallowed le_rfl) le_rfl

theorem probEvent_uniform_avoids_private_history_ge_three_quarters
    (history : Finset Digest) (hcard : history.card ≤ 2 ^ 126) :
    (3 / 4 : ENNReal) ≤ Pr[fun output => truncateHash output ∉ history | LazyRevealProbe.sampleHashOutput] := by
  have hbad : Pr[fun output => truncateHash output ∈ history | LazyRevealProbe.sampleHashOutput] ≤ (1 / 4 : ENNReal) := by
    calc
      _ = (history.card : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
        simpa only [LazyRevealProbe.sampleHashOutput, div_eq_mul_inv, show Fintype.card Digest = 2 ^ digestBits by simp] using
          SphincsSecurity.probEvent_uniform_truncateHash_mem history
      _ ≤ ((2 ^ 126 : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
        mul_le_mul' (Nat.cast_le.mpr hcard) le_rfl
      _ = _ := by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div, digestBits]
  have hdouble : Pr[fun output => ¬truncateHash output ∉ history | LazyRevealProbe.sampleHashOutput] ≤ (1 / 4 : ENNReal) := by
    simpa only [not_not] using hbad
  have hgood := probEvent_one_sub_le_of_compl_le (by simp : Pr[⊥ | LazyRevealProbe.sampleHashOutput] = 0) hdouble
  have hsum : (1 : ENNReal) ≤ Pr[fun output => truncateHash output ∉ history | LazyRevealProbe.sampleHashOutput] + 1 / 4 :=
    tsub_le_iff_right.mp hgood
  have hreal := (ENNReal.toReal_le_toReal (by finiteness)
    (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, by finiteness⟩)).mpr hsum
  apply (ENNReal.toReal_le_toReal (by finiteness) probEvent_ne_top).mp
  rw [ENNReal.toReal_add probEvent_ne_top (by finiteness)] at hreal
  norm_num [ENNReal.toReal_div] at hreal ⊢
  linarith

theorem privateValue_history_row_hit_le
    (history : Finset Digest) (weight : ENNReal) (likelihood : HashOutput → ENNReal) (candidate : Digest)
    (hrow : ∀ output, likelihood output = if truncateHash output ∉ history then weight else 0)
    (hcard : history.card ≤ 2 ^ 126) :
    (∑' output, if truncateHash output = candidate then
      Pr[= output | LazyRevealProbe.sampleHashOutput] * likelihood output else 0) ≤
      (∑' output, Pr[= output | LazyRevealProbe.sampleHashOutput] * likelihood output) *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) :=
  privateValue_compatible_row_hit_le (fun output => truncateHash output ∉ history) weight likelihood candidate
    (fun output => by
      by_cases hclean : truncateHash output ∉ history <;> simpa only [if_pos hclean, if_neg hclean] using hrow output)
    (probEvent_uniform_avoids_private_history_ge_three_quarters history hcard)

noncomputable def samplePrivateHistoryGuess
    (run : HashOutput → ProbComp (Option α)) (candidate : α → Option Digest) : ProbComp (HashOutput × Option Digest) := do
  let output ← LazyRevealProbe.sampleHashOutput
  let record ← run output
  pure (output, record.bind candidate)

theorem probEvent_samplePrivateHistoryGuess_eq_rows
    (run : HashOutput → ProbComp (Option α)) (candidate : α → Option Digest)
    (event : HashOutput × Option Digest → Prop) :
    Pr[event | samplePrivateHistoryGuess run candidate] =
      ∑' record, ∑' output, if event (output, record.bind candidate) then
        Pr[= output | LazyRevealProbe.sampleHashOutput] * Pr[= record | run output] else 0 := by
  unfold samplePrivateHistoryGuess
  simp_rw [probEvent_bind_eq_tsum, probEvent_pure]
  calc
    _ = ∑' output, ∑' record, if event (output, record.bind candidate) then
        Pr[= output | LazyRevealProbe.sampleHashOutput] * Pr[= record | run output] else 0 := by
      apply tsum_congr
      intro output
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro record
      split_ifs <;> simp
    _ = _ := ENNReal.tsum_comm

theorem probEvent_samplePrivateHistoryGuess_hit_le
    (run : HashOutput → ProbComp (Option α)) (candidate : α → Option Digest)
    (history : α → Finset Digest) (weight : α → ENNReal)
    (hrows : ∀ output record, Pr[= some record | run output] =
      if truncateHash output ∉ history record then weight record else 0)
    (hcard : ∀ record, (history record).card ≤ 2 ^ 126) :
    Pr[fun pair => pair.2 = some (truncateHash pair.1) | samplePrivateHistoryGuess run candidate] ≤
      Pr[fun pair => pair.2 ≠ none | samplePrivateHistoryGuess run candidate] *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  rw [probEvent_samplePrivateHistoryGuess_eq_rows, probEvent_samplePrivateHistoryGuess_eq_rows, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro record
  cases record with
  | none => simp
  | some record =>
      cases hcandidate : candidate record with
      | none => simp [hcandidate]
      | some digest =>
          simp only [Option.bind_some, hcandidate, Option.some.injEq, ne_eq, Option.some_ne_none, not_false_eq_true, if_true]
          simpa only [eq_comm] using privateValue_history_row_hit_le (history record) (weight record)
            (fun output => Pr[= some record | run output]) digest (fun output => hrows output record) (hcard record)

theorem probEvent_samplePrivateHistoryGuess_hit_le_of_compatible
    (run : HashOutput → ProbComp (Option α)) (candidate : α → Option Digest) (history : α → Finset Digest)
    (hcompatible : ∀ before after record, truncateHash before ∉ history record → truncateHash after ∉ history record →
      Pr[= some record | run before] = Pr[= some record | run after])
    (hreject : ∀ output record, truncateHash output ∈ history record → Pr[= some record | run output] = 0)
    (hcard : ∀ record, (history record).card ≤ 2 ^ 126) :
    Pr[fun pair => pair.2 = some (truncateHash pair.1) | samplePrivateHistoryGuess run candidate] ≤
      Pr[fun pair => pair.2 ≠ none | samplePrivateHistoryGuess run candidate] *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  have hexists : ∀ record, ∃ digest : Digest, digest ∉ history record := by
    intro record
    by_contra hnone
    push Not at hnone
    have huniv : history record = Finset.univ := Finset.eq_univ_iff_forall.mpr hnone
    have hlarge := hcard record
    rw [huniv, Finset.card_univ] at hlarge
    norm_num [digestBits] at hlarge
  choose digest hmiss using hexists
  let reference := fun record => hashOutputOfDigest (digest record)
  let weight := fun record => Pr[= some record | run (reference record)]
  apply probEvent_samplePrivateHistoryGuess_hit_le run candidate history weight _ hcard
  intro output record
  by_cases hclean : truncateHash output ∉ history record
  · rw [if_pos hclean]
    exact hcompatible output (reference record) record hclean (by
      simpa only [reference, truncateHash_hashOutputOfDigest] using hmiss record)
  · rw [if_neg hclean]
    exact hreject output record (not_not.mp hclean)

theorem probEvent_samplePrivateHistoryGuess_hit_le_of_supported_compatible
    (run : HashOutput → ProbComp (Option α)) (candidate : α → Option Digest) (history : α → Finset Digest)
    (hcompatible : ∀ before after record, truncateHash before ∉ history record → truncateHash after ∉ history record →
      Pr[= some record | run before] = Pr[= some record | run after])
    (hreject : ∀ output record, truncateHash output ∈ history record → Pr[= some record | run output] = 0)
    (hcard : ∀ output record, some record ∈ support (run output) → (history record).card ≤ 2 ^ 126) :
    Pr[fun pair => pair.2 = some (truncateHash pair.1) | samplePrivateHistoryGuess run candidate] ≤
      Pr[fun pair => pair.2 ≠ none | samplePrivateHistoryGuess run candidate] *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  have hzero (record) (hlarge : ¬(history record).card ≤ 2 ^ 126) (output) : Pr[= some record | run output] = 0 := by
    apply probOutput_eq_zero_of_not_mem_support
    intro hsupport
    exact hlarge (hcard output record hsupport)
  let boundedHistory := fun record => if (history record).card ≤ 2 ^ 126 then history record else ∅
  apply probEvent_samplePrivateHistoryGuess_hit_le_of_compatible run candidate boundedHistory
  · intro before after record hbefore hafter
    by_cases hsmall : (history record).card ≤ 2 ^ 126
    · exact hcompatible before after record
        (by simpa only [boundedHistory, if_pos hsmall] using hbefore)
        (by simpa only [boundedHistory, if_pos hsmall] using hafter)
    · rw [hzero record hsmall before, hzero record hsmall after]
  · intro output record hmem
    by_cases hsmall : (history record).card ≤ 2 ^ 126
    · exact hreject output record (by simpa only [boundedHistory, if_pos hsmall] using hmem)
    · exact hzero record hsmall output
  · intro record
    by_cases hsmall : (history record).card ≤ 2 ^ 126
    · simpa only [boundedHistory, if_pos hsmall] using hsmall
    · simp only [boundedHistory, if_neg hsmall, Finset.card_empty]
      exact Nat.zero_le _

end SphincsSecurity.Concrete.OtsProbeSimulation
