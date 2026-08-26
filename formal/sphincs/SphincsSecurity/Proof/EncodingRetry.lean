import SphincsSecurity.Proof.EncodingProbability

/-!
# Encoding retry risk

Before an encoding target is installed, every admissible cached answer contributes the reciprocal of the number of admissible digests. A rejected fresh answer preserves this risk, while an admissible fresh answer either hits a pending digest or consumes the pending set. Both transitions are bounded directly on the real random-oracle answer distribution.
-/

namespace SphincsSecurity.EncodingRetry

open OracleComp ENNReal

set_option maxRecDepth 100000

noncomputable def pendingRisk (targets : Finset Digest) : ℝ≥0∞ :=
  (targets.card : ℝ≥0∞) *
    (TargetSum.validDigests.card : ℝ≥0∞)⁻¹

@[simp] theorem pendingRisk_empty : pendingRisk ∅ = 0 := by
  unfold pendingRisk
  rw [Finset.card_empty, Nat.cast_zero, zero_mul]

theorem pendingRisk_insert_le (targets : Finset Digest) (digest : Digest) :
    pendingRisk (insert digest targets) ≤
      pendingRisk targets +
        (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ := by
  unfold pendingRisk
  calc
    ((insert digest targets).card : ℝ≥0∞) *
        (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ ≤
      ((targets.card + 1 : Nat) : ℝ≥0∞) *
        (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ := by
      gcongr
      exact_mod_cast Finset.card_insert_le digest targets
    _ = (targets.card : ℝ≥0∞) *
          (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ +
        (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ := by
      push_cast
      rw [add_mul, one_mul]

noncomputable def applyQuery
    (targets : Finset Digest)
    (resume : HashOutput → Finset Digest → ProbComp Bool) : ProbComp Bool := do
  let output ← ($ᵗ HashOutput : ProbComp HashOutput)
  let digest := truncateHash output
  if TargetSum.ValidDigest digest then
    resume output (insert digest targets)
  else
    resume output targets

theorem applyQuery_true_probability_le
    (targets : Finset Digest)
    (resume : HashOutput → Finset Digest → ProbComp Bool)
    (base : ℝ≥0∞)
    (hresume : ∀ output nextTargets,
      Pr[(· = true) | resume output nextTargets] ≤
        base + pendingRisk nextTargets) :
    Pr[(· = true) | applyQuery targets resume] ≤
      base + (Fintype.card Digest : ℝ≥0∞)⁻¹ + pendingRisk targets := by
  unfold applyQuery
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' output : HashOutput,
        Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (base + pendingRisk targets +
            if TargetSum.ValidDigest (truncateHash output) then
              (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ else 0) := by
      apply ENNReal.tsum_le_tsum
      intro output
      apply mul_le_mul_right
      by_cases hvalid : TargetSum.ValidDigest (truncateHash output)
      · simp only [hvalid, if_true]
        calc
          Pr[(· = true) | resume output (insert (truncateHash output) targets)] ≤
              base + pendingRisk (insert (truncateHash output) targets) :=
            hresume output _
          _ ≤ base + (pendingRisk targets +
              (TargetSum.validDigests.card : ℝ≥0∞)⁻¹) := by
            gcongr
            exact pendingRisk_insert_le targets (truncateHash output)
          _ = _ := by ac_rfl
      · simpa only [hvalid, if_false, add_zero] using hresume output targets
    _ = (base + pendingRisk targets) +
        ∑' output : HashOutput,
          Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
            (if TargetSum.ValidDigest (truncateHash output) then
              (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ else 0) := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right,
        ENNReal.tsum_mul_right,
        tsum_probOutput_of_liftM_PMF, one_mul]
      simp only [one_mul]
    _ = (base + pendingRisk targets) +
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
      rw [SphincsSecurity.uniformHashOutput_valid_bonus_sum_eq]
    _ = _ := by ac_rfl

noncomputable def applySelect
    (targets : Finset Digest)
    (resume : HashOutput → Finset Digest → ProbComp Bool) : ProbComp Bool := do
  let output ← ($ᵗ HashOutput : ProbComp HashOutput)
  let digest := truncateHash output
  if TargetSum.ValidDigest digest then
    if digest ∈ targets then pure true else resume output ∅
  else
    resume output targets

theorem applySelect_true_probability_le
    (targets : Finset Digest)
    (resume : HashOutput → Finset Digest → ProbComp Bool)
    (base : ℝ≥0∞)
    (hresume : ∀ output nextTargets,
      Pr[(· = true) | resume output nextTargets] ≤
        base + pendingRisk nextTargets) :
    Pr[(· = true) | applySelect targets resume] ≤
      base + pendingRisk targets := by
  unfold applySelect
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' output : HashOutput,
        Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (base +
            if TargetSum.ValidDigest (truncateHash output) then
              if truncateHash output ∈ targets then 1 else 0
            else pendingRisk targets) := by
      apply ENNReal.tsum_le_tsum
      intro output
      apply mul_le_mul_right
      by_cases hvalid : TargetSum.ValidDigest (truncateHash output)
      · simp only [hvalid, if_true]
        by_cases hmem : truncateHash output ∈ targets
        · simp only [hmem, if_true, probEvent_pure]
          exact le_add_left le_rfl
        · simp only [hmem, if_false]
          simpa using hresume output ∅
      · simp only [hvalid, if_false]
        exact hresume output targets
    _ = base + ∑' output : HashOutput,
        Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (if TargetSum.ValidDigest (truncateHash output) then
            if truncateHash output ∈ targets then 1 else 0
          else pendingRisk targets) := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
        tsum_probOutput_of_liftM_PMF, one_mul]
    _ ≤ base + pendingRisk targets := by
      gcongr
      exact SphincsSecurity.uniformHashOutput_select_bonus_sum_le targets

noncomputable def buildThenSelect : Nat → Finset Digest → ProbComp Bool
  | 0, targets => applySelect targets fun _ _ => pure false
  | steps + 1, targets =>
      applyQuery targets fun _ nextTargets => buildThenSelect steps nextTargets

theorem buildThenSelect_true_probability_le
    (steps : Nat) (targets : Finset Digest) :
    Pr[(· = true) | buildThenSelect steps targets] ≤
      (steps : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
        pendingRisk targets := by
  induction steps generalizing targets with
  | zero =>
      rw [buildThenSelect]
      simpa using applySelect_true_probability_le targets
        (fun _ _ => pure false) 0 (by simp)
  | succ steps ih =>
      rw [buildThenSelect]
      calc
        Pr[(· = true) |
            applyQuery targets fun _ nextTargets => buildThenSelect steps nextTargets] ≤
          (steps : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
            (Fintype.card Digest : ℝ≥0∞)⁻¹ + pendingRisk targets :=
          applyQuery_true_probability_le targets
            (fun _ nextTargets => buildThenSelect steps nextTargets)
            ((steps : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹)
            (fun _ nextTargets => ih nextTargets)
        _ = ((steps + 1 : Nat) : ℝ≥0∞) *
              (Fintype.card Digest : ℝ≥0∞)⁻¹ + pendingRisk targets := by
          push_cast
          rw [add_mul, one_mul]

theorem buildThenSelect_empty_true_probability_le (steps : Nat) :
    Pr[(· = true) | buildThenSelect steps ∅] ≤
      (steps : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  simpa using buildThenSelect_true_probability_le steps ∅

end SphincsSecurity.EncodingRetry
