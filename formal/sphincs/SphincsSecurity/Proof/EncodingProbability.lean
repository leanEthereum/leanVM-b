import SphincsSecurity.Proof.Code
import SphincsSecurity.Proof.FewTimeUniform

/-!
# Encoding acceptance probability

The target-sum decoder accepts a finite nonempty set of 128-bit digests. A fresh random-oracle
answer has a uniform 128-bit truncation, so acceptance has exactly the corresponding finite ratio.
-/

namespace SphincsSecurity

open OracleComp ENNReal
open scoped BigOperators

set_option maxRecDepth 100000

theorem evalDist_truncateHash_uniform :
    𝒟[truncateHash <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
      𝒟[($ᵗ Digest : ProbComp Digest)] := by
  change 𝒟[(fun output : HashOutput => output.extractLsb' 0 digestBits) <$>
      ($ᵗ HashOutput : ProbComp HashOutput)] = _
  exact evalDist_hashOutput_extract_uniform (width := digestBits) (by decide)

theorem probEvent_uniform_truncateHash_eq (target : Digest) :
    Pr[fun output : HashOutput => truncateHash output = target |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
      (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  rw [show (fun output : HashOutput => truncateHash output = target) =
      (fun output => output = target) ∘ truncateHash from rfl]
  rw [← probEvent_map]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) evalDist_truncateHash_uniform]
  rw [probEvent_eq_eq_probOutput, probOutput_uniformSample]

theorem probEvent_uniform_truncateHash_mem (targets : Finset Digest) :
    Pr[fun output : HashOutput => truncateHash output ∈ targets |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
      (targets.card : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) := by
  rw [show (fun output : HashOutput => truncateHash output ∈ targets) =
      (fun digest => digest ∈ targets) ∘ truncateHash from rfl]
  rw [← probEvent_map]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) evalDist_truncateHash_uniform]
  rw [probEvent_uniformSample]
  rw [Finset.filter_univ_mem]

theorem probEvent_uniform_encoding_valid :
    Pr[fun output : HashOutput => TargetSum.ValidDigest (truncateHash output) |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
      (TargetSum.validDigests.card : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  rw [show (fun output : HashOutput => TargetSum.ValidDigest (truncateHash output)) =
      (fun output => TargetSum.ValidDigest output) ∘ truncateHash from rfl]
  rw [← probEvent_map]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) evalDist_truncateHash_uniform]
  rw [probEvent_uniformSample]
  congr 1

theorem probEvent_uniform_encoding_invalid :
    Pr[fun output : HashOutput => ¬ TargetSum.ValidDigest (truncateHash output) |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
      1 - (TargetSum.validDigests.card : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  have hcompl := probEvent_compl
    ($ᵗ HashOutput : ProbComp HashOutput)
    (fun output : HashOutput => TargetSum.ValidDigest (truncateHash output))
  simp only [probFailure_of_liftM_PMF, tsub_zero] at hcompl
  rw [probEvent_uniform_encoding_valid] at hcompl
  apply ENNReal.eq_sub_of_add_eq' (by simp)
  rwa [add_comm]

theorem uniformHashOutput_valid_bonus_sum_eq :
    ∑' output : HashOutput,
        Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (if TargetSum.ValidDigest (truncateHash output) then
            (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ else 0) =
      (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  calc
    _ = Pr[fun output : HashOutput => TargetSum.ValidDigest (truncateHash output) |
          ($ᵗ HashOutput : ProbComp HashOutput)] *
        (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro output
      by_cases hvalid : TargetSum.ValidDigest (truncateHash output)
      · simp only [hvalid, if_true]
      · simp only [hvalid, if_false, mul_zero, zero_mul]
    _ = ((TargetSum.validDigests.card : ℝ≥0∞) /
          (Fintype.card Digest : ℝ≥0∞)) *
        (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ := by
      rw [probEvent_uniform_encoding_valid]
    _ = _ := by
      rw [div_eq_mul_inv]
      calc
        (TargetSum.validDigests.card : ℝ≥0∞) *
              (Fintype.card Digest : ℝ≥0∞)⁻¹ *
              (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ =
            (Fintype.card Digest : ℝ≥0∞)⁻¹ *
              ((TargetSum.validDigests.card : ℝ≥0∞) *
                (TargetSum.validDigests.card : ℝ≥0∞)⁻¹) := by ac_rfl
        _ = (Fintype.card Digest : ℝ≥0∞)⁻¹ * 1 := by
          rw [ENNReal.mul_inv_cancel]
          · exact_mod_cast Nat.ne_of_gt TargetSum.validDigests_card_pos
          · exact ENNReal.natCast_ne_top _
        _ = _ := mul_one _

theorem uniformHashOutput_mem_bonus_sum_eq (targets : Finset Digest) :
    ∑' output : HashOutput,
        Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (if truncateHash output ∈ targets then 1 else 0) =
      (targets.card : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  calc
    _ = Pr[fun output : HashOutput => truncateHash output ∈ targets |
          ($ᵗ HashOutput : ProbComp HashOutput)] := by
      rw [probEvent_eq_tsum_ite]
      apply tsum_congr
      intro output
      by_cases hmem : truncateHash output ∈ targets <;> simp [hmem]
    _ = (targets.card : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) :=
      probEvent_uniform_truncateHash_mem targets
    _ = _ := by rw [div_eq_mul_inv]

theorem uniformHashOutput_valid_scaled_bonus_sum_eq (scale : Nat) :
    ∑' output : HashOutput,
        Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (if TargetSum.ValidDigest (truncateHash output) then
            (scale : ℝ≥0∞) *
              (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ else 0) =
      (scale : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  calc
    _ = (scale : ℝ≥0∞) *
        (∑' output : HashOutput,
          Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
            (if TargetSum.ValidDigest (truncateHash output) then
              (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ else 0)) := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro output
      by_cases hvalid : TargetSum.ValidDigest (truncateHash output)
      · simp only [hvalid, ↓reduceIte]
        ac_rfl
      · simp only [hvalid, ↓reduceIte, mul_zero]
    _ = _ := by rw [uniformHashOutput_valid_bonus_sum_eq]

end SphincsSecurity
