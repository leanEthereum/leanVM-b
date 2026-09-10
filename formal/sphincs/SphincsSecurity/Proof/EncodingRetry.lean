import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.Code

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

end SphincsSecurity.EncodingRetry
