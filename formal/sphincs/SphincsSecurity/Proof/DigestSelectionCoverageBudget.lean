import SphincsSecurity.Proof.DigestSelectionCoverageRisk
import SphincsSecurity.Proof.RemainingSigningCoverage

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation.JointOriginal (unusedTargetExecutionCost)
set_option backward.isDefEq.respectTransparency false

noncomputable def signingCoverageBudgetGap (key : SecretKey) (cap budget : Nat) (message : Message) (state : CoverLogState) : ENNReal :=
  (cappedRemainingRawIndexEnvelope key cap budget state ∅ Finset.univ * (unusedTargetExecutionCost key.parameter state.1 (.inr message) : ENNReal) *
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) +
    remainingCoverageExecutionGap key cap budget (signingExecutionHashCost (.inr message))
      (targetArrivalHashCost key.parameter state.1 (.inr message)) state ∅ Finset.univ) * ((2 ^ 140 : Nat) : ENNReal)⁻¹

private theorem expected_logTraced_sign_weight (key : SecretKey) (message : Message) (state : CoverLogState)
    (weight : Option Signature → CoverLogState → ENNReal) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] * weight result.1 result.2) =
      ∑' result, Pr[= result | (simulateQ romImpl (sign key message)).run state.1] *
        weight result.1 (result.2, state.2 ++ [⟨message, result.1⟩]) := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  have hrun : (unloggedMappedAdversaryImpl key (.inr message)).run state.1 = (simulateQ romImpl (sign key message)).run state.1 := rfl
  rw [hrun]
  rfl

theorem expected_sign_remainingCoverage_scaled_add_gap_le (key : SecretKey) (cap budget : Nat) (hcap : cap ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ cap) (message : Message) (hcost : signingExecutionHashCost (.inr message) ≤ budget) :
    (∑' result, Pr[= result | (simulateQ romImpl (sign key message)).run state.1] *
      (remainingCoveragePotential key cap (budget - signingExecutionHashCost (.inr message))
        (result.2, state.2 ++ [⟨message, result.1⟩]) ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹)) +
      signingCoverageBudgetGap key cap budget message state ≤
        remainingCoveragePotential key cap budget state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ := by
  have hraw := expected_logTraced_sign_remainingCoverage_add_executionGap_le key cap budget hcap state hsigned hcache message hcost
    ∅ Finset.univ (by constructor <;> simp)
  rw [expected_logTraced_sign_weight key message state
    (fun _ current => remainingCoveragePotential key cap (budget - signingExecutionHashCost (.inr message)) current ∅ Finset.univ)] at hraw
  have h := mul_le_mul' hraw (le_refl (((2 ^ 140 : Nat) : ENNReal)⁻¹))
  simpa only [signingCoverageBudgetGap, add_mul, ← ENNReal.tsum_mul_right, mul_assoc] using h

theorem digestSelectionCoverageRisk_add_gap_le (key : SecretKey) (cap budget : Nat) (hcap : cap ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ cap) (message : Message) (hcost : signingExecutionHashCost (.inr message) ≤ budget) :
    digestSelectionCoverageRisk key cap (budget - signingExecutionHashCost (.inr message)) message state.1 state.2 +
      signingCoverageBudgetGap key cap budget message state ≤
        remainingCoveragePotential key cap budget state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ +
          encodingExhaustionTotalPotential state.1 := by
  have hrisk := digestSelectionCoverageRisk_le_signing_add_exhaustion key cap (budget - signingExecutionHashCost (.inr message)) message state.1 state.2
  have hactual := expected_sign_remainingCoverage_scaled_add_gap_le key cap budget hcap state hsigned hcache message hcost
  have hcapActual : (∑' result, Pr[= result | (simulateQ romImpl (sign key message)).run state.1] *
      boundedRemainingCoveragePotential key cap (budget - signingExecutionHashCost (.inr message)) (result.2, state.2 ++ [⟨message, result.1⟩])) ≤
      ∑' result, Pr[= result | (simulateQ romImpl (sign key message)).run state.1] *
        (remainingCoveragePotential key cap (budget - signingExecutionHashCost (.inr message))
          (result.2, state.2 ++ [⟨message, result.1⟩]) ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹) :=
    ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (min_le_right _ _)
  have h := add_le_add hrisk (le_refl (signingCoverageBudgetGap key cap budget message state))
  rw [add_right_comm] at h
  exact h.trans (add_le_add ((add_le_add hcapActual le_rfl).trans hactual) le_rfl)

end SphincsSecurity.Concrete
