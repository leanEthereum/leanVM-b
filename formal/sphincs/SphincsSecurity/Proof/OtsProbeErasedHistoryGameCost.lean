import SphincsSecurity.Proof.OtsProbeErasedHistoryCostBound
import SphincsSecurity.Proof.OtsProbeSharedHistoryGame

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

noncomputable def sampledErasedHistoryProbeCost (targets : Finset Position) (adversary : Adversary) (q : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      expectedErasedHistoryProbeCost (capProbeQueries (nativeChronologicalRetainedComputation adversary parameter ftsSecret) q)
        (ensuredInitialContext targets)

theorem sampledNativeHistoryCharge_le_erasedProbeCost
    (targets : Finset Position) (adversary : Adversary) (q : Nat) :
    sampledNativeHistoryStartCharge targets adversary q + sampledNativeHistoryPrivateCharge targets adversary q ≤
      sampledErasedHistoryProbeCost targets adversary q := by
  unfold sampledNativeHistoryStartCharge sampledNativeHistoryPrivateCharge sampledErasedHistoryProbeCost
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro parameter
  rw [← mul_add, ← ENNReal.tsum_add]
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro ftsSecret
  rw [← mul_add]
  exact mul_le_mul' le_rfl (sharedHistoryCutCharge_le_expectedProbeCost targets _ (ensuredInitialContext targets) q)

theorem sampledErasedHistoryProbeCost_le_q
    (targets : Finset Position) (adversary : Adversary) (q : Nat) :
    sampledErasedHistoryProbeCost targets adversary q ≤ q := by
  calc
    _ ≤ ∑' parameter, Pr[= parameter | sampleParameter] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] * (q : ENNReal) := by
      apply ENNReal.tsum_le_tsum
      intro parameter
      apply mul_le_mul' le_rfl
      apply ENNReal.tsum_le_tsum
      intro ftsSecret
      exact mul_le_mul' le_rfl (expectedErasedHistoryProbeCost_le_probeBound _ (ensuredInitialContext targets) q (capProbeQueries_probeBound _ q))
    _ ≤ _ := by
      simp_rw [ENNReal.tsum_mul_right]
      exact (mul_le_mul' tsum_probOutput_le_one (mul_le_mul' tsum_probOutput_le_one le_rfl)).trans_eq (by simp)

end SphincsSecurity.Concrete.OtsProbeSimulation
