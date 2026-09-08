import SphincsSecurity.Proof.ParentLossDecomposition

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def initializedDirectParentReleaseCharge
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) : ENNReal :=
  ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
    expectedBeforeFailureCharge (parentException parameter otsTable ftsTable)
      (directFtsParentReleaseCharge (secretKey parameter default otsTable ftsTable)) parameter initial.2.1 otsTable ftsTable
      (retainedComputation adversary parameter initial.2.1 q) initial.1 initial.2.2 false initial.1.isNone

theorem initialized_discard_add_directRelease_le_parentLoss
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) :
    initializedTerminalParentDiscard adversary parameter otsTable ftsTable q fuel +
      initializedSharedParentDiscard adversary parameter otsTable ftsTable q fuel +
      initializedDirectParentReleaseCharge adversary parameter otsTable ftsTable q fuel ≤
      initializedParentReserveLoss adversary parameter otsTable ftsTable q fuel := by
  rw [initializedTerminalParentDiscard, initializedSharedParentDiscard, initializedDirectParentReleaseCharge,
    initializedParentReserveLoss, add_assoc, ← ENNReal.tsum_add]
  apply add_le_add le_rfl
  apply ENNReal.tsum_le_tsum
  intro initial
  rw [← mul_add]
  by_cases hi : initial ∈ support (initializeRoot parameter otsTable ftsTable q fuel)
  · have hr := initializeRoot_original_support parameter otsTable ftsTable q fuel initial hi
    have hf := finite_cache_of_mem_support _ ∅ initial.2.1 initial.2.2 hr finite_empty
    apply mul_le_mul' le_rfl
    apply le_trans (add_le_add le_rfl ?_) le_self_add
    exact expectedBeforeFailureCharge_mono_of_finite (parentException parameter otsTable ftsTable) _ _
      (fun current _ input => directFtsParentReleaseCharge_le_released (secretKey parameter default otsTable ftsTable) current input)
      parameter initial.2.1 otsTable ftsTable (retainedComputation adversary parameter initial.2.1 q)
      initial.1 initial.2.2 hf false initial.1.isNone
  · rw [probOutput_eq_zero_of_not_mem_support hi, zero_mul, zero_mul]

noncomputable def sampledDirectParentReleaseCharge (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        initializedDirectParentReleaseCharge adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel

theorem sampled_discard_add_directRelease_le_parentLoss (adversary : Adversary) (q fuel : Nat) :
    sampledTerminalParentDiscard adversary q fuel + sampledSharedParentDiscard adversary q fuel +
      sampledDirectParentReleaseCharge adversary q fuel ≤ sampledParentReserveLoss adversary q fuel := by
  unfold sampledTerminalParentDiscard sampledSharedParentDiscard sampledDirectParentReleaseCharge sampledParentReserveLoss
  simp only [← ENNReal.tsum_add, ← mul_add]
  apply ENNReal.tsum_le_tsum
  intro parameter
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro ftsSecret
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro table
  exact mul_le_mul' le_rfl (initialized_discard_add_directRelease_le_parentLoss adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel)

theorem sampled_pending_discard_directRelease_le_funding (adversary : Adversary) (q fuel : Nat) :
    sampledPendingParentCount adversary q fuel + sampledTerminalParentDiscard adversary q fuel +
      sampledSharedParentDiscard adversary q fuel + sampledDirectParentReleaseCharge adversary q fuel ≤
      sampledFreshParentReserveCharge adversary q fuel := by
  have h := (add_le_add (le_refl (sampledPendingParentCount adversary q fuel))
    (sampled_discard_add_directRelease_le_parentLoss adversary q fuel)).trans_eq
      (sampledPendingParentCount_add_loss_eq_funding adversary q fuel)
  simpa only [add_assoc] using h

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
