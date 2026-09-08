import SphincsSecurity.Proof.PaidCoverageRefundBound
import SphincsSecurity.Proof.SampledPaidCoverage

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
attribute [local irreducible] expectedBudgetedLogCharge expectedRemainingUnusedCoverageCharge
set_option backward.isDefEq.respectTransparency false

theorem sampledPaidCoverageRefund_le_twice_remainingUnused (adversary : Adversary) (q fuel : Nat) :
    sampledPaidCoverageRefund adversary q fuel ≤ sampledRemainingUnusedCoverageCharge adversary q fuel * 2 := by
  unfold sampledPaidCoverageRefund sampledRemainingUnusedCoverageCharge
    initializedPaidCoverageRefund initializedRemainingUnusedCoverageCharge
  simp only [← ENNReal.tsum_mul_right, mul_assoc]
  apply ENNReal.tsum_le_tsum
  intro parameter
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro ftsSecret
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro table
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro initial
  apply mul_le_mul' le_rfl
  simpa only [mul_assoc, mul_comm, mul_left_comm] using expectedPaidCoverageRefund_le_twice_remainingUnused
    (parentException parameter table (curryFtsTableEquiv ftsSecret)) parameter initial.2.1 table (curryFtsTableEquiv ftsSecret)
    q q (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) initial.1 (initial.2.2, []) false initial.1.isNone

theorem sampledPaidCoverageResidual_le_refund_fraction (adversary : Adversary) (q fuel : Nat) :
    sampledPaidCoverageResidual adversary q fuel ≤
      sampledPaidCoverageRefund adversary q fuel * ((2 ^ 22 : Nat) : ENNReal)⁻¹ := by
  unfold sampledPaidCoverageResidual sampledPaidCoverageRefund initializedPaidCoverageResidual initializedPaidCoverageRefund
  simp only [← ENNReal.tsum_mul_right, mul_assoc]
  apply ENNReal.tsum_le_tsum
  intro parameter
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro ftsSecret
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro table
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro initial
  apply mul_le_mul' le_rfl
  apply expectedPaidCoverageResidual_le_refund_fraction
  intro entry hentry
  simp only [List.not_mem_nil] at hentry

theorem sampledPaidCoverageRefund_ne_top
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledPaidCoverageRefund adversary q fuel ≠ ⊤ := by
  have hbound := le_add_self.trans (sampledLiveNonSecretResidual_add_remainingUnused_le_sharp adversary q hq hqMax fuel)
  have hfinite : (q : ENNReal) * ((27 / 64 : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹) * 2 ≠ ⊤ := by finiteness
  exact ne_top_of_le_ne_top hfinite ((sampledPaidCoverageRefund_le_twice_remainingUnused adversary q fuel).trans
    (mul_le_mul' hbound le_rfl))

theorem sampledPaidCoverageResidual_ne_top
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledPaidCoverageResidual adversary q fuel ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top (sampledPaidCoverageRefund_ne_top adversary q hq hqMax fuel)
    (by finiteness)) (sampledPaidCoverageResidual_le_refund_fraction adversary q fuel)

noncomputable def sampledNetCoverageRefund (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  sampledPaidCoverageRefund adversary q fuel - sampledPaidCoverageResidual adversary q fuel

theorem sampledNetCoverageRefund_add_residual (adversary : Adversary) (q fuel : Nat) :
    sampledNetCoverageRefund adversary q fuel + sampledPaidCoverageResidual adversary q fuel =
      sampledPaidCoverageRefund adversary q fuel := by
  apply tsub_add_cancel_of_le
  exact (sampledPaidCoverageResidual_le_refund_fraction adversary q fuel).trans
    (mul_le_of_le_one_right' (by norm_num))

theorem sampledNetCoverageRefund_ge_fraction
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledPaidCoverageRefund adversary q fuel * (1 - ((2 ^ 22 : Nat) : ENNReal)⁻¹) ≤ sampledNetCoverageRefund adversary q fuel := by
  apply ENNReal.le_of_add_le_add_right (sampledPaidCoverageResidual_ne_top adversary q hq hqMax fuel)
  rw [sampledNetCoverageRefund_add_residual]
  calc
    _ ≤ sampledPaidCoverageRefund adversary q fuel * (1 - ((2 ^ 22 : Nat) : ENNReal)⁻¹) +
        sampledPaidCoverageRefund adversary q fuel * ((2 ^ 22 : Nat) : ENNReal)⁻¹ :=
      add_le_add le_rfl (sampledPaidCoverageResidual_le_refund_fraction adversary q fuel)
    _ = _ := by rw [← mul_add, tsub_add_cancel_of_le (show ((2 ^ 22 : Nat) : ENNReal)⁻¹ ≤ 1 by norm_num), mul_one]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
