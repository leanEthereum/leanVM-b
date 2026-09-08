import SphincsSecurity.Proof.CompleteCoverageBalance
import SphincsSecurity.Proof.SampledCoverageRefundBound
import SphincsSecurity.Proof.SampledSigningSurvival

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def completeCoverageRefundFamily : CoverageRefundFamily :=
  fun parameter root table ftsTable cap => completeCoverageStepRefund
    (parentException parameter table ftsTable) parameter root table ftsTable cap

theorem completeCoverageRefundFamily_bound (cap : Nat) (hcap : cap ≤ 2 ^ 127) :
    CoverageRefundFamilyBound completeCoverageRefundFamily cap := by
  intro parameter root table ftsTable budget input frame state hit failed hsigned hcache hcost hhead
  exact le_of_eq (stepWithFailure_coverage_pairs_completeRefund_eq_reserved_add_residual
    (parentException parameter table ftsTable) parameter root table ftsTable cap budget hcap
      input frame state hit failed hsigned hcache hcost hhead)

noncomputable def sampledCompleteCoverageRefund (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  sampledCoverageRefund completeCoverageRefundFamily adversary q fuel

theorem sampledPaidCoverageRefund_le_complete (adversary : Adversary) (q fuel : Nat) :
    sampledPaidCoverageRefund adversary q fuel ≤ sampledCompleteCoverageRefund adversary q fuel := by
  apply sampledCoverageRefund_mono
    (fun parameter root table ftsTable cap => paidRemainingCoverageStepRefund
      (parentException parameter table ftsTable) parameter root table ftsTable cap)
  intro parameter root table ftsTable cap budget input frame state hit failed
  exact paidRemainingCoverageStepRefund_le_complete (parentException parameter table ftsTable)
    parameter root table ftsTable cap budget input frame state hit failed

theorem sampledLiveNonSecretResidual_pairs_completeRefund_le_reserved_add_residual
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledLiveNonSecretResidual adversary q fuel + sampledCompleteCoverageRefund adversary q fuel +
      sampledSigningEncodingPairCharge adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (q : ENNReal) * initialRawIndexRate q +
        sampledSigningNonEncodingReserve adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
        sampledPaidCoverageResidual adversary q fuel :=
  sampledLiveNonSecretResidual_pairs_refund_of_family_le adversary q hq fuel
    completeCoverageRefundFamily (completeCoverageRefundFamily_bound q hqMax)

theorem sampledCompleteCoverageRefund_ne_top
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledCompleteCoverageRefund adversary q fuel ≠ ⊤ := by
  have h := (le_add_self.trans le_self_add).trans
    (sampledLiveNonSecretResidual_pairs_completeRefund_le_reserved_add_residual adversary q hq hqMax fuel)
  apply ne_top_of_le_ne_top _ h
  apply ENNReal.add_ne_top.mpr
  constructor
  · apply ENNReal.add_ne_top.mpr
    constructor
    · exact ENNReal.mul_ne_top (by finiteness)
        (ne_top_of_le_ne_top (by finiteness) (initialRawIndexRate_le_127_sharp q hqMax))
    · exact ENNReal.mul_ne_top (sampledSigningNonEncodingReserve_ne_top adversary q hq fuel)
        (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
  · exact sampledPaidCoverageResidual_ne_top adversary q hq hqMax fuel

noncomputable def sampledCompleteNetCoverageRefund (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  sampledCompleteCoverageRefund adversary q fuel - sampledPaidCoverageResidual adversary q fuel

theorem sampledCompleteNetCoverageRefund_add_residual (adversary : Adversary) (q fuel : Nat) :
    sampledCompleteNetCoverageRefund adversary q fuel + sampledPaidCoverageResidual adversary q fuel =
      sampledCompleteCoverageRefund adversary q fuel := by
  apply tsub_add_cancel_of_le
  exact (le_add_self.trans_eq (sampledNetCoverageRefund_add_residual adversary q fuel)).trans
    (sampledPaidCoverageRefund_le_complete adversary q fuel)

theorem sampledNetCoverageRefund_le_complete (adversary : Adversary) (q fuel : Nat) :
    sampledNetCoverageRefund adversary q fuel ≤ sampledCompleteNetCoverageRefund adversary q fuel :=
  tsub_le_tsub_right (sampledPaidCoverageRefund_le_complete adversary q fuel) _

theorem sampledCompleteNetCoverageRefund_ge_fraction
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledCompleteCoverageRefund adversary q fuel * (1 - ((2 ^ 22 : Nat) : ENNReal)⁻¹) ≤
      sampledCompleteNetCoverageRefund adversary q fuel := by
  apply ENNReal.le_of_add_le_add_right (sampledPaidCoverageResidual_ne_top adversary q hq hqMax fuel)
  rw [sampledCompleteNetCoverageRefund_add_residual]
  calc
    _ ≤ sampledCompleteCoverageRefund adversary q fuel * (1 - ((2 ^ 22 : Nat) : ENNReal)⁻¹) +
        sampledCompleteCoverageRefund adversary q fuel * ((2 ^ 22 : Nat) : ENNReal)⁻¹ :=
      add_le_add le_rfl ((sampledPaidCoverageResidual_le_refund_fraction adversary q fuel).trans
        (mul_le_mul' (sampledPaidCoverageRefund_le_complete adversary q fuel) le_rfl))
    _ = _ := by rw [← mul_add, tsub_add_cancel_of_le (show ((2 ^ 22 : Nat) : ENNReal)⁻¹ ≤ 1 by norm_num), mul_one]

noncomputable def sampledAdditionalCoverageRefund (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  sampledCompleteCoverageRefund adversary q fuel - sampledPaidCoverageRefund adversary q fuel

theorem sampledNetCoverageRefund_add_additional_eq_complete
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledNetCoverageRefund adversary q fuel + sampledAdditionalCoverageRefund adversary q fuel =
      sampledCompleteNetCoverageRefund adversary q fuel := by
  apply (ENNReal.add_left_inj (sampledPaidCoverageResidual_ne_top adversary q hq hqMax fuel)).mp
  rw [sampledCompleteNetCoverageRefund_add_residual]
  rw [add_right_comm, sampledNetCoverageRefund_add_residual]
  exact add_tsub_cancel_of_le (sampledPaidCoverageRefund_le_complete adversary q fuel)

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
