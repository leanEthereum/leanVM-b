import SphincsSecurity.Proof.InitializedPaidCoverage
import SphincsSecurity.Proof.SampledEncodingPairReserve
import SphincsSecurity.Proof.SecurityRemainingCoverage

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
attribute [local irreducible] expectedBeforeFailureSigningCharge expectedBudgetedLogCharge retainedComputation
set_option backward.isDefEq.respectTransparency false

noncomputable def sampledCoverageRefund (refund : CoverageRefundFamily) (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        initializedCoverageRefund refund adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel

noncomputable def sampledPaidCoverageRefund (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        initializedPaidCoverageRefund adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel

noncomputable def sampledPaidCoverageResidual (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        initializedPaidCoverageResidual adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel

theorem sampledCoverageRefund_mono (left right : CoverageRefundFamily) (hle : left ≤ right)
    (adversary : Adversary) (q fuel : Nat) :
    sampledCoverageRefund left adversary q fuel ≤ sampledCoverageRefund right adversary q fuel := by
  unfold sampledCoverageRefund initializedCoverageRefund
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
  exact expectedCoverageRefund_mono _ _ _ _ _ _ _ _ (hle parameter initial.2.1 table (curryFtsTableEquiv ftsSecret) q) _ _ _ _ _ _

private theorem expected_le_constant_add {α : Type} (computation : ProbComp α)
    (value risk : α → ENNReal) (bound : ENNReal)
    (h : ∀ result ∈ support computation, value result ≤ bound + risk result) :
    (∑' result, Pr[= result | computation] * value result) ≤
      bound + ∑' result, Pr[= result | computation] * risk result := by
  calc
    _ ≤ ∑' result, Pr[= result | computation] * (bound + risk result) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support computation
      · exact mul_le_mul' le_rfl (h result hr)
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ ≤ _ := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
      exact add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) le_rfl

theorem sampledLiveNonSecretResidual_pairs_refund_of_family_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat)
    (refund : CoverageRefundFamily) (hrefund : CoverageRefundFamilyBound refund q) :
    sampledLiveNonSecretResidual adversary q fuel + sampledCoverageRefund refund adversary q fuel +
      sampledSigningEncodingPairCharge adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (q : ENNReal) * initialRawIndexRate q +
        sampledSigningNonEncodingReserve adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
        sampledPaidCoverageResidual adversary q fuel := by
  unfold sampledLiveNonSecretResidual sampledCoverageRefund sampledPaidCoverageResidual
    sampledSigningEncodingPairCharge sampledSigningNonEncodingReserve
  simp only [← ENNReal.tsum_mul_right, mul_assoc, add_assoc, ← ENNReal.tsum_add, ← mul_add]
  apply expected_le_constant_add
  intro parameter hp
  apply expected_le_constant_add
  intro ftsSecret hfts
  apply expected_le_constant_add
  intro table _
  simpa only [initializedBeforeFailureSigningCharge, ← ENNReal.tsum_mul_right, mul_assoc,
    add_assoc, ← ENNReal.tsum_add, ← mul_add] using
    probEvent_liveNonSecretResidual_pairs_refund_of_family_le adversary q hq refund hrefund parameter hp table
      (curryFtsTableEquiv ftsSecret) hfts fuel

theorem sampledLiveNonSecretResidual_pairs_refund_le_reserved_add_residual
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledLiveNonSecretResidual adversary q fuel + sampledPaidCoverageRefund adversary q fuel +
      sampledSigningEncodingPairCharge adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (q : ENNReal) * initialRawIndexRate q +
        sampledSigningNonEncodingReserve adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
        sampledPaidCoverageResidual adversary q fuel := by
  exact sampledLiveNonSecretResidual_pairs_refund_of_family_le adversary q hq fuel
    (fun parameter root table ftsTable cap => paidRemainingCoverageStepRefund
      (parentException parameter table ftsTable) parameter root table ftsTable cap)
    (fun parameter root table ftsTable budget input frame state hit failed hsigned hcache hcost hhead =>
      stepWithFailure_coverage_pairs_refund_le_reserved_add_residual (parentException parameter table ftsTable)
        parameter root table ftsTable q budget hqMax input frame state hit failed hsigned hcache hcost hhead)

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
