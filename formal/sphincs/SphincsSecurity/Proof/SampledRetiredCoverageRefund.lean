import SphincsSecurity.Proof.RetiredCoverageProbability
import SphincsSecurity.Proof.SampledCompleteCoverageRefund

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
attribute [local irreducible] expectedBeforeFailureSigningCharge expectedBudgetedLogCharge retainedComputation
set_option backward.isDefEq.respectTransparency false

noncomputable def sampledRetiredCoverageRefund (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        initializedRetiredCoverageRefund adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel

noncomputable def sampledTerminalCoverageRetirement (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        ∑' initial, Pr[= initial | initializeRoot parameter table (curryFtsTableEquiv ftsSecret) q fuel] *
          expectedTerminalLogPotential (parentException parameter table (curryFtsTableEquiv ftsSecret))
            parameter initial.2.1 table (curryFtsTableEquiv ftsSecret)
            (terminalCoverageRetirement (secretKey parameter initial.2.1 table (curryFtsTableEquiv ftsSecret)) q)
            (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩)
            initial.1 (initial.2.2, []) false initial.1.isNone

theorem sampledRetiredCoverageRefund_eq_complete_add_terminal (adversary : Adversary) (q fuel : Nat) :
    sampledRetiredCoverageRefund adversary q fuel =
      sampledCompleteCoverageRefund adversary q fuel + sampledTerminalCoverageRetirement adversary q fuel := by
  unfold sampledRetiredCoverageRefund initializedRetiredCoverageRefund expectedRetiredCoverageRefund
    sampledCompleteCoverageRefund sampledCoverageRefund initializedCoverageRefund sampledTerminalCoverageRetirement
  simp only [mul_add, ENNReal.tsum_add]
  rfl

theorem sampledCompleteCoverageRefund_le_retired (adversary : Adversary) (q fuel : Nat) :
    sampledCompleteCoverageRefund adversary q fuel ≤ sampledRetiredCoverageRefund adversary q fuel := by
  rw [sampledRetiredCoverageRefund_eq_complete_add_terminal]
  exact le_self_add

theorem sampledLiveNonSecretResidual_pairs_retiredRefund_le_reserved_add_residual
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledLiveNonSecretResidual adversary q fuel + sampledRetiredCoverageRefund adversary q fuel +
      sampledSigningEncodingPairCharge adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (q : ENNReal) * initialRawIndexRate q +
        sampledSigningNonEncodingReserve adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
        sampledPaidCoverageResidual adversary q fuel := by
  unfold sampledLiveNonSecretResidual sampledRetiredCoverageRefund sampledPaidCoverageResidual
    sampledSigningEncodingPairCharge sampledSigningNonEncodingReserve
  simp only [← ENNReal.tsum_mul_right, mul_assoc, add_assoc, ← ENNReal.tsum_add, ← mul_add]
  apply coverage_expected_le_constant_add
  intro parameter hp
  apply coverage_expected_le_constant_add
  intro ftsSecret hfts
  apply coverage_expected_le_constant_add
  intro table _
  simpa only [initializedBeforeFailureSigningCharge, ← ENNReal.tsum_mul_right, mul_assoc,
    add_assoc, ← ENNReal.tsum_add, ← mul_add] using
    probEvent_liveNonSecretResidual_pairs_retiredRefund_le_reserved_add_residual adversary q hq hqMax parameter hp table
      (curryFtsTableEquiv ftsSecret) hfts fuel

theorem sampledRetiredCoverageRefund_ne_top
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledRetiredCoverageRefund adversary q fuel ≠ ⊤ := by
  have h := (le_add_self.trans le_self_add).trans
    (sampledLiveNonSecretResidual_pairs_retiredRefund_le_reserved_add_residual adversary q hq hqMax fuel)
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

noncomputable def sampledRetiredNetCoverageRefund (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  sampledRetiredCoverageRefund adversary q fuel - sampledPaidCoverageResidual adversary q fuel

theorem sampledRetiredNetCoverageRefund_add_residual (adversary : Adversary) (q fuel : Nat) :
    sampledRetiredNetCoverageRefund adversary q fuel + sampledPaidCoverageResidual adversary q fuel =
      sampledRetiredCoverageRefund adversary q fuel := by
  apply tsub_add_cancel_of_le
  exact (le_add_self.trans_eq (sampledCompleteNetCoverageRefund_add_residual adversary q fuel)).trans
    (sampledCompleteCoverageRefund_le_retired adversary q fuel)

theorem sampledCompleteNetCoverageRefund_le_retired (adversary : Adversary) (q fuel : Nat) :
    sampledCompleteNetCoverageRefund adversary q fuel ≤ sampledRetiredNetCoverageRefund adversary q fuel :=
  tsub_le_tsub_right (sampledCompleteCoverageRefund_le_retired adversary q fuel) _

theorem sampledRetiredNetCoverageRefund_eq_complete_add_terminal
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledRetiredNetCoverageRefund adversary q fuel =
      sampledCompleteNetCoverageRefund adversary q fuel + sampledTerminalCoverageRetirement adversary q fuel := by
  apply (ENNReal.add_left_inj (sampledPaidCoverageResidual_ne_top adversary q hq hqMax fuel)).mp
  rw [sampledRetiredNetCoverageRefund_add_residual, add_right_comm, sampledCompleteNetCoverageRefund_add_residual]
  exact sampledRetiredCoverageRefund_eq_complete_add_terminal adversary q fuel

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
