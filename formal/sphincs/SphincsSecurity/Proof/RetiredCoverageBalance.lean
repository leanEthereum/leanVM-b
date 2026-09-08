import SphincsSecurity.Proof.TerminalCoverageRetirement
import SphincsSecurity.Proof.CompleteCoverageBalance

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def expectedTerminalLogPotential
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (weight : CoverLogState → ENNReal) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) : ENNReal :=
  ∑' result, Pr[= result | runWithFailure exception parameter root otsTable ftsTable
      (withSigningLog computation state.2) frame state.1 hit failed] *
    survivingLogPotential weight (result.1.2.1.2, result.1.2.1.1.2) result.1.2.2 result.2

noncomputable def expectedRetiredCoverageRefund
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (budget : Nat) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) : ENNReal :=
  expectedCompleteCoverageRefund exception parameter root otsTable ftsTable cap computation budget frame state hit failed +
    expectedTerminalLogPotential exception parameter root otsTable ftsTable
      (terminalCoverageRetirement (secretKey parameter root otsTable ftsTable) cap) computation frame state hit failed

theorem expectedTerminal_current_add_retirement
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) :
    expectedTerminalLogPotential exception parameter root otsTable ftsTable (currentCoveragePotential (secretKey parameter root otsTable ftsTable))
        computation frame state hit failed +
      expectedTerminalLogPotential exception parameter root otsTable ftsTable (terminalCoverageRetirement (secretKey parameter root otsTable ftsTable) cap)
        computation frame state hit failed =
      expectedTerminalLogPotential exception parameter root otsTable ftsTable
        (fun current => cappedRemainingCachedTargetEnvelope (secretKey parameter root otsTable ftsTable) cap 0 current ∅ Finset.univ *
          ((2 ^ 140 : Nat) : ENNReal)⁻¹) computation frame state hit failed := by
  unfold expectedTerminalLogPotential
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro result
  rw [← mul_add]
  congr 1
  unfold survivingLogPotential
  split_ifs
  · simp only [zero_add]
  · exact currentCoveragePotential_add_retirement _ cap _

theorem expectedTerminal_current_eq_liveCover
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) :
    expectedTerminalLogPotential exception parameter root otsTable ftsTable (currentCoveragePotential (secretKey parameter root otsTable ftsTable))
      computation frame state hit failed =
      Pr[fun result => result.1.2.2 = false ∧ result.2 = false ∧ SigningTranscript.Valid result.1.2.1.1.2 ∧
        SigningCacheCovered parameter root result.1.2.1.2 result.1.2.1.1.2 |
        runWithFailure exception parameter root otsTable ftsTable (withSigningLog computation state.2) frame state.1 hit failed] := by
  rw [expectedTerminalLogPotential, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro result
  cases result.1.2.2 <;> cases result.2 <;>
    simp only [survivingLogPotential, currentCoveragePotential_eq_indicator, Bool.false_or, Bool.true_or,
      Bool.false_eq_true, Bool.true_eq_false, if_false, if_true, true_and, false_and, mul_zero, mul_ite, mul_one]
  rfl

theorem expected_runWithFailure_liveCover_pairs_retiredRefund_eq
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (hcapMax : cap ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (hbound : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).IsQueryBoundP (· matches Sum.inr _) budget)
    (hsigned : SigningDigestsCached parameter state.1 root state.2)
    (hcache : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).run state),
      QueryCache.enncard result.2.1 ≤ cap) :
    Pr[fun result => result.1.2.2 = false ∧ result.2 = false ∧ SigningTranscript.Valid result.1.2.1.1.2 ∧
      SigningCacheCovered parameter root result.1.2.1.2 result.1.2.1.1.2 |
      runWithFailure exception parameter root otsTable ftsTable (withSigningLog computation state.2) frame state.1 hit failed] +
      expectedRetiredCoverageRefund exception parameter root otsTable ftsTable cap computation budget frame state hit failed +
      expectedBeforeFailureSigningCharge exception (encodingPairIncrementCharge (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable computation frame state.1 hit failed * (Fintype.card Digest : ENNReal)⁻¹ =
      survivingLogPotential (fun current => remainingCoveragePotential (secretKey parameter root otsTable ftsTable)
        cap budget current ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹) state hit failed +
        expectedBeforeFailureSigningCharge exception (nonMessageNonEncodingHashCharge parameter)
          parameter root otsTable ftsTable computation frame state.1 hit failed * (Fintype.card Digest : ENNReal)⁻¹ +
        expectedPaidCoverageResidual exception parameter root otsTable ftsTable cap computation budget frame state hit failed := by
  have h := expected_runWithFailure_coverage_pairs_completeRefund_eq exception parameter root otsTable ftsTable
    cap budget hcapMax computation frame state hit failed hbound hsigned hcache
  change expectedTerminalLogPotential exception parameter root otsTable ftsTable _ computation frame state hit failed + _ + _ = _ at h
  rw [← expectedTerminal_current_add_retirement, expectedTerminal_current_eq_liveCover] at h
  unfold expectedRetiredCoverageRefund
  convert h using 1
  ring

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
