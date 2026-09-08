import SphincsSecurity.Proof.CompleteCoverageReserveLowerBound
import SphincsSecurity.Proof.SecurityJointCollisionCoverageCompletion

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

theorem currentCoveragePotential_eq_boundedCompleted (key : SecretKey) (state : CoverLogState) :
    currentCoveragePotential key state = boundedCompletedCoveragePotential key state := by
  unfold currentCoveragePotential boundedCompletedCoveragePotential completedCoveragePotential
  split_ifs <;> simp only [targetShapeMoments, Finset.prod_empty, one_mul, zero_mul, min_eq_right zero_le]

namespace FtsProbeSimulation.JointOriginal

open OtsProbeSimulation (OtsSecretIndex)

theorem jointCollisionCoverageCompletionCredit_le_terminalRetirement
    (key : SecretKey) (cap : Nat) (state : CoverLogState) (hit failed : Bool) :
    jointCollisionCoverageCompletionCredit key cap state hit failed ≤
      survivingLogPotential (terminalCoverageRetirement key cap) state hit failed := by
  by_cases hstop : (hit || failed) = true
  · cases hit <;> cases failed <;>
      simp_all only [Bool.false_or, Bool.true_or, Bool.false_eq_true,
        jointCollisionCoverageCompletionCredit, collisionStopPotential, collisionSurvivingStructuralPotential,
        if_true, if_false, min_self, tsub_self, mul_zero, survivingLogPotential, le_refl]
  · obtain ⟨rfl, rfl⟩ := Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hstop)
    simp only [jointCollisionCoverageCompletionCredit, survivingLogPotential, Bool.false_or,
      Bool.false_eq_true, if_false, ← currentCoveragePotential_eq_boundedCompleted]
    apply (mul_le_of_le_one_right' (tsub_le_self : (1 : ENNReal) - min 1 (collisionStopPotential key state.1 false false) ≤ 1)).trans
    unfold terminalCoverageRetirement boundedRemainingCoveragePotential remainingCoveragePotential
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
    exact tsub_le_tsub_right (min_le_right _ _) _

theorem expected_retained_completionCredit_le_terminalRetirement
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (root : Digest)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q : Nat)
    (htrace : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable))
      (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP (· matches Sum.inr _) q)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    (∑' result, Pr[= result | runWithFailure exception parameter root otsTable ftsTable
      (retainedComputation adversary parameter root q) frame cache hit failed] *
        retainedJointCollisionCoverageCompletionCredit parameter otsTable ftsTable q result) ≤
      expectedTerminalLogPotential exception parameter root otsTable ftsTable
        (terminalCoverageRetirement (secretKey parameter root otsTable ftsTable) q)
        (unloggedRetainedRestComputation adversary ⟨root, parameter⟩) frame (cache, []) hit failed := by
  rw [runWithFailure_retainedComputation_trace exception adversary parameter root otsTable ftsTable q htrace, tsum_probOutput_map_mul]
  apply ENNReal.tsum_le_tsum
  intro result
  exact mul_le_mul' le_rfl (jointCollisionCoverageCompletionCredit_le_terminalRetirement _ q _ _ _)

theorem sampledJointCollisionCoverageCompletionCredit_le_terminalRetirement
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    sampledJointCollisionCoverageCompletionCredit adversary q fuel ≤ sampledTerminalCoverageRetirement adversary q fuel := by
  unfold sampledJointCollisionCoverageCompletionCredit sampledTerminalCoverageRetirement
  apply ENNReal.tsum_le_tsum
  intro parameter
  by_cases hp : parameter ∈ support sampleParameter
  · apply mul_le_mul' le_rfl
    apply ENNReal.tsum_le_tsum
    intro ftsSecret
    apply mul_le_mul' le_rfl
    apply ENNReal.tsum_le_tsum
    intro table
    apply mul_le_mul' le_rfl
    rw [runRetainedWithFailure, tsum_probOutput_bind_mul]
    apply ENNReal.tsum_le_tsum
    intro initial
    apply mul_le_mul' le_rfl
    exact expected_retained_completionCredit_le_terminalRetirement
      (parentException parameter table (curryFtsTableEquiv ftsSecret)) adversary parameter initial.2.1 table (curryFtsTableEquiv ftsSecret) q
      (OtsProbeSimulation.isQueryBoundP_expandedRetained_all_tables_roots adversary q hq parameter hp table ftsSecret
        (mem_support_sampleFtsSecrets ftsSecret) initial.2.1) initial.1 initial.2.2 false initial.1.isNone
  · rw [probOutput_eq_zero_of_not_mem_support hp, zero_mul, zero_mul]

theorem sampled_remainingUnused_add_signingAfterPairs_add_completion_le_retiredNetRefund
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledRemainingUnusedCoverageCharge adversary q fuel +
      sampledSigningNonEncodingReserveAfterPairs adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledJointCollisionCoverageCompletionCredit adversary q fuel ≤ sampledRetiredNetCoverageRefund adversary q fuel :=
  (add_le_add le_rfl (sampledJointCollisionCoverageCompletionCredit_le_terminalRetirement adversary q hq fuel)).trans
    (sampled_remainingUnused_add_signingAfterPairs_add_terminal_le_retiredNetRefund adversary q hq hqMax fuel)

end FtsProbeSimulation.JointOriginal
end SphincsSecurity.Concrete
