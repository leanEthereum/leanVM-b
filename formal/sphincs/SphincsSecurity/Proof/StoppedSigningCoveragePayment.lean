import SphincsSecurity.Proof.SigningCoverageExecutionPayment
import SphincsSecurity.Proof.StoppedRemainingCoverage

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem stepWithFailure_expect_surviving_le_monitor
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (weight : CoverLogState → ENNReal) :
    (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
      survivingLogPotential weight (stepSigningLogState input state.2 result) result.1.2.2 result.2) ≤
      ∑' result, Pr[= result | runExceptionMonitor exception
        (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) state.1 hit] *
          (if result.2 = false then weight (result.1.2, state.2 ++ signingLogFragment input result.1.1) else 0) := by
  let cost := fun result : ((OracleWorld + SigningSpec).Range input × QueryCache HashSpec) × Bool =>
    if result.2 = false then weight (result.1.2, state.2 ++ signingLogFragment input result.1.1) else 0
  have hproject := tsum_probOutput_map_mul
    (stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed) Prod.fst
    (fun result => cost result.2)
  rw [stepWithFailure_project, step_expect_original] at hproject
  apply le_trans ?_ (le_of_eq hproject.symm)
  apply ENNReal.tsum_le_tsum
  intro result
  apply mul_le_mul' le_rfl
  cases hh : result.1.2.2 <;> cases hf : result.2 <;>
    simp only [survivingLogPotential, stepSigningLogState, cost, hh, Bool.false_or, Bool.true_or,
      Bool.false_eq_true, Bool.true_eq_false, if_false, if_true, zero_le, le_refl]

theorem stepWithFailure_sign_expect_surviving_le
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (message : Message) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) (weight : CoverLogState → ENNReal) :
    (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable (.inr message) frame state.1 hit failed] *
      survivingLogPotential weight (stepSigningLogState (.inr message) state.2 result) result.1.2.2 result.2) ≤
      expectedSurvivingSigningPotential exception (secretKey parameter root otsTable ftsTable) message state hit weight := by
  rw [expectedSurvivingSigningPotential_eq_sign]
  exact stepWithFailure_expect_surviving_le_monitor exception parameter root otsTable ftsTable (.inr message) frame state hit failed weight

noncomputable def paidRemainingCoverageStepRefund
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) : ENNReal :=
  match input with
  | .inl world => stoppedRemainingCoverageStepCharge exception parameter root otsTable ftsTable cap budget (.inl world)
      frame state hit failed ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹
  | .inr message => survivingLogPotential
      (signingCoverageExecutionRefund (secretKey parameter root otsTable ftsTable) cap budget message) state hit failed

noncomputable def paidRemainingCoverageStepResidual
    (key : SecretKey) (cap budget : Nat) (input : (OracleWorld + SigningSpec).Domain) (state : CoverLogState) (hit failed : Bool) : ENNReal :=
  match input with
  | .inl _ => 0
  | .inr message => if ValidSigningStep state.2 (.inr message) then
      survivingLogPotential (signingRemainingCoverageResidual key cap budget message) state hit failed else 0

theorem stepWithFailure_sign_coverage_pairs_refund_le_reserved_add_residual
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (hcapMax : cap ≤ 2 ^ 127) (message : Message) (frame : Option Frame) (state : CoverLogState) (hit : Bool)
    (hsigned : SigningDigestsCached parameter state.1 root state.2) (hcache : QueryCache.enncard state.1 ≤ cap)
    (hcost : signingExecutionHashCost (.inr message) ≤ budget)
    (hcap : ∀ result ∈ support ((simulateQ romImpl (sign (secretKey parameter root otsTable ftsTable) message)).run state.1),
      QueryCache.enncard result.2 ≤ cap) :
    (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable (.inr message) frame state.1 hit false] *
      survivingLogPotential (fun current => remainingCoveragePotential (secretKey parameter root otsTable ftsTable)
        cap (budget - signingExecutionHashCost (.inr message)) current ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹)
          (stepSigningLogState (.inr message) state.2 result) result.1.2.2 result.2) +
      expectedPreExceptionCharge exception (encodingPairIncrementCharge (secretKey parameter root otsTable ftsTable))
        (sign (secretKey parameter root otsTable ftsTable) message) state.1 hit * (Fintype.card Digest : ENNReal)⁻¹ +
      signingCoverageExecutionRefund (secretKey parameter root otsTable ftsTable) cap budget message state ≤
      remainingCoveragePotential (secretKey parameter root otsTable ftsTable) cap budget state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ +
        expectedPreExceptionCharge exception (nonMessageNonEncodingHashCharge parameter)
          (sign (secretKey parameter root otsTable ftsTable) message) state.1 hit * (Fintype.card Digest : ENNReal)⁻¹ +
        signingRemainingCoverageResidual (secretKey parameter root otsTable ftsTable) cap budget message state := by
  apply le_trans (add_le_add (add_le_add
    (stepWithFailure_sign_expect_surviving_le exception parameter root otsTable ftsTable message frame state hit false _) le_rfl) le_rfl)
  exact expected_surviving_sign_coverage_pairs_refund_le_reserved_add_residual exception (secretKey parameter root otsTable ftsTable)
    cap budget hcapMax message state hit hsigned hcache hcost hcap

theorem survivingLogPotential_mul (weight : CoverLogState → ENNReal) (factor : ENNReal)
    (state : CoverLogState) (hit failed : Bool) :
    survivingLogPotential (fun current => weight current * factor) state hit failed =
      survivingLogPotential weight state hit failed * factor := by
  unfold survivingLogPotential
  split_ifs <;> simp only [zero_mul]

theorem stepWithFailure_expect_surviving_eq_zero_of_stopped
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (weight : CoverLogState → ENNReal) (hstop : (hit || failed) = true) :
    (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
      survivingLogPotential weight (stepSigningLogState input state.2 result) result.1.2.2 result.2) = 0 := by
  apply le_antisymm ?_ zero_le
  have h := stepWithFailure_expect_surviving_le exception parameter root otsTable ftsTable input frame state hit failed weight ∞ le_top
  simpa only [hstop, if_true] using h

theorem beforeFailureSigningStepCharge_of_stopped
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal) (key : SecretKey) (cache : QueryCache HashSpec) (hit failed : Bool)
    (input : (OracleWorld + SigningSpec).Domain) (hstop : (hit || failed) = true) :
    beforeFailureSigningStepCharge exception charge key cache hit failed input = 0 := by
  cases input with
  | inl query => rfl
  | inr message =>
      cases hit <;> cases failed <;>
        simp_all only [Bool.false_or, Bool.true_or, Bool.false_eq_true, beforeFailureSigningStepCharge,
          if_true, if_false, expectedPreExceptionCharge_true]

theorem stepWithFailure_coverage_pairs_refund_le_reserved_add_residual
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (hcapMax : cap ≤ 2 ^ 127) (input : (OracleWorld + SigningSpec).Domain)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (hsigned : SigningDigestsCached parameter state.1 root state.2) (hcache : QueryCache.enncard state.1 ≤ cap)
    (hcost : signingExecutionHashCost input ≤ budget)
    (hcap : ∀ result ∈ support ((simulateQ romImpl (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input)).run state.1),
      QueryCache.enncard result.2 ≤ cap) :
    (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
      survivingLogPotential (fun current => remainingCoveragePotential (secretKey parameter root otsTable ftsTable)
        cap (budget - signingExecutionHashCost input) current ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹)
          (stepSigningLogState input state.2 result) result.1.2.2 result.2) +
      beforeFailureSigningStepCharge exception (encodingPairIncrementCharge (secretKey parameter root otsTable ftsTable))
        (secretKey parameter root otsTable ftsTable) state.1 hit failed input * (Fintype.card Digest : ENNReal)⁻¹ +
      paidRemainingCoverageStepRefund exception parameter root otsTable ftsTable cap budget input frame state hit failed ≤
      survivingLogPotential (fun current => remainingCoveragePotential (secretKey parameter root otsTable ftsTable)
        cap budget current ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹) state hit failed +
        beforeFailureSigningStepCharge exception (nonMessageNonEncodingHashCharge parameter)
          (secretKey parameter root otsTable ftsTable) state.1 hit failed input * (Fintype.card Digest : ENNReal)⁻¹ +
        paidRemainingCoverageStepResidual (secretKey parameter root otsTable ftsTable) cap budget input state hit failed := by
  cases input with
  | inl world =>
      simp only [beforeFailureSigningStepCharge, zero_mul, add_zero, paidRemainingCoverageStepRefund, paidRemainingCoverageStepResidual]
      have hvalid : TargetShapeValid ∅ (Finset.univ : Finset FtsTree) := by constructor <;> simp
      have h := mul_le_mul' (stepWithFailure_remainingCoverage_add_unused_le exception parameter root otsTable ftsTable cap budget
        hcapMax (.inl world) frame state hit failed hsigned hcache hcost ∅ Finset.univ hvalid)
        (le_refl (((2 ^ 140 : Nat) : ENNReal)⁻¹))
      simpa only [add_mul, ← ENNReal.tsum_mul_right, mul_assoc, survivingLogPotential_mul, add_zero] using h
  | inr message =>
      by_cases hstop : (hit || failed) = true
      · rw [stepWithFailure_expect_surviving_eq_zero_of_stopped exception parameter root otsTable ftsTable (.inr message)
          frame state hit failed _ hstop,
          beforeFailureSigningStepCharge_of_stopped exception _ _ _ _ _ _ hstop,
          beforeFailureSigningStepCharge_of_stopped exception _ _ _ _ _ _ hstop]
        simp only [paidRemainingCoverageStepRefund, paidRemainingCoverageStepResidual, survivingLogPotential, hstop,
          if_true, ite_self, zero_mul, zero_add, le_refl]
      · have hh : hit = false := by cases hit <;> simp_all
        have hf : failed = false := by cases failed <;> simp_all
        subst hit
        subst failed
        simp only [beforeFailureSigningStepCharge, paidRemainingCoverageStepRefund, paidRemainingCoverageStepResidual,
          survivingLogPotential, Bool.false_or, Bool.false_eq_true, if_false]
        have hsignCap : ∀ result ∈ support ((simulateQ romImpl (sign (secretKey parameter root otsTable ftsTable) message)).run state.1),
            QueryCache.enncard result.2 ≤ cap := by
          simpa only [OracleSpec.Range, OracleSpec.add_apply_inr, expandedAdversaryImpl, scheme] using hcap
        by_cases hactive : ValidSigningStep state.2 (.inr message)
        · rw [if_pos hactive]
          exact stepWithFailure_sign_coverage_pairs_refund_le_reserved_add_residual exception parameter root otsTable ftsTable
            cap budget hcapMax message frame state false hsigned hcache hcost hsignCap
        · rw [if_neg hactive, add_zero]
          apply le_trans (add_le_add (add_le_add
            (stepWithFailure_sign_expect_surviving_le exception parameter root otsTable ftsTable message frame state false false
              (fun current => remainingCoveragePotential (secretKey parameter root otsTable ftsTable) cap
                (budget - signingExecutionHashCost (.inr message)) current ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹)) le_rfl) le_rfl)
          exact expected_surviving_sign_coverage_pairs_refund_le_reserved_of_inactive exception (secretKey parameter root otsTable ftsTable)
            cap budget hcapMax message state false hactive hcache hcost hsignCap

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
