import SphincsSecurity.Proof.RemainingFreshSigningGap
import SphincsSecurity.Proof.AdaptivePaidCoverage

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable

noncomputable def signingEnvelopeStepGap (key : SecretKey) (cap budget : Nat)
    (input : (OracleWorld + SigningSpec).Domain) (_frame : Option Frame)
    (state : CoverLogState) (hit failed : Bool) : ENNReal :=
  match input with
  | .inl _ => 0
  | .inr message => survivingLogPotential
      (signingCoverageEnvelopeGap key cap (budget - signingExecutionHashCost (.inr message)) message) state hit failed

theorem coverageStepRefundBound_paid_add_signingEnvelopeGap
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap : Nat) (hcapMax : cap ≤ 2 ^ 127) :
    CoverageStepRefundBound exception parameter root otsTable ftsTable cap
      (fun budget input frame state hit failed =>
        paidRemainingCoverageStepRefund exception parameter root otsTable ftsTable cap budget input frame state hit failed +
          signingEnvelopeStepGap (secretKey parameter root otsTable ftsTable) cap budget input frame state hit failed) := by
  intro budget input frame state hit failed hsigned hcache hcost hcap
  have hold := stepWithFailure_coverage_pairs_refund_le_reserved_add_residual exception parameter root otsTable ftsTable
    cap budget hcapMax input frame state hit failed hsigned hcache hcost hcap
  cases input with
  | inl world => simpa only [signingEnvelopeStepGap, add_zero] using hold
  | inr message =>
      by_cases hstop : (hit || failed) = true
      · simpa only [signingEnvelopeStepGap, survivingLogPotential, hstop, if_true, add_zero] using hold
      · have hh : hit = false := by cases hit <;> simp_all
        have hf : failed = false := by cases failed <;> simp_all
        subst hit
        subst failed
        by_cases hactive : ValidSigningStep state.2 (.inr message)
        · have hsignCap : ∀ result ∈ support ((simulateQ romImpl (sign (secretKey parameter root otsTable ftsTable) message)).run state.1),
              QueryCache.enncard result.2 ≤ cap := by
            simp only [OracleSpec.add_apply_inr, expandedAdversaryImpl, scheme] at hcap
            convert hcap using 1; rfl
          have hproject := stepWithFailure_sign_expect_surviving_le exception parameter root otsTable ftsTable
            message frame state false false (fun current => remainingCoveragePotential (secretKey parameter root otsTable ftsTable)
              cap (budget - signingExecutionHashCost (.inr message)) current ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹)
          have h := (add_le_add (add_le_add (add_le_add hproject le_rfl) le_rfl) le_rfl).trans
            (expected_surviving_sign_coverage_pairs_refund_gap_le_reserved_add_residual exception
              (secretKey parameter root otsTable ftsTable) cap budget hcapMax message state false hsigned hcache hcost hsignCap)
          simp only [beforeFailureSigningStepCharge, paidRemainingCoverageStepRefund, paidRemainingCoverageStepResidual,
            signingEnvelopeStepGap, survivingLogPotential, Bool.false_or, Bool.false_eq_true, if_false, if_pos hactive,
            add_assoc] at h ⊢
          convert h using 1 <;> rfl
        · simpa only [signingEnvelopeStepGap, survivingLogPotential, Bool.false_or, Bool.false_eq_true, if_false,
            signingCoverageEnvelopeGap, remainingRawIndexSigningGap, if_neg hactive, zero_mul, add_zero] using hold

noncomputable abbrev expectedSigningEnvelopeRefund
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α) :=
  expectedCoverageRefund exception parameter root otsTable ftsTable cap
    (fun budget input frame state hit failed =>
      paidRemainingCoverageStepRefund exception parameter root otsTable ftsTable cap budget input frame state hit failed +
        signingEnvelopeStepGap (secretKey parameter root otsTable ftsTable) cap budget input frame state hit failed) computation

theorem expected_runWithFailure_coverage_pairs_signingEnvelopeRefund_le
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (hcapMax : cap ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (hbound : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).IsQueryBoundP (· matches Sum.inr _) budget)
    (hsigned : SigningDigestsCached parameter state.1 root state.2)
    (hcache : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).run state),
      QueryCache.enncard result.2.1 ≤ cap) :
    (∑' result, Pr[= result | runWithFailure exception parameter root otsTable ftsTable
        (withSigningLog computation state.2) frame state.1 hit failed] *
      survivingLogPotential (fun current => cappedRemainingCachedTargetEnvelope (secretKey parameter root otsTable ftsTable)
        cap 0 current ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹)
          (result.1.2.1.2, result.1.2.1.1.2) result.1.2.2 result.2) +
      expectedSigningEnvelopeRefund exception parameter root otsTable ftsTable cap computation budget frame state hit failed +
      expectedBeforeFailureSigningCharge exception (encodingPairIncrementCharge (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable computation frame state.1 hit failed * (Fintype.card Digest : ENNReal)⁻¹ ≤
      survivingLogPotential (fun current => remainingCoveragePotential (secretKey parameter root otsTable ftsTable)
        cap budget current ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹) state hit failed +
        expectedBeforeFailureSigningCharge exception (nonMessageNonEncodingHashCharge parameter)
          parameter root otsTable ftsTable computation frame state.1 hit failed * (Fintype.card Digest : ENNReal)⁻¹ +
        expectedPaidCoverageResidual exception parameter root otsTable ftsTable cap computation budget frame state hit failed :=
  expected_runWithFailure_coverage_pairs_refund_of_step_le exception parameter root otsTable ftsTable cap budget _
    (coverageStepRefundBound_paid_add_signingEnvelopeGap exception parameter root otsTable ftsTable cap hcapMax)
    computation frame state hit failed hbound hsigned hcache

noncomputable abbrev expectedSigningEnvelopeGap
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α) :=
  expectedBudgetedLogCharge exception parameter root otsTable ftsTable (fun _ _ _ _ => 0)
    (signingEnvelopeStepGap (secretKey parameter root otsTable ftsTable) cap) computation

theorem expectedSigningEnvelopeRefund_eq_paid_add_gap
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (budget : Nat) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) :
    expectedSigningEnvelopeRefund exception parameter root otsTable ftsTable cap computation budget frame state hit failed =
      expectedPaidCoverageRefund exception parameter root otsTable ftsTable cap computation budget frame state hit failed +
        expectedSigningEnvelopeGap exception parameter root otsTable ftsTable cap computation budget frame state hit failed := by
  induction computation using OracleComp.inductionOn generalizing budget frame state hit failed with
  | pure value => simp only [expectedSigningEnvelopeRefund, expectedCoverageRefund, expectedPaidCoverageRefund,
      expectedSigningEnvelopeGap, expectedBudgetedLogCharge_pure, add_zero]
  | query_bind input next ih =>
      simp only [expectedSigningEnvelopeRefund, expectedCoverageRefund, expectedPaidCoverageRefund,
        expectedSigningEnvelopeGap, expectedBudgetedLogCharge_query_bind] at ih ⊢
      simp_rw [ih]
      simp only [mul_add, ENNReal.tsum_add]
      ring

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
