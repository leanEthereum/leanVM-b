import SphincsSecurity.Proof.StoppedSigningCoveragePayment

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

noncomputable def expectedBudgetedLogCharge
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (terminal : Nat → CoverLogState → Bool → Bool → ENNReal)
    (charge : Nat → (OracleWorld + SigningSpec).Domain → Option Frame → CoverLogState → Bool → Bool → ENNReal)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : Nat → Option Frame → CoverLogState → Bool → Bool → ENNReal :=
  OracleComp.construct (fun _ budget _ state hit failed => terminal budget state hit failed)
    (fun input _ next budget frame state hit failed =>
      charge budget input frame state hit failed +
        ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
          next result.1.2.1.1 (budget - signingExecutionHashCost input) result.1.1
            (stepSigningLogState input state.2 result) result.1.2.2 result.2) computation

@[simp] theorem expectedBudgetedLogCharge_pure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (terminal : Nat → CoverLogState → Bool → Bool → ENNReal)
    (charge : Nat → (OracleWorld + SigningSpec).Domain → Option Frame → CoverLogState → Bool → Bool → ENNReal)
    (value : α) (budget : Nat) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) :
    expectedBudgetedLogCharge exception parameter root otsTable ftsTable terminal charge (pure value) budget frame state hit failed =
      terminal budget state hit failed := rfl

theorem expectedBudgetedLogCharge_query_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (terminal : Nat → CoverLogState → Bool → Bool → ENNReal)
    (charge : Nat → (OracleWorld + SigningSpec).Domain → Option Frame → CoverLogState → Bool → Bool → ENNReal)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (budget : Nat) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) :
    expectedBudgetedLogCharge exception parameter root otsTable ftsTable terminal charge (OracleSpec.query input >>= next)
        budget frame state hit failed =
      charge budget input frame state hit failed +
        ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
          expectedBudgetedLogCharge exception parameter root otsTable ftsTable terminal charge (next result.1.2.1.1)
            (budget - signingExecutionHashCost input) result.1.1 (stepSigningLogState input state.2 result) result.1.2.2 result.2 := rfl

noncomputable abbrev expectedPaidCoverageRefund
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α) :=
  expectedBudgetedLogCharge exception parameter root otsTable ftsTable
    (fun budget state hit failed => survivingLogPotential (fun current => remainingCoverageTerminalReserve
      (secretKey parameter root otsTable ftsTable) cap budget current ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹) state hit failed)
    (paidRemainingCoverageStepRefund exception parameter root otsTable ftsTable cap) computation

noncomputable abbrev expectedPaidCoverageResidual
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α) :=
  expectedBudgetedLogCharge exception parameter root otsTable ftsTable (fun _ _ _ _ => 0)
    (fun budget input _ state hit failed => paidRemainingCoverageStepResidual
      (secretKey parameter root otsTable ftsTable) cap budget input state hit failed) computation

private theorem expected_add_credit_le (computation : SPMF α) (value credit risk after : α → ENNReal)
    (currentCredit before currentRisk : ENNReal)
    (htail : ∀ result ∈ support computation, value result + credit result ≤ after result + risk result)
    (hstep : (∑' result, Pr[= result | computation] * after result) + currentCredit ≤ before + currentRisk) :
    (∑' result, Pr[= result | computation] * value result) +
        (currentCredit + ∑' result, Pr[= result | computation] * credit result) ≤
      before + (currentRisk + ∑' result, Pr[= result | computation] * risk result) := by
  calc
    _ = (∑' result, Pr[= result | computation] * (value result + credit result)) + currentCredit := by
      simp only [mul_add, ENNReal.tsum_add]
      ring
    _ ≤ (∑' result, Pr[= result | computation] * (after result + risk result)) + currentCredit := by
      apply add_le_add _ le_rfl
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support computation
      · exact mul_le_mul' le_rfl (htail result hr)
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ = ((∑' result, Pr[= result | computation] * after result) + currentCredit) +
        ∑' result, Pr[= result | computation] * risk result := by
      simp only [mul_add, ENNReal.tsum_add]
      ring
    _ ≤ _ := (add_le_add hstep le_rfl).trans_eq (add_assoc _ _ _)

theorem simulateQ_logTraced_head_raw_cache_bound {α : Type} (key : SecretKey) (cap : Nat)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState)
    (hcap : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) (OracleSpec.query input >>= next)).run state),
      QueryCache.enncard result.2.1 ≤ cap) :
    ∀ result ∈ support ((simulateQ romImpl (expandedAdversaryImpl key input)).run state.1), QueryCache.enncard result.2 ≤ cap := by
  intro result hr
  have hlogged : (result.1, (result.2, state.2 ++ signingLogFragment input result.1)) ∈
      support ((logTracedMappedAdversaryImpl key input).run state) := by
    rw [logTracedMappedAdversaryImpl_run_map, support_map]
    refine ⟨result, ?_, rfl⟩
    rw [unloggedMappedAdversaryImpl_eq_simulateQ_expanded]
    exact hr
  exact simulateQ_logTraced_initial_cache_bound key cap (next result.1) _
    (simulateQ_logTraced_tail_cache_bound key cap input next state hcap _ hlogged)

theorem expected_runWithFailure_coverage_pairs_refund_le_reserved_add_residual
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (hcapMax : cap ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
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
      expectedPaidCoverageRefund exception parameter root otsTable ftsTable cap computation budget frame state hit failed +
      expectedBeforeFailureSigningCharge exception (encodingPairIncrementCharge (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable computation frame state.1 hit failed * (Fintype.card Digest : ENNReal)⁻¹ ≤
      survivingLogPotential (fun current => remainingCoveragePotential (secretKey parameter root otsTable ftsTable)
        cap budget current ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹) state hit failed +
        expectedBeforeFailureSigningCharge exception (nonMessageNonEncodingHashCharge parameter)
          parameter root otsTable ftsTable computation frame state.1 hit failed * (Fintype.card Digest : ENNReal)⁻¹ +
        expectedPaidCoverageResidual exception parameter root otsTable ftsTable cap computation budget frame state hit failed := by
  let key := secretKey parameter root otsTable ftsTable
  have hvalid : TargetShapeValid ∅ (Finset.univ : Finset FtsTree) := by constructor <;> simp
  induction computation using OracleComp.inductionOn generalizing budget frame state hit failed with
  | pure value =>
      simp only [withSigningLog_pure, runWithFailure_pure, tsum_probOutput_pure_mul,
        expectedPaidCoverageRefund, expectedPaidCoverageResidual, expectedBudgetedLogCharge_pure,
        expectedBeforeFailureSigningCharge_pure, zero_mul, add_zero, Prod.mk.eta]
      unfold survivingLogPotential
      split_ifs
      · simp only [zero_add, le_refl]
      · exact le_of_eq (by
          simpa only [add_mul] using
            congrArg (fun value => value * ((2 ^ 140 : Nat) : ENNReal)⁻¹)
              (remainingTarget_add_terminalReserve key cap budget state ∅ Finset.univ hvalid))
  | query_bind input next ih =>
      have htail := simulateQ_logTraced_tail_cache_bound key cap input next state hcache
      have hbefore := simulateQ_logTraced_initial_cache_bound key cap (OracleSpec.query input >>= next) state hcache
      have hcost : signingExecutionHashCost input ≤ budget := by
        obtain ⟨result, hr⟩ := simulateQ_logTraced_support_nonempty key (OracleSpec.query input) state
        rw [simulateQ_spec_query] at hr
        exact (expanded_query_bound_signing_execution key input next budget hbound state result hr).1
      have hstep := stepWithFailure_coverage_pairs_refund_le_reserved_add_residual exception parameter root otsTable ftsTable
        cap budget hcapMax input frame state hit failed hsigned hbefore hcost
        (simulateQ_logTraced_head_raw_cache_bound key cap input next state hcache)
      rw [withSigningLog_query_bind, runWithFailure_query_bind, tsum_probOutput_bind_mul]
      simp only [expectedPaidCoverageRefund, expectedPaidCoverageResidual, expectedBudgetedLogCharge_query_bind,
        expectedBeforeFailureSigningCharge_query_bind]
      have hcombined := expected_add_credit_le (stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed)
        (fun result => ∑' final, Pr[= final | runWithFailure exception parameter root otsTable ftsTable
          (withSigningLog (next result.1.2.1.1) (state.2 ++ signingLogFragment input result.1.2.1.1))
            result.1.1 result.1.2.1.2 result.1.2.2 result.2] *
              survivingLogPotential (fun current => cappedRemainingCachedTargetEnvelope key cap 0 current ∅ Finset.univ *
                ((2 ^ 140 : Nat) : ENNReal)⁻¹) (final.1.2.1.2, final.1.2.1.1.2) final.1.2.2 final.2)
        (fun result => expectedPaidCoverageRefund exception parameter root otsTable ftsTable cap (next result.1.2.1.1)
            (budget - signingExecutionHashCost input) result.1.1 (stepSigningLogState input state.2 result) result.1.2.2 result.2 +
          expectedBeforeFailureSigningCharge exception (encodingPairIncrementCharge key) parameter root otsTable ftsTable
            (next result.1.2.1.1) result.1.1 result.1.2.1.2 result.1.2.2 result.2 * (Fintype.card Digest : ENNReal)⁻¹)
        (fun result => expectedBeforeFailureSigningCharge exception (nonMessageNonEncodingHashCharge parameter) parameter root otsTable ftsTable
            (next result.1.2.1.1) result.1.1 result.1.2.1.2 result.1.2.2 result.2 * (Fintype.card Digest : ENNReal)⁻¹ +
          expectedPaidCoverageResidual exception parameter root otsTable ftsTable cap (next result.1.2.1.1)
            (budget - signingExecutionHashCost input) result.1.1 (stepSigningLogState input state.2 result) result.1.2.2 result.2)
        (fun result => survivingLogPotential (fun current => remainingCoveragePotential key cap
            (budget - signingExecutionHashCost input) current ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹)
          (stepSigningLogState input state.2 result) result.1.2.2 result.2)
        (paidRemainingCoverageStepRefund exception parameter root otsTable ftsTable cap budget input frame state hit failed +
          beforeFailureSigningStepCharge exception (encodingPairIncrementCharge key) key state.1 hit failed input * (Fintype.card Digest : ENNReal)⁻¹)
        (survivingLogPotential (fun current => remainingCoveragePotential key cap budget current ∅ Finset.univ *
          ((2 ^ 140 : Nat) : ENNReal)⁻¹) state hit failed)
        (beforeFailureSigningStepCharge exception (nonMessageNonEncodingHashCharge parameter) key state.1 hit failed input *
            (Fintype.card Digest : ENNReal)⁻¹ + paidRemainingCoverageStepResidual key cap budget input state hit failed)
        (by
          intro result hr
          have hlogged := stepWithFailure_logged_support exception parameter root otsTable ftsTable input frame state.1 state.2 hit failed result hr
          have h := ih result.1.2.1.1 (budget - signingExecutionHashCost input) result.1.1 (stepSigningLogState input state.2 result)
            result.1.2.2 result.2 (expanded_query_bound_signing_execution key input next budget hbound state _ hlogged).2
            (logTracedMappedAdversaryImpl_signingDigestsCached key input state hsigned _ hlogged) (htail _ hlogged)
          simpa only [stepSigningLogState, add_assoc] using h)
        (by convert hstep using 1 <;> ring)
      simp only [mul_add, ENNReal.tsum_add, ← mul_assoc, ENNReal.tsum_mul_right] at hcombined ⊢
      dsimp only [key, expectedPaidCoverageRefund, expectedPaidCoverageResidual] at hcombined
      convert hcombined using 1 <;> ring

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
