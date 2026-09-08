import SphincsSecurity.Proof.CoverageCompletionRetirement

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

private theorem min_one_le_min_one_add (before after gap : ENNReal) (h : before ≤ after + gap) :
    min 1 before ≤ min 1 after + gap := by
  by_cases ha : after ≤ 1
  · rw [min_eq_right ha]
    exact (min_le_right _ _).trans h
  · rw [min_eq_left (le_of_not_ge ha)]
    exact (min_le_left _ _).trans le_self_add

private theorem boundedUnion_tsub_le_gap (left before after gap : ENNReal) (h : before ≤ after + gap) :
    boundedUnionPotential left before - boundedUnionPotential left after ≤ gap := by
  apply tsub_le_iff_left.mpr
  rw [boundedUnionPotential_comm left before, boundedUnionPotential_comm left after]
  unfold boundedUnionPotential
  calc
    _ ≤ min 1 left + (1 - min 1 left) * (min 1 after + gap) :=
      add_le_add le_rfl (mul_le_mul' le_rfl (min_one_le_min_one_add before after gap h))
    _ ≤ _ := by
      rw [mul_add, ← add_assoc]
      exact add_le_add le_rfl (mul_le_of_le_one_left' tsub_le_self)

namespace FtsProbeSimulation.JointOriginal

open OtsProbeSimulation (OtsSecretIndex)

theorem jointCollisionCoverageHashCredit_le_unused
    (key : SecretKey) (cap budget : Nat) (input : HashInput) (state : CoverLogState) (hbudget : 1 ≤ budget) :
    jointCollisionCoverageHashCredit key cap budget input state ≤
      remainingUnusedCoverageStepCharge key cap budget state (.inl (.inr input)) ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ := by
  unfold jointCollisionCoverageHashCredit
  split_ifs with hm
  · exact zero_le
  · apply (mul_le_of_le_one_right' tsub_le_self).trans
    apply tsub_le_iff_left.mpr
    apply min_one_le_min_one_add
    have h := congrArg (fun value : ENNReal => value * ((2 ^ 140 : Nat) : ENNReal)⁻¹)
      (remainingCoveragePotential_add_budgetGap key cap budget hbudget state ∅ Finset.univ (by constructor <;> simp))
    have hu : unusedTargetExecutionCost key.parameter state.1 (.inl (.inr input)) = 1 := by
      simp only [unusedTargetExecutionCost, unusedSigningExecutionCost, unusedTargetHashCost, targetArrivalHashCost,
        freshWorldTargetHashCost, hm, false_and, if_false, signingMacroHashCost, Nat.sub_zero, Nat.add_zero]
    simpa only [remainingUnusedCoverageStepCharge, hm, false_and, if_false, hu, Nat.cast_one, mul_one, add_mul]
      using h.symm.le

theorem jointSigningCoverageCredit_le_unused
    (key : SecretKey) (cap budget : Nat) (message : Message) (state : CoverLogState) :
    jointSigningCoverageCredit key cap budget message state ≤
      remainingUnusedCoverageStepCharge key cap budget state (.inr message) ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ := by
  unfold jointSigningCoverageCredit
  split_ifs
  · exact mul_le_of_le_one_left' tsub_le_self
  · exact zero_le

theorem jointCollisionCoverageTerminalCredit_le_unused_add_exhaustion
    (key : SecretKey) (cap budget : Nat) (state : CoverLogState) (hit failed : Bool) :
    jointCollisionCoverageTerminalCredit key cap budget state hit failed ≤
      survivingLogPotential (fun current => remainingCoverageTerminalReserve key cap budget current ∅ Finset.univ) state hit failed *
        ((2 ^ 140 : Nat) : ENNReal)⁻¹ + encodingExhaustionBudgetReserve budget state.1 := by
  unfold jointCollisionCoverageTerminalCredit
  apply add_le_add ?_ le_rfl
  by_cases hstop : (hit || failed) = true
  · rw [jointCollisionCoveragePotential_eq_one_of_stopped _ _ _ _ _ _ hstop,
      jointCollisionCoveragePotential_eq_one_of_stopped _ _ _ _ _ _ hstop, tsub_self]
    exact zero_le
  · simp only [survivingLogPotential, hstop, Bool.false_eq_true, if_false]
    unfold jointCollisionCoveragePotential
    apply boundedUnion_tsub_le_gap
    have h := congrArg (fun value : ENNReal => value * ((2 ^ 140 : Nat) : ENNReal)⁻¹)
      (remainingTarget_add_terminalReserve key cap budget state ∅ Finset.univ (by constructor <;> simp))
    simpa only [remainingCoveragePotential, Nat.cast_zero, mul_zero, zero_mul, add_zero, add_mul] using h.symm.le

theorem jointCollisionCoverageStepCredit_le_unused_add_exhaustion
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : (OracleWorld + SigningSpec).Domain)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) (hcost : signingExecutionHashCost input ≤ budget) :
    jointCollisionCoverageBudgetStepCredit (secretKey parameter root otsTable ftsTable) cap budget input state hit failed ≤
      stoppedRemainingCoverageStepCharge (parentException parameter otsTable ftsTable)
        parameter root otsTable ftsTable cap budget input frame state hit failed ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ +
      (signingExecutionHashCost input : ENNReal) * encodingExhaustionTotalPotential state.1 := by
  by_cases hstop : (hit || failed) = true
  · simp only [jointCollisionCoverageBudgetStepCredit, hstop, if_true, zero_le]
  · simp only [jointCollisionCoverageBudgetStepCredit, hstop, Bool.false_eq_true, if_false]
    apply le_trans ?_ (add_le_add (mul_le_mul' le_self_add le_rfl) le_rfl)
    simp only [survivingLogPotential, hstop, Bool.false_eq_true, if_false]
    cases input with
    | inl world =>
        cases world with
        | inl sample => exact zero_le
        | inr hash =>
            simpa only [signingExecutionHashCost, Nat.cast_one, one_mul] using
              add_le_add (jointCollisionCoverageHashCredit_le_unused (secretKey parameter root otsTable ftsTable)
                cap budget hash state hcost) (le_refl (encodingExhaustionTotalPotential state.1))
    | inr message =>
        exact (jointSigningCoverageCredit_le_unused (secretKey parameter root otsTable ftsTable) cap budget message state).trans le_self_add

theorem expectedJointCollisionCoverageCredit_le_unused_add_exhaustion
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (hbound : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).IsQueryBoundP (· matches Sum.inr _) budget) :
    expectedJointCollisionCoverageCredit parameter root otsTable ftsTable cap computation budget frame state hit failed ≤
      expectedRemainingUnusedCoverageCharge (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable cap ∅ Finset.univ
        computation budget frame state hit failed * ((2 ^ 140 : Nat) : ENNReal)⁻¹ + encodingExhaustionBudgetReserve budget state.1 := by
  let key := secretKey parameter root otsTable ftsTable
  let exception := parentException parameter otsTable ftsTable
  induction computation using OracleComp.inductionOn generalizing budget frame state hit failed with
  | pure value =>
      simp only [expectedJointCollisionCoverageCredit, construct_pure, expectedRemainingUnusedCoverageCharge_pure]
      exact jointCollisionCoverageTerminalCredit_le_unused_add_exhaustion key cap budget state hit failed
  | query_bind input next ih =>
      have hcost : signingExecutionHashCost input ≤ budget := by
        obtain ⟨result, hr⟩ := simulateQ_logTraced_support_nonempty key (OracleSpec.query input) state
        rw [simulateQ_spec_query] at hr
        exact (expanded_query_bound_signing_execution key input next budget hbound state result hr).1
      rw [expectedJointCollisionCoverageCredit, construct_query_bind]
      calc
        _ ≤ (stoppedRemainingCoverageStepCharge exception parameter root otsTable ftsTable cap budget input frame state hit failed ∅ Finset.univ *
            ((2 ^ 140 : Nat) : ENNReal)⁻¹ + (signingExecutionHashCost input : ENNReal) * encodingExhaustionTotalPotential state.1) +
            ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
              (expectedRemainingUnusedCoverageCharge exception parameter root otsTable ftsTable cap ∅ Finset.univ
                  (next result.1.2.1.1) (budget - signingExecutionHashCost input) result.1.1
                    (stepSigningLogState input state.2 result) result.1.2.2 result.2 * ((2 ^ 140 : Nat) : ENNReal)⁻¹ +
                encodingExhaustionBudgetReserve (budget - signingExecutionHashCost input) result.1.2.1.2) := by
          apply add_le_add (jointCollisionCoverageStepCredit_le_unused_add_exhaustion parameter root otsTable ftsTable
            cap budget input frame state hit failed hcost)
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed)
          · have hlogged := stepWithFailure_logged_support exception parameter root otsTable ftsTable input frame state.1 state.2 hit failed result hr
            exact mul_le_mul' le_rfl (ih result.1.2.1.1 (budget - signingExecutionHashCost input) result.1.1
              (stepSigningLogState input state.2 result) result.1.2.2 result.2
                (expanded_query_bound_signing_execution key input next budget hbound state _ hlogged).2)
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
        _ = _ := by
          simp only [expectedRemainingUnusedCoverageCharge_query_bind, add_mul, mul_add, ENNReal.tsum_add,
            ← mul_assoc, ENNReal.tsum_mul_right]
          rw [← expected_stepWithFailure_exhaustionReserve_add_cost_eq exception parameter root otsTable ftsTable
            input frame state.1 hit failed budget _ hcost]
          ring

theorem initializedJointCollisionCoverageCredit_le_unused_add_exhaustion
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    initializedJointCollisionCoverageCredit adversary parameter otsTable ftsTable q fuel ≤
      initializedRemainingUnusedCoverageCharge adversary parameter otsTable ftsTable q fuel + encodingExhaustionBudgetReserve q ∅ := by
  unfold initializedJointCollisionCoverageCredit initializedRemainingUnusedCoverageCharge
  rw [← expected_initializeRoot_encodingExhaustionReserve parameter otsTable ftsTable q fuel, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro initial
  rw [← mul_add]
  by_cases hi : initial ∈ support (initializeRoot parameter otsTable ftsTable q fuel)
  · let key := secretKey parameter initial.2.1 otsTable ftsTable
    have hroot := initializeRoot_original_support parameter otsTable ftsTable q fuel initial hi
    rw [originalRoot, simulateQ_romImpl_liftM] at hroot
    have hgame := isQueryBoundP_gameAfterSecrets adversary q hq hp
      (OtsProbeSimulation.mem_support_sampleOtsSecrets_all key.otsSecret) hfts
    have hbound := retainedRoot_expanded_rest_queryBound adversary parameter key.otsSecret ftsTable q hgame initial.2 hroot
    exact mul_le_mul' le_rfl (expectedJointCollisionCoverageCredit_le_unused_add_exhaustion parameter initial.2.1 otsTable ftsTable q q
      (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) initial.1 (initial.2.2, []) false initial.1.isNone hbound)
  · rw [probOutput_eq_zero_of_not_mem_support hi, zero_mul, zero_mul]

theorem sampledJointCollisionCoverageCredit_le_unused_add_exhaustion
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    sampledJointCollisionCoverageCredit adversary q fuel ≤
      sampledRemainingUnusedCoverageCharge adversary q fuel + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  rw [add_comm]
  unfold sampledJointCollisionCoverageCredit sampledRemainingUnusedCoverageCharge
  apply coverage_expected_le_constant_add
  intro parameter hp
  apply coverage_expected_le_constant_add
  intro ftsSecret hfts
  apply coverage_expected_le_constant_add
  intro table _
  exact ((initializedJointCollisionCoverageCredit_le_unused_add_exhaustion adversary q hq parameter hp table
    (curryFtsTableEquiv ftsSecret) hfts fuel).trans
      (add_le_add le_rfl (encodingExhaustionBudgetReserve_initial_le q))).trans_eq (add_comm _ _)

theorem sampled_jointCredit_add_signingAfterPairs_add_completion_le_retiredNetRefund_add_exhaustion
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledJointCollisionCoverageCredit adversary q fuel +
      sampledSigningNonEncodingReserveAfterPairs adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledJointCollisionCoverageCompletionCredit adversary q fuel ≤
      sampledRetiredNetCoverageRefund adversary q fuel + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  have h := add_le_add (add_le_add (sampledJointCollisionCoverageCredit_le_unused_add_exhaustion adversary q hq fuel)
    (le_refl (sampledSigningNonEncodingReserveAfterPairs adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹)))
    (le_refl (sampledJointCollisionCoverageCompletionCredit adversary q fuel))
  apply le_trans ?_ (add_le_add
    (sampled_remainingUnused_add_signingAfterPairs_add_completion_le_retiredNetRefund adversary q hq hqMax fuel)
    (le_refl ((q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹)))
  convert h using 1
  ring

end FtsProbeSimulation.JointOriginal
end SphincsSecurity.Concrete
