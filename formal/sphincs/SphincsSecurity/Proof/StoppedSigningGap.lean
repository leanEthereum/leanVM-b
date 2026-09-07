import SphincsSecurity.Proof.SigningRawIndexGap
import SphincsSecurity.Proof.StoppedBudgetRemainder

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

noncomputable def expectedStoppedSigningGap
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap : Nat) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : Nat → Option Frame → CoverLogState → Bool → Bool → ENNReal :=
  OracleComp.construct (fun _ _ _ _ _ _ => 0)
    (fun input _ next budget frame state hit failed =>
      survivingLogPotential (fun current => ((budget - signingExecutionHashCost input : Nat) : ENNReal) *
        cappedRawIndexStepGap (secretKey parameter root otsTable ftsTable) cap current input groups remaining) state hit failed +
      ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
        next result.1.2.1.1 (budget - signingExecutionHashCost input) result.1.1
          (stepSigningLogState input state.2 result) result.1.2.2 result.2) computation

@[simp] theorem expectedStoppedSigningGap_pure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap : Nat) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (value : α) (budget : Nat) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) :
    expectedStoppedSigningGap exception parameter root otsTable ftsTable cap groups remaining (pure value) budget frame state hit failed = 0 := rfl

theorem expectedStoppedSigningGap_query_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap : Nat) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (budget : Nat) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) :
    expectedStoppedSigningGap exception parameter root otsTable ftsTable cap groups remaining (OracleSpec.query input >>= next) budget frame state hit failed =
      survivingLogPotential (fun current => ((budget - signingExecutionHashCost input : Nat) : ENNReal) *
        cappedRawIndexStepGap (secretKey parameter root otsTable ftsTable) cap current input groups remaining) state hit failed +
      ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
        expectedStoppedSigningGap exception parameter root otsTable ftsTable cap groups remaining (next result.1.2.1.1)
          (budget - signingExecutionHashCost input) result.1.1 (stepSigningLogState input state.2 result) result.1.2.2 result.2 := rfl

theorem expectedStoppedSigningGap_of_stopped
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap : Nat) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (budget : Nat) (frame : Option Frame) (state : CoverLogState)
    (hit failed : Bool) (hstop : (hit || failed) = true) :
    expectedStoppedSigningGap exception parameter root otsTable ftsTable cap groups remaining computation budget frame state hit failed = 0 := by
  induction computation using OracleComp.inductionOn generalizing budget frame state hit failed with
  | pure value => rfl
  | query_bind input next ih =>
      rw [expectedStoppedSigningGap_query_bind, survivingLogPotential, if_pos hstop, zero_add]
      apply ENNReal.tsum_eq_zero.mpr
      intro result
      by_cases hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed)
      · rw [ih result.1.2.1.1 (budget - signingExecutionHashCost input) result.1.1 (stepSigningLogState input state.2 result) result.1.2.2 result.2
          (stepWithFailure_stopped exception parameter root otsTable ftsTable input frame state.1 hit failed hstop result hr), mul_zero]
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]

theorem expectedStoppedExecutionCharge_add_remainder_gap_le_queryBudget
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap : Nat) (hcap : cap ≤ 2 ^ 127) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (hvalid : TargetShapeValid groups remaining) (computation : OracleComp (OracleWorld + SigningSpec) α) (budget : Nat)
    (hbound : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).IsQueryBoundP (· matches Sum.inr _) budget)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (hsigned : SigningDigestsCached parameter state.1 root state.2)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).run state),
      QueryCache.enncard result.2.1 ≤ cap) :
    expectedStoppedIndexCharge exception parameter root otsTable ftsTable cap (fun _ => signingExecutionHashCost)
        groups remaining computation frame state hit failed +
      expectedStoppedBudgetRemainder exception (fun current => cappedRawIndexCacheEnvelope (secretKey parameter root otsTable ftsTable) cap current groups remaining)
        parameter root otsTable ftsTable computation budget frame state hit failed +
      expectedStoppedSigningGap exception parameter root otsTable ftsTable cap groups remaining computation budget frame state hit failed ≤
      (budget : ENNReal) * cappedRawIndexCacheEnvelope (secretKey parameter root otsTable ftsTable) cap state groups remaining := by
  let key := secretKey parameter root otsTable ftsTable
  let potential := fun current => cappedRawIndexCacheEnvelope key cap current groups remaining
  induction computation using OracleComp.inductionOn generalizing budget frame state hit failed with
  | pure value => simp only [expectedStoppedIndexCharge, expectedStoppedLogCharge_pure, expectedStoppedBudgetRemainder_pure,
      expectedStoppedSigningGap_pure, zero_add, add_zero, le_refl]
  | query_bind input next ih =>
      by_cases hstop : (hit || failed) = true
      · rw [expectedStoppedIndexCharge, expectedStoppedLogCharge_of_stopped _ _ _ _ _ _ _ _ _ _ _ hstop,
          expectedStoppedBudgetRemainder_of_stopped _ _ _ _ _ _ _ _ _ _ _ _ hstop,
          expectedStoppedSigningGap_of_stopped _ _ _ _ _ _ _ _ _ _ _ _ _ _ hstop, zero_add, add_zero]
      · have htail := simulateQ_logTraced_tail_cache_bound key cap input next state hbudget
        have hbefore := simulateQ_logTraced_initial_cache_bound key cap (OracleSpec.query input >>= next) state hbudget
        have hstep := expected_logTraced_cappedRawIndex_add_gap_le key cap hcap state hsigned hbefore input
          (fun result hr => simulateQ_logTraced_initial_cache_bound key cap (next result.1) result.2 (htail result hr)) groups remaining hvalid
        have hcost : signingExecutionHashCost input ≤ budget := by
          obtain ⟨result, hr⟩ := simulateQ_logTraced_support_nonempty key (OracleSpec.query input) state
          rw [simulateQ_spec_query] at hr
          exact (expanded_query_bound_signing_execution key input next budget hbound state result hr).1
        simp only [expectedStoppedIndexCharge] at ih ⊢
        rw [expectedStoppedLogCharge_query_bind, expectedStoppedBudgetRemainder_query_bind, expectedStoppedSigningGap_query_bind,
          if_neg hstop, survivingLogPotential, if_neg hstop, survivingLogPotential, if_neg hstop]
        rw [show ∀ a b c d e : ENNReal, a + b + c + (d + e) = a + ((b + c + e) + d) from fun _ _ _ _ _ => by ac_rfl]
        rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
        have hrest : (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
            (((budget - signingExecutionHashCost input : Nat) : ENNReal) * potential (stepSigningLogState input state.2 result))) +
            ((budget - signingExecutionHashCost input : Nat) : ENNReal) * cappedRawIndexStepGap key cap state input groups remaining ≤
            ((budget - signingExecutionHashCost input : Nat) : ENNReal) * potential state := by
          simp_rw [mul_left_comm (Pr[= _ | _])]
          rw [ENNReal.tsum_mul_left, ← mul_add, stepWithFailure_expect_logged exception parameter root otsTable ftsTable input frame state.1 state.2 hit failed (fun _ => potential)]
          exact mul_le_mul' le_rfl hstep
        have hsum : (∑' result, (Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
            expectedStoppedLogCharge exception (fun current input => (signingExecutionHashCost input : ENNReal) * potential current)
              parameter root otsTable ftsTable (next result.1.2.1.1) result.1.1 (stepSigningLogState input state.2 result) result.1.2.2 result.2 +
            Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
              expectedStoppedBudgetRemainder exception potential parameter root otsTable ftsTable (next result.1.2.1.1)
                (budget - signingExecutionHashCost input) result.1.1 (stepSigningLogState input state.2 result) result.1.2.2 result.2 +
            Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
              expectedStoppedSigningGap exception parameter root otsTable ftsTable cap groups remaining (next result.1.2.1.1)
                (budget - signingExecutionHashCost input) result.1.1 (stepSigningLogState input state.2 result) result.1.2.2 result.2)) ≤
            ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
              (((budget - signingExecutionHashCost input : Nat) : ENNReal) * potential (stepSigningLogState input state.2 result)) := by
          apply ENNReal.tsum_le_tsum
          intro result
          rw [← mul_add, ← mul_add]
          by_cases hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed)
          · have hl := stepWithFailure_logged_support exception parameter root otsTable ftsTable input frame state.1 state.2 hit failed result hr
            exact mul_le_mul' le_rfl (ih result.1.2.1.1 (budget - signingExecutionHashCost input)
              (expanded_query_bound_signing_execution key input next budget hbound state _ hl).2 result.1.1
              (stepSigningLogState input state.2 result) result.1.2.2 result.2
              (logTracedMappedAdversaryImpl_signingDigestsCached key input state hsigned _ hl) (htail _ hl))
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
        apply (add_le_add le_rfl ((add_le_add hsum le_rfl).trans hrest)).trans_eq
        change (signingExecutionHashCost input : ENNReal) * potential state +
          ((budget - signingExecutionHashCost input : Nat) : ENNReal) * potential state = (budget : ENNReal) * potential state
        rw [← add_mul, ← Nat.cast_add, Nat.add_sub_of_le hcost]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
