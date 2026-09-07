import SphincsSecurity.Proof.StoppedExecutionReserve

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

noncomputable def expectedStoppedBudgetRemainder
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (potential : CoverLogState → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : Nat → Option Frame → CoverLogState → Bool → Bool → ENNReal :=
  OracleComp.construct (fun _ budget _ state _ _ => (budget : ENNReal) * potential state)
    (fun input _ next budget frame state hit failed =>
      if hit || failed then (budget : ENNReal) * potential state else
        ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
          next result.1.2.1.1 (budget - signingExecutionHashCost input) result.1.1
            (stepSigningLogState input state.2 result) result.1.2.2 result.2) computation

@[simp] theorem expectedStoppedBudgetRemainder_pure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (potential : CoverLogState → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (value : α) (budget : Nat) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) :
    expectedStoppedBudgetRemainder exception potential parameter root otsTable ftsTable (pure value) budget frame state hit failed =
      (budget : ENNReal) * potential state := rfl

theorem expectedStoppedBudgetRemainder_query_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (potential : CoverLogState → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (budget : Nat) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) :
    expectedStoppedBudgetRemainder exception potential parameter root otsTable ftsTable (OracleSpec.query input >>= next) budget frame state hit failed =
      if hit || failed then (budget : ENNReal) * potential state else
        ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
          expectedStoppedBudgetRemainder exception potential parameter root otsTable ftsTable (next result.1.2.1.1)
            (budget - signingExecutionHashCost input) result.1.1 (stepSigningLogState input state.2 result) result.1.2.2 result.2 := rfl

theorem expectedStoppedLogCharge_of_stopped
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : CoverLogState → (OracleWorld + SigningSpec).Domain → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (state : CoverLogState)
    (hit failed : Bool) (hstop : (hit || failed) = true) :
    expectedStoppedLogCharge exception charge parameter root otsTable ftsTable computation frame state hit failed = 0 := by
  induction computation using OracleComp.inductionOn generalizing frame state hit failed with
  | pure value => rfl
  | query_bind input next ih =>
      rw [expectedStoppedLogCharge_query_bind, survivingLogPotential, if_pos hstop, zero_add]
      apply ENNReal.tsum_eq_zero.mpr
      intro result
      by_cases hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed)
      · rw [ih result.1.2.1.1 result.1.1 (stepSigningLogState input state.2 result) result.1.2.2 result.2
          (stepWithFailure_stopped exception parameter root otsTable ftsTable input frame state.1 hit failed hstop result hr), mul_zero]
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]

theorem expectedStoppedBudgetRemainder_of_stopped
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (potential : CoverLogState → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (budget : Nat) (frame : Option Frame) (state : CoverLogState)
    (hit failed : Bool) (hstop : (hit || failed) = true) :
    expectedStoppedBudgetRemainder exception potential parameter root otsTable ftsTable computation budget frame state hit failed =
      (budget : ENNReal) * potential state := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next _ => rw [expectedStoppedBudgetRemainder_query_bind, if_pos hstop]

theorem expectedStoppedExecutionCharge_add_remainder_le_queryBudget
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
        parameter root otsTable ftsTable computation budget frame state hit failed ≤
      (budget : ENNReal) * cappedRawIndexCacheEnvelope (secretKey parameter root otsTable ftsTable) cap state groups remaining := by
  let key := secretKey parameter root otsTable ftsTable
  let potential := fun current => cappedRawIndexCacheEnvelope key cap current groups remaining
  induction computation using OracleComp.inductionOn generalizing budget frame state hit failed with
  | pure value => simp only [expectedStoppedIndexCharge, expectedStoppedLogCharge_pure, expectedStoppedBudgetRemainder_pure, zero_add, le_refl]
  | query_bind input next ih =>
      by_cases hstop : (hit || failed) = true
      · rw [expectedStoppedIndexCharge, expectedStoppedLogCharge_of_stopped _ _ _ _ _ _ _ _ _ _ _ hstop,
          expectedStoppedBudgetRemainder_of_stopped _ _ _ _ _ _ _ _ _ _ _ _ hstop, zero_add]
      · have htail := simulateQ_logTraced_tail_cache_bound key cap input next state hbudget
        have hbefore := simulateQ_logTraced_initial_cache_bound key cap (OracleSpec.query input >>= next) state hbudget
        have hstep := expected_logTraced_cappedRawIndexCacheEnvelope_le key cap hcap state hsigned hbefore input
          (fun result hr => simulateQ_logTraced_initial_cache_bound key cap (next result.1) result.2 (htail result hr)) groups remaining hvalid
        have hcost : signingExecutionHashCost input ≤ budget := by
          obtain ⟨result, hr⟩ := simulateQ_logTraced_support_nonempty key (OracleSpec.query input) state
          rw [simulateQ_spec_query] at hr
          exact (expanded_query_bound_signing_execution key input next budget hbound state result hr).1
        simp only [expectedStoppedIndexCharge] at ih ⊢
        rw [expectedStoppedLogCharge_query_bind, expectedStoppedBudgetRemainder_query_bind, if_neg hstop,
          survivingLogPotential, if_neg hstop, add_assoc, ← ENNReal.tsum_add]
        have hrest : (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
            (((budget - signingExecutionHashCost input : Nat) : ENNReal) * potential (stepSigningLogState input state.2 result))) ≤
            ((budget - signingExecutionHashCost input : Nat) : ENNReal) * potential state := by
          simp_rw [mul_left_comm (Pr[= _ | _])]
          rw [ENNReal.tsum_mul_left, stepWithFailure_expect_logged exception parameter root otsTable ftsTable input frame state.1 state.2 hit failed (fun _ => potential)]
          exact mul_le_mul' le_rfl hstep
        apply le_trans (add_le_add le_rfl (le_trans (ENNReal.tsum_le_tsum (fun result => ?_)) hrest))
        · change (signingExecutionHashCost input : ENNReal) * potential state +
            ((budget - signingExecutionHashCost input : Nat) : ENNReal) * potential state ≤ (budget : ENNReal) * potential state
          rw [← add_mul, ← Nat.cast_add, Nat.add_sub_of_le hcost]
        · rw [← mul_add]
          by_cases hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed)
          · have hl := stepWithFailure_logged_support exception parameter root otsTable ftsTable input frame state.1 state.2 hit failed result hr
            exact mul_le_mul' le_rfl (ih result.1.2.1.1 (budget - signingExecutionHashCost input)
              (expanded_query_bound_signing_execution key input next budget hbound state _ hl).2 result.1.1
              (stepSigningLogState input state.2 result) result.1.2.2 result.2
              (logTracedMappedAdversaryImpl_signingDigestsCached key input state hsigned _ hl) (htail _ hl))
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
