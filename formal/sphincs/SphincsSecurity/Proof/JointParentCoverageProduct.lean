import SphincsSecurity.Proof.ParentCoverageProduct
import SphincsSecurity.Proof.JointOverlapParentRun

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem step_parentCoverageProduct_le
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (hcap : cap ≤ 2 ^ 127) (input : (OracleWorld + SigningSpec).Domain)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (hsigned : SigningDigestsCached parameter state.1 root state.2) (hcache : QueryCache.enncard state.1 ≤ cap)
    (hcost : signingExecutionHashCost input ≤ budget) :
    (∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      input frame state.1 hit failed] * survivingLogPotential (parentCoverageProduct (secretKey parameter root otsTable ftsTable)
        cap (budget - signingExecutionHashCost input)) (stepSigningLogState input state.2 result) result.1.2.2 result.2) ≤
      survivingLogPotential (parentCoverageProduct (secretKey parameter root otsTable ftsTable) cap budget) state hit failed +
        jointCollisionCoverageStepAfterParentRefund parameter root otsTable ftsTable cap budget input frame state hit failed := by
  let key := secretKey parameter root otsTable ftsTable
  have h := stepWithFailure_expect_surviving_le (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
    input frame state hit failed (parentCoverageProduct key cap (budget - signingExecutionHashCost input)) _ le_rfl
  apply h.trans
  by_cases hstop : (hit || failed) = true
  · simp only [survivingLogPotential, jointCollisionCoverageStepAfterParentRefund, if_pos hstop, zero_add, le_refl]
  · obtain ⟨rfl, rfl⟩ := Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hstop)
    simp only [survivingLogPotential, jointCollisionCoverageStepAfterParentRefund, Bool.false_or, Bool.false_eq_true, if_false]
    cases input with
    | inr message =>
        exact (expected_parentCoverageProduct_sign_le key cap budget hcap state hsigned hcache message hcost).trans le_self_add
    | inl world =>
        cases world with
        | inl n =>
            have hparent : (logTracedMappedAdversaryImpl key (.inl (.inl n))).run state =
                (fun answer => (answer, state)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
              rw [logTracedMappedAdversaryImpl_run_map]
              simp only [unloggedMappedAdversaryImpl, signingLogFragment, List.append_nil]
              rfl
            rw [hparent, tsum_probOutput_map_mul]
            simp only [signingExecutionHashCost, Nat.sub_zero, add_zero, ENNReal.tsum_mul_right]
            exact mul_le_of_le_one_left' tsum_probOutput_le_one
        | inr hash =>
            dsimp only
            by_cases hm : MessageHashInput parameter hash
            · rw [if_pos hm, zero_add]
              exact (expected_parentCoverageProduct_message_le key cap budget hcap state hsigned hcache hash hm hcost).trans le_self_add
            · rw [if_neg hm]
              have hraw : expectedPreExceptionCharge (parentException parameter otsTable ftsTable) (collisionSigningStructuralCharge key)
                  (expandedAdversaryImpl key (.inl (.inr hash))) state.1 false = collisionSigningStructuralCharge key state.1 hash := by
                change expectedPreExceptionCharge _ _ ((liftM (OracleWorld.query (Sum.inr hash)) : OracleComp OracleWorld _) >>= pure) state.1 false = _
                simp only [expectedPreExceptionCharge_query_bind, Bool.false_eq_true, if_false, hashQueryCharge, Sum.elim_inr,
                  expectedPreExceptionCharge_pure, mul_zero, tsum_zero, add_zero]
              rw [hraw]
              exact (expected_parentCoverageProduct_nonmessage_le key cap budget state hsigned hash hm).trans
                (add_le_add le_rfl le_self_add)

theorem expected_parentCoverageProduct_le_afterParentRefund
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (hcap : cap ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (hbudget : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).IsQueryBoundP
      (· matches Sum.inr _) budget)
    (hsigned : SigningDigestsCached parameter state.1 root state.2)
    (hcache : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).run state),
      QueryCache.enncard result.2.1 ≤ cap) :
    (∑' result, Pr[= result | runWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      (withSigningLog computation state.2) frame state.1 hit failed] *
        survivingLogPotential (parentCoverageProduct (secretKey parameter root otsTable ftsTable) cap 0)
          (result.1.2.1.2, result.1.2.1.1.2) result.1.2.2 result.2) ≤
      survivingLogPotential (parentCoverageProduct (secretKey parameter root otsTable ftsTable) cap budget) state hit failed +
        expectedJointCollisionCoverageAfterParentRefund parameter root otsTable ftsTable cap computation budget frame state hit failed := by
  let key := secretKey parameter root otsTable ftsTable
  let exception := parentException parameter otsTable ftsTable
  induction computation using OracleComp.inductionOn generalizing budget frame state hit failed with
  | pure value =>
      simp only [withSigningLog_pure, runWithFailure_pure, tsum_probOutput_pure_mul, Prod.mk.eta,
        expectedJointCollisionCoverageAfterParentRefund, construct_pure, add_zero]
      unfold survivingLogPotential
      split_ifs
      · exact le_rfl
      · exact parentCoverageProduct_budget_mono key cap state (Nat.zero_le budget)
  | query_bind input next ih =>
      have htail := simulateQ_logTraced_tail_cache_bound key cap input next state hcache
      have hbefore := simulateQ_logTraced_initial_cache_bound key cap (OracleSpec.query input >>= next) state hcache
      have hcost : signingExecutionHashCost input ≤ budget := by
        obtain ⟨result, hr⟩ := simulateQ_logTraced_support_nonempty key (OracleSpec.query input) state
        rw [simulateQ_spec_query] at hr
        exact (expanded_query_bound_signing_execution key input next budget hbudget state result hr).1
      have hstep := step_parentCoverageProduct_le parameter root otsTable ftsTable cap budget hcap input frame state hit failed hsigned hbefore hcost
      rw [withSigningLog_query_bind, runWithFailure_query_bind, tsum_probOutput_bind_mul]
      simp only [expectedJointCollisionCoverageAfterParentRefund, construct_query_bind]
      rw [← add_assoc]
      apply le_trans ?_ (add_le_add hstep le_rfl)
      rw [← ENNReal.tsum_add]
      apply ENNReal.tsum_le_tsum
      intro result
      rw [← mul_add]
      by_cases hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed)
      · have hlogged := stepWithFailure_logged_support exception parameter root otsTable ftsTable input frame state.1 state.2 hit failed result hr
        exact mul_le_mul' le_rfl (ih result.1.2.1.1 (budget - signingExecutionHashCost input) result.1.1
          (stepSigningLogState input state.2 result) result.1.2.2 result.2
          (expanded_query_bound_signing_execution key input next budget hbudget state _ hlogged).2
          (logTracedMappedAdversaryImpl_signingDigestsCached key input state hsigned _ hlogged) (htail _ hlogged))
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
