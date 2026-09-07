import SphincsSecurity.Proof.CollisionAnswerEncodingQueryBound
import SphincsSecurity.Proof.PreExceptionQueryCharge
import SphincsSecurity.Proof.OtsProbeNativeRootQueryCharge

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] validCacheEntries
set_option backward.isDefEq.respectTransparency false

theorem expected_collisionAnswerEncodingMonitorPotential_le_preExceptionCharge
    (secretKey : SecretKey) (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit : Bool) :
    (∑' result, Pr[= result | runExceptionMonitor
        (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret) computation cache hit] *
      collisionAnswerEncodingMonitorPotential secretKey result.1.2 result.2) ≤
      collisionAnswerEncodingMonitorPotential secretKey cache hit +
        expectedPreExceptionCharge (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret)
          (collisionParentStoppedEncodingQueryCharge secretKey) computation cache hit * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [← expectedPreExceptionCharge_mul]
  apply expected_runExceptionMonitor_potential_le_preExceptionCharge _ _ _ ?_ computation cache hfinite hit
  intro query cache hfinite hit
  cases hit with
  | true => simp [collisionAnswerEncodingMonitorPotential]
  | false =>
      simpa only [Bool.false_eq_true, if_false] using
        expected_collisionAnswerEncodingMonitorPotential_query_le secretKey query cache hfinite false

theorem probEvent_bad_or_encodingBad_without_parent_le_collisionPreExceptionCharge
    (secretKey : SecretKey) (computation : OracleComp OracleWorld α) :
    Pr[fun result =>
      (Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret result.1.2 ∨ EncodingBad result.1.2 secretKey) ∧ result.2 = false |
      runExceptionMonitor (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret) computation ∅ false] ≤
      expectedPreExceptionCharge (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret)
        (collisionParentStoppedEncodingQueryCharge secretKey) computation ∅ false * (Fintype.card Digest : ENNReal)⁻¹ := by
  have hbound := expected_collisionAnswerEncodingMonitorPotential_le_preExceptionCharge secretKey computation ∅ finite_empty false
  have hempty : collisionAnswerEncodingMonitorPotential secretKey ∅ false = 0 := by
    simp [collisionAnswerEncodingMonitorPotential, collisionAnswerEncodingAdaptivePotential_eq finite_empty]
  rw [hempty, zero_add] at hbound
  apply le_trans _ hbound
  rw [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ support (runExceptionMonitor
      (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret) computation ∅ false)
  · have hproject := runExceptionMonitor_support_project
      (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret) computation ∅ false hr
    have hfinite := finite_cache_of_mem_support computation ∅ result.1.1 result.1.2 hproject finite_empty
    by_cases hevent : (Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret result.1.2 ∨ EncodingBad result.1.2 secretKey) ∧ result.2 = false
    · rw [if_pos hevent]
      simp only [collisionAnswerEncodingMonitorPotential, hevent.2, Bool.false_eq_true, if_false,
        collisionAnswerEncodingAdaptivePotential_eq hfinite, collisionAnswerEncodingTotalPotential_eq_one_of_bad_or_encodingBad hfinite hevent.1, mul_one]
      exact le_rfl
    · simp only [if_neg hevent, zero_le]
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]
    split_ifs <;> rfl

theorem probEvent_le_collisionPreExceptionCharge_add_parent_encoding_residual
    (secretKey : SecretKey) (computation : OracleComp OracleWorld α) (event : α × QueryCache HashSpec → Prop) :
    Pr[event | (simulateQ romImpl computation).run ∅] ≤
      expectedPreExceptionCharge (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret)
        (collisionParentStoppedEncodingQueryCharge secretKey) computation ∅ false * (Fintype.card Digest : ENNReal)⁻¹ +
        Pr[fun result => event result.1 ∧ (result.2 = true ∨
          ¬ (Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret result.1.2 ∨ EncodingBad result.1.2 secretKey)) |
          runExceptionMonitor (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret) computation ∅ false] :=
  (probEvent_le_bad_without_exception_add_residual
    (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret)
    (fun cache => Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache ∨ EncodingBad cache secretKey)
    event computation ∅).trans
      (add_le_add (probEvent_bad_or_encodingBad_without_parent_le_collisionPreExceptionCharge secretKey computation) le_rfl)


theorem expected_encodingPairIncrementCharge_scaled_le_127 {α : Type} (key : SecretKey)
    (computation : OracleComp OracleWorld α) (q : Nat)
    (hbound : computation.IsQueryBoundP (· matches Sum.inr _) q) (hq : q ≤ 2 ^ 127) :
    expectedQueryCharge (encodingPairIncrementCharge key) computation ∅ * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (q : ENNReal) * (1 / 64) * (Fintype.card Digest : ENNReal)⁻¹ :=
  (mul_le_mul' (expectedQueryCharge_mono _ _ (encodingPairIncrementCharge_le_global key) computation ∅) le_rfl).trans
    (expected_validCachePairIncrementCharge_scaled_le_127 computation q hbound hq)

theorem expectedPre_encodingPairIncrementCharge_scaled_le_127 {α : Type}
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (key : SecretKey)
    (computation : OracleComp OracleWorld α) (q : Nat)
    (hbound : computation.IsQueryBoundP (· matches Sum.inr _) q) (hq : q ≤ 2 ^ 127) :
    expectedPreExceptionCharge exception (encodingPairIncrementCharge key) computation ∅ false *
      (Fintype.card Digest : ENNReal)⁻¹ ≤ (q : ENNReal) * (1 / 64) * (Fintype.card Digest : ENNReal)⁻¹ :=
  (mul_le_mul' (expectedPreExceptionCharge_le_queryCharge exception _ computation ∅ false) le_rfl).trans
    (expected_encodingPairIncrementCharge_scaled_le_127 key computation q hbound hq)

theorem expectedPre_collisionCharge_le_base_add_127 {α : Type}
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (key : SecretKey)
    (computation : OracleComp OracleWorld α) (q : Nat)
    (hbound : computation.IsQueryBoundP (· matches Sum.inr _) q) (hq : q ≤ 2 ^ 127) :
    expectedPreExceptionCharge exception (collisionParentStoppedEncodingQueryCharge key) computation ∅ false *
      (Fintype.card Digest : ENNReal)⁻¹ ≤
      expectedPreExceptionCharge exception (collisionParentStoppedEncodingBaseCharge key) computation ∅ false *
        (Fintype.card Digest : ENNReal)⁻¹ + (q : ENNReal) * (1 / 64) * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [show collisionParentStoppedEncodingQueryCharge key = (fun cache input =>
    collisionParentStoppedEncodingBaseCharge key cache input + encodingPairIncrementCharge key cache input) from rfl,
    expectedPreExceptionCharge_add, add_mul]
  exact add_le_add le_rfl (expectedPre_encodingPairIncrementCharge_scaled_le_127 exception key computation q hbound hq)

theorem probEvent_bad_or_encodingBad_without_parent_le_collisionBase127 {α : Type}
    (key : SecretKey) (computation : OracleComp OracleWorld α) (q : Nat)
    (hbound : computation.IsQueryBoundP (· matches Sum.inr _) q) (hq : q ≤ 2 ^ 127) :
    Pr[fun result =>
      (Bad key.parameter key.otsSecret key.ftsSecret result.1.2 ∨ EncodingBad result.1.2 key) ∧ result.2 = false |
      runExceptionMonitor (CleanParentSettlement key.parameter key.otsSecret key.ftsSecret) computation ∅ false] ≤
      expectedPreExceptionCharge (CleanParentSettlement key.parameter key.otsSecret key.ftsSecret)
        (collisionParentStoppedEncodingBaseCharge key) computation ∅ false * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) * (1 / 64) * (Fintype.card Digest : ENNReal)⁻¹ :=
  (probEvent_bad_or_encodingBad_without_parent_le_collisionPreExceptionCharge key computation).trans
    (expectedPre_collisionCharge_le_base_add_127 _ key computation q hbound hq)

end SphincsSecurity.Concrete
