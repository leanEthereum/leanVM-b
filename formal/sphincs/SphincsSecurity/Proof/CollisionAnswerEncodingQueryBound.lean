import SphincsSecurity.Proof.CollisionAnswerEncodingPotential
import SphincsSecurity.Proof.ValidCacheCollisionCharge
import SphincsSecurity.Proof.AmortizedStoppedCharge
import SphincsSecurity.Proof.ExceptionWitness

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition instFintypeEncodingPosition validCacheEntries
set_option backward.isDefEq.respectTransparency false

noncomputable def collisionParentStoppedEncodingBaseCharge (key : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  if cache input = none then
    if ∃ position : EncodingPosition, AtEncodingPosition key.parameter input position then 1
    else if ∃ position : Position, AtPosition key.parameter input position ∧
        ¬ Settled key.parameter key.otsSecret key.ftsSecret cache position ∧
        ∀ answer : HashOutput, Settled key.parameter key.otsSecret key.ftsSecret (cache.cacheQuery input answer) position then 0
    else if ∃ position : Position, AtPosition key.parameter input position then 1 else 0
  else 0

noncomputable def encodingPairIncrementCharge (key : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  if ∃ position : EncodingPosition, AtEncodingPosition key.parameter input position then validCachePairIncrementCharge cache input else 0

theorem encodingPairIncrementCharge_le_global (key : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) :
    encodingPairIncrementCharge key cache input ≤ validCachePairIncrementCharge cache input := by
  unfold encodingPairIncrementCharge
  split_ifs <;> simp only [le_refl, zero_le]

noncomputable def collisionParentStoppedEncodingQueryCharge (key : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  collisionParentStoppedEncodingBaseCharge key cache input + encodingPairIncrementCharge key cache input

theorem collisionParentStoppedEncodingBaseCharge_le_one (key : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) :
    collisionParentStoppedEncodingBaseCharge key cache input ≤ 1 := by
  unfold collisionParentStoppedEncodingBaseCharge
  split_ifs <;> simp

theorem uniform_collisionMonitor_step_of_settling
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {key : SecretKey} {input : HashInput} {queried : Position}
    (hfresh : cache input = none) (hat : AtPosition key.parameter input queried)
    (hbefore : ¬ Settled key.parameter key.otsSecret key.ftsSecret cache queried)
    (hafter : ∀ answer, Settled key.parameter key.otsSecret key.ftsSecret (cache.cacheQuery input answer) queried) :
    (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if CleanParentSettlement key.parameter key.otsSecret key.ftsSecret cache input answer then 0
        else collisionAnswerEncodingTotalPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) key)) ≤
      collisionAnswerEncodingTotalPotential cache hfinite key := by
  apply le_trans (uniform_collisionAnswerEncodingTotalPotential_without_parent_le_step hfinite 0 ?_)
  · simp only [Nat.cast_zero, zero_mul, add_zero, le_refl]
  · intro hclean
    obtain ⟨targets, hcard, hsafe⟩ := collisionAnswerEncoding_step_of_settling hfinite hclean hfresh hat hbefore hafter
    refine ⟨targets, hcard.trans (Nat.le_add_right _ 0), ?_⟩
    intro answer hnoParent havoid
    obtain ⟨hc, hp, hs⟩ := hsafe answer hnoParent havoid
    exact ⟨hc, hp.trans (Nat.le_add_right _ 0), hs⟩

theorem uniform_collisionMonitor_step_of_structural
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {key : SecretKey} {input : HashInput} {queried : Position}
    (hfresh : cache input = none) (hat : AtPosition key.parameter input queried) :
    (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if CleanParentSettlement key.parameter key.otsSecret key.ftsSecret cache input answer then 0
        else collisionAnswerEncodingTotalPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) key)) ≤
      collisionAnswerEncodingTotalPotential cache hfinite key + (Fintype.card Digest : ENNReal)⁻¹ := by
  simpa only [Nat.cast_one, one_mul] using uniform_collisionAnswerEncodingTotalPotential_without_parent_le_step hfinite 1
    (fun hclean => collisionAnswerEncoding_step_of_structural hfinite hclean hfresh hat)

theorem uniform_collisionMonitor_step_of_nonstructural
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {key : SecretKey} {input : HashInput}
    (hfresh : cache input = none)
    (hne : ∀ position : EncodingPosition, ¬ AtEncodingPosition key.parameter input position)
    (hns : ∀ position : Position, ¬ AtPosition key.parameter input position) :
    (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if CleanParentSettlement key.parameter key.otsSecret key.ftsSecret cache input answer then 0
        else collisionAnswerEncodingTotalPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) key)) ≤
      collisionAnswerEncodingTotalPotential cache hfinite key := by
  calc
    _ ≤ ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        collisionAnswerEncodingTotalPotential cache hfinite key := by
      apply ENNReal.tsum_le_tsum
      intro answer
      apply mul_le_mul' le_rfl
      split_ifs
      · exact bot_le
      · exact collisionAnswerEncodingTotalPotential_cacheQuery_le_of_nonstructural hfinite hfresh hne hns
    _ = _ := by rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]

theorem uniform_collisionMonitor_step_of_encoding
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {key : SecretKey} {input : HashInput} {position : EncodingPosition}
    (hfresh : cache input = none) (hat : AtEncodingPosition key.parameter input position) :
    (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if CleanParentSettlement key.parameter key.otsSecret key.ftsSecret cache input answer then 0
        else collisionAnswerEncodingTotalPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) key)) ≤
      collisionAnswerEncodingTotalPotential cache hfinite key + (Fintype.card Digest : ENNReal)⁻¹ +
        validCachePairIncrementCharge cache input * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [validCachePairIncrementCharge, if_pos hfresh]
  apply le_trans ?_ (uniform_collisionAnswerEncodingTotalPotential_atEncoding_le hfinite hfresh hat)
  apply ENNReal.tsum_le_tsum
  intro answer
  apply mul_le_mul' le_rfl
  split_ifs
  · exact bot_le
  · exact le_rfl

theorem uniform_collisionAnswerEncodingTotalPotential_without_parent_le_charge
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {secretKey : SecretKey} {input : HashInput}
    (hfresh : cache input = none) :
    (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache input answer then 0
        else collisionAnswerEncodingTotalPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) secretKey)) ≤
      collisionAnswerEncodingTotalPotential cache hfinite secretKey + collisionParentStoppedEncodingQueryCharge secretKey cache input *
        (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [collisionParentStoppedEncodingQueryCharge, add_mul, ← add_assoc,
    collisionParentStoppedEncodingBaseCharge, if_pos hfresh, encodingPairIncrementCharge]
  by_cases hencoding : ∃ position : EncodingPosition, AtEncodingPosition secretKey.parameter input position
  · rw [if_pos hencoding, if_pos hencoding, one_mul]
    exact uniform_collisionMonitor_step_of_encoding hfinite hfresh (Classical.choose_spec hencoding)
  · rw [if_neg hencoding, if_neg hencoding, zero_mul, add_zero]
    split_ifs with hsettles hstructural
    · rw [zero_mul, add_zero]
      obtain ⟨queried, hat, hbefore, hafter⟩ := hsettles
      exact uniform_collisionMonitor_step_of_settling hfinite hfresh hat hbefore hafter
    · rw [one_mul]
      obtain ⟨queried, hat⟩ := hstructural
      exact uniform_collisionMonitor_step_of_structural hfinite hfresh hat
    · rw [zero_mul, add_zero]
      exact uniform_collisionMonitor_step_of_nonstructural hfinite hfresh
        (fun position h => hencoding ⟨position, h⟩) (fun position h => hstructural ⟨position, h⟩)

noncomputable def collisionAnswerEncodingAdaptivePotential (cache : QueryCache HashSpec) (secretKey : SecretKey) : ℝ≥0∞ :=
  if hfinite : Finite cache then collisionAnswerEncodingTotalPotential cache hfinite secretKey else 0

theorem collisionAnswerEncodingAdaptivePotential_eq {cache : QueryCache HashSpec} (hfinite : Finite cache) (secretKey : SecretKey) :
    collisionAnswerEncodingAdaptivePotential cache secretKey = collisionAnswerEncodingTotalPotential cache hfinite secretKey := by
  rw [collisionAnswerEncodingAdaptivePotential, dif_pos hfinite]

noncomputable def collisionAnswerEncodingMonitorPotential (secretKey : SecretKey) (cache : QueryCache HashSpec) (hit : Bool) : ℝ≥0∞ :=
  if hit then 0 else collisionAnswerEncodingAdaptivePotential cache secretKey

theorem expected_collisionAnswerEncodingMonitorPotential_query_le
    (secretKey : SecretKey) (query : OracleWorld.Domain) (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit : Bool) :
    (∑' result, Pr[= result | (romImpl query).run cache] *
      collisionAnswerEncodingMonitorPotential secretKey result.2
        (hit || queryException (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret) cache query result.1)) ≤
      collisionAnswerEncodingMonitorPotential secretKey cache hit +
        hashQueryCharge (fun cache input => collisionParentStoppedEncodingQueryCharge secretKey cache input *
          (Fintype.card Digest : ℝ≥0∞)⁻¹) cache query := by
  cases hit with
  | true => simp [collisionAnswerEncodingMonitorPotential]
  | false =>
      cases query with
      | inl sample =>
          have hquery : (romImpl (.inl sample)).run cache =
              (fun answer => (answer, cache)) <$> (liftM (unifSpec.query sample) : ProbComp _) := rfl
          rw [hquery, tsum_probOutput_map_mul]
          simp only [queryException, collisionAnswerEncodingMonitorPotential, Bool.false_or, Bool.false_eq_true, if_false,
            hashQueryCharge, Sum.elim_inl, add_zero]
          rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
      | inr input =>
          change (∑' result, Pr[= result | (randomOracle input).run cache] *
            collisionAnswerEncodingMonitorPotential secretKey result.2
              (false || queryException (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret) cache (.inr input) result.1)) ≤ _
          by_cases hfresh : cache input = none
          · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
            simp only [collisionAnswerEncodingMonitorPotential, queryException, hfresh, true_and, Bool.false_or, decide_eq_true_eq,
              Bool.false_eq_true, if_false, hashQueryCharge, Sum.elim_inr]
            simp_rw [collisionAnswerEncodingAdaptivePotential_eq (finite_cacheQuery hfinite input _)]
            rw [collisionAnswerEncodingAdaptivePotential_eq hfinite]
            exact uniform_collisionAnswerEncodingTotalPotential_without_parent_le_charge hfinite hfresh
          · obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hfresh
            rw [randomOracle, QueryImpl.withCaching_run_some _ hanswer, tsum_probOutput_pure_mul]
            simp only [queryException, hfresh, false_and, decide_false, Bool.false_or]
            exact le_self_add

theorem expected_collisionAnswerEncodingMonitorPotential_le_queryCharge
    (secretKey : SecretKey) (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit : Bool) :
    (∑' result, Pr[= result | runExceptionMonitor
        (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret) computation cache hit] *
      collisionAnswerEncodingMonitorPotential secretKey result.1.2 result.2) ≤
      collisionAnswerEncodingMonitorPotential secretKey cache hit +
        expectedQueryCharge (collisionParentStoppedEncodingQueryCharge secretKey) computation cache * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  rw [← expectedQueryCharge_mul]
  exact expected_runExceptionMonitor_potential_le_queryCharge
    (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret)
    (collisionAnswerEncodingMonitorPotential secretKey) _ (expected_collisionAnswerEncodingMonitorPotential_query_le secretKey) computation cache hfinite hit

theorem probEvent_bad_or_encodingBad_without_parent_le_collisionQueryCharge
    (secretKey : SecretKey) (computation : OracleComp OracleWorld α) :
    Pr[fun result =>
      (Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret result.1.2 ∨ EncodingBad result.1.2 secretKey) ∧ result.2 = false |
      runExceptionMonitor (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret) computation ∅ false] ≤
      expectedQueryCharge (collisionParentStoppedEncodingQueryCharge secretKey) computation ∅ * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  have hbound := expected_collisionAnswerEncodingMonitorPotential_le_queryCharge secretKey computation ∅ finite_empty false
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

theorem probEvent_le_collisionAnswerEncodingQueryCharge_add_parent_residual
    (secretKey : SecretKey) (computation : OracleComp OracleWorld α) (event : α × QueryCache HashSpec → Prop) :
    Pr[event | (simulateQ romImpl computation).run ∅] ≤
      expectedQueryCharge (collisionParentStoppedEncodingQueryCharge secretKey) computation ∅ * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
        Pr[fun result => event result.1 ∧ (result.2 = true ∨
          ¬ (Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret result.1.2 ∨ EncodingBad result.1.2 secretKey)) |
          runExceptionMonitor (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret) computation ∅ false] :=
  (probEvent_le_bad_without_exception_add_residual
    (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret)
    (fun cache => Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache ∨ EncodingBad cache secretKey)
    event computation ∅).trans
      (add_le_add (probEvent_bad_or_encodingBad_without_parent_le_collisionQueryCharge secretKey computation) le_rfl)

end SphincsSecurity.Concrete
