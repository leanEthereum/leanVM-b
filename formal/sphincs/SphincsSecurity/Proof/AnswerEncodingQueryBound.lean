import SphincsSecurity.Proof.AnswerEncodingPotential
import SphincsSecurity.Proof.AmortizedStoppedCharge
import SphincsSecurity.Proof.ExceptionWitness

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def parentStoppedEncodingQueryCharge (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) : ℝ≥0∞ :=
  if cache input = none then
    if hencoding : ∃ position : EncodingPosition, AtEncodingPosition secretKey.parameter input position then
      ((encodingMessageIncrement cache secretKey (Classical.choose hencoding) + 1 : Nat) : ℝ≥0∞)
    else if ∃ position : Position, AtPosition secretKey.parameter input position ∧
        ¬ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache position ∧
        ∀ answer : HashOutput, Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret (cache.cacheQuery input answer) position then 0
    else if ∃ position : Position, AtPosition secretKey.parameter input position then 1 else 0
  else 0

theorem uniform_answerEncodingTotalPotential_without_parent_le_charge
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {secretKey : SecretKey} {input : HashInput}
    (hfresh : cache input = none) :
    (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache input answer then 0
        else answerEncodingTotalPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) secretKey)) ≤
      answerEncodingTotalPotential cache hfinite secretKey + parentStoppedEncodingQueryCharge secretKey cache input *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  rw [parentStoppedEncodingQueryCharge, if_pos hfresh]
  split_ifs with hencoding hsettles hstructural
  · apply le_trans _ (uniform_answerEncodingTotalPotential_atEncoding_le hfinite hfresh (Classical.choose_spec hencoding))
    apply ENNReal.tsum_le_tsum
    intro answer
    apply mul_le_mul' le_rfl
    split_ifs <;> simp
  · obtain ⟨queried, hat, hbefore, hafter⟩ := hsettles
    apply le_trans (uniform_answerEncodingTotalPotential_without_parent_le_step hfinite 0 ?_)
    · simp only [Nat.cast_zero, zero_mul, add_zero, le_refl]
    · intro hclean
      obtain ⟨targets, hcard, hsafe⟩ := answerEncoding_step_of_settling hfinite hclean hfresh hat hbefore hafter
      refine ⟨targets, hcard.trans (Nat.le_add_right _ 0), ?_⟩
      intro answer hnoParent havoid
      obtain ⟨hc, hp, hs⟩ := hsafe answer hnoParent havoid
      exact ⟨hc, hp.trans (Nat.le_add_right _ 0), hs⟩
  · obtain ⟨queried, hat⟩ := hstructural
    simpa only [Nat.cast_one, one_mul] using uniform_answerEncodingTotalPotential_without_parent_le_step hfinite 1
      (fun hclean => answerEncoding_step_of_structural hfinite hclean hfresh hat)
  · rw [zero_mul, add_zero]
    calc
      _ ≤ ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
          answerEncodingTotalPotential cache hfinite secretKey := by
        apply ENNReal.tsum_le_tsum
        intro answer
        apply mul_le_mul' le_rfl
        split_ifs
        · exact bot_le
        · exact answerEncodingTotalPotential_cacheQuery_le_of_nonstructural hfinite hfresh
            (fun position h => hencoding ⟨position, h⟩) (fun position h => hstructural ⟨position, h⟩)
      _ = _ := by rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]

noncomputable def answerEncodingAdaptivePotential (cache : QueryCache HashSpec) (secretKey : SecretKey) : ℝ≥0∞ :=
  if hfinite : Finite cache then answerEncodingTotalPotential cache hfinite secretKey else 0

theorem answerEncodingAdaptivePotential_eq {cache : QueryCache HashSpec} (hfinite : Finite cache) (secretKey : SecretKey) :
    answerEncodingAdaptivePotential cache secretKey = answerEncodingTotalPotential cache hfinite secretKey := by
  rw [answerEncodingAdaptivePotential, dif_pos hfinite]

noncomputable def answerEncodingMonitorPotential (secretKey : SecretKey) (cache : QueryCache HashSpec) (hit : Bool) : ℝ≥0∞ :=
  if hit then 0 else answerEncodingAdaptivePotential cache secretKey

theorem expected_answerEncodingMonitorPotential_query_le
    (secretKey : SecretKey) (query : OracleWorld.Domain) (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit : Bool) :
    (∑' result, Pr[= result | (romImpl query).run cache] *
      answerEncodingMonitorPotential secretKey result.2
        (hit || queryException (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret) cache query result.1)) ≤
      answerEncodingMonitorPotential secretKey cache hit +
        hashQueryCharge (fun cache input => parentStoppedEncodingQueryCharge secretKey cache input *
          (Fintype.card Digest : ℝ≥0∞)⁻¹) cache query := by
  cases hit with
  | true => simp [answerEncodingMonitorPotential]
  | false =>
      cases query with
      | inl sample =>
          have hquery : (romImpl (.inl sample)).run cache =
              (fun answer => (answer, cache)) <$> (liftM (unifSpec.query sample) : ProbComp _) := rfl
          rw [hquery, tsum_probOutput_map_mul]
          simp only [queryException, answerEncodingMonitorPotential, Bool.false_or, Bool.false_eq_true, if_false,
            hashQueryCharge, Sum.elim_inl, add_zero]
          rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
      | inr input =>
          change (∑' result, Pr[= result | (randomOracle input).run cache] *
            answerEncodingMonitorPotential secretKey result.2
              (false || queryException (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret) cache (.inr input) result.1)) ≤ _
          by_cases hfresh : cache input = none
          · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
            simp only [answerEncodingMonitorPotential, queryException, hfresh, true_and, Bool.false_or, decide_eq_true_eq,
              Bool.false_eq_true, if_false, hashQueryCharge, Sum.elim_inr]
            simp_rw [answerEncodingAdaptivePotential_eq (finite_cacheQuery hfinite input _)]
            rw [answerEncodingAdaptivePotential_eq hfinite]
            exact uniform_answerEncodingTotalPotential_without_parent_le_charge hfinite hfresh
          · obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hfresh
            rw [randomOracle, QueryImpl.withCaching_run_some _ hanswer, tsum_probOutput_pure_mul]
            simp only [queryException, hfresh, false_and, decide_false, Bool.false_or]
            exact le_self_add

theorem expected_answerEncodingMonitorPotential_le_queryCharge
    (secretKey : SecretKey) (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit : Bool) :
    (∑' result, Pr[= result | runExceptionMonitor
        (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret) computation cache hit] *
      answerEncodingMonitorPotential secretKey result.1.2 result.2) ≤
      answerEncodingMonitorPotential secretKey cache hit +
        expectedQueryCharge (parentStoppedEncodingQueryCharge secretKey) computation cache * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  rw [← expectedQueryCharge_mul]
  exact expected_runExceptionMonitor_potential_le_queryCharge
    (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret)
    (answerEncodingMonitorPotential secretKey) _ (expected_answerEncodingMonitorPotential_query_le secretKey) computation cache hfinite hit

theorem probEvent_bad_or_encodingBad_without_parent_le_queryCharge
    (secretKey : SecretKey) (computation : OracleComp OracleWorld α) :
    Pr[fun result =>
      (Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret result.1.2 ∨ EncodingBad result.1.2 secretKey) ∧ result.2 = false |
      runExceptionMonitor (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret) computation ∅ false] ≤
      expectedQueryCharge (parentStoppedEncodingQueryCharge secretKey) computation ∅ * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  have hbound := expected_answerEncodingMonitorPotential_le_queryCharge secretKey computation ∅ finite_empty false
  have hempty : answerEncodingMonitorPotential secretKey ∅ false = 0 := by
    simp [answerEncodingMonitorPotential, answerEncodingAdaptivePotential_eq finite_empty]
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
      simp only [answerEncodingMonitorPotential, hevent.2, Bool.false_eq_true, if_false,
        answerEncodingAdaptivePotential_eq hfinite, answerEncodingTotalPotential_eq_one_of_bad_or_encodingBad hfinite hevent.1, mul_one]
      exact le_rfl
    · simp only [if_neg hevent, zero_le]
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]
    split_ifs <;> rfl

theorem probEvent_le_answerEncodingQueryCharge_add_parent_residual
    (secretKey : SecretKey) (computation : OracleComp OracleWorld α) (event : α × QueryCache HashSpec → Prop) :
    Pr[event | (simulateQ romImpl computation).run ∅] ≤
      expectedQueryCharge (parentStoppedEncodingQueryCharge secretKey) computation ∅ * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
        Pr[fun result => event result.1 ∧ (result.2 = true ∨
          ¬ (Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret result.1.2 ∨ EncodingBad result.1.2 secretKey)) |
          runExceptionMonitor (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret) computation ∅ false] :=
  (probEvent_le_bad_without_exception_add_residual
    (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret)
    (fun cache => Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache ∨ EncodingBad cache secretKey)
    event computation ∅).trans
      (add_le_add (probEvent_bad_or_encodingBad_without_parent_le_queryCharge secretKey computation) le_rfl)

end SphincsSecurity.Concrete
