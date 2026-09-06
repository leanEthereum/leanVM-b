import SphincsSecurity.Proof.PreExceptionQueryCharge
import SphincsSecurity.Proof.AnswerEncodingGame

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

theorem expected_answerEncodingMonitorPotential_le_preExceptionCharge
    (secretKey : SecretKey) (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit : Bool) :
    (∑' result, Pr[= result | runExceptionMonitor
        (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret) computation cache hit] *
      answerEncodingMonitorPotential secretKey result.1.2 result.2) ≤
      answerEncodingMonitorPotential secretKey cache hit +
        expectedPreExceptionCharge (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret)
          (parentStoppedEncodingQueryCharge secretKey) computation cache hit * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [← expectedPreExceptionCharge_mul]
  apply expected_runExceptionMonitor_potential_le_preExceptionCharge _ _ _ ?_ computation cache hfinite hit
  intro query cache hfinite hit
  cases hit with
  | true => simp [answerEncodingMonitorPotential]
  | false =>
      simpa only [Bool.false_eq_true, if_false] using
        expected_answerEncodingMonitorPotential_query_le secretKey query cache hfinite false

theorem probEvent_bad_or_encodingBad_without_parent_le_preExceptionCharge
    (secretKey : SecretKey) (computation : OracleComp OracleWorld α) :
    Pr[fun result =>
      (Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret result.1.2 ∨ EncodingBad result.1.2 secretKey) ∧ result.2 = false |
      runExceptionMonitor (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret) computation ∅ false] ≤
      expectedPreExceptionCharge (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret)
        (parentStoppedEncodingQueryCharge secretKey) computation ∅ false * (Fintype.card Digest : ENNReal)⁻¹ := by
  have hbound := expected_answerEncodingMonitorPotential_le_preExceptionCharge secretKey computation ∅ finite_empty false
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

theorem probEvent_le_preExceptionCharge_add_parent_encoding_residual
    (secretKey : SecretKey) (computation : OracleComp OracleWorld α) (event : α × QueryCache HashSpec → Prop) :
    Pr[event | (simulateQ romImpl computation).run ∅] ≤
      expectedPreExceptionCharge (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret)
        (parentStoppedEncodingQueryCharge secretKey) computation ∅ false * (Fintype.card Digest : ENNReal)⁻¹ +
        Pr[fun result => event result.1 ∧ (result.2 = true ∨
          ¬ (Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret result.1.2 ∨ EncodingBad result.1.2 secretKey)) |
          runExceptionMonitor (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret) computation ∅ false] :=
  (probEvent_le_bad_without_exception_add_residual
    (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret)
    (fun cache => Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache ∨ EncodingBad cache secretKey)
    event computation ∅).trans
      (add_le_add (probEvent_bad_or_encodingBad_without_parent_le_preExceptionCharge secretKey computation) le_rfl)

noncomputable def sampledPreParentEncodingCharge (adversary : Adversary) : ENNReal :=
  ∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets] *
    expectedPreExceptionCharge (CleanParentSettlement secrets.parameter secrets.otsSecret secrets.ftsSecret)
      (parentStoppedEncodingQueryCharge (primitiveAccountingKey secrets.parameter secrets.otsSecret secrets.ftsSecret))
      (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ false

theorem sampledPreParentEncodingCharge_le_queryCharge (adversary : Adversary) :
    sampledPreParentEncodingCharge adversary ≤ sampledQueryCharge parentStoppedEncodingQueryCharge adversary := by
  unfold sampledPreParentEncodingCharge sampledQueryCharge
  exact ENNReal.tsum_le_tsum fun secrets => mul_le_mul' le_rfl (expectedPreExceptionCharge_le_queryCharge _ _ _ _ _)

theorem forgeAdvantage_le_preParentEncodingCharge_add_parent_residual (adversary : Adversary) :
    forgeAdvantage scheme adversary ≤
      sampledPreParentEncodingCharge adversary * (Fintype.card Digest : ENNReal)⁻¹ +
        Pr[parentEncodingResidual | sampledParentSettlementGame adversary] := by
  rw [forgeAdvantage_eq_sampledGame, sampledGame, probOutput_bind_eq_tsum]
  calc
    _ ≤ ∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets] *
        (expectedPreExceptionCharge (CleanParentSettlement secrets.parameter secrets.otsSecret secrets.ftsSecret)
            (parentStoppedEncodingQueryCharge (primitiveAccountingKey secrets.parameter secrets.otsSecret secrets.ftsSecret))
            (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ false *
              (Fintype.card Digest : ENNReal)⁻¹ +
          Pr[fun result => parentEncodingResidual (secrets, result) |
            runExceptionMonitor (CleanParentSettlement secrets.parameter secrets.otsSecret secrets.ftsSecret)
              (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ false]) := by
      apply ENNReal.tsum_le_tsum
      intro secrets
      apply mul_le_mul' le_rfl
      rw [StateT.run'_eq, probOutput_map]
      exact probEvent_le_preExceptionCharge_add_parent_encoding_residual
        (primitiveAccountingKey secrets.parameter secrets.otsSecret secrets.ftsSecret) _ _
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add]
      congr 1
      · unfold sampledPreParentEncodingCharge
        simp_rw [← mul_assoc, ENNReal.tsum_mul_right]
      · rw [sampledParentSettlementGame, probEvent_bind_eq_tsum]
        apply tsum_congr
        intro secrets
        rw [bind_pure_comp, probEvent_map]
        rfl

theorem forgeAdvantage_le_preParentEncodingCharge_add_first_parent_residual (adversary : Adversary) :
    forgeAdvantage scheme adversary ≤
      sampledPreParentEncodingCharge adversary * (Fintype.card Digest : ENNReal)⁻¹ +
        Pr[firstParentEncodingResidual | sampledFirstParentSettlementGame adversary] := by
  have hbound := forgeAdvantage_le_preParentEncodingCharge_add_parent_residual adversary
  rw [← sampledFirstParentSettlementGame_flag_projection, probEvent_map] at hbound
  exact hbound

end SphincsSecurity.Concrete
