import SphincsSecurity.Proof.AnswerEncodingQueryBound
import SphincsSecurity.Proof.FirstParentSettlementGame
import SphincsSecurity.Proof.JointPrimitiveQueryBudget

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

def parentEncodingResidual (result : SampledSecrets × ((Bool × QueryCache HashSpec) × Bool)) : Prop :=
  result.2.1.1 = true ∧ (result.2.2 = true ∨
    ¬ (Bad result.1.parameter result.1.otsSecret result.1.ftsSecret result.2.1.2 ∨
      EncodingBad result.2.1.2 (primitiveAccountingKey result.1.parameter result.1.otsSecret result.1.ftsSecret)))

def firstParentEncodingResidual
    (result : SampledSecrets × ((Bool × QueryCache HashSpec) × Option ExceptionRecord)) : Prop :=
  parentEncodingResidual (result.1, result.2.1, result.2.2.isSome)

theorem forgeAdvantage_le_answerEncodingQueryCharge_add_parent_residual (adversary : Adversary) :
    forgeAdvantage scheme adversary ≤
      sampledQueryCharge parentStoppedEncodingQueryCharge adversary * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
        Pr[parentEncodingResidual | sampledParentSettlementGame adversary] := by
  rw [forgeAdvantage_eq_sampledGame, sampledGame, probOutput_bind_eq_tsum]
  calc
    _ ≤ ∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets] *
        (expectedQueryCharge (parentStoppedEncodingQueryCharge (primitiveAccountingKey secrets.parameter secrets.otsSecret secrets.ftsSecret))
            (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ *
              (Fintype.card Digest : ℝ≥0∞)⁻¹ +
          Pr[fun result => parentEncodingResidual (secrets, result) |
            runExceptionMonitor (CleanParentSettlement secrets.parameter secrets.otsSecret secrets.ftsSecret)
              (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ false]) := by
      apply ENNReal.tsum_le_tsum
      intro secrets
      apply mul_le_mul' le_rfl
      rw [StateT.run'_eq, probOutput_map]
      exact probEvent_le_answerEncodingQueryCharge_add_parent_residual
        (primitiveAccountingKey secrets.parameter secrets.otsSecret secrets.ftsSecret) _ _
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add]
      congr 1
      · unfold sampledQueryCharge
        simp_rw [← mul_assoc, ENNReal.tsum_mul_right]
      · rw [sampledParentSettlementGame, probEvent_bind_eq_tsum]
        apply tsum_congr
        intro secrets
        rw [bind_pure_comp, probEvent_map]
        rfl

theorem forgeAdvantage_le_answerEncodingQueryCharge_add_first_parent_residual (adversary : Adversary) :
    forgeAdvantage scheme adversary ≤
      sampledQueryCharge parentStoppedEncodingQueryCharge adversary * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
        Pr[firstParentEncodingResidual | sampledFirstParentSettlementGame adversary] := by
  have hbound := forgeAdvantage_le_answerEncodingQueryCharge_add_parent_residual adversary
  rw [← sampledFirstParentSettlementGame_flag_projection, probEvent_map] at hbound
  exact hbound

end SphincsSecurity.Concrete
