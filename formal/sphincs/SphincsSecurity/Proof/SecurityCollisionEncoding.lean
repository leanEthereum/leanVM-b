import SphincsSecurity.Proof.CollisionAnswerEncodingStoppedBound
import SphincsSecurity.Proof.StoppedParentGame

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem forgeAdvantage_le_collisionPreParentCharge_add_parent_residual (adversary : Adversary) :
    forgeAdvantage scheme adversary ≤
      sampledPreParentQueryCharge collisionParentStoppedEncodingQueryCharge adversary * (Fintype.card Digest : ENNReal)⁻¹ +
        Pr[parentEncodingResidual | sampledParentSettlementGame adversary] := by
  rw [forgeAdvantage_eq_sampledGame, sampledGame, probOutput_bind_eq_tsum]
  calc
    _ ≤ ∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets] *
        (expectedPreExceptionCharge (CleanParentSettlement secrets.parameter secrets.otsSecret secrets.ftsSecret)
            (collisionParentStoppedEncodingQueryCharge (primitiveAccountingKey secrets.parameter secrets.otsSecret secrets.ftsSecret))
            (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ false *
              (Fintype.card Digest : ENNReal)⁻¹ +
          Pr[fun result => parentEncodingResidual (secrets, result) |
            runExceptionMonitor (CleanParentSettlement secrets.parameter secrets.otsSecret secrets.ftsSecret)
              (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ false]) := by
      apply ENNReal.tsum_le_tsum
      intro secrets
      apply mul_le_mul' le_rfl
      rw [StateT.run'_eq, probOutput_map]
      exact probEvent_le_collisionPreExceptionCharge_add_parent_encoding_residual
        (primitiveAccountingKey secrets.parameter secrets.otsSecret secrets.ftsSecret) _ _
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add]
      congr 1
      · unfold sampledPreParentQueryCharge
        simp_rw [← mul_assoc, ENNReal.tsum_mul_right]
      · rw [sampledParentSettlementGame, probEvent_bind_eq_tsum]
        apply tsum_congr
        intro secrets
        rw [bind_pure_comp, probEvent_map]
        rfl

theorem forgeAdvantage_le_collisionPreParentCharge_add_first_parent_residual (adversary : Adversary) :
    forgeAdvantage scheme adversary ≤
      sampledPreParentQueryCharge collisionParentStoppedEncodingQueryCharge adversary * (Fintype.card Digest : ENNReal)⁻¹ +
        Pr[firstParentEncodingResidual | sampledFirstParentSettlementGame adversary] := by
  have hbound := forgeAdvantage_le_collisionPreParentCharge_add_parent_residual adversary
  rw [← sampledFirstParentSettlementGame_flag_projection, probEvent_map] at hbound
  exact hbound

theorem sampledPreParent_encodingPairIncrement_scaled_le_127
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    sampledPreParentQueryCharge encodingPairIncrementCharge adversary * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (q : ENNReal) * (1 / 64) * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [sampledPreParentQueryCharge, ← ENNReal.tsum_mul_right]
  calc
    _ ≤ ∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets] *
        ((q : ENNReal) * (1 / 64) * (Fintype.card Digest : ENNReal)⁻¹) := by
      apply ENNReal.tsum_le_tsum
      intro secrets
      rw [mul_assoc]
      by_cases hs : secrets ∈ support sampleSecrets
      · obtain ⟨hp, ho, hf⟩ := secrets.support_components hs
        exact mul_le_mul' le_rfl (expectedPre_encodingPairIncrementCharge_scaled_le_127 _
          (primitiveAccountingKey secrets.parameter secrets.otsSecret secrets.ftsSecret)
          (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) q
          (isQueryBoundP_gameAfterSecrets adversary q hq hp ho hf) hqMax)
      · rw [probOutput_eq_zero_of_not_mem_support hs, zero_mul, zero_mul]
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left zero_le tsum_probOutput_le_one

theorem sampledPreParent_collisionCharge_le_base_add_127
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    sampledPreParentQueryCharge collisionParentStoppedEncodingQueryCharge adversary * (Fintype.card Digest : ENNReal)⁻¹ ≤
      sampledPreParentQueryCharge collisionParentStoppedEncodingBaseCharge adversary * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) * (1 / 64) * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [show collisionParentStoppedEncodingQueryCharge = (fun key cache input =>
    collisionParentStoppedEncodingBaseCharge key cache input + encodingPairIncrementCharge key cache input) from rfl,
    sampledPreParentQueryCharge_add, add_mul]
  exact add_le_add le_rfl (sampledPreParent_encodingPairIncrement_scaled_le_127 adversary q hq hqMax)

theorem forgeAdvantage_le_collisionBase127_add_parent_residual
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary ≤
      sampledPreParentQueryCharge collisionParentStoppedEncodingBaseCharge adversary * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) * (1 / 64) * (Fintype.card Digest : ENNReal)⁻¹ +
        Pr[parentEncodingResidual | sampledParentSettlementGame adversary] :=
  (forgeAdvantage_le_collisionPreParentCharge_add_parent_residual adversary).trans
    (add_le_add (sampledPreParent_collisionCharge_le_base_add_127 adversary q hq hqMax) le_rfl)

end SphincsSecurity.Concrete
