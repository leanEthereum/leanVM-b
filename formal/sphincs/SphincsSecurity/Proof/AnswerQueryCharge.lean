import SphincsSecurity.Proof.AmortizedStoppedCharge
import SphincsSecurity.Proof.AnswerChargeStep
import SphincsSecurity.Proof.FirstParentSettlementGame
import SphincsSecurity.Proof.JointPrimitiveQueryBudget

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

attribute [local irreducible] instFintypePosition answerPotential

noncomputable def answerQueryUnits (parameter : PublicParameter) (input : HashInput) : Nat :=
  open Classical in
  if ∃ position, AtPosition parameter input position then 1 else 0

theorem answerQueryUnits_le_one (parameter : PublicParameter) (input : HashInput) :
    answerQueryUnits parameter input ≤ 1 := by
  unfold answerQueryUnits
  split_ifs <;> omega

theorem answerQueryUnits_eq_zero_of_atEncoding
    (parameter : PublicParameter) {input : HashInput} {position : Concrete.EncodingPosition}
    (hat : Concrete.AtEncodingPosition parameter input position) : answerQueryUnits parameter input = 0 := by
  unfold answerQueryUnits
  exact if_neg (fun ⟨candidate, hcandidate⟩ => hat.not_atPosition candidate hcandidate)

private theorem add_empty_card_le (n : Nat) : n + (∅ : Finset Digest).card ≤ n := by simp

theorem answerCharge_step_queryUnits (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    {cache : QueryCache HashSpec} (hfinite : Finite cache) (hclean : ¬ Bad parameter otsSecret ftsSecret cache)
    (input : HashInput) (hfresh : cache input = none) :
    ∃ targets : Finset Digest, targets.card ≤ answerPotential parameter otsSecret ftsSecret cache + answerQueryUnits parameter input ∧
      ∀ answer, ¬ CleanParentSettlement parameter otsSecret ftsSecret cache input answer → truncateHash answer ∉ targets →
        ¬ Bad parameter otsSecret ftsSecret (cache.cacheQuery input answer) ∧
          answerPotential parameter otsSecret ftsSecret (cache.cacheQuery input answer) + targets.card ≤
            answerPotential parameter otsSecret ftsSecret cache + answerQueryUnits parameter input := by
  classical
  by_cases hat : ∃ position, AtPosition parameter input position
  · rw [answerQueryUnits, if_pos hat]
    obtain ⟨targets, hcard, hsafe⟩ := answerCharge_step parameter otsSecret ftsSecret hfinite hclean input hfresh
    exact ⟨targets, hcard, fun answer hnoParent havoid => hsafe answer (fun h => hnoParent ⟨hclean, h⟩) havoid⟩
  · rw [answerQueryUnits, if_neg hat, Nat.add_zero]
    refine ⟨∅, by rw [Finset.card_empty]; exact Nat.zero_le _, fun answer _ _ => ⟨?_, ?_⟩⟩
    · exact (clean_and_potential_cacheQuery_of_not_atPosition parameter otsSecret ftsSecret hclean hfresh
        (fun position h => hat ⟨position, h⟩)).1
    · exact (Nat.add_le_add
        (answerPotential_cacheQuery_le_of_not_atPosition parameter otsSecret ftsSecret (answer := answer) hfresh
          (fun position h => hat ⟨position, h⟩)) (Nat.le_refl _)).trans
          (add_empty_card_le (answerPotential parameter otsSecret ftsSecret cache))

theorem probEvent_le_answerQueryCharge_add_parent_residual (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp OracleWorld α) (event : α × QueryCache HashSpec → Prop) :
    Pr[event | (simulateQ romImpl computation).run ∅] ≤
      expectedQueryCharge (fun _ input => (answerQueryUnits parameter input : ℝ≥0∞)) computation ∅ *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
        Pr[fun result => event result.1 ∧ (result.2 = true ∨ ¬ Bad parameter otsSecret ftsSecret result.1.2) |
          runExceptionMonitor (CleanParentSettlement parameter otsSecret ftsSecret) computation ∅ false] := by
  have hbound := probEvent_bad_without_exception_le_expectedCharge
    (CleanParentSettlement parameter otsSecret ftsSecret) (Bad parameter otsSecret ftsSecret)
    (answerPotential parameter otsSecret ftsSecret) (fun _ input => answerQueryUnits parameter input)
    ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹
    (fun target => by rw [← probOutput_map]; exact probOutput_truncateHash_le target)
    (fun _ hfinite hclean input hfresh => answerCharge_step_queryUnits parameter otsSecret ftsSecret hfinite hclean input hfresh)
    computation ∅ finite_empty (not_bad_empty parameter otsSecret ftsSecret)
  rw [answerPotential_empty, Nat.cast_zero, zero_mul, zero_add] at hbound
  exact (probEvent_le_bad_without_exception_add_residual
    (CleanParentSettlement parameter otsSecret ftsSecret) (Bad parameter otsSecret ftsSecret) event computation ∅).trans
      (add_le_add hbound le_rfl)

namespace Concrete

noncomputable def structuralAnswerQueryCharge (secretKey : SecretKey) (_cache : QueryCache HashSpec) (input : HashInput) : ℝ≥0∞ :=
  answerQueryUnits secretKey.parameter input

theorem forgeAdvantage_le_answerQueryCharge_add_parent_residual (adversary : Adversary) :
    forgeAdvantage scheme adversary ≤
      sampledQueryCharge structuralAnswerQueryCharge adversary * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
        Pr[parentSettlementResidual | sampledParentSettlementGame adversary] := by
  rw [forgeAdvantage_eq_sampledGame, sampledGame, probOutput_bind_eq_tsum]
  calc
    _ ≤ ∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets] *
        (expectedQueryCharge (fun _ input => (answerQueryUnits secrets.parameter input : ℝ≥0∞))
            (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ *
              ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
          Pr[fun result => result.1.1 = true ∧ (result.2 = true ∨ ¬ Bad secrets.parameter secrets.otsSecret secrets.ftsSecret result.1.2) |
            runExceptionMonitor (CleanParentSettlement secrets.parameter secrets.otsSecret secrets.ftsSecret)
              (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ false]) := by
      apply ENNReal.tsum_le_tsum
      intro secrets
      apply mul_le_mul' le_rfl
      rw [StateT.run'_eq, probOutput_map]
      exact probEvent_le_answerQueryCharge_add_parent_residual secrets.parameter secrets.otsSecret secrets.ftsSecret _ _
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add]
      congr 1
      · unfold sampledQueryCharge structuralAnswerQueryCharge
        simp only [primitiveAccountingKey]
        simp_rw [← mul_assoc, ENNReal.tsum_mul_right]
      · rw [sampledParentSettlementGame, probEvent_bind_eq_tsum]
        apply tsum_congr
        intro secrets
        rw [bind_pure_comp, probEvent_map]
        rfl

theorem forgeAdvantage_le_answerQueryCharge_add_first_parent_residual (adversary : Adversary) :
    forgeAdvantage scheme adversary ≤
      sampledQueryCharge structuralAnswerQueryCharge adversary * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
        Pr[firstParentSettlementResidual | sampledFirstParentSettlementGame adversary] := by
  have hbound := forgeAdvantage_le_answerQueryCharge_add_parent_residual adversary
  rw [← sampledFirstParentSettlementGame_flag_projection, probEvent_map] at hbound
  exact hbound

end Concrete
end SphincsSecurity
