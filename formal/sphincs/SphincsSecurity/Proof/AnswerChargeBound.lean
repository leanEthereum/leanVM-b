import SphincsSecurity.Proof.AnswerChargeStep
import SphincsSecurity.Proof.AmortizedExceptions
import SphincsSecurity.Proof.TerminalSampling

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

attribute [local irreducible] answerPotential

theorem probEvent_bad_le_answer_add_parent
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp OracleWorld α) (q : Nat)
    (hq : computation.IsQueryBoundP (· matches Sum.inr _) q)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (hclean : ¬ Bad parameter otsSecret ftsSecret cache) :
    Pr[fun result => Bad parameter otsSecret ftsSecret result.2 | (simulateQ romImpl computation).run cache] ≤
      ((q + answerPotential parameter otsSecret ftsSecret cache : Nat) : ℝ≥0∞) *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
        Pr[fun result => result.2 = true |
          runExceptionMonitor (ParentSettlement parameter otsSecret ftsSecret) computation cache false] := by
  have hbound := probEvent_bad_le_amortized_add_exception
    (ParentSettlement parameter otsSecret ftsSecret) (Inv := Finite)
    (potential := answerPotential parameter otsSecret ftsSecret) (c := 1)
    (ε := ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹)
    (fun target => by
      rw [← probOutput_map]
      exact probOutput_truncateHash_le target)
    (fun cache input answer hfinite => finite_cacheQuery hfinite input answer)
    (fun cache hfinite hclean input hfresh =>
      answerCharge_step parameter otsSecret ftsSecret hfinite hclean input hfresh)
    computation q hq cache hfinite hclean
  simpa only [Nat.one_mul] using hbound

theorem probEvent_le_answer_add_parent_residual
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp OracleWorld α) (event : α × QueryCache HashSpec → Prop) (q : Nat)
    (hq : computation.IsQueryBoundP (· matches Sum.inr _) q)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (hclean : ¬ Bad parameter otsSecret ftsSecret cache) :
    Pr[event | (simulateQ romImpl computation).run cache] ≤
      ((q + answerPotential parameter otsSecret ftsSecret cache : Nat) : ℝ≥0∞) *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
        Pr[fun result => event result.1 ∧ (result.2 = true ∨ ¬ Bad parameter otsSecret ftsSecret result.1.2) |
          runExceptionMonitor (ParentSettlement parameter otsSecret ftsSecret) computation cache false] := by
  have hbound := probEvent_bad_without_exception_le_amortized
    (ParentSettlement parameter otsSecret ftsSecret) (Inv := Finite)
    (potential := answerPotential parameter otsSecret ftsSecret) (c := 1)
    (ε := ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹)
    (fun target => by
      rw [← probOutput_map]
      exact probOutput_truncateHash_le target)
    (fun cache input answer hfinite => finite_cacheQuery hfinite input answer)
    (fun cache hfinite hclean input hfresh =>
      answerCharge_step parameter otsSecret ftsSecret hfinite hclean input hfresh)
    computation q hq cache hfinite hclean
  simp only [Nat.one_mul] at hbound
  exact (probEvent_le_bad_without_exception_add_residual
    (ParentSettlement parameter otsSecret ftsSecret) (Bad parameter otsSecret ftsSecret) event computation cache).trans
      (add_le_add hbound le_rfl)

noncomputable def sampledParentSettlementGame (adversary : Adversary) :
    ProbComp (SampledSecrets × ((Bool × QueryCache HashSpec) × Bool)) := do
  let secrets ← sampleSecrets
  let result ← runExceptionMonitor (ParentSettlement secrets.parameter secrets.otsSecret secrets.ftsSecret)
    (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ false
  pure (secrets, result)

theorem sampledParentSettlementGame_project (adversary : Adversary) :
    (fun result => result.2.1.1) <$> sampledParentSettlementGame adversary = sampledGame adversary := by
  rw [sampledParentSettlementGame, sampledGame, map_bind]
  apply bind_congr
  intro secrets
  rw [bind_pure_comp, Functor.map_map]
  change (Prod.fst ∘ Prod.fst) <$>
    runExceptionMonitor (ParentSettlement secrets.parameter secrets.otsSecret secrets.ftsSecret)
      (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ false = _
  rw [StateT.run'_eq, ← runExceptionMonitor_project
    (ParentSettlement secrets.parameter secrets.otsSecret secrets.ftsSecret)
    (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ false,
    Functor.map_map]
  rfl

def parentSettlementResidual (result : SampledSecrets × ((Bool × QueryCache HashSpec) × Bool)) : Prop :=
  result.2.1.1 = true ∧ (result.2.2 = true ∨
    ¬ Bad result.1.parameter result.1.otsSecret result.1.ftsSecret result.2.1.2)

theorem forgeAdvantage_le_answer_add_parent_residual
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) :
    forgeAdvantage scheme adversary ≤
      (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
        Pr[parentSettlementResidual | sampledParentSettlementGame adversary] := by
  rw [forgeAdvantage_eq_sampledGame, sampledGame, probOutput_bind_eq_tsum]
  calc
    _ ≤ ∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets] *
        ((q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
          Pr[fun result => result.1.1 = true ∧
              (result.2 = true ∨ ¬ Bad secrets.parameter secrets.otsSecret secrets.ftsSecret result.1.2) |
            runExceptionMonitor (ParentSettlement secrets.parameter secrets.otsSecret secrets.ftsSecret)
              (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ false]) := by
      apply ENNReal.tsum_le_tsum
      intro secrets
      by_cases hsecrets : secrets ∈ support sampleSecrets
      · apply mul_le_mul' le_rfl
        obtain ⟨hparameter, hots, hfts⟩ := secrets.support_components hsecrets
        have hbound := probEvent_le_answer_add_parent_residual secrets.parameter secrets.otsSecret secrets.ftsSecret
          (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) (fun result => result.1 = true) q
          (isQueryBoundP_gameAfterSecrets adversary q hq hparameter hots hfts) ∅ finite_empty
          (not_bad_empty secrets.parameter secrets.otsSecret secrets.ftsSecret)
        rw [answerPotential_empty, Nat.add_zero] at hbound
        rw [StateT.run'_eq, probOutput_map]
        exact hbound
      · simp [probOutput_eq_zero_of_not_mem_support hsecrets]
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
      rw [tsum_probOutput_eq_one' (mx := sampleSecrets) (by simp), one_mul]
      congr 1
      rw [sampledParentSettlementGame, probEvent_bind_eq_tsum]
      apply tsum_congr
      intro secrets
      rw [bind_pure_comp, probEvent_map]
      rfl

theorem probEvent_sampledViewedGame_bad_le_answer_add_parent
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) :
    Pr[SampledViewedEvent (fun parameter otsSecret ftsSecret result => Bad parameter otsSecret ftsSecret result.2.cache) |
      sampledViewedGame adversary] ≤
      (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
        Pr[fun result => result.2.2 = true | sampledParentSettlementGame adversary] := by
  rw [probEvent_sampledViewedGame_eq_weighted]
  calc
    _ ≤ ∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets] *
        ((q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
          Pr[fun result => result.2 = true |
            runExceptionMonitor (ParentSettlement secrets.parameter secrets.otsSecret secrets.ftsSecret)
              (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ false]) := by
      apply ENNReal.tsum_le_tsum
      intro secrets
      by_cases hsecrets : secrets ∈ support sampleSecrets
      · apply mul_le_mul' le_rfl
        obtain ⟨hparameter, hots, hfts⟩ := secrets.support_components hsecrets
        have hbound := probEvent_bad_le_answer_add_parent secrets.parameter secrets.otsSecret secrets.ftsSecret
          (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) q
          (isQueryBoundP_gameAfterSecrets adversary q hq hparameter hots hfts) ∅ finite_empty
          (not_bad_empty secrets.parameter secrets.otsSecret secrets.ftsSecret)
        rw [answerPotential_empty, Nat.add_zero] at hbound
        rw [← gameAfterSecretsWithViewTrace_verdictCache_projection, probEvent_map] at hbound
        exact hbound
      · simp [probOutput_eq_zero_of_not_mem_support hsecrets]
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
      rw [tsum_probOutput_eq_one' (mx := sampleSecrets) (by simp), one_mul]
      congr 1
      rw [sampledParentSettlementGame, probEvent_bind_eq_tsum]
      apply tsum_congr
      intro secrets
      rw [bind_pure_comp, probEvent_map]
      rfl

end SphincsSecurity.Concrete
