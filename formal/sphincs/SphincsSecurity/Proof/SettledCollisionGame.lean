import SphincsSecurity.Proof.SettledCollisionSupport
import SphincsSecurity.Proof.JointPrimitiveQueryBudget
import SphincsSecurity.Proof.VerifierStructuralCollision

namespace SphincsSecurity.Concrete.SettledCollision

open OracleComp OracleSpec ENNReal

structure GameResult where
  secrets : SampledSecrets
  verdict : Bool
  cache : QueryCache HashSpec
  history : History

noncomputable def sampledMonitorGame (adversary : Adversary) : ProbComp GameResult := do
  let secrets ← sampleSecrets
  (fun result => ⟨secrets, result.1.1, result.1.2, result.2⟩) <$>
    runMonitor (primitiveAccountingKey secrets.parameter secrets.otsSecret secrets.ftsSecret)
      (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ initialHistory

def WinningUnsettledCollision (result : GameResult) : Prop :=
  result.verdict = true ∧ BadOnInputs
    (primitiveAccountingKey result.secrets.parameter result.secrets.otsSecret result.secrets.ftsSecret)
    result.cache ↑result.history.unsettled

theorem sampledMonitorGame_verdict_projection (adversary : Adversary) :
    GameResult.verdict <$> sampledMonitorGame adversary = sampledGame adversary := by
  unfold sampledMonitorGame sampledGame
  rw [map_bind]
  apply bind_congr
  intro secrets
  rw [Functor.map_map, StateT.run'_eq]
  rw [← runMonitor_project
    (primitiveAccountingKey secrets.parameter secrets.otsSecret secrets.ftsSecret)
    (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ initialHistory,
    Functor.map_map]

theorem probEvent_sampledMonitorGame_hit_le_queryCharge (adversary : Adversary) :
    Pr[fun result => result.history.hit = true | sampledMonitorGame adversary] ≤
      sampledQueryCharge queryCharge adversary * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  unfold sampledMonitorGame sampledQueryCharge
  rw [probEvent_bind_eq_tsum, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro secrets
  rw [mul_assoc]
  apply mul_le_mul' le_rfl
  rw [probEvent_map]
  exact probEvent_runMonitor_hit_le_queryCharge
    (primitiveAccountingKey secrets.parameter secrets.otsSecret secrets.ftsSecret)
    (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅

theorem sampled_queryCharge_le_queryBound (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q) : sampledQueryCharge queryCharge adversary ≤ q := by
  unfold sampledQueryCharge
  calc
    _ ≤ ∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets] * (q : ℝ≥0∞) := by
      apply ENNReal.tsum_le_tsum
      intro secrets
      by_cases hsecrets : secrets ∈ support sampleSecrets
      · obtain ⟨hparameter, hots, hfts⟩ := secrets.support_components hsecrets
        apply mul_le_mul' le_rfl
        simpa only [one_mul] using expectedQueryCharge_le_queryBound _ 1
          (queryCharge_le_one (primitiveAccountingKey secrets.parameter secrets.otsSecret secrets.ftsSecret))
          (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) q
          (isQueryBoundP_gameAfterSecrets adversary q hq hparameter hots hfts) ∅
      · rw [probOutput_eq_zero_of_not_mem_support hsecrets, zero_mul, zero_mul]
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left (by positivity) tsum_probOutput_le_one

theorem probEvent_sampledMonitorGame_hit_le_queryBound (adversary : Adversary)
    (q : Nat) (hq : HasHashQueryBound scheme adversary q) :
    Pr[fun result => result.history.hit = true | sampledMonitorGame adversary] ≤
      (q : ℝ≥0∞) * ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ := by
  apply (probEvent_sampledMonitorGame_hit_le_queryCharge adversary).trans
  simpa [digestBits] using mul_le_mul'
    (sampled_queryCharge_le_queryBound adversary q hq) (le_refl (Fintype.card Digest : ℝ≥0∞)⁻¹)

theorem probEvent_verifierStructuralCollision_le_charge_add_unsettled
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Pr[ViewedVerifierStructuralCollision parameter otsSecret ftsSecret |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
    expectedQueryCharge (queryCharge (primitiveAccountingKey parameter otsSecret ftsSecret))
      (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅ * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
      Pr[fun result => result.1.1 = true ∧
        BadOnInputs (primitiveAccountingKey parameter otsSecret ftsSecret) result.1.2 ↑result.2.unsettled |
        runMonitor (primitiveAccountingKey parameter otsSecret ftsSecret)
          (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅ initialHistory] := by
  let sk := primitiveAccountingKey parameter otsSecret ftsSecret
  calc
    _ ≤ Pr[fun result => result.1.2.2 = true ∧ BadOnInputs sk result.2.cache Set.univ |
        gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] := by
      apply probEvent_mono
      intro result _ hcollision
      refine ⟨hcollision.1, ?_⟩
      obtain ⟨position, hsettled, input, ax, ay, hat, hne, hx, hy, heq⟩ := hcollision.bad
      exact ⟨position, input, ax, ay, Set.mem_univ _, hsettled, hat, hne, hx, hy, heq⟩
    _ = Pr[fun result => result.1 = true ∧ BadOnInputs sk result.2 Set.univ |
        (simulateQ romImpl (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run ∅] := by
      rw [← gameAfterSecretsWithViewTrace_verdictCache_projection, probEvent_map]
      rfl
    _ ≤ _ := by
      simpa only [Set.univ_inter] using probEvent_badOnInputs_le_charge_add_unsettled sk
        (gameAfterSecrets adversary parameter otsSecret ftsSecret) (fun result => result.1 = true)
        (fun _ => Set.univ)

theorem probEvent_sampled_verifierStructuralCollision_le_charge_add_unsettled
    (adversary : Adversary) :
    Pr[SampledViewedEvent ViewedVerifierStructuralCollision | sampledViewedGame adversary] ≤
      sampledQueryCharge queryCharge adversary * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
      Pr[WinningUnsettledCollision | sampledMonitorGame adversary] := by
  rw [probEvent_sampledViewedGame_eq_weighted]
  unfold sampledMonitorGame
  rw [probEvent_bind_eq_tsum]
  simp_rw [probEvent_map]
  calc
    _ ≤ ∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets] *
        (expectedQueryCharge (queryCharge (primitiveAccountingKey secrets.parameter secrets.otsSecret secrets.ftsSecret))
          (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ *
            (Fintype.card Digest : ℝ≥0∞)⁻¹ +
          Pr[fun result => result.1.1 = true ∧
            BadOnInputs (primitiveAccountingKey secrets.parameter secrets.otsSecret secrets.ftsSecret)
              result.1.2 ↑result.2.unsettled |
            runMonitor (primitiveAccountingKey secrets.parameter secrets.otsSecret secrets.ftsSecret)
              (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ initialHistory]) :=
      ENNReal.tsum_le_tsum fun secrets => mul_le_mul' le_rfl
        (probEvent_verifierStructuralCollision_le_charge_add_unsettled adversary secrets.parameter
          secrets.otsSecret secrets.ftsSecret)
    _ = _ := by
      simp_rw [mul_add, ← mul_assoc, ENNReal.tsum_add, ENNReal.tsum_mul_right]
      rfl

end SphincsSecurity.Concrete.SettledCollision
