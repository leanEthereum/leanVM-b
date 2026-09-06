import SphincsSecurity.Proof.SettledCollisionViewedTerminal

namespace SphincsSecurity.Concrete.SettledCollision

open OracleComp OracleSpec ENNReal

structure SampledViewedMonitorResult where
  secrets : SampledSecrets
  result : ViewedResult

noncomputable def sampledViewedMonitorGame (adversary : Adversary) : ProbComp SampledViewedMonitorResult := do
  let secrets ← sampleSecrets
  (fun result => ⟨secrets, result⟩) <$>
    gameAfterSecretsWithView adversary secrets.parameter secrets.otsSecret secrets.ftsSecret

def SampledViewedMonitorResult.erase (result : SampledViewedMonitorResult) : SampledViewedResult :=
  ⟨result.secrets, eraseHistory result.result⟩

def SampledViewedMonitorResult.monitor (result : SampledViewedMonitorResult) : GameResult :=
  ⟨result.secrets, result.result.1.2.2, result.result.2.1.cache, result.result.2.2⟩

def SampledMonitorEvent
    (event : PublicParameter →
      (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) →
      (Index → FtsTree → FtsLeaf → Digest) → ViewedResult → Prop)
    (result : SampledViewedMonitorResult) : Prop :=
  event result.secrets.parameter result.secrets.otsSecret result.secrets.ftsSecret result.result

theorem sampledViewedMonitorGame_erase (adversary : Adversary) :
    SampledViewedMonitorResult.erase <$> sampledViewedMonitorGame adversary = sampledViewedGame adversary := by
  unfold sampledViewedMonitorGame sampledViewedGame
  rw [map_bind]
  apply bind_congr
  intro secrets
  rw [Functor.map_map, ← gameAfterSecretsWithView_projection]
  simp only [bind_pure_comp, Functor.map_map]
  rfl

theorem sampledViewedMonitorGame_monitor (adversary : Adversary) :
    SampledViewedMonitorResult.monitor <$> sampledViewedMonitorGame adversary = sampledMonitorGame adversary := by
  unfold sampledViewedMonitorGame sampledMonitorGame
  rw [map_bind]
  apply bind_congr
  intro secrets
  rw [Functor.map_map, ← gameAfterSecretsWithView_monitor_projection, Functor.map_map]
  rfl

theorem probEvent_sampledViewedMonitorGame_hit_le_queryCharge (adversary : Adversary) :
    Pr[fun result => result.result.2.2.hit = true | sampledViewedMonitorGame adversary] ≤
      sampledQueryCharge queryCharge adversary * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  have hbound := probEvent_sampledMonitorGame_hit_le_queryCharge adversary
  rw [← sampledViewedMonitorGame_monitor, probEvent_map] at hbound
  exact hbound

theorem probEvent_sampledMonitorEvent_eq_weighted (adversary : Adversary)
    (event : PublicParameter →
      (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) →
      (Index → FtsTree → FtsLeaf → Digest) → ViewedResult → Prop) :
    Pr[SampledMonitorEvent event | sampledViewedMonitorGame adversary] =
      ∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets] *
        Pr[event secrets.parameter secrets.otsSecret secrets.ftsSecret |
          gameAfterSecretsWithView adversary secrets.parameter secrets.otsSecret secrets.ftsSecret] := by
  unfold sampledViewedMonitorGame
  rw [probEvent_bind_eq_tsum]
  simp only [probEvent_map]
  rfl

theorem probEvent_sampled_verifierPrimitive_le_charge_add_remaining (adversary : Adversary) :
    Pr[SampledViewedEvent verifierPrimitiveEvent | sampledViewedGame adversary] ≤
      sampledQueryCharge queryCharge adversary * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
      Pr[SampledMonitorEvent remainingPrimitiveEvent | sampledViewedMonitorGame adversary] := by
  rw [← sampledViewedMonitorGame_erase, probEvent_map]
  calc
    _ ≤ Pr[fun result => result.result.2.2.hit = true ∨
        SampledMonitorEvent remainingPrimitiveEvent result | sampledViewedMonitorGame adversary] := by
      apply probEvent_mono
      intro result hresult hevent
      rw [sampledViewedMonitorGame, mem_support_bind_iff] at hresult
      obtain ⟨secrets, _, hresult⟩ := hresult
      rw [support_map] at hresult
      obtain ⟨viewed, hviewed, rfl⟩ := hresult
      exact verifierPrimitiveEvent_implies_hit_or_remaining adversary secrets.parameter secrets.otsSecret
        secrets.ftsSecret viewed hviewed hevent
    _ ≤ _ := (probEvent_or_le _ _ _).trans
      (add_le_add (probEvent_sampledViewedMonitorGame_hit_le_queryCharge adversary) le_rfl)

theorem probEvent_sampled_remaining_le_verifierPrimitive (adversary : Adversary) :
    Pr[SampledMonitorEvent remainingPrimitiveEvent | sampledViewedMonitorGame adversary] ≤
      Pr[SampledViewedEvent verifierPrimitiveEvent | sampledViewedGame adversary] := by
  rw [← sampledViewedMonitorGame_erase, probEvent_map]
  apply probEvent_mono
  intro result _ hevent
  exact remainingPrimitiveEvent_implies_verifierPrimitiveEvent result.secrets.parameter
    result.secrets.otsSecret result.secrets.ftsSecret result.result hevent

end SphincsSecurity.Concrete.SettledCollision
