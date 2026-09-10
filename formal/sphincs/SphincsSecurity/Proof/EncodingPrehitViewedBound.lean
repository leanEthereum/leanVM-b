import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.EncodingPrehitGame
import SphincsSecurity.Proof.EncodingPrehitViewedProjection
import SphincsSecurity.Proof.EncodingTerminalView
import SphincsSecurity.Proof.FtsProbeQueryBudget126
import SphincsSecurity.Proof.OtsOpeningRefinedReserve
import SphincsSecurity.Proof.Security126RefinedEndpoint

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal TightEncoding

noncomputable def sampledEncodingPrehitViewedGame (adversary : Adversary) :
    ProbComp (SampledViewedResult × Bool) := do
  let secrets ← sampleSecrets
  (fun result => ((⟨secrets, (result.1, result.2.1)⟩ : SampledViewedResult), result.2.2)) <$>
    gameAfterSecretsWithEncodingPrehitView adversary secrets.parameter secrets.otsSecret secrets.ftsSecret

def encodingPrehitViewedSummary (result : SampledViewedResult × Bool) : EncodingPrehitGameResult :=
  ⟨result.1.secrets, result.1.result.1.2.2, result.1.result.2.cache, result.2⟩

def prehitFreeResidualOtsOpeningEvent (result : SampledViewedResult × Bool) : Prop :=
  result.2 = false ∧ SampledViewedEvent residualOtsOpeningEvent result.1

theorem sampledEncodingPrehitViewedGame_view_projection (adversary : Adversary) :
    Prod.fst <$> sampledEncodingPrehitViewedGame adversary = sampledViewedGame adversary := by
  rw [sampledEncodingPrehitViewedGame, sampledViewedGame, map_bind]
  apply bind_congr
  intro secrets
  rw [← gameAfterSecretsWithEncodingPrehitView_projection]
  simp

theorem sampledEncodingPrehitViewedGame_monitor_projection (adversary : Adversary) :
    encodingPrehitViewedSummary <$> sampledEncodingPrehitViewedGame adversary =
      sampledEncodingPrehitGame adversary := by
  rw [sampledEncodingPrehitViewedGame, sampledEncodingPrehitGame, map_bind]
  apply bind_congr
  intro secrets
  rw [← gameAfterSecretsWithEncodingPrehitView_monitor_projection]
  simp [encodingPrehitViewedSummary]

theorem probEvent_sampledEncodingPrehitViewedGame_bad_le_queryCharge (adversary : Adversary) :
    Pr[fun result => (encodingPrehitViewedSummary result).Bad | sampledEncodingPrehitViewedGame adversary] ≤
      sampledQueryCharge refinedStructuralEncodingQueryCharge adversary * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  have hbound := probEvent_sampledEncodingPrehitGame_bad_le_queryCharge adversary
  rw [← sampledEncodingPrehitViewedGame_monitor_projection, probEvent_map] at hbound
  exact hbound

theorem sampled_jointPrimitive_prehit_classify (result : SampledViewedResult × Bool)
    (hprimitive : SampledViewedEvent jointPrimitiveEvent result.1) :
    (encodingPrehitViewedSummary result).Bad ∨
      prehitFreeResidualOtsOpeningEvent result ∨ SampledViewedEvent cleanUncoveredEvent result.1 := by
  classical
  obtain ⟨hwin, hevent⟩ := hprimitive
  by_cases hhit : result.2 = true
  · exact Or.inl (Or.inl hhit)
  by_cases hbad : Bad result.1.secrets.parameter result.1.secrets.otsSecret result.1.secrets.ftsSecret
      result.1.result.2.cache
  · exact Or.inl (Or.inr (Or.inl hbad))
  by_cases hencoding : ViewedEncodingCollisionWitness result.1.secrets.parameter result.1.secrets.otsSecret
      result.1.secrets.ftsSecret result.1.result
  · apply Or.inl
    apply Or.inr
    apply Or.inr
    exact (encodingBad_mk_root_iff result.1.secrets.parameter result.1.secrets.otsSecret
      result.1.secrets.ftsSecret result.1.result.2.cache result.1.result.1.1 default).mp hencoding.encodingBad
  rcases (hevent.resolve_left hbad).resolve_left hencoding with hots | hfts
  · exact Or.inr (Or.inl ⟨Bool.eq_false_iff.mpr hhit, hwin, hbad, hencoding, hots⟩)
  · exact Or.inr (Or.inr hfts)

theorem probEvent_sampled_jointPrimitive_le_prehit_charge_add_openings (adversary : Adversary) :
    Pr[SampledViewedEvent jointPrimitiveEvent | sampledViewedGame adversary] ≤
      sampledQueryCharge refinedStructuralEncodingQueryCharge adversary * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
      (Pr[prehitFreeResidualOtsOpeningEvent | sampledEncodingPrehitViewedGame adversary] +
        Pr[SampledViewedEvent cleanUncoveredEvent | sampledViewedGame adversary]) := by
  rw [← sampledEncodingPrehitViewedGame_view_projection, probEvent_map]
  apply (probEvent_mono (q := fun result => (encodingPrehitViewedSummary result).Bad ∨
    prehitFreeResidualOtsOpeningEvent result ∨ SampledViewedEvent cleanUncoveredEvent result.1)
    (fun result _ hprimitive => sampled_jointPrimitive_prehit_classify result hprimitive)).trans
  apply (probEvent_or_le _ _ _).trans
  apply add_le_add (probEvent_sampledEncodingPrehitViewedGame_bad_le_queryCharge adversary)
  have hopenings := probEvent_or_le (sampledEncodingPrehitViewedGame adversary)
    prehitFreeResidualOtsOpeningEvent (fun result => SampledViewedEvent cleanUncoveredEvent result.1)
  simpa only [probEvent_map, Function.comp_def] using hopenings

theorem security126_of_sampled_prehitFree_otsOpening_le_refinedQueryReserve_add_query_erasure
    (hots : ∀ (q : Nat), 1 ≤ q → ∀ adversary : Adversary,
      HasHashQueryBound scheme adversary q → q ≤ 2 ^ 126 →
        Pr[prehitFreeResidualOtsOpeningEvent | sampledEncodingPrehitViewedGame adversary] ≤
          sampledQueryCharge otsOpeningRefinedQueryReserve adversary * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
            (q : ℝ≥0∞) * ((2 ^ 216 : Nat) : ℝ≥0∞)⁻¹) :
    HasClassicalSecurityBits scheme 126 := by
  apply security126_of_sampled_jointPrimitive_le_ten_thirds_mul_add_query_erasure
  intro q hqPos adversary hq hqMax
  have hfts := FtsProbeSimulation.probEvent_sampledViewedGame_cleanUncovered_le_queryCharge126 adversary q hq hqMax
  rw [← sampled_ftsOpeningQueryReserve_eq] at hfts
  apply (probEvent_sampled_jointPrimitive_le_prehit_charge_add_openings adversary).trans
  apply (add_le_add le_rfl (add_le_add (hots q hqPos adversary hq hqMax) hfts)).trans
  calc
    _ = ((sampledQueryCharge refinedStructuralEncodingQueryCharge adversary +
        sampledQueryCharge ftsOpeningQueryReserve adversary) +
        sampledQueryCharge otsOpeningRefinedQueryReserve adversary) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
          (q : ℝ≥0∞) * ((2 ^ 216 : Nat) : ℝ≥0∞)⁻¹ := by ring
    _ ≤ ((10 / 3 : ℝ≥0∞) * q) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
          (q : ℝ≥0∞) * ((2 ^ 216 : Nat) : ℝ≥0∞)⁻¹ :=
      add_le_add (mul_le_mul' (sampled_structural_add_refined_openingQueryReserve_le adversary q hq) le_rfl) le_rfl
    _ = _ := by simp [digestBits]

end SphincsSecurity.Concrete
