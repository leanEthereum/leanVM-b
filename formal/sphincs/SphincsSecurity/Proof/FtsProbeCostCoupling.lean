import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FtsProbeCostExecution
import SphincsSecurity.Proof.MarginalCoupling

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

theorem probeCachedInputs_finite_univ (parameter : PublicParameter) (cache : QueryCache HashSpec) :
    (probeCachedInputs parameter cache).Finite := by
  let encode := fun pair : Coordinate × Digest =>
    (⟨pair.1.1, pair.1.2.1, pair.1.2.2, pair.2⟩ : FtsSecretProbe).input parameter
  apply (Set.finite_range encode).subset
  rintro input ⟨_, probe, rfl⟩
  exact ⟨((probe.index, probe.tree, probe.leafIdx), probe.candidate), rfl⟩

set_option maxRecDepth 30000 in
theorem relTriple_runCharged_maskedRetainedGameAfterSecrets
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (table : Coordinate → Digest) (q : Nat)
    (hbound : (gameAfterSecrets adversary parameter otsSecret
      (fun index tree leafIdx => table (index, tree, leafIdx))).IsQueryBoundP
        (· matches Sum.inr _) q) :
    RelTriple
      (AdaptiveRevealProbe.runCharged table AdaptiveRevealProbe.State.empty q
        ((maskedRetainedGameAfterSecrets adversary parameter otsSecret).run emptySplitHashCache))
      (actualRetainedGameAfterSecrets adversary parameter otsSecret table)
      (fun charged actual => CleanStepRel parameter table charged.1 actual ∧
        charged ∈ support (AdaptiveRevealProbe.runCharged table AdaptiveRevealProbe.State.empty q
          ((maskedRetainedGameAfterSecrets adversary parameter otsSecret).run emptySplitHashCache))) := by
  classical
  have hgraph := SphincsSecurity.relTriple_of_evalDist_map_eq_with_support_general
    (AdaptiveRevealProbe.runCharged table AdaptiveRevealProbe.State.empty q
      ((maskedRetainedGameAfterSecrets adversary parameter otsSecret).run emptySplitHashCache))
    (AdaptiveRevealProbe.runDetailed table AdaptiveRevealProbe.State.empty q
      ((maskedRetainedGameAfterSecrets adversary parameter otsSecret).run emptySplitHashCache))
    Prod.fst id (by simp only [id_map, AdaptiveRevealProbe.runCharged_result_eq_runDetailed])
  apply relTriple_post_mono (SphincsSecurity.relTriple_trans_exists hgraph
    (relTriple_maskedRetainedGameAfterSecrets adversary parameter otsSecret table q hbound))
  rintro charged actual ⟨detailed, ⟨heq, hsupport, _⟩, hclean⟩
  exact ⟨by simpa only [heq, id_eq] using hclean, hsupport⟩

theorem runCharged_cost_le_actual_cache_add_hit (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (table : Coordinate → Digest) (q : Nat)
    (charged : AdaptiveRevealProbe.DetailedResult Coordinate (RetainedGameResult × SplitHashCache) × Nat)
    (actual : RetainedGameResult × QueryCache HashSpec)
    (hclean : CleanStepRel parameter table charged.1 actual)
    (hsupport : charged ∈ support (AdaptiveRevealProbe.runCharged table AdaptiveRevealProbe.State.empty q
      ((maskedRetainedGameAfterSecrets adversary parameter otsSecret).run emptySplitHashCache))) :
    (charged.2 : ℝ≥0∞) ≤ (probeCachedInputs parameter actual.2).ncard +
      if charged.1.hit = true then (q : ℝ≥0∞) else 0 := by
  classical
  by_cases hhit : charged.1.hit = true
  · rw [if_pos hhit]
    exact (Nat.cast_le.mpr (AdaptiveRevealProbe.runCharged_cost_le_fuel _ _ _ _ charged hsupport)).trans
      (le_add_left le_rfl)
  · rw [if_neg hhit, add_zero]
    have hcleanResult := hclean.resolve_left hhit
    rcases charged with ⟨detailed, cost⟩
    cases detailed with
    | stopped hit => exact hcleanResult.elim
    | done hit state result =>
        obtain ⟨value, cache⟩ := result
        obtain ⟨_, rfl, htable, hsynced⟩ := hcleanResult
        obtain ⟨hcovered, _, hcost⟩ := runCharged_maskedRetainedGameAfterSecrets_cost_le_cache
          adversary parameter otsSecret table q hit state value cache cost hsupport
        exact_mod_cast hcost.trans (Set.ncard_le_ncard
          (hcovered.probeCachedInputs_subset_merged htable hsynced)
          (probeCachedInputs_finite_univ parameter (mergedCache parameter table cache)))

end SphincsSecurity.Concrete.FtsProbeSimulation
