import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.AdaptiveRevealProbeCostExpectation
import SphincsSecurity.Proof.CoupledQueryCost
import SphincsSecurity.Proof.FtsProbeCostCoupling
import SphincsSecurity.Proof.FtsProbeQueryCharge

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

noncomputable def sampledActualFtsCacheCount (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) : ℝ≥0∞ :=
  ∑' result, Pr[= result | sampledActualRetainedFts adversary parameter otsSecret] *
    (probeCachedInputs parameter result.2.2).ncard

set_option maxRecDepth 30000 in
theorem relTriple_chargedExperiment_cost_le_actual_cache_add_hit
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (q : Nat)
    (hbound : ∀ table : Coordinate → Digest, (gameAfterSecrets adversary parameter otsSecret
      (fun index tree leafIdx => table (index, tree, leafIdx))).IsQueryBoundP (· matches Sum.inr _) q) :
    RelTriple
      (AdaptiveRevealProbe.chargedExperiment AdaptiveRevealProbe.State.empty q
        ((maskedRetainedGameAfterSecrets adversary parameter otsSecret).run emptySplitHashCache))
      (sampledActualRetainedFts adversary parameter otsSecret)
      (fun charged actual => (charged.2 : ℝ≥0∞) ≤ (probeCachedInputs parameter actual.2.2).ncard +
        if charged.1.hit = true then (q : ℝ≥0∞) else 0) := by
  classical
  unfold AdaptiveRevealProbe.chargedExperiment sampledActualRetainedFts
  apply relTriple_bind (relTriple_refl (AdaptiveRevealProbe.sampleTable (Coordinate := Coordinate)))
  intro table other heq
  cases heq
  have hextend : AdaptiveRevealProbe.extendTable
      (AdaptiveRevealProbe.State.empty : AdaptiveRevealProbe.State Coordinate) table = table := by
    funext coordinate
    simp [AdaptiveRevealProbe.extendTable, AdaptiveRevealProbe.State.empty]
  rw [hextend]
  have hrel := relTriple_runCharged_maskedRetainedGameAfterSecrets adversary parameter otsSecret table q (hbound table)
  have hcost := relTriple_post_mono hrel (fun {charged actual} h =>
    runCharged_cost_le_actual_cache_add_hit adversary parameter otsSecret table q charged actual h.1 h.2)
  simpa only [id_map, map_eq_bind_pure_comp, Function.comp_def, id_eq, bind_pure] using
    (relTriple_map (f := id) (g := fun actual => (table, actual))
      (R := fun (charged : AdaptiveRevealProbe.DetailedResult Coordinate
          (RetainedGameResult × SplitHashCache) × Nat)
        (actual : (Coordinate → Digest) × (RetainedGameResult × QueryCache HashSpec)) =>
        (charged.2 : ℝ≥0∞) ≤ (probeCachedInputs parameter actual.2.2).ncard +
          if charged.1.hit = true then (q : ℝ≥0∞) else 0) hcost)

theorem maskedFtsProbeCharge_le_actual_cache_add_hit
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (q : Nat)
    (hbound : ∀ table : Coordinate → Digest, (gameAfterSecrets adversary parameter otsSecret
      (fun index tree leafIdx => table (index, tree, leafIdx))).IsQueryBoundP (· matches Sum.inr _) q) :
    maskedFtsProbeCharge adversary parameter otsSecret q ≤ sampledActualFtsCacheCount adversary parameter otsSecret +
      Pr[fun result => result.1.hit = true |
        AdaptiveRevealProbe.chargedExperiment AdaptiveRevealProbe.State.empty q
          ((maskedRetainedGameAfterSecrets adversary parameter otsSecret).run emptySplitHashCache)] * q := by
  classical
  have hcost := expected_cost_le_of_relTriple
    (relTriple_chargedExperiment_cost_le_actual_cache_add_hit adversary parameter otsSecret q hbound)
    (fun charged => (charged.2 : ℝ≥0∞)) (fun actual => (probeCachedInputs parameter actual.2.2).ncard)
    (fun charged => if charged.1.hit = true then (q : ℝ≥0∞) else 0) (fun _ _ h => h)
  rw [AdaptiveRevealProbe.chargedExperiment_expectedCost_eq] at hcost
  apply hcost.trans_eq
  congr 1
  rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro result
  split_ifs <;> simp

end SphincsSecurity.Concrete.FtsProbeSimulation
