import SphincsSecurity.Proof.LazyRevealProbeCostBind
import SphincsSecurity.Proof.OtsProbeResolvedAdaptiveClean

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local irreducible] maskedPublishedTreeRoot

theorem probEvent_sampledRunThenFinalizeClean_none_le_expectedCharge
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe fuel) :
    Pr[= none | sampledRunThenFinalizeClean state fuel computation] ≤
      (LazyRevealProbe.expectedProbeCharge computation state fuel + (state.pending.card : ℝ≥0∞)) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    _ = Pr[= none | detailedExperimentCleanWithCompletionTable state fuel computation] :=
      probOutput_congr rfl (by
        unfold sampledRunThenFinalizeClean
        exact evalDist_runThenFinalizeCleanFromTable_eq_detailed computation state fuel)
    _ = Pr[= true | LazyRevealProbe.experiment state fuel computation] :=
      probEvent_detailedExperimentClean_none_eq_hit computation state fuel hbound
    _ ≤ _ := by
      rw [← probEvent_eq_eq_probOutput]
      exact LazyRevealProbe.experiment_probability_le_expectedProbeCharge state fuel computation

theorem probEvent_sampledRunThenFinalizeClean_empty_none_le_expectedCharge_of_not_stopped_false
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (fuel : Nat)
    (hnotStopped : LazyRevealProbe.RawResult.stopped false ∉ support
      (LazyRevealProbe.runRaw (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel computation)) :
    Pr[= none | sampledRunThenFinalizeClean
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel computation] ≤
      LazyRevealProbe.expectedProbeCharge computation LazyRevealProbe.State.empty fuel *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    _ = Pr[= none | detailedExperimentCleanWithCompletionTable
        (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel computation] :=
      probOutput_congr rfl (by
        unfold sampledRunThenFinalizeClean
        exact evalDist_runThenFinalizeCleanFromTable_eq_detailed computation LazyRevealProbe.State.empty fuel)
    _ = Pr[= true | LazyRevealProbe.experiment
        (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel computation] :=
      probEvent_detailedExperimentClean_none_eq_hit_of_not_stopped_false computation
        LazyRevealProbe.State.empty fuel hnotStopped
    _ ≤ _ := by
      rw [← probEvent_eq_eq_probOutput]
      exact LazyRevealProbe.experiment_empty_probability_le_expectedProbeCharge fuel computation

noncomputable def deferredOtsProbeCharge (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat) : ℝ≥0∞ :=
  LazyRevealProbe.expectedProbeCharge (deferredCleanRetainedRun adversary parameter ftsSecret)
    LazyRevealProbe.State.empty q

theorem deferredOtsProbeCharge_le_q (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat) :
    deferredOtsProbeCharge adversary parameter ftsSecret q ≤ q :=
  LazyRevealProbe.expectedProbeCharge_le_fuel _ _ _

theorem deferredOtsProbeCharge_eq_expectedCost (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat) :
    deferredOtsProbeCharge adversary parameter ftsSecret q =
      ∑' result, Pr[= result | LazyRevealProbe.runCharged LazyRevealProbe.State.empty q
        (deferredCleanRetainedRun adversary parameter ftsSecret)] * (result.2 : ℝ≥0∞) :=
  (LazyRevealProbe.runCharged_expectedCost_eq _ _ _).symm

theorem maskedSign_expectedProbeCharge_eq_zero (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) (fuel : Nat) :
    LazyRevealProbe.expectedProbeCharge ((maskedSign parameter root ftsSecret message).run cache) state fuel = 0 :=
  LazyRevealProbe.expectedProbeCharge_eq_zero_of_probeFree _ state fuel
    (maskedSign_probeFree parameter root ftsSecret message cache)

theorem maskedPublishedTreeRoot_expectedProbeCharge_eq_zero
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) (fuel : Nat) :
    LazyRevealProbe.expectedProbeCharge (maskedPublishedTreeRoot.run cache) state fuel = 0 :=
  LazyRevealProbe.expectedProbeCharge_eq_zero_of_probeFree _ state fuel (maskedPublishedTreeRoot_probeFree cache)

theorem probEvent_sampledDeferredCleanFinish_none_le_expectedCharge
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[= none | sampledRunThenFinalizeClean
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) q
        (deferredCleanRetainedRun adversary parameter ftsSecret)] ≤
      deferredOtsProbeCharge adversary parameter ftsSecret q * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
  probEvent_sampledRunThenFinalizeClean_empty_none_le_expectedCharge_of_not_stopped_false
    (deferredCleanRetainedRun adversary parameter ftsSecret) q
    (stopped_false_not_mem_support_deferredCleanRetainedRun adversary q hq parameter hparameter ftsSecret hfts)

end SphincsSecurity.Concrete.OtsProbeSimulation
