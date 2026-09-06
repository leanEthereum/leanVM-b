import SphincsSecurity.Proof.JointProbeRawInterpreterOrder
import SphincsSecurity.Proof.OtsProbeErasedHistoryCostBound

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem expectedErasedHistoryProbeCost_map
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (f : α → β) (context : DeferredContext) :
    expectedErasedHistoryProbeCost (f <$> computation) context = expectedErasedHistoryProbeCost computation context := by
  rw [map_eq_bind_pure_comp, expectedErasedHistoryProbeCost_bind]
  have hpure (value : β) (context : DeferredContext) : expectedErasedHistoryProbeCost (pure value) context = 0 := by
    simp [expectedErasedHistoryProbeCost, runErasedHistoryCharged]
  simp only [Function.comp_def, hpure]
  calc
    _ = expectedErasedHistoryProbeCost computation context + 0 := by
      congr 1
      apply ENNReal.tsum_eq_zero.mpr
      intro entry
      cases entry <;> simp
    _ = _ := add_zero _

end SphincsSecurity.Concrete.OtsProbeSimulation

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (HistoryResolvedPrefix)
set_option backward.isDefEq.respectTransparency false

noncomputable def expectedJointNativeProbeCost (table : Coordinate → Digest) (computation : OracleComp JointProbeWorld α)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat) (context : OtsProbeSimulation.DeferredContext) : ENNReal :=
  OtsProbeSimulation.expectedErasedHistoryProbeCost (runJointFtsRaw table computation state ftsFuel) context

theorem expectedJointNativeProbeCost_eq_finalized
    (table : Coordinate → Digest) (computation : OracleComp JointProbeWorld α)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat) (context : OtsProbeSimulation.DeferredContext) :
    expectedJointNativeProbeCost table computation state ftsFuel context =
      OtsProbeSimulation.expectedErasedHistoryProbeCost (runJointFts table computation state ftsFuel) context := by
  rw [runJointFts_eq_finalize_raw, OtsProbeSimulation.expectedErasedHistoryProbeCost_map]
  rfl

theorem expectedJointNativeProbeCost_bind
    (table : Coordinate → Digest) (left : OracleComp JointProbeWorld α) (next : α → OracleComp JointProbeWorld β)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat) (context : OtsProbeSimulation.DeferredContext) :
    expectedJointNativeProbeCost table (left >>= next) state ftsFuel context =
      expectedJointNativeProbeCost table left state ftsFuel context +
        ∑' result, Pr[= result | AdaptiveRevealProbe.runRaw table state ftsFuel (runJointErasedHistory left context 0 [])] *
          match result with
          | .stopped _ => 0
          | .done finalState remaining result => match result with
            | none => 0
            | some entry => expectedJointNativeProbeCost table (next entry.value) finalState remaining entry.context := by
  let tailCost : Option (HistoryResolvedPrefix (AdaptiveRevealProbe.State Coordinate × Nat × α)) → ENNReal
    | none => 0
    | some entry => expectedJointNativeProbeCost table (next entry.value.2.2) entry.value.1 entry.value.2.1 entry.context
  unfold expectedJointNativeProbeCost at ⊢
  rw [runJointFtsRaw_bind, OtsProbeSimulation.expectedErasedHistoryProbeCost_bind]
  congr 1
  calc
    _ = ∑' result, Pr[= result | flattenRawHistory <$>
        OtsProbeSimulation.runResolvedHistoryPrefix
          (OtsProbeSimulation.eraseProbeQueries (runJointFtsRaw table left state ftsFuel)) context 0 []] * tailCost result := by
      rw [tsum_probOutput_map_mul]
      apply tsum_congr
      intro result
      congr 1
      cases result with
      | none => rfl
      | some entry =>
          cases hvalue : entry.value with
          | stopped hit =>
              simp [flattenRawHistory, tailCost, hvalue, OtsProbeSimulation.expectedErasedHistoryProbeCost,
                OtsProbeSimulation.runErasedHistoryCharged]
          | done finalState remaining value => simp [flattenRawHistory, tailCost, hvalue, expectedJointNativeProbeCost]
    _ = ∑' result, Pr[= result | rawJointHistory <$>
        AdaptiveRevealProbe.runRaw table state ftsFuel (runJointErasedHistory left context 0 [])] * tailCost result := by
      rw [runJointFtsRaw_erasedHistory_commute]
    _ = _ := by
      rw [tsum_probOutput_map_mul]
      apply tsum_congr
      intro result
      congr 1
      cases result with
      | stopped hit => rfl
      | done finalState remaining entry => cases entry <;> rfl

end SphincsSecurity.Concrete.FtsProbeSimulation
