import SphincsSecurity.Proof.JointProbeNativeCost

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem runJointFtsRaw_native (table : Coordinate → Digest)
    (computation : OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate) α)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) :
    runJointFtsRaw table (jointNativeSource computation) state fuel =
      (fun value => AdaptiveRevealProbe.RawResult.done state fuel value) <$> computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [jointNativeSource, construct_query_bind, runJointFtsRaw_query_bind, map_bind]
      exact bind_congr ih

theorem runJointFtsRaw_probeBound (table : Coordinate → Digest) (computation : OracleComp JointProbeWorld α)
    (q : Nat) (hbound : computation.IsQueryBoundP JointProbeIsProbe q)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) :
    (runJointFtsRaw table computation state fuel).IsQueryBoundP LazyRevealProbe.IsProbe q := by
  have h := runJointFts_probeBound table computation q hbound state fuel
  rw [runJointFts_eq_finalize_raw, isQueryBoundP_map_iff] at h
  exact h

theorem runJointFtsRaw_fts_probeFree (table : Coordinate → Digest)
    (computation : OracleComp (AdaptiveRevealProbe.World Coordinate) α)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) :
    (runJointFtsRaw table (jointFtsSource computation) state fuel).IsQueryBoundP LazyRevealProbe.IsProbe 0 := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value => simp [jointFtsSource, runJointFtsRaw]
  | query_bind input next ih =>
      rw [jointFtsSource, construct_query_bind, runJointFtsRaw_query_bind]
      cases input with
      | uniform n =>
          rw [isQueryBoundP_query_bind_iff]
          exact ⟨Or.inl (by simp [LazyRevealProbe.IsProbe]), fun output => ih output state fuel⟩
      | hashOutput =>
          rw [isQueryBoundP_query_bind_iff]
          exact ⟨Or.inl (by simp [LazyRevealProbe.IsProbe]), fun output => ih output state fuel⟩
      | probe coordinate candidate =>
          dsimp only
          cases fuel with
          | zero => simp
          | succ remaining =>
              cases state.revealed coordinate with
              | none => exact ih () (state.addPending coordinate candidate) remaining
              | some value => exact ih () state remaining
      | reveal coordinate =>
          dsimp only
          cases state.revealed coordinate with
          | some value => exact ih value state fuel
          | none =>
              split_ifs
              · simp
              · exact ih (table coordinate) (state.install coordinate (table coordinate)) fuel

theorem expectedJointNativeProbeCost_pure (table : Coordinate → Digest) (value : α)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) (context : OtsProbeSimulation.DeferredContext) :
    expectedJointNativeProbeCost table (pure value) state fuel context = 0 := by
  simp [expectedJointNativeProbeCost, runJointFtsRaw_pure, OtsProbeSimulation.expectedErasedHistoryProbeCost,
    OtsProbeSimulation.runErasedHistoryCharged]

theorem expectedJointNativeProbeCost_map (table : Coordinate → Digest) (computation : OracleComp JointProbeWorld α) (f : α → β)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) (context : OtsProbeSimulation.DeferredContext) :
    expectedJointNativeProbeCost table (f <$> computation) state fuel context =
      expectedJointNativeProbeCost table computation state fuel context := by
  rw [map_eq_bind_pure_comp, expectedJointNativeProbeCost_bind]
  calc
    _ = expectedJointNativeProbeCost table computation state fuel context + 0 := by
      congr 1
      apply ENNReal.tsum_eq_zero.mpr
      intro result
      cases result with
      | stopped hit => simp
      | done finalState remaining entry => cases entry <;> simp [expectedJointNativeProbeCost_pure]
    _ = _ := add_zero _


theorem expectedJointNativeProbeCost_eq_zero_of_probeFree (table : Coordinate → Digest) (computation : OracleComp JointProbeWorld α)
    (hbound : computation.IsQueryBoundP JointProbeIsProbe 0)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) (context : OtsProbeSimulation.DeferredContext) :
    expectedJointNativeProbeCost table computation state fuel context = 0 :=
  OtsProbeSimulation.expectedErasedHistoryProbeCost_eq_zero_of_probeFree _ context
    (runJointFtsRaw_probeBound table computation 0 hbound state fuel)

theorem expectedJointNativeProbeCost_nativeBlock (table : Coordinate → Digest)
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) (context : OtsProbeSimulation.DeferredContext) (cache : JointSourceCache) :
    expectedJointNativeProbeCost table ((jointSourceNativeBlock computation).run cache) state fuel context =
      OtsProbeSimulation.expectedErasedHistoryProbeCost (computation.run (prepareNativeCache cache.2 cache.1)) context := by
  conv_lhs => dsimp only [jointSourceNativeBlock, StateT.run]
  rw [expectedJointNativeProbeCost_map, expectedJointNativeProbeCost, runJointFtsRaw_native,
    OtsProbeSimulation.expectedErasedHistoryProbeCost_map]
  rfl

theorem expectedJointNativeProbeCost_ftsBlock (table : Coordinate → Digest)
    (computation : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) (context : OtsProbeSimulation.DeferredContext) (cache : JointSourceCache) :
    expectedJointNativeProbeCost table ((jointSourceFtsBlock computation).run cache) state fuel context = 0 := by
  conv_lhs => dsimp only [jointSourceFtsBlock, StateT.run]
  rw [expectedJointNativeProbeCost_map]
  exact OtsProbeSimulation.expectedErasedHistoryProbeCost_eq_zero_of_probeFree _ context
    (runJointFtsRaw_fts_probeFree table _ state fuel)

end SphincsSecurity.Concrete.FtsProbeSimulation
