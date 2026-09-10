import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeStoredRoot
import SphincsSecurity.Proof.OtsProbeNativeValueResolver
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootState

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem replaceNativePosition_materializePosition
    (target position : Position) (after : HashOutput) (context : DeferredContext)
    (result : DeferredResolution) :
    materializeResolvedPosition (replaceNativePosition target after context) position
        (replaceNativeResolution target after (some position) result) =
      replaceNativePosition target after (materializeResolvedPosition context position result) := by
  by_cases heq : position = target
  · subst position
    simp [materializeResolvedPosition, replaceNativeResolution, replaceNativePosition,
      LazyRevealProbe.State.materialize, LazyRevealProbe.State.pendingAway]
  · have hcoordinate : Coordinate.position position ≠ .position target := by simpa using heq
    have hcomm := Function.update_comm (Ne.symm hcoordinate)
      ((context.state.values (.position target)).map fun _ => after) (some result.output)
      context.state.values
    simp [materializeResolvedPosition, replaceNativeResolution, replaceNativePosition, heq,
      Ne.symm hcoordinate, LazyRevealProbe.State.materialize, LazyRevealProbe.State.pendingAway, hcomm]

theorem replaceNativePosition_materializeChainStart
    (target : Position) (after : HashOutput) (context : DeferredContext)
    (index : OtsSecretIndex) (result : DeferredResolution) :
    materializeResolvedChainStart (replaceNativePosition target after context) index
        (replaceNativeResolution target after none result) =
      replaceNativePosition target after (materializeResolvedChainStart context index result) := by
  have hcoordinate : index.coordinate ≠ Coordinate.position target := by
    cases index
    simp [OtsSecretIndex.coordinate]
  have hcomm := Function.update_comm (Ne.symm hcoordinate)
    ((context.state.values (.position target)).map fun _ => after) (some result.output)
    context.state.values
  simp [materializeResolvedChainStart, replaceNativeResolution, replaceNativePosition,
    Ne.symm hcoordinate, LazyRevealProbe.State.materialize, LazyRevealProbe.State.pendingAway, hcomm]

theorem NativePositionReplaceable.of_materialized_reveal
    {target : Position} {before after : HashOutput} {context : DeferredContext}
    (h : NativePositionReplaceable target before after context)
    (position : Position) (table : OtsSecretIndex → HashOutput) (result : DeferredResolution)
    (hresult : some result ∈ support (resolveDeferredReveal table position context)) :
    NativePositionReplaceable target before after (materializeResolvedPosition context position result) := by
  have hstate := resolveDeferredReveal_preserves_state_values table position context result hresult
  have hvalue := resolveDeferredReveal_resolves table position context result hresult
  have hknown := resolveDeferredReveal_preserves_native_value table position context result target before h.known hresult
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [materializeResolvedPosition_positionValue_eq context position result hstate hvalue]
    exact hknown
  · exact h.consistent.materializeResolvedPosition_of table position result hresult
  all_goals
    intro hhit
    simp only [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.mem_pendingAt_iff,
      materializeResolvedPosition, LazyRevealProbe.State.materialize,
      LazyRevealProbe.State.pendingAway, Finset.mem_filter] at hhit
    first
    | apply h.beforeMiss
      simpa [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.mem_pendingAt_iff] using hhit.1
    | apply h.afterMiss
      simpa [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.mem_pendingAt_iff] using hhit.1

def replaceNativeRevealRunResult (target : Position) (after : HashOutput) (coordinate : Coordinate)
    (result : ResolvedRunResult (HashOutput × SplitHashCache)) :
    ResolvedRunResult (HashOutput × SplitHashCache) :=
  { context := replaceNativePosition target after result.context
    remaining := result.remaining
    value := (if coordinate = .position target then after else result.value.1,
      replaceHiddenRootCache target after result.value.2)
    table := result.table }

theorem replaceHiddenRootCache_update_reveal
    (target : Position) (after : HashOutput) (coordinate : Coordinate) (output : HashOutput)
    (cache : SplitHashCache) :
    Function.update (replaceHiddenRootCache target after cache) (.hidden coordinate)
        (some (if coordinate = .position target then after else output)) =
      replaceHiddenRootCache target after (Function.update cache (.hidden coordinate) (some output)) := by
  by_cases heq : coordinate = .position target
  · simp [heq, replaceHiddenRootCache]
  · have hkey : SplitHashKey.hidden coordinate ≠ .hidden (.position target) := by simpa using heq
    simp only [if_neg heq, replaceHiddenRootCache]
    exact Function.update_comm (Ne.symm hkey) _ _ _

theorem evalDist_revealCoordinateOutput_replaceNativePosition
    (target : Position) (before after : HashOutput) (context : DeferredContext)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (cache : SplitHashCache) (h : NativePositionReplaceable target before after context) :
    evalDist (runResolvedFromTable (replaceNativePosition target after context) fuel table
      ((revealCoordinateOutput coordinate).run (replaceHiddenRootCache target after cache))) =
    evalDist (Option.map (replaceNativeRevealRunResult target after coordinate) <$>
      runResolvedFromTable context fuel table ((revealCoordinateOutput coordinate).run cache)) := by
  rw [runResolvedFromTable_revealCoordinateOutput, runResolvedFromTable_revealCoordinateOutput]
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      simp only [resolveDeferredChainStart_replaceNativePosition, pure_bind]
      cases hresolved : resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ context with
      | none => simp
      | some resolved =>
          simp only [Option.map_some, map_pure]
          change evalDist (pure (some (⟨
            materializeResolvedChainStart (replaceNativePosition target after context)
              ⟨lay, tree, leafIdx, chainIdx⟩ (replaceNativeResolution target after none resolved),
            fuel, (resolved.output, Function.update (replaceHiddenRootCache target after cache)
              (.hidden (.chainStart lay tree leafIdx chainIdx)) (some resolved.output)), table⟩ :
                ResolvedRunResult (HashOutput × SplitHashCache)))) = _
          rw [replaceNativePosition_materializeChainStart]
          simp [replaceNativeRevealRunResult, materializeResolvedChainStart,
            ← replaceHiddenRootCache_update_reveal, OtsSecretIndex.coordinate]
  | position position =>
      rw [map_bind, evalDist_bind, evalDist_resolveDeferredReveal_replaceNativePosition target position before after table
        context h, ← evalDist_bind, bind_map_left]
      apply evalDist_bind_congr
      intro resolvedOption _
      cases resolvedOption with
      | none => simp
      | some resolved =>
          simp only [Option.map_some, map_pure]
          change evalDist (pure (some (⟨
            materializeResolvedPosition (replaceNativePosition target after context) position
              (replaceNativeResolution target after (some position) resolved),
            fuel, ((replaceNativeResolution target after (some position) resolved).output,
              Function.update (replaceHiddenRootCache target after cache) (.hidden (.position position))
                (some (replaceNativeResolution target after (some position) resolved).output)), table⟩ :
                  ResolvedRunResult (HashOutput × SplitHashCache)))) = _
          rw [replaceNativePosition_materializePosition]
          simp [replaceNativeRevealRunResult, materializeResolvedPosition, replaceNativeResolution,
            ← replaceHiddenRootCache_update_reveal]

end SphincsSecurity.Concrete.OtsProbeSimulation
