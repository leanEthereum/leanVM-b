import SphincsSecurity.Proof.JointProbeSource
import SphincsSecurity.Proof.FtsProbeJointQuery

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (HistoryResolvedPrefix)

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

abbrev JointSourceCache := OtsProbeSimulation.SplitHashCache × SplitHashCache
abbrev JointSource (α : Type) := StateT JointSourceCache (OracleComp JointProbeWorld) α

noncomputable def jointSourceNativeBlock
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α) :
    JointSource α := fun cache =>
  (fun result => (result.1, result.2, withNativeOrdinaryCache cache.2 result.2)) <$>
    jointNativeSource (computation.run (prepareNativeCache cache.2 cache.1))

noncomputable def jointSourceFtsBlock
    (computation : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α) :
    JointSource α := fun cache =>
  (fun result => (result.1, cache.1, result.2)) <$> jointFtsSource (computation.run cache.2)

def packJointStepResult (result : NativeStepResult α × SplitHashCache) :
    Option (HistoryResolvedPrefix (α × JointSourceCache)) :=
  result.1.map (fun entry => ⟨entry.context, entry.remaining, (entry.value.1, entry.value.2, result.2), entry.history⟩)

def JointSourceImplements (source : JointSource α) (step : NativeFtsStep α) : Prop :=
  ∀ context fuel history cache,
    runJointErasedHistory (source.run cache) context fuel history =
      packJointStepResult <$> (step context fuel history cache.1).run cache.2

theorem JointSourceImplements.bind
    {left : JointSource α} {next : α → JointSource β}
    {step : NativeFtsStep α} {stepNext : α → NativeFtsStep β}
    (hleft : JointSourceImplements left step)
    (hnext : ∀ value, JointSourceImplements (next value) (stepNext value)) :
    JointSourceImplements (left >>= next) (bindNativeSteps step stepNext) := by
  intro context fuel history cache
  rw [StateT.run_bind, runJointErasedHistory_bind, hleft, bind_map_left]
  rw [bindNativeSteps, StateT.run_bind, map_bind]
  apply bind_congr
  rintro ⟨result, finalCache⟩
  cases result with
  | none => rfl
  | some entry => exact hnext entry.value.1 entry.context entry.remaining entry.history (entry.value.2, finalCache)

theorem runJointErasedHistory_nativeBlock
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : JointSourceCache) :
    runJointErasedHistory ((jointSourceNativeBlock computation).run cache) context fuel history =
      packJointStepResult <$> (liftNativeBlock computation context fuel history cache.1).run cache.2 := by
  conv_lhs => dsimp only [jointSourceNativeBlock, StateT.run]
  rw [runJointErasedHistory_map, runJointErasedHistory_native, liftNativeBlock_run, map_bind]
  rw [map_eq_bind_pure_comp]
  apply bind_congr
  intro result
  cases result <;> rfl

theorem runJointErasedHistory_ftsBlock
    (computation : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : JointSourceCache) :
    runJointErasedHistory ((jointSourceFtsBlock computation).run cache) context fuel history =
      packJointStepResult <$> (liftFtsBlock computation context fuel history cache.1).run cache.2 := by
  conv_lhs => dsimp only [jointSourceFtsBlock, StateT.run]
  rw [runJointErasedHistory_map, runJointErasedHistory_fts, liftFtsBlock, StateT.run_map]
  simp only [Functor.map_map]
  rfl

theorem jointSourceNativeBlock_probeBound
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (q : Nat) (hbound : ∀ cache, (computation.run cache).IsQueryBoundP LazyRevealProbe.IsProbe q)
    (cache : JointSourceCache) :
    ((jointSourceNativeBlock computation).run cache).IsQueryBoundP JointProbeIsProbe q := by
  dsimp only [jointSourceNativeBlock, StateT.run]
  rw [isQueryBoundP_map_iff]
  exact jointNativeSource_probeBound _ q (hbound _)

theorem jointSourceFtsBlock_probeBound
    (computation : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α)
    (q : Nat) (hbound : ∀ cache, (computation.run cache).IsQueryBoundP AdaptiveRevealProbe.IsProbe q)
    (cache : JointSourceCache) :
    ((jointSourceFtsBlock computation).run cache).IsQueryBoundP JointProbeIsProbe q := by
  dsimp only [jointSourceFtsBlock, StateT.run]
  rw [isQueryBoundP_map_iff]
  exact jointFtsSource_probeBound _ q (hbound _)

noncomputable def jointSourceHashQuery (parameter : PublicParameter) (input : HashInput) : JointSource HashOutput :=
  match decodeProbe? parameter input with
  | none => jointSourceNativeBlock (OtsProbeSimulation.probingHashQuery parameter input)
  | some _ => jointSourceFtsBlock (probingHashQuery parameter input)

theorem runJointErasedHistory_hashQuery
    (parameter : PublicParameter) (input : HashInput)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : JointSourceCache) :
    runJointErasedHistory ((jointSourceHashQuery parameter input).run cache) context fuel history =
      packJointStepResult <$> (maskedJointHashQuery parameter input context fuel history cache.1).run cache.2 := by
  unfold jointSourceHashQuery maskedJointHashQuery
  cases decodeProbe? parameter input with
  | none => exact runJointErasedHistory_nativeBlock _ context fuel history cache
  | some probe => exact runJointErasedHistory_ftsBlock _ context fuel history cache

theorem jointSourceHashQuery_probeBound
    (parameter : PublicParameter) (input : HashInput) (cache : JointSourceCache) :
    ((jointSourceHashQuery parameter input).run cache).IsQueryBoundP JointProbeIsProbe 1 := by
  unfold jointSourceHashQuery
  cases decodeProbe? parameter input with
  | none =>
      exact jointSourceNativeBlock_probeBound _ 1
        (OtsProbeSimulation.probingHashQuery_run_isProbeBound parameter input) cache
  | some probe => exact jointSourceFtsBlock_probeBound _ 1 (probingHashQuery_run_isProbeBound parameter input) cache

end SphincsSecurity.Concrete.FtsProbeSimulation
