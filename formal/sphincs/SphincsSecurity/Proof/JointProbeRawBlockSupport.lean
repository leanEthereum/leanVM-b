import SphincsSecurity.Proof.JointProbeResolvedBlockSupport
import SphincsSecurity.Proof.JointProbeCachePotential

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem runRaw_jointSourceNativeBlock
    (table : Coordinate → Digest) (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache) :
    AdaptiveRevealProbe.runRaw table state ftsFuel
      (runJointResolved ((jointSourceNativeBlock computation).run cache) context fuel otsTable) =
      (fun result => AdaptiveRevealProbe.RawResult.done state ftsFuel
        (result.map (packResolvedNativeBlock cache.2))) <$>
        OtsProbeSimulation.runResolvedFromTable context fuel otsTable (computation.run (prepareNativeCache cache.2 cache.1)) := by
  conv_lhs => dsimp only [jointSourceNativeBlock, StateT.run]
  rw [runJointResolved_map, runJointResolved_native, AdaptiveRevealProbe.runRaw_mapValue,
    AdaptiveRevealProbe.runRaw_liftProbComp, Functor.map_map]
  rfl

theorem mem_support_jointSourceNativeBlock_raw_done
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel remaining : Nat)
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (entry : ResolvedRunResult (α × JointSourceCache))
    (hresult : .done finalState remaining (some entry) ∈ support (AdaptiveRevealProbe.runRaw table state ftsFuel
      (runJointResolved ((jointSourceNativeBlock computation).run cache) context fuel otsTable))) :
    ∃ native, some native ∈ support (OtsProbeSimulation.runResolvedFromTable context fuel otsTable
      (computation.run (prepareNativeCache cache.2 cache.1))) ∧
      finalState = state ∧ remaining = ftsFuel ∧ entry = packResolvedNativeBlock cache.2 native := by
  rw [runRaw_jointSourceNativeBlock, support_map] at hresult
  obtain ⟨nativeOption, hnative, heq⟩ := hresult
  cases nativeOption with
  | none => simp at heq
  | some native =>
      simp only [Option.map_some, AdaptiveRevealProbe.RawResult.done.injEq, Option.some.injEq] at heq
      exact ⟨native, hnative, heq.1.symm, heq.2.1.symm, heq.2.2.symm⟩

def wrapRawResolvedFtsBlock (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput)
    (cache : OtsProbeSimulation.SplitHashCache) : AdaptiveRevealProbe.RawResult Coordinate (α × SplitHashCache) →
      AdaptiveRevealProbe.RawResult Coordinate (Option (ResolvedRunResult (α × JointSourceCache))) :=
  AdaptiveRevealProbe.RawResult.mapValue (fun result => some ⟨context, fuel, (result.1, cache, result.2), otsTable⟩)

theorem runRaw_jointSourceFtsBlock
    (table : Coordinate → Digest) (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (computation : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache) :
    AdaptiveRevealProbe.runRaw table state ftsFuel
      (runJointResolved ((jointSourceFtsBlock computation).run cache) context fuel otsTable) =
      wrapRawResolvedFtsBlock context fuel otsTable cache.1 <$>
        AdaptiveRevealProbe.runRaw table state ftsFuel (computation.run cache.2) := by
  conv_lhs => dsimp only [jointSourceFtsBlock, StateT.run]
  rw [runJointResolved_map, runJointResolved_fts, Functor.map_map, AdaptiveRevealProbe.runRaw_mapValue]
  rfl

theorem mem_support_jointSourceFtsBlock_raw_done
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel remaining : Nat)
    (computation : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (entry : ResolvedRunResult (α × JointSourceCache))
    (hresult : .done finalState remaining (some entry) ∈ support (AdaptiveRevealProbe.runRaw table state ftsFuel
      (runJointResolved ((jointSourceFtsBlock computation).run cache) context fuel otsTable))) :
    ∃ value finalCache, entry = ⟨context, fuel, (value, cache.1, finalCache), otsTable⟩ ∧
      .done finalState remaining (value, finalCache) ∈
        support (AdaptiveRevealProbe.runRaw table state ftsFuel (computation.run cache.2)) := by
  rw [runRaw_jointSourceFtsBlock, support_map] at hresult
  obtain ⟨result, hresult, heq⟩ := hresult
  cases result with
  | stopped hit => simp [wrapRawResolvedFtsBlock, AdaptiveRevealProbe.RawResult.mapValue] at heq
  | done resultState resultFuel value =>
      simp only [wrapRawResolvedFtsBlock, AdaptiveRevealProbe.RawResult.mapValue,
        AdaptiveRevealProbe.RawResult.done.injEq, Option.some.injEq] at heq
      obtain ⟨hstate, hfuel, hentry⟩ := heq
      subst finalState
      subst remaining
      subst entry
      exact ⟨value.1, value.2, rfl, hresult⟩

theorem mem_support_jointSource_bind_raw_done
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel remaining : Nat)
    (left : JointSource α) (next : α → JointSource β)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (entry : ResolvedRunResult (β × JointSourceCache))
    (hresult : .done finalState remaining (some entry) ∈ support (AdaptiveRevealProbe.runRaw table state ftsFuel
      (runJointResolved ((left >>= next).run cache) context fuel otsTable))) :
    ∃ middleState middleFuel middle,
      AdaptiveRevealProbe.RawResult.done middleState middleFuel (some middle) ∈ support
        (AdaptiveRevealProbe.runRaw table state ftsFuel (runJointResolved (left.run cache) context fuel otsTable)) ∧
      .done finalState remaining (some entry) ∈ support (AdaptiveRevealProbe.runRaw table middleState middleFuel
        (runJointResolved ((next middle.value.1).run middle.value.2) middle.context middle.remaining middle.table)) := by
  rw [StateT.run_bind, runJointResolved_bind, AdaptiveRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨middle, hmiddle, hrest⟩ := hresult
  cases middle with
  | stopped hit => simp at hrest
  | done middleState middleFuel middle =>
      cases middle with
      | none => simp [AdaptiveRevealProbe.runRaw] at hrest
      | some middle => exact ⟨middleState, middleFuel, middle, hmiddle, hrest⟩

theorem mem_support_jointSourceUnmergedNativeBlock_raw_done
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel remaining : Nat)
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (entry : ResolvedRunResult (α × JointSourceCache))
    (hresult : .done finalState remaining (some entry) ∈ support (AdaptiveRevealProbe.runRaw table state ftsFuel
      (runJointResolved ((jointSourceUnmergedNativeBlock computation).run cache) context fuel otsTable))) :
    ∃ native, some native ∈ support (OtsProbeSimulation.runResolvedFromTable context fuel otsTable (computation.run cache.1)) ∧
      finalState = state ∧ remaining = ftsFuel ∧
      entry = ⟨native.context, native.remaining, (native.value.1, native.value.2, cache.2), native.table⟩ := by
  simp only [jointSourceUnmergedNativeBlock, StateT.run] at hresult
  rw [runJointResolved_map, runJointResolved_native, AdaptiveRevealProbe.runRaw_mapValue,
    AdaptiveRevealProbe.runRaw_liftProbComp, Functor.map_map, support_map] at hresult
  obtain ⟨nativeOption, hnative, heq⟩ := hresult
  cases nativeOption with
  | none => simp [AdaptiveRevealProbe.RawResult.mapValue] at heq
  | some native =>
      simp only [AdaptiveRevealProbe.RawResult.mapValue, Option.map_some,
        AdaptiveRevealProbe.RawResult.done.injEq, Option.some.injEq] at heq
      exact ⟨native, hnative, heq.1.symm, heq.2.1.symm, heq.2.2.symm⟩

end SphincsSecurity.Concrete.FtsProbeSimulation
