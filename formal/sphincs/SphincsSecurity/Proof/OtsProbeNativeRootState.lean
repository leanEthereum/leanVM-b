import SphincsSecurity.Proof.OtsProbeNativeValueObservation

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

structure NativeRootContextRel (target : Position) (before after : HashOutput)
    (left right : DeferredContext) : Prop where
  replaceable : NativePositionReplaceable target before after left
  right_eq : right = replaceNativePosition target after left

theorem NativeRootContextRel.ensure
    {target : Position} {before after : HashOutput} {left right : DeferredContext}
    (h : NativeRootContextRel target before after left right) (coordinate : Coordinate) :
    NativeRootContextRel target before after
      { left with state := left.state.ensure coordinate }
      { right with state := right.state.ensure coordinate } := by
  refine ⟨⟨h.replaceable.known, h.replaceable.consistent.ensure coordinate,
    h.replaceable.beforeMiss, h.replaceable.afterMiss⟩, ?_⟩
  rw [h.right_eq]
  rfl

theorem NativeRootContextRel.publish
    {target : Position} {before after : HashOutput} {left right : DeferredContext}
    (h : NativeRootContextRel target before after left right) (coordinate : Coordinate) :
    NativeRootContextRel target before after
      { left with state := left.state.publish coordinate }
      { right with state := right.state.publish coordinate } := by
  refine ⟨⟨h.replaceable.known, h.replaceable.consistent.publish coordinate,
    h.replaceable.beforeMiss, h.replaceable.afterMiss⟩, ?_⟩
  rw [h.right_eq]
  rfl

theorem RootHiddenCacheRel.right_eq_replace
    {target : Position} {before after : HashOutput} {left right : SplitHashCache}
    (h : RootHiddenCacheRel target before after left right) :
    right = replaceHiddenRootCache target after left := by
  funext key
  cases key with
  | ordinary input => simpa [replaceHiddenRootCache] using (h.ordinary input).symm
  | hidden coordinate =>
      by_cases heq : coordinate = .position target
      · subst coordinate
        simpa [replaceHiddenRootCache] using h.right_target
      · simpa [replaceHiddenRootCache, heq] using (h.other_hidden coordinate heq).symm

theorem NativePositionReplaceable.of_materialized_chainStart
    {target : Position} {before after : HashOutput} {context : DeferredContext}
    (h : NativePositionReplaceable target before after context)
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex) (result : DeferredResolution)
    (hresult : resolveDeferredChainStart table index context = some result) :
    NativePositionReplaceable target before after (materializeResolvedChainStart context index result) := by
  refine ⟨?_, h.consistent.materializeResolvedChainStart_of table index result hresult, ?_, ?_⟩
  · rw [materializeResolvedChainStart_positionValue_eq table index context result hresult]
    exact h.known
  all_goals
    intro hhit
    simp only [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.mem_pendingAt_iff,
      materializeResolvedChainStart, LazyRevealProbe.State.materialize,
      LazyRevealProbe.State.pendingAway, Finset.mem_filter] at hhit
    first
    | apply h.beforeMiss
      simpa [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.mem_pendingAt_iff] using hhit.1
    | apply h.afterMiss
      simpa [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.mem_pendingAt_iff] using hhit.1

theorem nativeRevealOutput_support
    (target : Position) (before after : HashOutput) (context : DeferredContext)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (cache : SplitHashCache) (h : NativePositionReplaceable target before after context)
    (result : ResolvedRunResult (HashOutput × SplitHashCache))
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table ((revealCoordinateOutput coordinate).run cache))) :
    NativePositionReplaceable target before after result.context ∧
      result.value.2 = Function.update cache (.hidden coordinate) (some result.value.1) := by
  rw [runResolvedFromTable_revealCoordinateOutput] at hresult
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      cases hresolved : resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ context with
      | none => simp [hresolved] at hresult
      | some resolved =>
          simp [hresolved] at hresult
          subst result
          exact ⟨h.of_materialized_chainStart table ⟨lay, tree, leafIdx, chainIdx⟩ resolved hresolved, rfl⟩
  | position position =>
      rw [mem_support_bind_iff] at hresult
      obtain ⟨resolvedOption, hresolved, hrest⟩ := hresult
      cases resolvedOption with
      | none => simp at hrest
      | some resolved =>
          simp at hrest
          subst result
          exact ⟨h.of_materialized_reveal position table resolved hresolved, rfl⟩

def NativeRootRevealOutputRel (target : Position) (before after : HashOutput) (coordinate : Coordinate) :
    Option (ResolvedRunResult (HashOutput × SplitHashCache)) →
      Option (ResolvedRunResult (HashOutput × SplitHashCache)) → Prop
  | some left, some right =>
      NativeRootContextRel target before after left.context right.context ∧
        left.remaining = right.remaining ∧ left.table = right.table ∧
        right.value.1 = (if coordinate = .position target then after else left.value.1) ∧
        (coordinate = .position target → left.value.1 = before) ∧
        RootHiddenCacheRel target before after left.value.2 right.value.2
  | none, none => True
  | _, _ => False

theorem relTriple_nativeRoot_revealCoordinateOutput
    (target : Position) (before after : HashOutput) (coordinate : Coordinate)
    (left right : DeferredContext) (hcontext : NativeRootContextRel target before after left right)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (leftCache rightCache : SplitHashCache)
    (hcache : RootHiddenCacheRel target before after leftCache rightCache) :
    RelTriple
      (runResolvedFromTable left fuel table ((revealCoordinateOutput coordinate).run leftCache))
      (runResolvedFromTable right fuel table ((revealCoordinateOutput coordinate).run rightCache))
      (NativeRootRevealOutputRel target before after coordinate) := by
  rw [hcontext.right_eq, hcache.right_eq_replace]
  apply relTriple_of_evalDist_eq_right
    (evalDist_revealCoordinateOutput_replaceNativePosition target before after left fuel table
      coordinate leftCache hcontext.replaceable).symm
  let run := runResolvedFromTable left fuel table ((revealCoordinateOutput coordinate).run leftCache)
  have hcoupling := FtsProbeSimulation.relTriple_and_left_support (relTriple_refl run)
    (fun result => result ∈ support run) (fun _ hresult => hresult)
  have hpost : RelTriple run run (fun leftResult rightResult =>
      NativeRootRevealOutputRel target before after coordinate leftResult
        (Option.map (replaceNativeRevealRunResult target after coordinate) rightResult)) := by
    apply relTriple_post_mono hcoupling
    intro leftResult rightResult hrel
    rcases hrel with ⟨heq, hsupported⟩
    subst rightResult
    cases leftResult with
    | none => trivial
    | some result =>
        obtain ⟨hnext, hnextCache⟩ := nativeRevealOutput_support target before after left fuel table
          coordinate leftCache hcontext.replaceable result hsupported
        have hvalue : coordinate = .position target → result.value.1 = before := by
          intro heq
          subst coordinate
          have hstate := value_of_mem_runResolvedFromTable_revealCoordinateOutput left fuel table
            (.position target) leftCache result hsupported
          simpa [DeferredContext.positionValue, hstate] using hnext.known
        have hcached : result.value.2 (.hidden (.position target)) = some before := by
          rw [hnextCache]
          by_cases heq : coordinate = .position target
          · simp [heq, hvalue heq]
          · have hkey : SplitHashKey.hidden (.position target) ≠ .hidden coordinate := by
              simpa using Ne.symm heq
            rw [Function.update_of_ne hkey]
            exact hcache.left_target
        exact ⟨⟨hnext, rfl⟩, rfl, rfl, rfl, hvalue,
          rootHiddenCacheRel_replace target before after result.value.2 hcached⟩
  simpa only [id_map] using
    (relTriple_map (f := id) (g := Option.map (replaceNativeRevealRunResult target after coordinate)) hpost)

end SphincsSecurity.Concrete.OtsProbeSimulation
