import SphincsSecurity.Proof.OtsProbePrivateValueReplacement

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def IsPrivateValueExposure (target : Position) (before after : HashOutput) : LazyRevealProbe.Query Coordinate → Prop
  | .reveal coordinate | .publish coordinate => coordinate = .position target
  | .probe coordinate digest => coordinate = .position target ∧
      (digest = truncateHash before ∨ digest = truncateHash after)
  | _ => False

def replacePrivateRunResult (target : Position) (output : HashOutput) (result : ResolvedRunResult α) : ResolvedRunResult α :=
  { result with context := replacePrivatePosition target output result.context }

theorem PrivatePositionReplaceable.addPending
    {target : Position} {before after : HashOutput} {context : DeferredContext}
    (h : PrivatePositionReplaceable target before after context) (coordinate : Coordinate) (digest : Digest)
    (hsafe : ¬IsPrivateValueExposure target before after (.probe coordinate digest)) :
    PrivatePositionReplaceable target before after
      { context with state := context.state.addPending coordinate digest } := by
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  all_goals
    intro hhit
    simp only [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.mem_pendingAt_iff,
      LazyRevealProbe.State.addPending, Finset.mem_insert] at hhit
    rcases hhit with hhit | hhit
    · apply hsafe
      obtain ⟨hcoordinate, hdigest⟩ := Prod.mk.inj hhit
      exact ⟨hcoordinate.symm, by first | exact Or.inl hdigest.symm | exact Or.inr hdigest.symm⟩
    · first
      | apply h.2.2.1
        simpa [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.mem_pendingAt_iff] using hhit
      | apply h.2.2.2
        simpa [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.mem_pendingAt_iff] using hhit

theorem PrivatePositionReplaceable.materialize_other
    {target : Position} {before after : HashOutput} {context : DeferredContext}
    (h : PrivatePositionReplaceable target before after context)
    (coordinate : Coordinate) (output : HashOutput) (values : DeferredStructuralValues)
    (hne : coordinate ≠ .position target) (hvalue : values target = some before) :
    PrivatePositionReplaceable target before after
      { state := context.state.materialize coordinate output, values := values } := by
  refine ⟨?_, hvalue, ?_, ?_⟩
  · simpa [LazyRevealProbe.State.materialize, Function.update_of_ne (Ne.symm hne)] using h.1
  all_goals
    intro hhit
    simp only [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.mem_pendingAt_iff,
      LazyRevealProbe.State.materialize, LazyRevealProbe.State.pendingAway, Finset.mem_filter] at hhit
    first
    | apply h.2.2.1
      simpa [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.mem_pendingAt_iff] using hhit.1
    | apply h.2.2.2
      simpa [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.mem_pendingAt_iff] using hhit.1

theorem privateValue_preserved_by_resolveDeferredReveal
    (target position : Position) (before : HashOutput) (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (result : DeferredResolution)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = some before)
    (hresult : some result ∈ support (resolveDeferredReveal table position context)) :
    result.values target = some before := by
  have hknown : context.positionValue target = some before := by simp [DeferredContext.positionValue, hstate, hvalue]
  have hpreserved : result.toDeferredContext.positionValue target = some before := by
    unfold resolveDeferredReveal at hresult
    split_ifs at hresult
    · exact resolveDeferredPosition_preserves_positionValue table position context result target before hknown hresult
    · exact resolveDeferredPositionValue_preserves_positionValue position target context result before hknown hresult
  have hstates := resolveDeferredReveal_preserves_state_values table position context result hresult
  simpa [DeferredContext.positionValue, hstates, hstate] using hpreserved

theorem evalDist_runResolved_replacePrivatePosition
    (target : Position) (before after : HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (h : PrivatePositionReplaceable target before after context)
    (hsafe : computation.IsQueryBoundP (IsPrivateValueExposure target before after) 0) :
    evalDist (runResolvedFromTable (replacePrivatePosition target after context) fuel table computation) =
      evalDist (Option.map (replacePrivateRunResult target after) <$> runResolvedFromTable context fuel table computation) := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value => simp [runResolvedFromTable, replacePrivateRunResult]
  | query_bind query next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hsafe
      have hquery : ¬IsPrivateValueExposure target before after query := by simpa using hsafe.1
      have hnext : ∀ output, (next output).IsQueryBoundP (IsPrivateValueExposure target before after) 0 := by
        intro output
        simpa using hsafe.2 output
      cases query with
      | uniform n =>
          rw [runResolvedFromTable_uniform_query_bind, runResolvedFromTable_uniform_query_bind, map_bind]
          apply evalDist_bind_congr
          intro output _
          exact ih output context fuel h (hnext output)
      | hashOutput =>
          rw [runResolvedFromTable_hashOutput_query_bind, runResolvedFromTable_hashOutput_query_bind, map_bind]
          apply evalDist_bind_congr
          intro output _
          exact ih output context fuel h (hnext output)
      | ensure coordinate =>
          rw [runResolvedFromTable_ensure_query_bind, runResolvedFromTable_ensure_query_bind]
          exact ih () { context with state := context.state.ensure coordinate } fuel h (hnext ())
      | peek coordinate =>
          rw [runResolvedFromTable_peek_query_bind, runResolvedFromTable_peek_query_bind]
          exact ih _ context fuel h (hnext _)
      | publish coordinate =>
          rw [runResolvedFromTable_publish_query_bind, runResolvedFromTable_publish_query_bind]
          exact ih () { context with state := context.state.publish coordinate } fuel h (hnext ())
      | probe coordinate digest =>
          rw [runResolvedFromTable_probe_query_bind, runResolvedFromTable_probe_query_bind]
          cases fuel with
          | zero => simp
          | succ remaining =>
              dsimp only [replacePrivatePosition]
              split_ifs with hrevealed
              · exact ih () context remaining h (hnext ())
              · exact ih () { context with state := context.state.addPending coordinate digest } remaining
                  (h.addPending coordinate digest hquery) (hnext ())
      | reveal coordinate =>
          rw [runResolvedFromTable_reveal_query_bind, runResolvedFromTable_reveal_query_bind]
          have hne : coordinate ≠ .position target := hquery
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              simp only [resolveDeferredChainStart_replacePrivatePosition, pure_bind]
              cases hresolved : resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ context with
              | none => simp
              | some result =>
                  have hvalues : result.values = context.values := by
                    unfold resolveDeferredChainStart at hresolved
                    dsimp only at hresolved
                    split at hresolved <;> split_ifs at hresolved <;> simp_all
                    all_goals rw [← hresolved]
                  have hcontinue := h.materialize_other (.chainStart lay tree leafIdx chainIdx) result.output result.values
                    (by simp) (hvalues ▸ h.2.1)
                  exact ih result.output _ fuel hcontinue (hnext result.output)
          | position position =>
              have hposition : position ≠ target := fun heq => hne (congrArg Coordinate.position heq)
              rw [evalDist_bind, evalDist_resolveDeferredReveal_replacePrivatePosition target position before after table
                context h, ← evalDist_bind, bind_map_left, map_bind]
              apply evalDist_bind_congr
              intro option hoption
              cases option with
              | none => simp
              | some result =>
                  have hvalue := privateValue_preserved_by_resolveDeferredReveal target position before table context result
                    h.1 h.2.1 hoption
                  have hcontinue := h.materialize_other (.position position) result.output result.values hne hvalue
                  simpa only [Option.map, replacePrivateResolution, replacePrivatePosition, Option.some.injEq, hposition, ↓reduceIte] using
                    ih result.output _ fuel hcontinue (hnext result.output)

end SphincsSecurity.Concrete.OtsProbeSimulation
