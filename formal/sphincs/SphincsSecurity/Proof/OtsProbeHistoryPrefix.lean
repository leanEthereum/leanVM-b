import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeHistoryAdaptiveInterpreter

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

structure HistoryResolvedPrefix (α : Type) where
  context : DeferredContext
  remaining : Nat
  value : α
  history : List Probe

noncomputable def runResolvedHistoryPrefix
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    DeferredContext → Nat → List Probe → ProbComp (Option (HistoryResolvedPrefix α)) :=
  OracleComp.construct
    (fun value context fuel history => pure (some ⟨context, fuel, value, history⟩))
    (fun input _ next => historyAdaptiveQueryStep input next) computation

theorem runResolvedHistoryPrefix_query_bind
    (input : (LazyRevealProbe.World Coordinate).Domain)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) :
    runResolvedHistoryPrefix (OracleSpec.query input >>= next) context fuel history =
      historyAdaptiveQueryStep input (fun output => runResolvedHistoryPrefix (next output)) context fuel history := rfl

noncomputable def completeHistoryResolvedPrefix :
    Option (HistoryResolvedPrefix α) → ProbComp (Option (ResolvedRunResult α))
  | none => pure none
  | some entry => completeResolvedHistory entry.context entry.remaining entry.history entry.value

theorem historyCompletionQueryStep_bind
    (history : List Probe) (input : (LazyRevealProbe.World Coordinate).Domain)
    (next : (LazyRevealProbe.World Coordinate).Range input → DeferredContext → Nat → ProbComp (Option α))
    (context : DeferredContext) (fuel : Nat) (observe : Option α → ProbComp (Option β))
    (hnone : observe none = pure none) :
    historyCompletionQueryStep history input next context fuel >>= observe =
      historyCompletionQueryStep history input (fun output context fuel => next output context fuel >>= observe) context fuel := by
  cases input with
  | uniform n => simp only [historyCompletionQueryStep, bind_assoc]
  | hashOutput => simp only [historyCompletionQueryStep, bind_assoc]
  | ensure coordinate => rfl
  | peek coordinate => rfl
  | publish coordinate => rfl
  | probe coordinate digest => simpa only [historyCompletionQueryStep, pure_bind] using hnone
  | reveal coordinate =>
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          simp only [historyCompletionQueryStep, OtsSecretIndex.coordinate]
          cases hknown : context.state.values (.chainStart lay tree leafIdx chainIdx) with
          | some output =>
              dsimp only
              split_ifs <;> simp only [pure_bind, hnone]
          | none =>
              dsimp only
              rw [bind_assoc]
              apply bind_congr
              intro output
              split_ifs <;> simp only [pure_bind, hnone]
      | position position =>
          simp only [historyCompletionQueryStep, bind_assoc]
          apply bind_congr
          intro option
          cases option <;> simp only [pure_bind, hnone]

theorem historyAdaptiveQueryStep_bind
    (input : (LazyRevealProbe.World Coordinate).Domain)
    (next : (LazyRevealProbe.World Coordinate).Range input → DeferredContext → Nat → List Probe → ProbComp (Option α))
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (observe : Option α → ProbComp (Option β))
    (hnone : observe none = pure none) :
    historyAdaptiveQueryStep input next context fuel history >>= observe =
      historyAdaptiveQueryStep input (fun output context fuel history => next output context fuel history >>= observe)
        context fuel history := by
  cases input
  case probe coordinate digest =>
    cases fuel with
    | zero => simpa only [historyAdaptiveQueryStep, pure_bind] using hnone
    | succ remaining =>
        simp only [historyAdaptiveQueryStep]
        split_ifs <;> rfl
  all_goals
    simp only [historyAdaptiveQueryStep]
    exact historyCompletionQueryStep_bind history _ _ context fuel observe hnone

noncomputable def runResolvedHistoryWith
    (terminal : HistoryResolvedPrefix α → ProbComp (Option β))
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    DeferredContext → Nat → List Probe → ProbComp (Option β) :=
  OracleComp.construct
    (fun value context fuel history => terminal ⟨context, fuel, value, history⟩)
    (fun input _ next => historyAdaptiveQueryStep input next) computation

theorem runResolvedHistoryWith_eq_prefix
    (terminal : HistoryResolvedPrefix α → ProbComp (Option β))
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) :
    runResolvedHistoryWith terminal computation context fuel history =
      runResolvedHistoryPrefix computation context fuel history >>= fun option =>
        match option with
        | none => pure none
        | some entry => terminal entry := by
  induction computation using OracleComp.inductionOn generalizing context fuel history with
  | pure value => simp only [runResolvedHistoryWith, runResolvedHistoryPrefix, OracleComp.construct_pure, pure_bind]
  | query_bind input next ih =>
      rw [runResolvedHistoryWith, OracleComp.construct_query_bind, runResolvedHistoryPrefix_query_bind,
        historyAdaptiveQueryStep_bind input (fun output => runResolvedHistoryPrefix (next output))
          context fuel history (fun option => match option with | none => pure none | some entry => terminal entry) rfl]
      apply congrArg (fun next => historyAdaptiveQueryStep input next context fuel history)
      funext output context fuel history
      exact ih output context fuel history

theorem runResolvedHistoryAdaptive_eq_prefix_complete
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) :
    runResolvedHistoryAdaptive computation context fuel history =
      runResolvedHistoryPrefix computation context fuel history >>= completeHistoryResolvedPrefix := by
  exact runResolvedHistoryWith_eq_prefix
    (fun entry => completeResolvedHistory entry.context entry.remaining entry.history entry.value)
    computation context fuel history

theorem historyPrefix_invariant_of_mem
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel bound : Nat) (history : List Probe) (result : HistoryResolvedPrefix α)
    (hcovered : PendingCoveredBy history context)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe bound)
    (hresult : some result ∈ support (runResolvedHistoryPrefix computation context fuel history)) :
    PendingCoveredBy result.history result.context ∧ result.history.length ≤ history.length + bound := by
  induction computation using OracleComp.inductionOn generalizing context fuel bound history with
  | pure value =>
      simp only [runResolvedHistoryPrefix, OracleComp.construct_pure, mem_support_pure_iff, Option.some.injEq] at hresult
      subst result
      exact ⟨hcovered, Nat.le_add_right _ _⟩
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [runResolvedHistoryPrefix_query_bind] at hresult
      cases input with
      | uniform n =>
          simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output context fuel bound history hcovered
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output) htail
      | hashOutput =>
          simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output context fuel bound history hcovered
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output) htail
      | ensure coordinate =>
          exact ih () { context with state := context.state.ensure coordinate } fuel bound history hcovered
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 ()) hresult
      | peek coordinate =>
          exact ih (context.state.values coordinate) context fuel bound history hcovered
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 _) hresult
      | publish coordinate =>
          exact ih () { context with state := context.state.publish coordinate } fuel bound history hcovered
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 ()) hresult
      | probe coordinate digest =>
          have hpositive : 0 < bound := by simpa [LazyRevealProbe.IsProbe] using hbound.1
          have htailBound : (next ()).IsQueryBoundP LazyRevealProbe.IsProbe (bound - 1) := by
            simpa [LazyRevealProbe.IsProbe] using hbound.2 ()
          cases fuel with
          | zero => simp [historyAdaptiveQueryStep] at hresult
          | succ remaining =>
              simp only [historyAdaptiveQueryStep] at hresult
              split_ifs at hresult with hrevealed
              · have htail := ih () context remaining (bound - 1) history hcovered htailBound hresult
                exact ⟨htail.1, by omega⟩
              · have htail := ih () { context with state := context.state.addPending coordinate digest }
                  remaining (bound - 1) (history ++ [⟨coordinate, digest⟩])
                  (hcovered.addPending_append history context ⟨coordinate, digest⟩) htailBound hresult
                refine ⟨htail.1, ?_⟩
                have hlength := htail.2
                simp only [List.length_append, List.length_singleton] at hlength
                omega
      | reveal coordinate =>
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, OtsSecretIndex.coordinate] at hresult
              cases hknown : context.state.values (.chainStart lay tree leafIdx chainIdx) with
              | some output =>
                  rw [hknown] at hresult
                  dsimp only at hresult
                  split_ifs at hresult with hhit
                  · simp at hresult
                  · exact ih output
                      { context with state := context.state.materialize (.chainStart lay tree leafIdx chainIdx) output }
                      fuel bound history (hcovered.of_subset (Finset.filter_subset _ _))
                      (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output) hresult
              | none =>
                  rw [hknown] at hresult
                  dsimp only at hresult
                  rw [mem_support_bind_iff] at hresult
                  obtain ⟨output, _houtput, htail⟩ := hresult
                  split_ifs at htail with hhit
                  · simp at htail
                  · exact ih output
                      { context with state := context.state.materialize (.chainStart lay tree leafIdx chainIdx) output }
                      fuel bound history (hcovered.of_subset (Finset.filter_subset _ _))
                      (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output) htail
          | position position =>
              simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, mem_support_bind_iff] at hresult
              obtain ⟨option, _hoption, htail⟩ := hresult
              cases option with
              | none => simp at htail
              | some resolved =>
                  exact ih resolved.output
                    { state := context.state.materialize (.position position) resolved.output, values := resolved.values }
                    fuel bound history (hcovered.of_subset (Finset.filter_subset _ _))
                    (by simpa [LazyRevealProbe.IsProbe] using hbound.2 resolved.output) htail

end SphincsSecurity.Concrete.OtsProbeSimulation
