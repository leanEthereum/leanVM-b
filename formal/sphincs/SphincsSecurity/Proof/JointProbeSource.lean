import SphincsSecurity.Proof.FtsProbeNativeStep
import SphincsSecurity.Proof.OtsProbeHistoryCutCap

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (HistoryResolvedPrefix)

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

abbrev JointProbeWorld := LazyRevealProbe.World OtsProbeSimulation.Coordinate + AdaptiveRevealProbe.World Coordinate

def JointProbeIsProbe : JointProbeWorld.Domain → Prop
  | .inl input => LazyRevealProbe.IsProbe input
  | .inr input => AdaptiveRevealProbe.IsProbe input

def jointNativeSource (computation : OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate) α) :
    OracleComp JointProbeWorld α :=
  OracleComp.construct pure (fun input _ next =>
    (liftM (OracleSpec.query (spec := JointProbeWorld) (.inl input)) : OracleComp JointProbeWorld _) >>= next) computation

def jointFtsSource (computation : OracleComp (AdaptiveRevealProbe.World Coordinate) α) :
    OracleComp JointProbeWorld α :=
  OracleComp.construct pure (fun input _ next =>
    (liftM (OracleSpec.query (spec := JointProbeWorld) (.inr input)) : OracleComp JointProbeWorld _) >>= next) computation

noncomputable def runJointErasedHistory (computation : OracleComp JointProbeWorld α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe) :
    OracleComp (AdaptiveRevealProbe.World Coordinate) (Option (HistoryResolvedPrefix α)) :=
  OracleComp.construct
    (C := fun _ => OtsProbeSimulation.DeferredContext → Nat → List OtsProbeSimulation.Probe →
      OracleComp (AdaptiveRevealProbe.World Coordinate) (Option (HistoryResolvedPrefix α)))
    (fun value context fuel history => pure (some ⟨context, fuel, value, history⟩))
    (fun input _ next context fuel history => match input with
      | .inl input =>
          AdaptiveRevealProbe.liftProbComp
            (OtsProbeSimulation.runResolvedHistoryPrefix
              (OtsProbeSimulation.eraseProbeQueries
                (liftM (OracleSpec.query (spec := LazyRevealProbe.World OtsProbeSimulation.Coordinate) input))) context fuel history) >>= fun result =>
            match result with
            | none => pure none
            | some entry => next entry.value entry.context entry.remaining entry.history
      | .inr input => (liftM (OracleSpec.query (spec := AdaptiveRevealProbe.World Coordinate) input) : OracleComp (AdaptiveRevealProbe.World Coordinate) _) >>=
          fun output => next output context fuel history)
    computation context fuel history

theorem runJointErasedHistory_pure (value : α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe) :
    runJointErasedHistory (pure value) context fuel history = pure (some ⟨context, fuel, value, history⟩) := rfl

theorem runJointErasedHistory_query_bind
    (input : JointProbeWorld.Domain) (next : JointProbeWorld.Range input → OracleComp JointProbeWorld α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe) :
    runJointErasedHistory ((liftM (OracleSpec.query input) : OracleComp JointProbeWorld _) >>= next) context fuel history =
      match input with
      | .inl input =>
          AdaptiveRevealProbe.liftProbComp
            (OtsProbeSimulation.runResolvedHistoryPrefix
              (OtsProbeSimulation.eraseProbeQueries
                (liftM (OracleSpec.query (spec := LazyRevealProbe.World OtsProbeSimulation.Coordinate) input))) context fuel history) >>= fun result =>
            match result with
            | none => pure none
            | some entry => runJointErasedHistory (next entry.value) entry.context entry.remaining entry.history
      | .inr input => (liftM (OracleSpec.query (spec := AdaptiveRevealProbe.World Coordinate) input) : OracleComp (AdaptiveRevealProbe.World Coordinate) _) >>=
          fun output => runJointErasedHistory (next output) context fuel history := by
  cases input <;> rfl

theorem runJointErasedHistory_bind
    (left : OracleComp JointProbeWorld α) (next : α → OracleComp JointProbeWorld β)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe) :
    runJointErasedHistory (left >>= next) context fuel history =
      runJointErasedHistory left context fuel history >>= fun result => match result with
        | none => pure none
        | some entry => runJointErasedHistory (next entry.value) entry.context entry.remaining entry.history := by
  induction left using OracleComp.inductionOn generalizing context fuel history with
  | pure value => rfl
  | query_bind input continuation ih =>
      rw [bind_assoc, runJointErasedHistory_query_bind, runJointErasedHistory_query_bind]
      cases input with
      | inl input =>
          rw [bind_assoc]
          apply bind_congr
          intro result
          cases result with
          | none => rfl
          | some entry => exact ih entry.value entry.context entry.remaining entry.history
      | inr input =>
          rw [bind_assoc]
          exact bind_congr (fun output => ih output context fuel history)

theorem runJointErasedHistory_native
    (computation : OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe) :
    runJointErasedHistory (jointNativeSource computation) context fuel history =
      AdaptiveRevealProbe.liftProbComp
        (OtsProbeSimulation.runResolvedHistoryPrefix (OtsProbeSimulation.eraseProbeQueries computation) context fuel history) := by
  induction computation using OracleComp.inductionOn generalizing context fuel history with
  | pure value => rfl
  | query_bind input next ih =>
      rw [jointNativeSource, construct_query_bind, runJointErasedHistory_query_bind]
      rw [OtsProbeSimulation.eraseProbeQueries_query_bind, OtsProbeSimulation.runResolvedHistoryPrefix_bind,
        AdaptiveRevealProbe.liftProbComp, simulateQ_bind]
      apply bind_congr
      intro result
      cases result with
      | none => rfl
      | some entry => exact ih entry.value entry.context entry.remaining entry.history

theorem runJointErasedHistory_map
    (computation : OracleComp JointProbeWorld α) (f : α → β)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe) :
    runJointErasedHistory (f <$> computation) context fuel history =
      (Option.map (fun entry => (⟨entry.context, entry.remaining, f entry.value, entry.history⟩ : HistoryResolvedPrefix β))) <$>
        runJointErasedHistory computation context fuel history := by
  rw [map_eq_bind_pure_comp, runJointErasedHistory_bind, map_eq_bind_pure_comp]
  apply bind_congr
  intro result
  cases result <;> rfl

theorem runJointErasedHistory_fts
    (computation : OracleComp (AdaptiveRevealProbe.World Coordinate) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe) :
    runJointErasedHistory (jointFtsSource computation) context fuel history =
      (fun value => some (⟨context, fuel, value, history⟩ : HistoryResolvedPrefix α)) <$> computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [jointFtsSource, construct_query_bind, runJointErasedHistory_query_bind, map_bind]
      exact bind_congr ih

theorem jointNativeSource_probeBound
    (computation : OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate) α) (q : Nat)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe q) :
    (jointNativeSource computation).IsQueryBoundP JointProbeIsProbe q := by
  induction computation using OracleComp.inductionOn generalizing q with
  | pure value => simp [jointNativeSource]
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [jointNativeSource, construct_query_bind, isQueryBoundP_query_bind_iff]
      refine ⟨hbound.1, fun output => ih output _ ?_⟩
      by_cases hp : LazyRevealProbe.IsProbe input <;> simpa [JointProbeIsProbe, hp] using hbound.2 output

theorem jointFtsSource_probeBound
    (computation : OracleComp (AdaptiveRevealProbe.World Coordinate) α) (q : Nat)
    (hbound : computation.IsQueryBoundP AdaptiveRevealProbe.IsProbe q) :
    (jointFtsSource computation).IsQueryBoundP JointProbeIsProbe q := by
  induction computation using OracleComp.inductionOn generalizing q with
  | pure value => simp [jointFtsSource]
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [jointFtsSource, construct_query_bind, isQueryBoundP_query_bind_iff]
      refine ⟨hbound.1, fun output => ih output _ ?_⟩
      by_cases hp : AdaptiveRevealProbe.IsProbe input <;> simpa [JointProbeIsProbe, hp] using hbound.2 output

end SphincsSecurity.Concrete.FtsProbeSimulation
