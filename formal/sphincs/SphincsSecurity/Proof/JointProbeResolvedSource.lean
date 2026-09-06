import SphincsSecurity.Proof.JointProbeRawInterpreterOrder

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def runJointResolved (computation : OracleComp JointProbeWorld α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    OracleComp (AdaptiveRevealProbe.World Coordinate) (Option (ResolvedRunResult α)) :=
  OracleComp.construct
    (C := fun _ => OtsProbeSimulation.DeferredContext → Nat → (OtsSecretIndex → HashOutput) →
      OracleComp (AdaptiveRevealProbe.World Coordinate) (Option (ResolvedRunResult α)))
    (fun value context fuel table => pure (some ⟨context, fuel, value, table⟩))
    (fun input _ next context fuel table => match input with
      | .inl input =>
          AdaptiveRevealProbe.liftProbComp
            (OtsProbeSimulation.runResolvedFromTable context fuel table
              (liftM (OracleSpec.query (spec := LazyRevealProbe.World OtsProbeSimulation.Coordinate) input))) >>= fun result =>
            match result with
            | none => pure none
            | some entry => next entry.value entry.context entry.remaining entry.table
      | .inr input => (liftM (OracleSpec.query (spec := AdaptiveRevealProbe.World Coordinate) input) :
          OracleComp (AdaptiveRevealProbe.World Coordinate) _) >>= fun output => next output context fuel table)
    computation context fuel table

theorem runJointResolved_pure (value : α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    runJointResolved (pure value) context fuel table = pure (some ⟨context, fuel, value, table⟩) := rfl

theorem runJointResolved_query_bind
    (input : JointProbeWorld.Domain) (next : JointProbeWorld.Range input → OracleComp JointProbeWorld α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    runJointResolved ((liftM (OracleSpec.query input) : OracleComp JointProbeWorld _) >>= next) context fuel table =
      match input with
      | .inl input =>
          AdaptiveRevealProbe.liftProbComp
            (OtsProbeSimulation.runResolvedFromTable context fuel table
              (liftM (OracleSpec.query (spec := LazyRevealProbe.World OtsProbeSimulation.Coordinate) input))) >>= fun result =>
            match result with
            | none => pure none
            | some entry => runJointResolved (next entry.value) entry.context entry.remaining entry.table
      | .inr input => (liftM (OracleSpec.query (spec := AdaptiveRevealProbe.World Coordinate) input) :
          OracleComp (AdaptiveRevealProbe.World Coordinate) _) >>= fun output => runJointResolved (next output) context fuel table := by
  cases input <;> rfl

theorem runJointResolved_bind (left : OracleComp JointProbeWorld α) (next : α → OracleComp JointProbeWorld β)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    runJointResolved (left >>= next) context fuel table =
      runJointResolved left context fuel table >>= fun result => match result with
        | none => pure none
        | some entry => runJointResolved (next entry.value) entry.context entry.remaining entry.table := by
  induction left using OracleComp.inductionOn generalizing context fuel table with
  | pure value => rfl
  | query_bind input continuation ih =>
      rw [bind_assoc, runJointResolved_query_bind, runJointResolved_query_bind]
      cases input with
      | inl input =>
          rw [bind_assoc]
          apply bind_congr
          intro result
          cases result with
          | none => rfl
          | some entry => exact ih entry.value entry.context entry.remaining entry.table
      | inr input =>
          rw [bind_assoc]
          exact bind_congr (fun output => ih output context fuel table)

theorem runJointResolved_native
    (computation : OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    runJointResolved (jointNativeSource computation) context fuel table =
      AdaptiveRevealProbe.liftProbComp (OtsProbeSimulation.runResolvedFromTable context fuel table computation) := by
  induction computation using OracleComp.inductionOn generalizing context fuel table with
  | pure value => rfl
  | query_bind input next ih =>
      rw [jointNativeSource, construct_query_bind, runJointResolved_query_bind,
        OtsProbeSimulation.runResolvedFromTable_bind, AdaptiveRevealProbe.liftProbComp, simulateQ_bind]
      apply bind_congr
      intro result
      cases result with
      | none => rfl
      | some entry => exact ih entry.value entry.context entry.remaining entry.table

theorem runJointResolved_fts
    (computation : OracleComp (AdaptiveRevealProbe.World Coordinate) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    runJointResolved (jointFtsSource computation) context fuel table =
      (fun value => some (⟨context, fuel, value, table⟩ : ResolvedRunResult α)) <$> computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [jointFtsSource, construct_query_bind, runJointResolved_query_bind, map_bind]
      exact bind_congr ih

theorem runJointResolved_map (computation : OracleComp JointProbeWorld α) (f : α → β)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    runJointResolved (f <$> computation) context fuel table =
      Option.map (fun entry => (⟨entry.context, entry.remaining, f entry.value, entry.table⟩ : ResolvedRunResult β)) <$>
        runJointResolved computation context fuel table := by
  rw [map_eq_bind_pure_comp, runJointResolved_bind, map_eq_bind_pure_comp]
  apply bind_congr
  intro result
  cases result <;> rfl

end SphincsSecurity.Concrete.FtsProbeSimulation
