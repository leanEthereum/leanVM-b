import SphincsSecurity.Proof.JointProbeNativeFtsRisk

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def runJointFtsRaw (table : Coordinate → Digest) (computation : OracleComp JointProbeWorld α)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) :
    OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate) (AdaptiveRevealProbe.RawResult Coordinate α) :=
  OracleComp.construct
    (C := fun _ => AdaptiveRevealProbe.State Coordinate → Nat →
      OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate) (AdaptiveRevealProbe.RawResult Coordinate α))
    (fun value state remaining => pure (.done state remaining value))
    (fun input _ next state fuel => match input with
      | .inl input => (liftM (OracleSpec.query (spec := LazyRevealProbe.World OtsProbeSimulation.Coordinate) input) :
          OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate) _) >>= fun output => next output state fuel
      | .inr (.uniform n) => (liftM (OracleSpec.query (spec := LazyRevealProbe.World OtsProbeSimulation.Coordinate) (.uniform n)) :
          OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate) _) >>= fun output => next output state fuel
      | .inr .hashOutput => (liftM (OracleSpec.query (spec := LazyRevealProbe.World OtsProbeSimulation.Coordinate) .hashOutput) :
          OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate) _) >>= fun output => next output state fuel
      | .inr (.probe coordinate candidate) => match fuel with
        | 0 => pure (.stopped (AdaptiveRevealProbe.tableHits state table))
        | remaining + 1 => match state.revealed coordinate with
          | some _ => next () state remaining
          | none => next () (state.addPending coordinate candidate) remaining
      | .inr (.reveal coordinate) => match state.revealed coordinate with
        | some value => next value state fuel
        | none => if table coordinate ∈ state.pending coordinate then pure (.stopped true)
            else next (table coordinate) (state.install coordinate (table coordinate)) fuel)
    computation state fuel

theorem runJointFtsRaw_pure (table : Coordinate → Digest) (value : α)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) :
    runJointFtsRaw table (pure value) state fuel = pure (.done state fuel value) := rfl

theorem runJointFtsRaw_query_bind (table : Coordinate → Digest)
    (input : JointProbeWorld.Domain) (next : JointProbeWorld.Range input → OracleComp JointProbeWorld α)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) :
    runJointFtsRaw table ((liftM (OracleSpec.query input) : OracleComp JointProbeWorld _) >>= next) state fuel =
      match input with
      | .inl input => (liftM (OracleSpec.query (spec := LazyRevealProbe.World OtsProbeSimulation.Coordinate) input) :
          OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate) _) >>= fun output => runJointFtsRaw table (next output) state fuel
      | .inr (.uniform n) => (liftM (OracleSpec.query (spec := LazyRevealProbe.World OtsProbeSimulation.Coordinate) (.uniform n)) :
          OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate) _) >>= fun output => runJointFtsRaw table (next output) state fuel
      | .inr .hashOutput => (liftM (OracleSpec.query (spec := LazyRevealProbe.World OtsProbeSimulation.Coordinate) .hashOutput) :
          OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate) _) >>= fun output => runJointFtsRaw table (next output) state fuel
      | .inr (.probe coordinate candidate) => match fuel with
        | 0 => pure (.stopped (AdaptiveRevealProbe.tableHits state table))
        | remaining + 1 => match state.revealed coordinate with
          | some _ => runJointFtsRaw table (next ()) state remaining
          | none => runJointFtsRaw table (next ()) (state.addPending coordinate candidate) remaining
      | .inr (.reveal coordinate) => match state.revealed coordinate with
        | some value => runJointFtsRaw table (next value) state fuel
        | none => if table coordinate ∈ state.pending coordinate then pure (.stopped true)
            else runJointFtsRaw table (next (table coordinate)) (state.install coordinate (table coordinate)) fuel := by
  cases input with
  | inl input => rfl
  | inr input => cases input <;> rfl

theorem runJointFtsRaw_bind (table : Coordinate → Digest)
    (left : OracleComp JointProbeWorld α) (next : α → OracleComp JointProbeWorld β)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) :
    runJointFtsRaw table (left >>= next) state fuel =
      runJointFtsRaw table left state fuel >>= fun result => match result with
        | .stopped hit => pure (.stopped hit)
        | .done finalState remaining value => runJointFtsRaw table (next value) finalState remaining := by
  induction left using OracleComp.inductionOn generalizing state fuel with
  | pure value => rfl
  | query_bind input continuation ih =>
      rw [bind_assoc, runJointFtsRaw_query_bind, runJointFtsRaw_query_bind]
      cases input with
      | inl input =>
          rw [bind_assoc]
          exact bind_congr (fun output => ih output state fuel)
      | inr input =>
          cases input with
          | uniform n =>
              rw [bind_assoc]
              exact bind_congr (fun output => ih output state fuel)
          | hashOutput =>
              rw [bind_assoc]
              exact bind_congr (fun output => ih output state fuel)
          | probe coordinate candidate =>
              dsimp only
              cases fuel with
              | zero => rfl
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
                  · rfl
                  · exact ih (table coordinate) (state.install coordinate (table coordinate)) fuel

def finalizeJointFtsRaw (table : Coordinate → Digest) : AdaptiveRevealProbe.RawResult Coordinate α → Option α
  | .stopped _ => none
  | .done state _ value => if AdaptiveRevealProbe.tableHits state table then none else some value

theorem runJointFts_eq_finalize_raw (table : Coordinate → Digest) (computation : OracleComp JointProbeWorld α)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) :
    runJointFts table computation state fuel = finalizeJointFtsRaw table <$> runJointFtsRaw table computation state fuel := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value => rfl
  | query_bind input next ih =>
      rw [runJointFts_query_bind, runJointFtsRaw_query_bind]
      cases input with
      | inl input =>
          rw [map_bind]
          exact bind_congr (fun output => ih output state fuel)
      | inr input =>
          cases input with
          | uniform n =>
              rw [map_bind]
              exact bind_congr (fun output => ih output state fuel)
          | hashOutput =>
              rw [map_bind]
              exact bind_congr (fun output => ih output state fuel)
          | probe coordinate candidate =>
              dsimp only
              cases fuel with
              | zero => rfl
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
                  · rfl
                  · exact ih (table coordinate) (state.install coordinate (table coordinate)) fuel

end SphincsSecurity.Concrete.FtsProbeSimulation
