import SphincsSecurity.Proof.JointProbeSourceRetained

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def runJointFts (table : Coordinate → Digest) (computation : OracleComp JointProbeWorld α)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) :
    OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate) (Option α) :=
  OracleComp.construct
    (C := fun _ => AdaptiveRevealProbe.State Coordinate → Nat →
      OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate) (Option α))
    (fun value state _ => pure (if AdaptiveRevealProbe.tableHits state table then none else some value))
    (fun input _ next state fuel => match input with
      | .inl input => (liftM (OracleSpec.query (spec := LazyRevealProbe.World OtsProbeSimulation.Coordinate) input) :
          OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate) _) >>= fun output => next output state fuel
      | .inr (.uniform n) => (liftM (OracleSpec.query (spec := LazyRevealProbe.World OtsProbeSimulation.Coordinate) (.uniform n)) :
          OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate) _) >>= fun output => next output state fuel
      | .inr .hashOutput => (liftM (OracleSpec.query (spec := LazyRevealProbe.World OtsProbeSimulation.Coordinate) .hashOutput) :
          OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate) _) >>= fun output => next output state fuel
      | .inr (.probe coordinate candidate) => match fuel with
        | 0 => pure none
        | remaining + 1 => match state.revealed coordinate with
          | some _ => next () state remaining
          | none => next () (state.addPending coordinate candidate) remaining
      | .inr (.reveal coordinate) => match state.revealed coordinate with
        | some value => next value state fuel
        | none => if table coordinate ∈ state.pending coordinate then pure none
            else next (table coordinate) (state.install coordinate (table coordinate)) fuel)
    computation state fuel

theorem runJointFts_pure (table : Coordinate → Digest) (value : α)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) :
    runJointFts table (pure value) state fuel = pure (if AdaptiveRevealProbe.tableHits state table then none else some value) := rfl

theorem runJointFts_query_bind (table : Coordinate → Digest)
    (input : JointProbeWorld.Domain) (next : JointProbeWorld.Range input → OracleComp JointProbeWorld α)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) :
    runJointFts table ((liftM (OracleSpec.query input) : OracleComp JointProbeWorld _) >>= next) state fuel =
      match input with
      | .inl input => (liftM (OracleSpec.query (spec := LazyRevealProbe.World OtsProbeSimulation.Coordinate) input) :
          OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate) _) >>= fun output => runJointFts table (next output) state fuel
      | .inr (.uniform n) => (liftM (OracleSpec.query (spec := LazyRevealProbe.World OtsProbeSimulation.Coordinate) (.uniform n)) :
          OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate) _) >>= fun output => runJointFts table (next output) state fuel
      | .inr .hashOutput => (liftM (OracleSpec.query (spec := LazyRevealProbe.World OtsProbeSimulation.Coordinate) .hashOutput) :
          OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate) _) >>= fun output => runJointFts table (next output) state fuel
      | .inr (.probe coordinate candidate) => match fuel with
        | 0 => pure none
        | remaining + 1 => match state.revealed coordinate with
          | some _ => runJointFts table (next ()) state remaining
          | none => runJointFts table (next ()) (state.addPending coordinate candidate) remaining
      | .inr (.reveal coordinate) => match state.revealed coordinate with
        | some value => runJointFts table (next value) state fuel
        | none => if table coordinate ∈ state.pending coordinate then pure none
            else runJointFts table (next (table coordinate)) (state.install coordinate (table coordinate)) fuel := by
  cases input with
  | inl input => rfl
  | inr input => cases input <;> rfl

theorem runJointFts_probeBound (table : Coordinate → Digest) (computation : OracleComp JointProbeWorld α)
    (q : Nat) (hbound : computation.IsQueryBoundP JointProbeIsProbe q)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) :
    (runJointFts table computation state fuel).IsQueryBoundP LazyRevealProbe.IsProbe q := by
  induction computation using OracleComp.inductionOn generalizing q state fuel with
  | pure value => simp [runJointFts_pure]
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [runJointFts_query_bind]
      cases input with
      | inl input =>
          rw [isQueryBoundP_query_bind_iff]
          refine ⟨hbound.1, fun output => ih output _ ?_ state fuel⟩
          by_cases hp : LazyRevealProbe.IsProbe input <;> simpa [JointProbeIsProbe, hp] using hbound.2 output
      | inr input =>
          cases input with
          | uniform n =>
              rw [isQueryBoundP_query_bind_iff]
              refine ⟨Or.inl (by simp [LazyRevealProbe.IsProbe]), fun output => ?_⟩
              exact ih output q (by simpa [JointProbeIsProbe, AdaptiveRevealProbe.IsProbe] using hbound.2 output) state fuel
          | hashOutput =>
              rw [isQueryBoundP_query_bind_iff]
              refine ⟨Or.inl (by simp [LazyRevealProbe.IsProbe]), fun output => ?_⟩
              exact ih output q (by simpa [JointProbeIsProbe, AdaptiveRevealProbe.IsProbe] using hbound.2 output) state fuel
          | probe coordinate candidate =>
              dsimp only
              have htail := hbound.2 ()
              simp only [JointProbeIsProbe, AdaptiveRevealProbe.IsProbe, if_true] at htail
              cases fuel with
              | zero => simp
              | succ remaining =>
                  cases state.revealed coordinate with
                  | none => exact (ih () (q - 1) htail (state.addPending coordinate candidate) remaining).mono (Nat.sub_le _ _)
                  | some value => exact (ih () (q - 1) htail state remaining).mono (Nat.sub_le _ _)
          | reveal coordinate =>
              dsimp only
              have htail (value) := ih value q
                (by simpa [JointProbeIsProbe, AdaptiveRevealProbe.IsProbe] using hbound.2 value)
              cases state.revealed coordinate with
              | some value => exact htail value state fuel
              | none =>
                  split_ifs
                  · simp
                  · exact htail (table coordinate) (state.install coordinate (table coordinate)) fuel

end SphincsSecurity.Concrete.FtsProbeSimulation
