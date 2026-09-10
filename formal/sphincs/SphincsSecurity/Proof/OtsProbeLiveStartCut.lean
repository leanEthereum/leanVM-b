import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbePrivateValueCut

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def nativeProbeCutAt (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    Nat → OracleComp (LazyRevealProbe.World Coordinate) (PrivateValueCut α) :=
  OracleComp.construct (fun value _ => pure (.done value))
    (fun input next recursivelyCut ordinal =>
      if LazyRevealProbe.IsProbe input then
        match ordinal with
        | 0 => pure (.query input next)
        | ordinal + 1 => (liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= fun output => recursivelyCut output ordinal
      else (liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= fun output => recursivelyCut output ordinal) computation

theorem nativeProbeCutAt_query_bind
    (input : (LazyRevealProbe.World Coordinate).Domain)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α) (ordinal : Nat) :
    nativeProbeCutAt ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) ordinal =
      (if LazyRevealProbe.IsProbe input then
        match ordinal with
        | 0 => pure (.query input next)
        | ordinal + 1 => (liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= fun output => nativeProbeCutAt (next output) ordinal
      else (liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= fun output => nativeProbeCutAt (next output) ordinal) := rfl

theorem nativeProbeCutAt_probeBound (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (ordinal : Nat) :
    (nativeProbeCutAt computation ordinal).IsQueryBoundP LazyRevealProbe.IsProbe ordinal := by
  induction computation using OracleComp.inductionOn generalizing ordinal with
  | pure value => simp [nativeProbeCutAt]
  | query_bind input next ih =>
      rw [nativeProbeCutAt_query_bind]
      by_cases hprobe : LazyRevealProbe.IsProbe input
      · rw [if_pos hprobe]
        cases ordinal with
        | zero => simp
        | succ ordinal =>
            rw [OracleComp.isQueryBoundP_query_bind_iff]
            exact ⟨Or.inr (by omega), fun output => by simpa only [if_pos hprobe, Nat.add_sub_cancel] using ih output ordinal⟩
      · rw [if_neg hprobe, OracleComp.isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl hprobe, fun output => by simpa only [if_neg hprobe] using ih output ordinal⟩

def nativeCutCandidate (_context : DeferredContext) : PrivateValueCut α → Option Probe
  | .query (.probe coordinate digest) _ => some ⟨coordinate, digest⟩
  | _ => none

end SphincsSecurity.Concrete.OtsProbeSimulation
