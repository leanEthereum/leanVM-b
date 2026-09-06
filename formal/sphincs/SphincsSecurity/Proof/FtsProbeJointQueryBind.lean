import SphincsSecurity.Proof.FtsProbeJointQueryInvariants
import SphincsSecurity.Proof.AdaptiveRevealProbeBind

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def jointHashRemaining (parameter : PublicParameter) (input : HashInput) (remaining : Nat) : Nat :=
  match decodeProbe? parameter input with
  | none => remaining + 1
  | some _ => remaining

theorem maskedJointHashQuery_run_decode_some
    (parameter : PublicParameter) (input : HashInput) (probe : FtsSecretProbe)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache)
    (hdecode : decodeProbe? parameter input = some probe) :
    (maskedJointHashQuery parameter input context fuel history cache).run ftsCache =
      (AdaptiveRevealProbe.probeQuery (probe.index, probe.tree, probe.leafIdx) probe.candidate >>= fun _ =>
        (liftFtsBlock (splitHashQuery (.ordinary input)) context fuel history cache).run ftsCache) := by
  unfold maskedJointHashQuery
  simp only [hdecode]
  rw [liftFtsBlock, StateT.run_map, probingHashQuery_run_eq, hdecode]
  simp only [map_bind]
  rfl

theorem runDetailed_maskedJointHashQuery_bind
    (parameter : PublicParameter) (table : Coordinate → Digest) (input : HashInput)
    (state : AdaptiveRevealProbe.State Coordinate) (remaining : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache)
    (next : NativeStepResult HashOutput × SplitHashCache → OracleComp (AdaptiveRevealProbe.World Coordinate) α) :
    AdaptiveRevealProbe.runDetailed table state (remaining + 1)
      (((maskedJointHashQuery parameter input context fuel history cache).run ftsCache) >>= next) =
      AdaptiveRevealProbe.runDetailed table state (remaining + 1)
        ((maskedJointHashQuery parameter input context fuel history cache).run ftsCache) >>= fun result =>
          match result with
          | .stopped hit => pure (.stopped hit)
          | .done _ finalState value =>
              AdaptiveRevealProbe.runDetailed table finalState (jointHashRemaining parameter input remaining) (next value) := by
  cases hdecode : decodeProbe? parameter input with
  | none =>
      simp only [maskedJointHashQuery, jointHashRemaining, hdecode]
      convert (AdaptiveRevealProbe.runDetailed_bind_probeFree table state (remaining + 1)
        ((liftNativeBlock (OtsProbeSimulation.probingHashQuery parameter input) context fuel history cache).run ftsCache) next
        (liftNativeBlock_probeFree (OtsProbeSimulation.probingHashQuery parameter input) context fuel history cache ftsCache)) using 1
      apply bind_congr
      intro result
      cases result <;> rfl
  | some probe =>
      rw [maskedJointHashQuery_run_decode_some parameter input probe context fuel history cache ftsCache hdecode]
      simp only [jointHashRemaining, hdecode]
      convert (AdaptiveRevealProbe.runDetailed_bind_probePrefix table state remaining
        (probe.index, probe.tree, probe.leafIdx) probe.candidate
        ((liftFtsBlock (splitHashQuery (.ordinary input)) context fuel history cache).run ftsCache) next
        (liftFtsBlock_probeFree _ context fuel history cache (splitHashQuery_probeFree (.ordinary input)) ftsCache)) using 1
      apply bind_congr
      intro result
      cases result <;> rfl

end SphincsSecurity.Concrete.FtsProbeSimulation
