import SphincsSecurity.Proof.FtsProbeJointExecution
import SphincsSecurity.Proof.AdaptiveRevealProbeCostProbeFree

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def jointHashProbeCharge (parameter : PublicParameter) (input : HashInput)
    (state : AdaptiveRevealProbe.State Coordinate) : Nat :=
  match decodeProbe? parameter input with
  | none => 0
  | some probe => AdaptiveRevealProbe.unrevealedProbeCharge state (probe.index, probe.tree, probe.leafIdx) probe.candidate

theorem jointHashProbeCharge_le_one (parameter : PublicParameter) (input : HashInput)
    (state : AdaptiveRevealProbe.State Coordinate) : jointHashProbeCharge parameter input state ≤ 1 := by
  unfold jointHashProbeCharge
  cases decodeProbe? parameter input with
  | none => simp only; omega
  | some probe => exact AdaptiveRevealProbe.unrevealedProbeCharge_le_one state _ _

theorem runCharged_maskedJointHashQuery_bind
    (parameter : PublicParameter) (table : Coordinate → Digest) (input : HashInput)
    (state : AdaptiveRevealProbe.State Coordinate) (remaining : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache)
    (next : NativeStepResult HashOutput × SplitHashCache → OracleComp (AdaptiveRevealProbe.World Coordinate) α) :
    AdaptiveRevealProbe.runCharged table state (remaining + 1)
      (((maskedJointHashQuery parameter input context fuel history cache).run ftsCache) >>= next) =
      AdaptiveRevealProbe.runDetailed table state (remaining + 1)
        ((maskedJointHashQuery parameter input context fuel history cache).run ftsCache) >>= fun result =>
          match result with
          | .stopped hit => pure (.stopped hit, jointHashProbeCharge parameter input state)
          | .done _ finalState value =>
              (fun result => (result.1, result.2 + jointHashProbeCharge parameter input state)) <$>
                AdaptiveRevealProbe.runCharged table finalState (jointHashRemaining parameter input remaining) (next value) := by
  cases hdecode : decodeProbe? parameter input with
  | none =>
      simp only [maskedJointHashQuery, jointHashRemaining, jointHashProbeCharge, hdecode]
      rw [AdaptiveRevealProbe.runCharged_bind_probeFree table state (remaining + 1) _ _
        (liftNativeBlock_probeFree (OtsProbeSimulation.probingHashQuery parameter input) context fuel history cache ftsCache)]
      apply bind_congr
      intro result
      cases result <;> simp
  | some probe =>
      rw [maskedJointHashQuery_run_decode_some parameter input probe context fuel history cache ftsCache hdecode]
      simp only [jointHashRemaining, jointHashProbeCharge, hdecode]
      convert (AdaptiveRevealProbe.runCharged_bind_probePrefix table state remaining
        (probe.index, probe.tree, probe.leafIdx) probe.candidate _ next
        (liftFtsBlock_probeFree _ context fuel history cache (splitHashQuery_probeFree (.ordinary input)) ftsCache)) using 1
      apply bind_congr
      intro result
      cases result <;> rfl

theorem runCharged_maskedJointSign
    (parameter : PublicParameter) (root : Digest) (message : Message) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache) :
    AdaptiveRevealProbe.runCharged table state ftsFuel
      ((maskedJointSign parameter root message context fuel history cache).run ftsCache) =
      (fun result => (result, 0)) <$> AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((maskedJointSign parameter root message context fuel history cache).run ftsCache) :=
  AdaptiveRevealProbe.runCharged_probeFree table state ftsFuel _
    (maskedJointSign_probeFree parameter root message context fuel history cache ftsCache)

theorem runCharged_maskedJointSign_bind
    (parameter : PublicParameter) (root : Digest) (message : Message) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache)
    (next : NativeStepResult (Option Signature) × SplitHashCache → OracleComp (AdaptiveRevealProbe.World Coordinate) α) :
    AdaptiveRevealProbe.runCharged table state ftsFuel
      (((maskedJointSign parameter root message context fuel history cache).run ftsCache) >>= next) =
      AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((maskedJointSign parameter root message context fuel history cache).run ftsCache) >>= fun result =>
          match result with
          | .stopped hit => pure (.stopped hit, 0)
          | .done _ finalState value => AdaptiveRevealProbe.runCharged table finalState ftsFuel (next value) := by
  convert (AdaptiveRevealProbe.runCharged_bind_probeFree table state ftsFuel _ next
    (maskedJointSign_probeFree parameter root message context fuel history cache ftsCache)) using 1
  apply bind_congr
  intro result
  cases result <;> rfl

end SphincsSecurity.Concrete.FtsProbeSimulation
