import SphincsSecurity.Proof.OtsProbeErasedHistoryCostBound
import SphincsSecurity.Proof.FtsProbeJointStepCharge

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] OtsProbeSimulation.maskedPublishedTreeRoot

theorem joint_erased_probe_step_cost_le_one
    (parameter : PublicParameter) (input : HashInput)
    (context : OtsProbeSimulation.DeferredContext) (cache : OtsProbeSimulation.SplitHashCache)
    (state : AdaptiveRevealProbe.State FtsProbeSimulation.Coordinate) :
    OtsProbeSimulation.expectedErasedHistoryProbeCost ((OtsProbeSimulation.probingHashQuery parameter input).run cache) context +
      (FtsProbeSimulation.jointHashProbeCharge parameter input state : ENNReal) ≤ 1 := by
  cases hdecode : FtsProbeSimulation.decodeProbe? parameter input with
  | none =>
      simp only [FtsProbeSimulation.jointHashProbeCharge, hdecode, Nat.cast_zero, add_zero]
      simpa only [Nat.cast_one] using OtsProbeSimulation.expectedErasedHistoryProbeCost_le_probeBound _ context 1
        (OtsProbeSimulation.probingHashQuery_run_isProbeBound parameter input cache)
  | some probe =>
      rw [FtsProbeSimulation.nativeProbingHashQuery_eq_ordinary_of_decodeProbe parameter input probe hdecode]
      change OtsProbeSimulation.expectedErasedHistoryProbeCost ((OtsProbeSimulation.splitHashQuery (.ordinary input)).run cache) context + _ ≤ _
      rw [OtsProbeSimulation.expectedErasedHistoryProbeCost_eq_zero_of_probeFree _ context
          (OtsProbeSimulation.splitHashQuery_probeFree (.ordinary input) cache), zero_add]
      exact (Nat.cast_le.mpr (FtsProbeSimulation.jointHashProbeCharge_le_one parameter input state)).trans_eq (by simp)

theorem erased_signing_probe_cost_eq_zero
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (message : Message) (context : OtsProbeSimulation.DeferredContext) (cache : OtsProbeSimulation.SplitHashCache) :
    OtsProbeSimulation.expectedErasedHistoryProbeCost
      ((OtsProbeSimulation.maskedPublishedChronologicalSign parameter root ftsSecret message).run cache) context = 0 :=
  OtsProbeSimulation.expectedErasedHistoryProbeCost_eq_zero_of_probeFree _ context
    (OtsProbeSimulation.maskedPublishedChronologicalSign_probeFree parameter root ftsSecret message cache)

theorem erased_root_probe_cost_eq_zero
    (context : OtsProbeSimulation.DeferredContext) (cache : OtsProbeSimulation.SplitHashCache) :
    OtsProbeSimulation.expectedErasedHistoryProbeCost (OtsProbeSimulation.maskedPublishedTreeRoot.run cache) context = 0 :=
  OtsProbeSimulation.expectedErasedHistoryProbeCost_eq_zero_of_probeFree _ context
    (OtsProbeSimulation.maskedPublishedTreeRoot_probeFree cache)

end SphincsSecurity.Concrete
