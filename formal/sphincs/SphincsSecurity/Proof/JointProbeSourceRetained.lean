import SphincsSecurity.Proof.JointProbeSourceBudget
import SphincsSecurity.Proof.FtsProbeJointRetainedRisk

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] OtsProbeSimulation.maskedPublishedTreeRoot

noncomputable def jointSourceRetained (adversary : Adversary) (parameter : PublicParameter) (q : Nat) :
    JointSource (Option RetainedGameResult) := do
  let root ← jointSourceNativeBlock OtsProbeSimulation.maskedPublishedTreeRoot
  jointSourceComputation parameter root
    (Option.map (fun rest => (root, rest)) <$>
      OtsProbeSimulation.capOuterHashQueries (retainedGameRestComputation adversary ⟨root, parameter⟩) q)

theorem jointSourceRetained_implements (adversary : Adversary) (parameter : PublicParameter) (q : Nat) :
    JointSourceImplements (jointSourceRetained adversary parameter q) (maskedJointRetained adversary parameter q) :=
  JointSourceImplements.bind (runJointErasedHistory_nativeBlock _)
    (fun root => jointSourceComputation_implements parameter root _)

theorem jointSourceRetained_probeBound (adversary : Adversary) (parameter : PublicParameter) (q : Nat) :
    JointSourceProbeBound (jointSourceRetained adversary parameter q) q := by
  unfold jointSourceRetained
  simpa only [Nat.zero_add] using
    JointSourceProbeBound.bind (jointSourceNativeBlock_probeBound _ 0 OtsProbeSimulation.maskedPublishedTreeRoot_probeFree)
      (fun root => jointSourceComputation_probeBound parameter root _ q
        (by
          rw [isQueryBoundP_map_iff]
          exact OtsProbeSimulation.capOuterHashQueries_hashBound _ q))

theorem runDetailed_jointSourceRetained (adversary : Adversary) (parameter : PublicParameter)
    (table : Coordinate → Digest) (q : Nat) :
    AdaptiveRevealProbe.runDetailed table AdaptiveRevealProbe.State.empty q
      (runJointErasedHistory ((jointSourceRetained adversary parameter q).run
        (OtsProbeSimulation.emptySplitHashCache, emptySplitHashCache))
        (OtsProbeSimulation.ensuredInitialContext ∅) 0 []) =
      AdaptiveRevealProbe.DetailedResult.mapValue packJointStepResult <$>
        jointRetainedDetailed adversary parameter table q := by
  rw [jointSourceRetained_implements adversary parameter q, AdaptiveRevealProbe.runDetailed_mapValue]
  rfl

end SphincsSecurity.Concrete.FtsProbeSimulation
