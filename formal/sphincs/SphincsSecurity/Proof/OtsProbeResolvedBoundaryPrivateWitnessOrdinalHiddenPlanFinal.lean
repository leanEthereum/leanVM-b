import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalHiddenPlan

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

theorem purePlanProbingHashQuery_candidate_hasStructuralParent
    (parameter : PublicParameter) (input : HashInput)
    (state : LazyRevealProbe.State Coordinate) (candidate : Probe)
    (hplan : (purePlanProbingHashQuery parameter input state).candidate? = some candidate) :
    candidate.HasStructuralParent := by
  cases hprobe : decodeProbe? parameter input with
  | some decoded =>
      rcases decodePosition?_chain_or_leaf_of_decodeProbe? parameter input decoded hprobe with
        hchain | hleaf
      · obtain ⟨lay, tree, leafIdx, chainIdx, step, hposition⟩ := hchain
        exact purePlan_candidate_parent_probe_chain parameter input state decoded candidate lay
          tree leafIdx chainIdx step hprobe hposition hplan
      · obtain ⟨lay, tree, leafIdx, hposition⟩ := hleaf
        exact purePlan_candidate_parent_probe_leaf parameter input state decoded candidate lay tree
          leafIdx hprobe hposition hplan
  | none =>
      by_cases hnode : ∃ lay tree level nodeIdx,
          decodePosition? parameter input = some (.node lay tree level nodeIdx)
      · obtain ⟨lay, tree, level, nodeIdx, hposition⟩ := hnode
        exact purePlan_candidate_parent_node parameter input state candidate lay tree level nodeIdx
          hprobe hposition hplan
      · have hnone := purePlan_candidate_none_of_probe_none_nonnode parameter input state
          hprobe hnode
        rw [hnone] at hplan
        contradiction

end SphincsSecurity.Concrete.OtsProbeSimulation
