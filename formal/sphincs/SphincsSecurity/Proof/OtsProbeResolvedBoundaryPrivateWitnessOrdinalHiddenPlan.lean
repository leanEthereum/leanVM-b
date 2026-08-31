import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalHidden

/-!
# Planned candidate provenance

Every candidate produced by the pure hash planner is either a chain probe or one exact child of a
leaf or node input. Hence a structural candidate always has a named parent. The dependent decoder
branches are stated separately to keep elaboration local.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

theorem purePlan_candidate_parent_probe_leaf
    (parameter : PublicParameter) (input : HashInput)
    (state : LazyRevealProbe.State Coordinate) (decoded candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (hprobe : decodeProbe? parameter input = some decoded)
    (hposition : decodePosition? parameter input = some (.leaf lay tree leafIdx))
    (hplan : (purePlanProbingHashQuery parameter input state).candidate? = some candidate) :
    candidate.HasStructuralParent := by
  have hdecoded := decoded.hasStructuralParent_of_decodeProbe?_eq_some parameter input hprobe
  unfold purePlanProbingHashQuery at hplan
  rw [hprobe, hposition] at hplan
  exact leafInputProbePlan_hasStructuralParent state input decoded candidate lay tree leafIdx
    hdecoded hplan

theorem purePlan_candidate_parent_probe_chain
    (parameter : PublicParameter) (input : HashInput)
    (state : LazyRevealProbe.State Coordinate) (decoded candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (step : ChainStep)
    (hprobe : decodeProbe? parameter input = some decoded)
    (hposition : decodePosition? parameter input =
      some (.chain lay tree leafIdx chainIdx step))
    (hplan : (purePlanProbingHashQuery parameter input state).candidate? = some candidate) :
    candidate.HasStructuralParent := by
  have hdecoded := decoded.hasStructuralParent_of_decodeProbe?_eq_some parameter input hprobe
  unfold purePlanProbingHashQuery at hplan
  rw [hprobe, hposition] at hplan
  exact Option.some.inj hplan.symm ▸ hdecoded

theorem purePlan_candidate_parent_probe_node
    (parameter : PublicParameter) (input : HashInput)
    (state : LazyRevealProbe.State Coordinate) (decoded candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (level : Fin maxLayerHeight) (nodeIdx : LeafIndex)
    (hprobe : decodeProbe? parameter input = some decoded)
    (hposition : decodePosition? parameter input = some (.node lay tree level nodeIdx))
    (hplan : (purePlanProbingHashQuery parameter input state).candidate? = some candidate) :
    candidate.HasStructuralParent := by
  have hdecoded := decoded.hasStructuralParent_of_decodeProbe?_eq_some parameter input hprobe
  unfold purePlanProbingHashQuery at hplan
  rw [hprobe, hposition] at hplan
  exact Option.some.inj hplan.symm ▸ hdecoded

theorem purePlan_candidate_parent_probe_ftsLeaf
    (parameter : PublicParameter) (input : HashInput)
    (state : LazyRevealProbe.State Coordinate) (decoded candidate : Probe)
    (index : Index) (tree : FtsTree) (leafIdx : FtsLeaf)
    (hprobe : decodeProbe? parameter input = some decoded)
    (hposition : decodePosition? parameter input = some (.ftsLeaf index tree leafIdx))
    (hplan : (purePlanProbingHashQuery parameter input state).candidate? = some candidate) :
    candidate.HasStructuralParent := by
  have hdecoded := decoded.hasStructuralParent_of_decodeProbe?_eq_some parameter input hprobe
  unfold purePlanProbingHashQuery at hplan
  rw [hprobe, hposition] at hplan
  exact Option.some.inj hplan.symm ▸ hdecoded

theorem purePlan_candidate_parent_probe_ftsNode
    (parameter : PublicParameter) (input : HashInput)
    (state : LazyRevealProbe.State Coordinate) (decoded candidate : Probe)
    (index : Index) (tree : FtsTree) (level : Fin ftsTreeHeight) (nodeIdx : FtsLeaf)
    (hprobe : decodeProbe? parameter input = some decoded)
    (hposition : decodePosition? parameter input = some (.ftsNode index tree level nodeIdx))
    (hplan : (purePlanProbingHashQuery parameter input state).candidate? = some candidate) :
    candidate.HasStructuralParent := by
  have hdecoded := decoded.hasStructuralParent_of_decodeProbe?_eq_some parameter input hprobe
  unfold purePlanProbingHashQuery at hplan
  rw [hprobe, hposition] at hplan
  exact Option.some.inj hplan.symm ▸ hdecoded

theorem purePlan_candidate_parent_probe_ftsRoots
    (parameter : PublicParameter) (input : HashInput)
    (state : LazyRevealProbe.State Coordinate) (decoded candidate : Probe)
    (index : Index)
    (hprobe : decodeProbe? parameter input = some decoded)
    (hposition : decodePosition? parameter input = some (.ftsRoots index))
    (hplan : (purePlanProbingHashQuery parameter input state).candidate? = some candidate) :
    candidate.HasStructuralParent := by
  have hdecoded := decoded.hasStructuralParent_of_decodeProbe?_eq_some parameter input hprobe
  unfold purePlanProbingHashQuery at hplan
  rw [hprobe, hposition] at hplan
  exact Option.some.inj hplan.symm ▸ hdecoded

theorem purePlan_candidate_parent_probe_no_position
    (parameter : PublicParameter) (input : HashInput)
    (state : LazyRevealProbe.State Coordinate) (decoded candidate : Probe)
    (hprobe : decodeProbe? parameter input = some decoded)
    (hposition : decodePosition? parameter input = none)
    (hplan : (purePlanProbingHashQuery parameter input state).candidate? = some candidate) :
    candidate.HasStructuralParent := by
  have hdecoded := decoded.hasStructuralParent_of_decodeProbe?_eq_some parameter input hprobe
  unfold purePlanProbingHashQuery at hplan
  rw [hprobe, hposition] at hplan
  exact Option.some.inj hplan.symm ▸ hdecoded

theorem purePlan_candidate_parent_node
    (parameter : PublicParameter) (input : HashInput)
    (state : LazyRevealProbe.State Coordinate) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (level : Fin maxLayerHeight) (nodeIdx : LeafIndex)
    (hprobe : decodeProbe? parameter input = none)
    (hposition : decodePosition? parameter input = some (.node lay tree level nodeIdx))
    (hplan : (purePlanProbingHashQuery parameter input state).candidate? = some candidate) :
    candidate.HasStructuralParent := by
  unfold purePlanProbingHashQuery at hplan
  rw [hprobe, hposition] at hplan
  exact hasStructuralParent_of_mem_children_coordinates (.node lay tree level nodeIdx) candidate
    (firstMissingInputCoordinatePlan_some_mem state input 0
      ((Position.node lay tree level nodeIdx).children.map Coordinate.position) candidate hplan)

set_option maxRecDepth 100000 in
theorem purePlan_candidate_none_of_probe_none_nonnode
    (parameter : PublicParameter) (input : HashInput)
    (state : LazyRevealProbe.State Coordinate)
    (hprobe : decodeProbe? parameter input = none)
    (hposition : ¬∃ lay tree level nodeIdx,
      decodePosition? parameter input = some (.node lay tree level nodeIdx)) :
    (purePlanProbingHashQuery parameter input state).candidate? = none := by
  unfold purePlanProbingHashQuery
  rw [hprobe]
  cases hdecoded : decodePosition? parameter input with
  | none => rfl
  | some position =>
      cases position with
      | node lay tree level nodeIdx =>
          exact False.elim (hposition ⟨lay, tree, level, nodeIdx, hdecoded⟩)
      | chain | leaf | ftsLeaf | ftsNode | ftsRoots => rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
