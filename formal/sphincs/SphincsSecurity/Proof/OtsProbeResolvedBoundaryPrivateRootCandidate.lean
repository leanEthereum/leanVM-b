import SphincsSecurity.Proof.EncodingTarget
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivatePlanExecution

/-!
# Root-aware planned candidates

An encoding-domain query carries its guessed layer message in payload slot zero. Top and middle
layer messages are the roots later materialized by the masked signer. This module records that
guess as a proof-only candidate without changing execution of the concrete hash handler.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

def Probe.HasStructuralParent (candidate : Probe) : Prop :=
  match candidate.coordinate with
  | .chainStart _ _ _ _ => True
  | .position position => ∃ parent, Position.parentOf position = some parent

def layerRootPosition (lay : Layer) (tree : TreeIndex) : Position :=
  .node lay tree
    ⟨layerHeight lay - 1, by
      have hpos : 0 < layerHeight lay := by
        unfold layerHeight
        split <;> norm_num [maxLayerHeight]
      have hle := layerHeight_le lay
      omega⟩
    0

def IsLayerRoot (position : Position) : Prop :=
  ∃ lay tree, position = layerRootPosition lay tree

def Probe.IsLayerRoot (candidate : Probe) : Prop :=
  ∃ position, candidate.coordinate = .position position ∧
    SphincsSecurity.Concrete.OtsProbeSimulation.IsLayerRoot position

theorem isShortLayerRoot_of_isLayerRoot_of_parent
    {position parent : Position} (hroot : IsLayerRoot position)
    (hparent : Position.parentOf position = some parent) :
    ∃ lay tree, lay ≠ topLayer ∧ position = layerRootPosition lay tree := by
  obtain ⟨lay, tree, rfl⟩ := hroot
  fin_cases lay
  · simp [layerRootPosition, Position.parentOf, layerHeight,
      maxLayerHeight] at hparent
  · exact ⟨middleLayer, tree, by decide, rfl⟩
  · exact ⟨bottomLayer, tree, by decide, rfl⟩

def EncodingLayerRootCandidateAt (parameter : PublicParameter) (input : HashInput)
    (candidate : Probe) : Prop :=
  ∃ (position : EncodingPosition) (index : Index),
    AtEncodingPosition parameter input position ∧
      treeIndexAt index position.lay = position.tree ∧
      leafIndexAt index position.lay = position.leafIdx ∧
      position.lay ≠ bottomLayer ∧
      candidate = ⟨.position (layerMessagePosition index position.lay), slotDigest 0 input⟩

theorem encodingLayerRootCandidateAt_unique
    {parameter : PublicParameter} {input : HashInput} {left right : Probe}
    (hleft : EncodingLayerRootCandidateAt parameter input left)
    (hright : EncodingLayerRootCandidateAt parameter input right) : left = right := by
  obtain ⟨leftPosition, leftIndex, hleftAt, hleftTree, hleftLeaf, _hleftLayer,
    hleftCandidate⟩ := hleft
  obtain ⟨rightPosition, rightIndex, hrightAt, hrightTree, hrightLeaf, _hrightLayer,
    hrightCandidate⟩ := hright
  have hposition : leftPosition = rightPosition :=
    atEncodingPosition_unique hleftAt hrightAt
  subst rightPosition
  have hmessage : layerMessagePosition leftIndex leftPosition.lay =
      layerMessagePosition rightIndex leftPosition.lay :=
    layerMessagePosition_eq_of_position_eq leftIndex rightIndex leftPosition.lay
      (hleftTree.trans hrightTree.symm) (hleftLeaf.trans hrightLeaf.symm)
  rw [hleftCandidate, hrightCandidate, hmessage]

noncomputable def decodeEncodingLayerRootCandidate?
    (parameter : PublicParameter) (input : HashInput) : Option Probe := by
  classical
  exact if hcandidate : ∃ candidate, EncodingLayerRootCandidateAt parameter input candidate then
    some (Classical.choose hcandidate)
  else none

theorem decodeEncodingLayerRootCandidate?_eq_some_iff
    (parameter : PublicParameter) (input : HashInput) (candidate : Probe) :
    decodeEncodingLayerRootCandidate? parameter input = some candidate ↔
      EncodingLayerRootCandidateAt parameter input candidate := by
  classical
  unfold decodeEncodingLayerRootCandidate?
  split
  next hexists =>
    constructor
    · intro heq
      have hchosen : Classical.choose hexists = candidate := by simpa using heq
      simpa [← hchosen] using Classical.choose_spec hexists
    · intro hcandidate
      have hchosen : Classical.choose hexists = candidate :=
        encodingLayerRootCandidateAt_unique (Classical.choose_spec hexists) hcandidate
      simp [hchosen]
  next hnone =>
    constructor
    · simp
    · intro hcandidate
      exact (hnone ⟨candidate, hcandidate⟩).elim

theorem encodingLayerRootCandidateAt_isLayerRoot
    {parameter : PublicParameter} {input : HashInput} {candidate : Probe}
    (hcandidate : EncodingLayerRootCandidateAt parameter input candidate) :
    ∃ position, candidate.coordinate = .position position ∧ IsLayerRoot position := by
  obtain ⟨position, index, _hat, _htree, _hleaf, hnotBottom, rfl⟩ := hcandidate
  rcases position with ⟨lay, tree, leafIdx⟩
  fin_cases lay
  · refine ⟨layerMessagePosition index topLayer, rfl, middleLayer,
      treeIndexAt index middleLayer, ?_⟩
    simp [layerRootPosition]
  · refine ⟨layerMessagePosition index middleLayer, rfl, bottomLayer,
      treeIndexAt index bottomLayer, ?_⟩
    simp [layerRootPosition]
  · exact False.elim (hnotBottom rfl)

theorem decodeEncodingLayerRootCandidate?_some_isLayerRoot
    {parameter : PublicParameter} {input : HashInput} {candidate : Probe}
    (hdecode : decodeEncodingLayerRootCandidate? parameter input = some candidate) :
    candidate.IsLayerRoot :=
  encodingLayerRootCandidateAt_isLayerRoot
    ((decodeEncodingLayerRootCandidate?_eq_some_iff parameter input candidate).mp hdecode)

theorem encodingLayerRootCandidateAt_hasStructuralParent
    {parameter : PublicParameter} {input : HashInput} {candidate : Probe}
    (hcandidate : EncodingLayerRootCandidateAt parameter input candidate) :
    candidate.HasStructuralParent := by
  obtain ⟨position, index, _hat, _htree, _hleaf, hnotBottom, rfl⟩ := hcandidate
  rcases position with ⟨lay, tree, leafIdx⟩
  fin_cases lay
  · change ∃ parent, Position.parentOf (layerMessagePosition index topLayer) = some parent
    rw [layerMessagePosition_top]
    simp [Position.parentOf, layerHeight, middleLayer, maxLayerHeight]
  · change ∃ parent, Position.parentOf (layerMessagePosition index middleLayer) = some parent
    rw [layerMessagePosition_middle]
    simp [Position.parentOf, layerHeight, bottomLayer, maxLayerHeight, numLayers]
  · exact False.elim (hnotBottom rfl)

noncomputable def rootAwarePlannedCandidate?
    (parameter : PublicParameter) (input : HashInput)
    (state : LazyRevealProbe.State Coordinate) : Option Probe :=
  let planned := (purePlanProbingHashQuery parameter input state).candidate?
  match planned with
  | some candidate => some candidate
  | none => decodeEncodingLayerRootCandidate? parameter input

theorem rootAwarePlannedCandidate?_eq_of_plan_some
    {parameter : PublicParameter} {input : HashInput}
    {state : LazyRevealProbe.State Coordinate} {candidate : Probe}
    (hplan : (purePlanProbingHashQuery parameter input state).candidate? = some candidate) :
    rootAwarePlannedCandidate? parameter input state = some candidate := by
  simp [rootAwarePlannedCandidate?, hplan]

end SphincsSecurity.Concrete.OtsProbeSimulation
