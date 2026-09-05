import SphincsSecurity.Proof.OtsProbeNativePlannedReserveComposition

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem exists_node_of_layerRoot_mem_children
    {target parent : Position} (hroot : IsLayerRoot target) (hmem : target ∈ parent.children) :
    ∃ lay tree level nodeIdx, parent = .node lay tree level nodeIdx := by
  obtain ⟨lay, tree, rfl⟩ := hroot
  have hparent := Position.mem_children_iff.mp hmem
  simp only [layerRootPosition, Position.parentOf] at hparent
  split_ifs at hparent with hlevel
  · exact ⟨lay, tree, _, _, (Option.some.inj hparent).symm⟩

theorem firstMissingInputCoordinatePlan_eq_none_of_known
    (state : LazyRevealProbe.State Coordinate) (input : HashInput) (coordinates : List Coordinate)
    (hknown : ∀ coordinate ∈ coordinates, state.values coordinate ≠ none) (slot : Nat) :
    firstMissingInputCoordinatePlan state input slot coordinates = none := by
  induction coordinates generalizing slot with
  | nil => rfl
  | cons coordinate remaining ih =>
      cases hvalue : state.values coordinate with
      | none => exact False.elim (hknown coordinate List.mem_cons_self hvalue)
      | some value =>
          simp only [firstMissingInputCoordinatePlan, hvalue]
          exact ih (fun other hmem => hknown other (List.mem_cons_of_mem coordinate hmem)) (slot + 1)

theorem decodeProbe_eq_none_of_at_node
    (parameter : PublicParameter) (input : HashInput)
    (lay : Layer) (tree : TreeIndex) (level : Fin maxLayerHeight) (nodeIdx : LeafIndex)
    (hat : AtPosition parameter input (.node lay tree level nodeIdx)) :
    decodeProbe? parameter input = none := by
  obtain ⟨payload, hinput⟩ := hat
  rw [hinput]
  exact decodeProbe?_tweakableHashInput_of_not_chain_leaf parameter
    (Position.node lay tree level nodeIdx).domain payload
    (Position.domain_inRange (.node lay tree level nodeIdx))
    (by intro _ _ _ _ _ heq; cases heq)
    (by intro _ _ _ heq; cases heq)

theorem purePlanProbingHashQuery_candidate_none_of_known_node
    (parameter : PublicParameter) (input : HashInput) (state : LazyRevealProbe.State Coordinate)
    (lay : Layer) (tree : TreeIndex) (level : Fin maxLayerHeight) (nodeIdx : LeafIndex)
    (hat : AtPosition parameter input (.node lay tree level nodeIdx))
    (hknown : purePeekTableInput parameter state (.position (.node lay tree level nodeIdx)) ≠ none) :
    (purePlanProbingHashQuery parameter input state).candidate? = none := by
  have hdecode := (decodePosition?_eq_some_iff parameter input (.node lay tree level nodeIdx)).mpr hat
  have hprobe := decodeProbe_eq_none_of_at_node parameter input lay tree level nodeIdx hat
  have hchildren : purePeekPositionValues state (Position.node lay tree level nodeIdx).children ≠ none := by
    intro hnone
    exact hknown (by simp [purePeekTableInput, hnone])
  have hvalues : ∀ coordinate ∈ (Position.node lay tree level nodeIdx).children.map Coordinate.position,
      state.values coordinate ≠ none := by
    intro coordinate hmem hnone
    obtain ⟨position, hposition, rfl⟩ := List.mem_map.mp hmem
    exact hchildren ((purePeekPositionValues_eq_none_iff_missing state _).mpr ⟨position, hposition, hnone⟩)
  rw [purePlanProbingHashQuery, hprobe, hdecode]
  exact firstMissingInputCoordinatePlan_eq_none_of_known state input _ hvalues 0

def KnownHiddenStructuralRootQuery (parameter : PublicParameter) (input : HashInput) (context : DeferredContext) : Prop :=
  ∃ parent target, AtPosition parameter input parent ∧ IsLayerRoot target ∧ target ∈ parent.children ∧
    .position target ∉ context.state.revealed ∧ purePeekTableInput parameter context.state (.position parent) ≠ none

theorem KnownHiddenStructuralRootQuery.no_candidate
    {parameter : PublicParameter} {input : HashInput} {context : DeferredContext}
    (h : KnownHiddenStructuralRootQuery parameter input context) :
    (purePlanProbingHashQuery parameter input context.state).candidate? = none := by
  obtain ⟨parent, target, hat, hroot, hmem, _, hknown⟩ := h
  obtain ⟨lay, tree, level, nodeIdx, rfl⟩ := exists_node_of_layerRoot_mem_children hroot hmem
  exact purePlanProbingHashQuery_candidate_none_of_known_node parameter input context.state lay tree level nodeIdx hat hknown

theorem KnownHiddenStructuralRootQuery.otsHashInputCharge
    {parameter : PublicParameter} {input : HashInput} {context : DeferredContext}
    (h : KnownHiddenStructuralRootQuery parameter input context) : otsHashInputCharge parameter input = 1 := by
  obtain ⟨parent, target, hat, hroot, hmem, _, _⟩ := h
  obtain ⟨lay, tree, level, nodeIdx, rfl⟩ := exists_node_of_layerRoot_mem_children hroot hmem
  exact if_pos ⟨.node lay tree level nodeIdx, trivial, hat⟩

noncomputable def knownStructuralRootOuterCharge (parameter : PublicParameter)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (_fuel : Nat) (_cache : SplitHashCache) : ENNReal :=
  match input with
  | .inl (.inr input) => if KnownHiddenStructuralRootQuery parameter input context then 1 else 0
  | _ => 0

theorem knownStructuralRootOuterCharge_le_unused
    (parameter : PublicParameter) (input : (OracleWorld + SigningSpec).Domain)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    knownStructuralRootOuterCharge parameter input context fuel cache ≤
      nativeUnusedProbeOuterCharge parameter input context fuel cache := by
  cases input with
  | inl input =>
      cases input with
      | inl n => rfl
      | inr input =>
          simp only [knownStructuralRootOuterCharge]
          split_ifs with hknown
          · simp [nativeUnusedProbeOuterCharge, hknown.no_candidate, hknown.otsHashInputCharge]
          · exact zero_le
  | inr message => rfl

theorem knownHiddenStructuralRootQuery_replace_root_iff
    {target : Position} {before after : HashOutput} {left right : DeferredContext}
    (h : NativeRootContextRel target before after left right) (parameter : PublicParameter) (input : HashInput) :
    KnownHiddenStructuralRootQuery parameter input left ↔ KnownHiddenStructuralRootQuery parameter input right := by
  have hrevealed : left.state.revealed = right.state.revealed := by rw [h.right_eq]; rfl
  constructor
  · rintro ⟨parent, rootPosition, hat, hroot, hmem, hhidden, hknown⟩
    refine ⟨parent, rootPosition, hat, hroot, hmem, hrevealed ▸ hhidden, ?_⟩
    intro hnone
    exact hknown ((h.purePeekTableInput_none_iff parameter (.position parent)).mpr hnone)
  · rintro ⟨parent, rootPosition, hat, hroot, hmem, hhidden, hknown⟩
    refine ⟨parent, rootPosition, hat, hroot, hmem, hrevealed.symm ▸ hhidden, ?_⟩
    intro hnone
    exact hknown ((h.purePeekTableInput_none_iff parameter (.position parent)).mp hnone)

theorem chronological_liveProbe_add_knownStructural_le_liveOuterCharge
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    expectedLiveResolvedQueryCharge nativeProbeQueryCharge
        ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation).run cache) context fuel table +
      expectedLiveNativeContextCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        (knownStructuralRootOuterCharge parameter) computation context fuel table cache ≤
      expectedLiveNativeOuterCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        (otsOuterQueryCharge parameter) computation context fuel table cache := by
  apply simulateQ_expectedLiveQueryCharge_add_contextCharge_le_outer _ _ _ _ _
    computation context fuel table cache hconsistent hstarts
  intro input nextCache nextContext remaining nextTable
  exact (add_le_add le_rfl (knownStructuralRootOuterCharge_le_unused parameter input nextContext remaining nextCache)).trans
    (chronologicalAdversaryImpl_probeCharge_add_unused_le_ots parameter root ftsSecret input nextCache nextContext remaining nextTable)

end SphincsSecurity.Concrete.OtsProbeSimulation
