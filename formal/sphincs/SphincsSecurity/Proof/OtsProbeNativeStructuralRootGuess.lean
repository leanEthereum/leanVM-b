import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeRootExposure
import SphincsSecurity.Proof.OtsProbeNativeRootOuterCutStop

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem purePeekPositionValues_some_eq_map
    (state : LazyRevealProbe.State Coordinate) (positions : List Position) (values : List Digest)
    (hvalues : purePeekPositionValues state positions = some values) :
    values = positions.map (fun position => truncateHash ((state.values (.position position)).getD 0)) := by
  induction positions generalizing values with
  | nil => simpa [purePeekPositionValues] using hvalues.symm
  | cons position remaining ih =>
      cases hhead : state.values (.position position) with
      | none => simp [purePeekPositionValues, hhead] at hvalues
      | some output =>
          cases htail : purePeekPositionValues state remaining with
          | none => simp [purePeekPositionValues, hhead, htail] at hvalues
          | some tail =>
              simp [purePeekPositionValues, hhead, htail] at hvalues
              rw [← hvalues, ih tail htail]
              simp [hhead]

theorem slotDigest_purePeek_node_child
    (parameter : PublicParameter) (context : DeferredContext)
    (lay : Layer) (tree : TreeIndex) (level : Fin maxLayerHeight) (nodeIdx : LeafIndex)
    (target : Position) (output : HashOutput) (input : HashInput)
    (hmem : target ∈ (Position.node lay tree level nodeIdx).children)
    (hknown : context.positionValue target = some output)
    (hinput : purePeekTableInput parameter context.state (.position (.node lay tree level nodeIdx)) = some input) :
    slotDigest ((Position.node lay tree level nodeIdx).children.idxOf target) input = truncateHash output := by
  simp only [purePeekTableInput] at hinput
  cases hvalues : purePeekPositionValues context.state (Position.node lay tree level nodeIdx).children with
  | none => simp [hvalues] at hinput
  | some values =>
      simp only [hvalues, Option.some.injEq] at hinput
      have hmap := purePeekPositionValues_some_eq_map context.state _ values hvalues
      have hidx := List.idxOf_lt_length_iff.mpr hmem
      have hvalue : context.state.values (.position target) = some output := by
        cases hstate : context.state.values (.position target) with
        | none =>
            have hmissing := (purePeekPositionValues_eq_none_iff_missing context.state _).mpr ⟨target, hmem, hstate⟩
            rw [hvalues] at hmissing
            contradiction
        | some actual =>
            have heq : actual = output := by simpa [DeferredContext.positionValue, hstate] using hknown
            exact congrArg some heq
      rw [← hinput, slotDigest_flatMap parameter _ values _ (by simpa [hmap] using hidx)]
      simp [hmap, List.getElem_idxOf hidx, hvalue]

theorem nativeRootActionSafe_failure_structural_guess
    (parameter : PublicParameter) (target : Position) (hroot : IsLayerRoot target) (before after : HashOutput)
    (input : HashInput) (coordinate : Coordinate) (left right : DeferredContext)
    (hcontext : NativeRootContextRel target before after left right)
    (hneTarget : coordinate ≠ .position target)
    (hunsafe : ¬NativeRootActionSafe parameter target input left right (.resolve coordinate)) :
    ∃ lay tree level nodeIdx,
      coordinate = .position (.node lay tree level nodeIdx) ∧
      target ∈ (Position.node lay tree level nodeIdx).children ∧
      AtPosition parameter input (.node lay tree level nodeIdx) ∧
      (slotDigest ((Position.node lay tree level nodeIdx).children.idxOf target) input = truncateHash before ∨
        slotDigest ((Position.node lay tree level nodeIdx).children.idxOf target) input = truncateHash after) := by
  have hne : purePeekTableInput parameter left.state coordinate ≠ purePeekTableInput parameter right.state coordinate :=
    fun heq => hunsafe (Or.inl ⟨hneTarget, heq⟩)
  obtain ⟨parent, leftInput, rightInput, hcoordinate, hmem, hleft, hright⟩ :=
    hcontext.purePeekTableInput_ne_imp_known_child parameter coordinate hne
  subst coordinate
  obtain ⟨lay, tree, level, nodeIdx, rfl⟩ := exists_node_of_layerRoot_mem_children hroot hmem
  refine ⟨lay, tree, level, nodeIdx, rfl, hmem, ?_⟩
  by_cases hmatch : purePeekTableInput parameter left.state (.position (.node lay tree level nodeIdx)) = some input
  · exact ⟨purePeekTableInput_node_some_atPosition parameter left.state lay tree level nodeIdx input hmatch,
      Or.inl (slotDigest_purePeek_node_child parameter left lay tree level nodeIdx target before input hmem
        hcontext.replaceable.known hmatch)⟩
  · have hmatchRight : purePeekTableInput parameter right.state (.position (.node lay tree level nodeIdx)) = some input := by
      by_contra hmiss
      exact hunsafe (Or.inr ⟨hmatch, hmiss⟩)
    refine ⟨purePeekTableInput_node_some_atPosition parameter right.state lay tree level nodeIdx input hmatchRight, Or.inr ?_⟩
    apply slotDigest_purePeek_node_child parameter right lay tree level nodeIdx target after input hmem _ hmatchRight
    rw [hcontext.right_eq]
    exact replaceNativePosition_positionValue target after left

theorem layerRoot_unique_of_mem_children
    {left right parent : Position} (hleft : IsLayerRoot left) (hright : IsLayerRoot right)
    (hleftMem : left ∈ parent.children) (hrightMem : right ∈ parent.children) : left = right := by
  obtain ⟨leftLay, leftTree, rfl⟩ := hleft
  obtain ⟨rightLay, rightTree, rfl⟩ := hright
  have hleftParent := Position.mem_children_iff.mp hleftMem
  have hrightParent := Position.mem_children_iff.mp hrightMem
  simp only [layerRootPosition, Position.parentOf] at hleftParent hrightParent
  split_ifs at hleftParent with hleftLevel
  split_ifs at hrightParent with hrightLevel
  have heq := (Option.some.inj hleftParent).trans (Option.some.inj hrightParent).symm
  obtain ⟨rfl, rfl, _, _⟩ := Position.node.inj heq
  rfl

def StructuralLayerRootCandidateAt (parameter : PublicParameter) (input : HashInput) (candidate : Probe) : Prop :=
  ∃ parent target, AtPosition parameter input parent ∧ IsLayerRoot target ∧ target ∈ parent.children ∧
    candidate = ⟨.position target, slotDigest (parent.children.idxOf target) input⟩

theorem structuralLayerRootCandidateAt_unique
    {parameter : PublicParameter} {input : HashInput} {left right : Probe}
    (hleft : StructuralLayerRootCandidateAt parameter input left)
    (hright : StructuralLayerRootCandidateAt parameter input right) : left = right := by
  obtain ⟨leftParent, leftTarget, hleftAt, hleftRoot, hleftMem, rfl⟩ := hleft
  obtain ⟨rightParent, rightTarget, hrightAt, hrightRoot, hrightMem, rfl⟩ := hright
  have hparent := atPosition_unique parameter hleftAt hrightAt
  subst rightParent
  have htarget := layerRoot_unique_of_mem_children hleftRoot hrightRoot hleftMem hrightMem
  subst rightTarget
  rfl

theorem nativeRootActionSafe_failure_structural_candidate
    (parameter : PublicParameter) (target : Position) (hroot : IsLayerRoot target) (before after : HashOutput)
    (input : HashInput) (coordinate : Coordinate) (left right : DeferredContext)
    (hcontext : NativeRootContextRel target before after left right)
    (hneTarget : coordinate ≠ .position target)
    (hunsafe : ¬NativeRootActionSafe parameter target input left right (.resolve coordinate)) :
    ∃ candidate, StructuralLayerRootCandidateAt parameter input candidate ∧
      candidate.coordinate = .position target ∧
      (candidate.candidate = truncateHash before ∨ candidate.candidate = truncateHash after) := by
  obtain ⟨lay, tree, level, nodeIdx, _, hmem, hat, hguess⟩ :=
    nativeRootActionSafe_failure_structural_guess parameter target hroot before after input coordinate left right hcontext hneTarget hunsafe
  let parent := Position.node lay tree level nodeIdx
  let candidate : Probe := ⟨.position target, slotDigest (parent.children.idxOf target) input⟩
  refine ⟨candidate, ?_, ?_, ?_⟩
  · exact ⟨parent, target, hat, hroot, hmem, rfl⟩
  · rfl
  · simpa only [candidate, parent] using hguess

theorem nativeRootHashSafe_failure_of_hidden_result_guesses
    (parameter : PublicParameter) (target : Position) (hroot : IsLayerRoot target) (before after : HashOutput)
    (input : HashInput) (context : DeferredContext) (h : NativePositionReplaceable target before after context)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hunsafe : ¬NativeRootHashSafe parameter target before after input context)
    (result : ResolvedRunResult (HashOutput × SplitHashCache))
    (hresult : some result ∈ support (runResolvedFromTable context fuel table ((probingHashQuery parameter input).run cache)))
    (hhidden : .position target ∉ result.context.state.revealed) :
    (EncodingInputGuessesRoot parameter target (truncateHash before) input ∨
      EncodingInputGuessesRoot parameter target (truncateHash after) input) ∨
    (∃ candidate, (purePlanProbingHashQuery parameter input context.state).candidate? = some candidate ∧
      IsPrivateValueExposure target before after (.probe candidate.coordinate candidate.candidate)) ∨
    (KnownHiddenStructuralRootQuery parameter input context ∧
      ∃ candidate, StructuralLayerRootCandidateAt parameter input candidate ∧
        candidate.coordinate = .position target ∧
        (candidate.candidate = truncateHash before ∨ candidate.candidate = truncateHash after)) := by
  have hinitial : .position target ∉ context.state.revealed := fun hmem =>
    hhidden (revealed_subset_of_mem_runResolvedFromTable _ context fuel table result hresult hmem)
  have hfailure := nativeRootHashSafe_failure_classify parameter target before after input context hunsafe
  rw [h.replace_self] at hfailure
  rcases hfailure with hencoding | hprobe | haction
  · apply Or.inl
    by_cases hleft : EncodingInputGuessesRoot parameter target (truncateHash before) input
    · exact Or.inl hleft
    · apply Or.inr
      by_contra hright
      exact hencoding ⟨hleft, hright⟩
  · exact Or.inr (Or.inl hprobe)
  · have hrel : NativeRootContextRel target before after context (replaceNativePosition target after context) := ⟨h, rfl⟩
    cases hplan : (purePlanProbingHashQuery parameter input context.state).action with
    | ordinary => rw [hplan] at haction; exact False.elim (haction trivial)
    | resolve coordinate =>
        rw [hplan] at haction
        by_cases htarget : coordinate = .position target
        · subst coordinate
          exact False.elim (hhidden (nativeRootHash_target_action_failure_publishes parameter target hroot before after input
            context _ hrel fuel table cache hplan haction result hresult))
        · have hstructural := nativeRootActionSafe_failure_exposure_or_structuralCharge parameter target hroot before after input
            (.resolve coordinate) context _ hrel hinitial haction
          have hcharge : KnownHiddenStructuralRootQuery parameter input context := hstructural.resolve_left
            (fun heq => htarget (PlannedHashAction.resolve.inj heq))
          exact Or.inr (Or.inr ⟨hcharge, nativeRootActionSafe_failure_structural_candidate parameter target hroot before after
            input coordinate context _ hrel htarget haction⟩)

end SphincsSecurity.Concrete.OtsProbeSimulation
