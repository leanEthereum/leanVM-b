import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeRootState
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivatePlanExecution
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelectionMaterialized

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

theorem NativeRootContextRel.other_values
    {target : Position} {before after : HashOutput} {left right : DeferredContext}
    (h : NativeRootContextRel target before after left right)
    (coordinate : Coordinate) (hne : coordinate ≠ .position target) :
    left.state.values coordinate = right.state.values coordinate := by
  rw [h.right_eq]
  simp [replaceNativePosition, Function.update_of_ne hne]

theorem NativeRootContextRel.values_isSome_eq
    {target : Position} {before after : HashOutput} {left right : DeferredContext}
    (h : NativeRootContextRel target before after left right) (coordinate : Coordinate) :
    (left.state.values coordinate).isSome = (right.state.values coordinate).isSome := by
  by_cases heq : coordinate = .position target
  · subst coordinate
    rw [h.right_eq]
    simp [replaceNativePosition]
  · rw [h.other_values coordinate heq]

theorem firstMissingInputCoordinatePlan_eq_of_nativeRootContextRel
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : DeferredContext}
    (hrel : NativeRootContextRel target leftOutput rightOutput left right)
    (input : HashInput) : ∀ slot coordinates,
    firstMissingInputCoordinatePlan left.state input slot coordinates =
      firstMissingInputCoordinatePlan right.state input slot coordinates := by
  intro slot coordinates
  induction coordinates generalizing slot with
  | nil => rfl
  | cons coordinate remaining ih =>
      rw [firstMissingInputCoordinatePlan, firstMissingInputCoordinatePlan]
      have hpresent := hrel.values_isSome_eq coordinate
      cases hleft : left.state.values coordinate with
      | none =>
          cases hright : right.state.values coordinate with
          | none => rfl
          | some rightValue => simp [hleft, hright] at hpresent
      | some leftValue =>
          cases hright : right.state.values coordinate with
          | none => simp [hleft, hright] at hpresent
          | some rightValue =>
              exact ih (slot + 1)

theorem leafInputProbePlan_eq_of_nativeRootContextRel
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : DeferredContext}
    (hrel : NativeRootContextRel target leftOutput rightOutput left right)
    (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    leafInputProbePlan left.state input candidate lay tree leafIdx =
      leafInputProbePlan right.state input candidate lay tree leafIdx := by
  unfold leafInputProbePlan
  have hpresent := hrel.values_isSome_eq candidate.coordinate
  cases hleft : left.state.values candidate.coordinate with
  | none =>
      cases hright : right.state.values candidate.coordinate with
      | none => rfl
      | some rightValue => simp [hleft, hright] at hpresent
  | some leftValue =>
      cases hright : right.state.values candidate.coordinate with
      | none => simp [hleft, hright] at hpresent
      | some rightValue =>
          exact firstMissingInputCoordinatePlan_eq_of_nativeRootContextRel hrel input 0
            ((Position.leaf lay tree leafIdx).children.map Coordinate.position)

theorem purePlanProbingHashQuery_eq_of_nativeRootContextRel
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : DeferredContext}
    (hrel : NativeRootContextRel target leftOutput rightOutput left right)
    (parameter : PublicParameter) (input : HashInput) :
    purePlanProbingHashQuery parameter input left.state =
      purePlanProbingHashQuery parameter input right.state := by
  unfold purePlanProbingHashQuery
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      cases hposition : decodePosition? parameter input with
      | none => rfl
      | some position =>
          cases position with
          | leaf lay tree leafIdx =>
              simp only
              rw [leafInputProbePlan_eq_of_nativeRootContextRel hrel]
          | chain | node | ftsLeaf | ftsNode | ftsRoots => rfl
  | none =>
      cases hposition : decodePosition? parameter input with
      | none => rfl
      | some position =>
          cases position with
          | node lay tree level nodeIdx =>
              simp only
              rw [firstMissingInputCoordinatePlan_eq_of_nativeRootContextRel hrel]
          | chain | leaf | ftsLeaf | ftsNode | ftsRoots => rfl

theorem purePeekPositionValues_eq_none_iff_missing
    (state : LazyRevealProbe.State Coordinate) (positions : List Position) :
    purePeekPositionValues state positions = none ↔
      ∃ position ∈ positions, state.values (.position position) = none := by
  induction positions with
  | nil => simp [purePeekPositionValues]
  | cons position remaining ih =>
      cases hhead : state.values (.position position) with
      | none => simp [purePeekPositionValues, hhead]
      | some output =>
          cases htail : purePeekPositionValues state remaining <;>
            simpa [purePeekPositionValues, hhead, htail] using ih

theorem purePeekPositionValues_eq_of_values_eq_on
    (left right : LazyRevealProbe.State Coordinate) (positions : List Position)
    (h : ∀ position ∈ positions, left.values (.position position) = right.values (.position position)) :
    purePeekPositionValues left positions = purePeekPositionValues right positions := by
  induction positions with
  | nil => rfl
  | cons position remaining ih =>
      have hhead := h position (List.mem_cons_self)
      have htail := ih (fun other hmem => h other (List.mem_cons_of_mem position hmem))
      simp only [purePeekPositionValues, hhead, htail]

theorem NativeRootContextRel.values_none_iff
    {target : Position} {before after : HashOutput} {left right : DeferredContext}
    (h : NativeRootContextRel target before after left right) (coordinate : Coordinate) :
    left.state.values coordinate = none ↔ right.state.values coordinate = none := by
  have hpresent := h.values_isSome_eq coordinate
  cases hleft : left.state.values coordinate <;> cases hright : right.state.values coordinate <;>
    simp_all

theorem NativeRootContextRel.purePeekPositionValues_none_iff
    {target : Position} {before after : HashOutput} {left right : DeferredContext}
    (h : NativeRootContextRel target before after left right) (positions : List Position) :
    purePeekPositionValues left.state positions = none ↔ purePeekPositionValues right.state positions = none := by
  simp only [purePeekPositionValues_eq_none_iff_missing, h.values_none_iff]

theorem NativeRootContextRel.purePeekPositionValues_eq_of_not_mem
    {target : Position} {before after : HashOutput} {left right : DeferredContext}
    (h : NativeRootContextRel target before after left right) (positions : List Position) (hnot : target ∉ positions) :
    purePeekPositionValues left.state positions = purePeekPositionValues right.state positions := by
  apply purePeekPositionValues_eq_of_values_eq_on
  intro position hmem
  apply h.other_values
  intro heq
  have hposition : position = target := Coordinate.position.inj heq
  exact hnot (hposition ▸ hmem)

theorem NativeRootContextRel.purePeekTableInput_eq_of_not_mem_children
    {target : Position} {before after : HashOutput} {left right : DeferredContext}
    (h : NativeRootContextRel target before after left right) (parameter : PublicParameter)
    (position : Position) (hnot : target ∉ position.children) :
    purePeekTableInput parameter left.state (.position position) =
      purePeekTableInput parameter right.state (.position position) := by
  have hchildren := h.purePeekPositionValues_eq_of_not_mem position.children hnot
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      have hstart := h.other_values (.chainStart lay tree leafIdx chainIdx) (by simp)
      simp only [purePeekTableInput, hstart, hchildren]
  | leaf | node | ftsLeaf | ftsNode | ftsRoots => simp only [purePeekTableInput, hchildren]

theorem NativeRootContextRel.purePeekTableInput_none_iff
    {target : Position} {before after : HashOutput} {left right : DeferredContext}
    (h : NativeRootContextRel target before after left right) (parameter : PublicParameter)
    (coordinate : Coordinate) :
    purePeekTableInput parameter left.state coordinate = none ↔
      purePeekTableInput parameter right.state coordinate = none := by
  cases coordinate with
  | chainStart => rfl
  | position position =>
      have hchildren := h.purePeekPositionValues_none_iff position.children
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          by_cases hzero : step.val = 0
          · have hstart := h.other_values (.chainStart lay tree leafIdx chainIdx) (by simp)
            simp only [purePeekTableInput, if_pos hzero, hstart]
          · simp only [purePeekTableInput, if_neg hzero]
            cases hleft : purePeekPositionValues left.state _ <;>
              cases hright : purePeekPositionValues right.state _ <;> simp_all
      | leaf | node | ftsLeaf | ftsNode | ftsRoots =>
          simp only [purePeekTableInput]
          cases hleft : purePeekPositionValues left.state _ <;>
            cases hright : purePeekPositionValues right.state _ <;> simp_all

theorem NativeRootContextRel.purePeekTableInput_ne_imp_known_child
    {target : Position} {before after : HashOutput} {left right : DeferredContext}
    (h : NativeRootContextRel target before after left right) (parameter : PublicParameter)
    (coordinate : Coordinate)
    (hne : purePeekTableInput parameter left.state coordinate ≠ purePeekTableInput parameter right.state coordinate) :
    ∃ position leftInput rightInput, coordinate = .position position ∧ target ∈ position.children ∧
      purePeekTableInput parameter left.state coordinate = some leftInput ∧
      purePeekTableInput parameter right.state coordinate = some rightInput := by
  cases coordinate with
  | chainStart => exact False.elim (hne rfl)
  | position position =>
      have hmem : target ∈ position.children := by
        by_contra hnot
        exact hne (h.purePeekTableInput_eq_of_not_mem_children parameter position hnot)
      have hnone := h.purePeekTableInput_none_iff parameter (.position position)
      cases hleft : purePeekTableInput parameter left.state (.position position) with
      | none =>
          have hright := hnone.mp hleft
          exact False.elim (hne (hleft.trans hright.symm))
      | some leftInput =>
          cases hright : purePeekTableInput parameter right.state (.position position) with
          | none =>
              have hleftNone := hnone.mpr hright
              rw [hleft] at hleftNone
              contradiction
          | some rightInput => exact ⟨position, leftInput, rightInput, rfl, hmem, rfl, rfl⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
