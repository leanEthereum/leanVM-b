import SphincsSecurity.Proof.OtsProbeNativeRootCandidate

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem firstMissingInputCoordinatePlan_eq_of_value_presence
    (left right : LazyRevealProbe.State Coordinate)
    (hrel : ∀ coordinate, (left.values coordinate).isSome = (right.values coordinate).isSome)
    (input : HashInput) : ∀ slot coordinates,
    firstMissingInputCoordinatePlan left input slot coordinates =
      firstMissingInputCoordinatePlan right input slot coordinates := by
  intro slot coordinates
  induction coordinates generalizing slot with
  | nil => rfl
  | cons coordinate remaining ih =>
      rw [firstMissingInputCoordinatePlan, firstMissingInputCoordinatePlan]
      have hpresent := hrel coordinate
      cases hleft : left.values coordinate with
      | none =>
          cases hright : right.values coordinate with
          | none => rfl
          | some rightValue => simp [hleft, hright] at hpresent
      | some leftValue =>
          cases hright : right.values coordinate with
          | none => simp [hleft, hright] at hpresent
          | some rightValue =>
              exact ih (slot + 1)

theorem leafInputProbePlan_eq_of_value_presence
    (left right : LazyRevealProbe.State Coordinate)
    (hrel : ∀ coordinate, (left.values coordinate).isSome = (right.values coordinate).isSome)
    (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    leafInputProbePlan left input candidate lay tree leafIdx =
      leafInputProbePlan right input candidate lay tree leafIdx := by
  unfold leafInputProbePlan
  have hpresent := hrel candidate.coordinate
  cases hleft : left.values candidate.coordinate with
  | none =>
      cases hright : right.values candidate.coordinate with
      | none => rfl
      | some rightValue => simp [hleft, hright] at hpresent
  | some leftValue =>
      cases hright : right.values candidate.coordinate with
      | none => simp [hleft, hright] at hpresent
      | some rightValue =>
          exact firstMissingInputCoordinatePlan_eq_of_value_presence left right hrel input 0
            ((Position.leaf lay tree leafIdx).children.map Coordinate.position)

theorem purePlanProbingHashQuery_eq_of_value_presence
    (left right : LazyRevealProbe.State Coordinate)
    (hrel : ∀ coordinate, (left.values coordinate).isSome = (right.values coordinate).isSome)
    (parameter : PublicParameter) (input : HashInput) :
    purePlanProbingHashQuery parameter input left =
      purePlanProbingHashQuery parameter input right := by
  unfold purePlanProbingHashQuery
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      cases hposition : decodePosition? parameter input with
      | none => rfl
      | some position =>
          cases position with
          | leaf lay tree leafIdx =>
              simp only
              rw [leafInputProbePlan_eq_of_value_presence left right hrel]
          | chain | node | ftsLeaf | ftsNode | ftsRoots => rfl
  | none =>
      cases hposition : decodePosition? parameter input with
      | none => rfl
      | some position =>
          cases position with
          | node lay tree level nodeIdx =>
              simp only
              rw [firstMissingInputCoordinatePlan_eq_of_value_presence left right hrel]
          | chain | leaf | ftsLeaf | ftsNode | ftsRoots => rfl

theorem replaceNativePosition_values_isSome
    (target : Position) (output : HashOutput) (context : DeferredContext) (coordinate : Coordinate) :
    (context.state.values coordinate).isSome = ((replaceNativePosition target output context).state.values coordinate).isSome := by
  by_cases heq : coordinate = .position target
  · subst coordinate
    simp [replaceNativePosition]
  · simp [replaceNativePosition, Function.update_of_ne heq]

theorem purePlanProbingHashQuery_replaceNativePosition
    (parameter : PublicParameter) (input : HashInput) (target : Position) (output : HashOutput) (context : DeferredContext) :
    purePlanProbingHashQuery parameter input context.state =
      purePlanProbingHashQuery parameter input (replaceNativePosition target output context).state :=
  purePlanProbingHashQuery_eq_of_value_presence _ _ (replaceNativePosition_values_isSome target output context) parameter input

theorem purePeekPositionValues_none_replaceNativePosition
    (target : Position) (output : HashOutput) (context : DeferredContext) (positions : List Position) :
    purePeekPositionValues context.state positions = none ↔
      purePeekPositionValues (replaceNativePosition target output context).state positions = none := by
  have hnone (coordinate) : context.state.values coordinate = none ↔
      (replaceNativePosition target output context).state.values coordinate = none := by
    have h := replaceNativePosition_values_isSome target output context coordinate
    cases hleft : context.state.values coordinate <;>
      cases hright : (replaceNativePosition target output context).state.values coordinate <;> simp_all
  simp only [purePeekPositionValues_eq_none_iff_missing, hnone]

theorem purePeekTableInput_none_replaceNativePosition
    (parameter : PublicParameter) (target : Position) (output : HashOutput) (context : DeferredContext) (coordinate : Coordinate) :
    purePeekTableInput parameter context.state coordinate = none ↔
      purePeekTableInput parameter (replaceNativePosition target output context).state coordinate = none := by
  cases coordinate with
  | chainStart => rfl
  | position position =>
      have hchildren := purePeekPositionValues_none_replaceNativePosition target output context position.children
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          by_cases hzero : step.val = 0
          · have hstart : (replaceNativePosition target output context).state.values (.chainStart lay tree leafIdx chainIdx) =
                context.state.values (.chainStart lay tree leafIdx chainIdx) := by simp [replaceNativePosition]
            simp only [purePeekTableInput, if_pos hzero, hstart]
          · simp only [purePeekTableInput, if_neg hzero]
            cases hleft : purePeekPositionValues context.state _ <;>
              cases hright : purePeekPositionValues (replaceNativePosition target output context).state _ <;> simp_all
      | leaf | node | ftsLeaf | ftsNode | ftsRoots =>
          simp only [purePeekTableInput]
          cases hleft : purePeekPositionValues context.state _ <;>
            cases hright : purePeekPositionValues (replaceNativePosition target output context).state _ <;> simp_all

theorem knownHiddenStructuralRootQuery_replaceNativePosition
    (parameter : PublicParameter) (target : Position) (output : HashOutput) (context : DeferredContext) (input : HashInput) :
    KnownHiddenStructuralRootQuery parameter input context ↔
      KnownHiddenStructuralRootQuery parameter input (replaceNativePosition target output context) := by
  constructor
  · rintro ⟨parent, rootPosition, hat, hroot, hmem, hhidden, hknown⟩
    refine ⟨parent, rootPosition, hat, hroot, hmem, hhidden, ?_⟩
    intro hnone
    exact hknown ((purePeekTableInput_none_replaceNativePosition parameter target output context (.position parent)).mpr hnone)
  · rintro ⟨parent, rootPosition, hat, hroot, hmem, hhidden, hknown⟩
    refine ⟨parent, rootPosition, hat, hroot, hmem, hhidden, ?_⟩
    intro hnone
    exact hknown ((purePeekTableInput_none_replaceNativePosition parameter target output context (.position parent)).mp hnone)

theorem nativeRootCandidateAt_replaceNativePosition
    (parameter : PublicParameter) (target : Position) (output : HashOutput) (context : DeferredContext) (input : HashInput) (candidate : Probe) :
    NativeRootCandidateAt parameter input context candidate ↔
      NativeRootCandidateAt parameter input (replaceNativePosition target output context) candidate := by
  unfold NativeRootCandidateAt
  rw [purePlanProbingHashQuery_replaceNativePosition parameter input target output context,
    knownHiddenStructuralRootQuery_replaceNativePosition parameter target output context input]

theorem nativeRootCandidate_replaceNativePosition
    (parameter : PublicParameter) (target : Position) (output : HashOutput) (context : DeferredContext) (input : HashInput) :
    nativeRootCandidate? parameter input context = nativeRootCandidate? parameter input (replaceNativePosition target output context) := by
  cases hleft : nativeRootCandidate? parameter input context with
  | none =>
      cases hright : nativeRootCandidate? parameter input (replaceNativePosition target output context) with
      | none => rfl
      | some candidate =>
          have hcandidate := (nativeRootCandidateAt_replaceNativePosition parameter target output context input candidate).mpr
            ((nativeRootCandidate?_eq_some_iff parameter input _ candidate).mp hright)
          have heq := (nativeRootCandidate?_eq_some_iff parameter input context candidate).mpr hcandidate
          rw [hleft] at heq
          contradiction
  | some candidate =>
      have hcandidate := (nativeRootCandidateAt_replaceNativePosition parameter target output context input candidate).mp
        ((nativeRootCandidate?_eq_some_iff parameter input context candidate).mp hleft)
      exact ((nativeRootCandidate?_eq_some_iff parameter input _ candidate).mpr hcandidate).symm

end SphincsSecurity.Concrete.OtsProbeSimulation
