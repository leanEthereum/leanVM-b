import SphincsSecurity.Proof.OtsProbeNativeComputedRootMaterialization

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def MaterializedHiddenEncodingRootQuery (parameter : PublicParameter) (input : HashInput) (context : DeferredContext) : Prop :=
  ∃ (candidate : Probe) (target : Position),
    EncodingLayerRootCandidateAt parameter input candidate ∧ candidate.coordinate = .position target ∧
      (context.state.values (.position target)).isSome = true ∧ .position target ∉ context.state.revealed

theorem MaterializedHiddenEncodingRootQuery.known
    {parameter : PublicParameter} {input : HashInput} {context : DeferredContext}
    (h : MaterializedHiddenEncodingRootQuery parameter input context) :
    KnownHiddenEncodingRootQuery parameter input context := by
  obtain ⟨candidate, target, hcandidate, hposition, hvalue, hhidden⟩ := h
  cases hstate : context.state.values (.position target) with
  | none => simp [hstate] at hvalue
  | some output =>
      exact ⟨candidate, target, output, hcandidate, hposition,
        by simp [DeferredContext.positionValue, hstate], hhidden⟩

theorem materializedHiddenEncodingRootQuery_iff_known
    (parameter : PublicParameter) (input : HashInput) (context : DeferredContext)
    (hmat : LayerRootsMaterialized context) :
    MaterializedHiddenEncodingRootQuery parameter input context ↔ KnownHiddenEncodingRootQuery parameter input context := by
  refine ⟨fun h => h.known, ?_⟩
  rintro ⟨candidate, target, output, hcandidate, hposition, hvalue, hhidden⟩
  obtain ⟨rootPosition, hcoordinate, hroot⟩ := encodingLayerRootCandidateAt_isLayerRoot hcandidate
  have heq : rootPosition = target := Coordinate.position.inj (hcoordinate.symm.trans hposition)
  subst rootPosition
  refine ⟨candidate, target, hcandidate, hposition, ?_, hhidden⟩
  rw [hmat.state_value_of_known target hroot output hvalue]
  rfl

theorem materializedHiddenEncodingRootQuery_replaceNativePosition
    (parameter : PublicParameter) (input : HashInput) (target : Position) (output : HashOutput) (context : DeferredContext) :
    MaterializedHiddenEncodingRootQuery parameter input (replaceNativePosition target output context) ↔
      MaterializedHiddenEncodingRootQuery parameter input context := by
  simp only [MaterializedHiddenEncodingRootQuery, ← replaceNativePosition_values_isSome target output context]
  rfl

noncomputable def materializedEncodingRootOuterCharge (parameter : PublicParameter)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (_fuel : Nat) (_cache : SplitHashCache) : ENNReal :=
  match input with
  | .inl (.inr input) => if MaterializedHiddenEncodingRootQuery parameter input context then 4 / 3 else 0
  | _ => 0

theorem materializedEncodingRootOuterCharge_le_known
    (parameter : PublicParameter) (input : (OracleWorld + SigningSpec).Domain)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    materializedEncodingRootOuterCharge parameter input context fuel cache ≤
      knownEncodingRootOuterCharge parameter input context fuel cache := by
  cases input with
  | inl query =>
      cases query with
      | inl n => rfl
      | inr input =>
          simp only [materializedEncodingRootOuterCharge, knownEncodingRootOuterCharge]
          split_ifs with hmat hknown hknown
          · rfl
          · exact False.elim (hknown hmat.known)
          · exact zero_le
          · rfl
  | inr message => rfl

theorem materializedEncodingRootOuterCharge_eq_known
    (parameter : PublicParameter) (input : (OracleWorld + SigningSpec).Domain)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (hmat : LayerRootsMaterialized context) :
    materializedEncodingRootOuterCharge parameter input context fuel cache =
      knownEncodingRootOuterCharge parameter input context fuel cache := by
  cases input with
  | inl query =>
      cases query with
      | inl n => rfl
      | inr input => simp only [materializedEncodingRootOuterCharge, knownEncodingRootOuterCharge,
          materializedHiddenEncodingRootQuery_iff_known parameter input context hmat]
  | inr message => rfl

theorem materializedEncodingRootOuterCharge_replaceNativePosition
    (parameter : PublicParameter) (input : (OracleWorld + SigningSpec).Domain)
    (target : Position) (output : HashOutput) (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    materializedEncodingRootOuterCharge parameter input (replaceNativePosition target output context) fuel cache =
      materializedEncodingRootOuterCharge parameter input context fuel cache := by
  cases input with
  | inl query =>
      cases query with
      | inl n => rfl
      | inr input => simp only [materializedEncodingRootOuterCharge, materializedHiddenEncodingRootQuery_replaceNativePosition]
  | inr message => rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
