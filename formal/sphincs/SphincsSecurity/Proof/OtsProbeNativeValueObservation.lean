import SphincsSecurity.Proof.OtsProbeNativeValueMaterialization

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem replaceNativePosition_positionValue_of_ne
    (target position : Position) (output : HashOutput) (context : DeferredContext)
    (hne : position ≠ target) :
    (replaceNativePosition target output context).positionValue position = context.positionValue position := by
  have hcoordinate : Coordinate.position position ≠ .position target := by simpa using hne
  simp [replaceNativePosition, DeferredContext.positionValue, DeferredStructuralValues.install,
    hne, hcoordinate]

theorem replaceNativePosition_known_iff
    (target position : Position) (before after : HashOutput) (context : DeferredContext)
    (hknown : context.positionValue target = some before) :
    (∃ output, (replaceNativePosition target after context).positionValue position = some output) ↔
      ∃ output, context.positionValue position = some output := by
  by_cases heq : position = target
  · subst position
    exact ⟨fun _ => ⟨before, hknown⟩,
      fun _ => ⟨after, replaceNativePosition_positionValue target after context⟩⟩
  · rw [replaceNativePosition_positionValue_of_ne target position after context heq]

theorem knownHiddenEncodingRootQuery_replaceNativePosition_iff
    (parameter : PublicParameter) (input : HashInput) (target : Position)
    (before after : HashOutput) (context : DeferredContext)
    (hknown : context.positionValue target = some before) :
    KnownHiddenEncodingRootQuery parameter input (replaceNativePosition target after context) ↔
      KnownHiddenEncodingRootQuery parameter input context := by
  constructor
  · rintro ⟨candidate, position, output, hcandidate, hcoordinate, hvalue, hhidden⟩
    obtain ⟨original, horiginal⟩ :=
      (replaceNativePosition_known_iff target position before after context hknown).1 ⟨output, hvalue⟩
    exact ⟨candidate, position, original, hcandidate, hcoordinate, horiginal, hhidden⟩
  · rintro ⟨candidate, position, output, hcandidate, hcoordinate, hvalue, hhidden⟩
    obtain ⟨replaced, hreplaced⟩ :=
      (replaceNativePosition_known_iff target position before after context hknown).2 ⟨output, hvalue⟩
    exact ⟨candidate, position, replaced, hcandidate, hcoordinate, hreplaced, hhidden⟩

theorem knownEncodingRootOuterCharge_replaceNativePosition
    (parameter : PublicParameter) (input : (OracleWorld + SigningSpec).Domain)
    (target : Position) (before after : HashOutput) (context : DeferredContext)
    (fuel : Nat) (leftCache rightCache : SplitHashCache)
    (hknown : context.positionValue target = some before) :
    knownEncodingRootOuterCharge parameter input (replaceNativePosition target after context) fuel rightCache =
      knownEncodingRootOuterCharge parameter input context fuel leftCache := by
  cases input with
  | inl query =>
      cases query with
      | inl n => rfl
      | inr input =>
          simp only [knownEncodingRootOuterCharge,
            knownHiddenEncodingRootQuery_replaceNativePosition_iff parameter input target before after context hknown]
  | inr message => rfl

theorem replaceNativePosition_idem
    (target : Position) (first second : HashOutput) (context : DeferredContext) :
    replaceNativePosition target second (replaceNativePosition target first context) =
      replaceNativePosition target second context := by
  simp [replaceNativePosition, Function.comp_def, DeferredStructuralValues.install]

end SphincsSecurity.Concrete.OtsProbeSimulation
