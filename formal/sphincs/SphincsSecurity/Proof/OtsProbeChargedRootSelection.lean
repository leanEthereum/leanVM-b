import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeChargedRootCut

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem NativeRootCandidateAt.direct_or_charged_or_unknown_encoding
    {parameter : PublicParameter} {input : HashInput} {context : DeferredContext} {candidate : Probe}
    (h : NativeRootCandidateAt parameter input context candidate) (target : Position)
    (hroot : IsLayerRoot target) (hcoordinate : candidate.coordinate = .position target)
    (hhidden : .position target ∉ context.state.revealed) (hmat : LayerRootsMaterialized context) :
    (purePlanProbingHashQuery parameter input context.state).candidate? = some candidate ∨
      ChargedNativeRootQuery parameter input context ∨
      (EncodingLayerRootCandidateAt parameter input candidate ∧ context.positionValue target = none) := by
  rcases h with hnative | hencoding | ⟨hstructural, _⟩
  · exact Or.inl hnative
  · cases hknown : context.positionValue target with
    | none => exact Or.inr (Or.inr ⟨hencoding, rfl⟩)
    | some output =>
        apply Or.inr ∘ Or.inl ∘ Or.inr
        exact ⟨candidate, target, hencoding, hcoordinate,
          by rw [hmat.state_value_of_known target hroot output hknown]; rfl, hhidden⟩
  · exact Or.inr (Or.inl (Or.inl hstructural))

noncomputable def chargedNativeRootQueryCandidate (parameter : PublicParameter) (target : Position)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) : Option Digest :=
  match input with
  | .inl (.inr input) =>
      if ChargedNativeRootQuery parameter input context then do
        let candidate ← nativeRootCandidate? parameter input context
        if candidate.coordinate = .position target then some candidate.candidate else none
      else none
  | _ => none

noncomputable def chargedNativeRootSelectionCandidate (parameter : PublicParameter) (target : Position)
    (selection : Option CanonicalQuerySelection) : Option Digest :=
  selection.bind fun selection => chargedNativeRootQueryCandidate parameter target selection.input selection.context

theorem chargedNativeRootCutCandidate_eq_query
    (parameter : PublicParameter) (target : Position) (context : DeferredContext) (cut : OuterQueryCut α) :
    chargedNativeRootCutCandidate parameter target context cut =
      cut.input?.bind (fun input => chargedNativeRootQueryCandidate parameter target input context) := by
  unfold chargedNativeRootCutCandidate ChargedNativeRootCut nativeRootCutCandidate
  cases hinput : cut.input? with
  | none => simp
  | some input =>
      cases input with
      | inl query =>
          cases query with
          | inl n => simp [chargedNativeRootQueryCandidate]
          | inr input => simp [chargedNativeRootQueryCandidate]
      | inr message => simp [chargedNativeRootQueryCandidate]

theorem sum_targets_chargedRootQueryCandidate_le_charge
    (targets : Finset Position) (parameter : PublicParameter)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    (∑ target ∈ targets, if chargedNativeRootQueryCandidate parameter target input context ≠ none then (1 : ENNReal) else 0) * (4 / 3 : ENNReal) ≤
      knownStructuralRootOuterCharge parameter input context fuel cache * (4 / 3 : ENNReal) +
        materializedEncodingRootOuterCharge parameter input context fuel cache := by
  cases input with
  | inl query =>
      cases query with
      | inl n => simp [chargedNativeRootQueryCandidate, knownStructuralRootOuterCharge, materializedEncodingRootOuterCharge]
      | inr input =>
          by_cases hcharged : ChargedNativeRootQuery parameter input context
          · have hone : (∑ target ∈ targets,
                if chargedNativeRootQueryCandidate parameter target (.inl (.inr input)) context ≠ none then (1 : ENNReal) else 0) ≤ 1 := by
              cases hcandidate : nativeRootCandidate? parameter input context with
              | none => simp [chargedNativeRootQueryCandidate, hcharged, hcandidate]
              | some candidate =>
                  cases hcoordinate : candidate.coordinate with
                  | chainStart lay tree leafIdx chainIdx => simp [chargedNativeRootQueryCandidate, hcharged, hcandidate, hcoordinate]
                  | position position =>
                      by_cases hmem : position ∈ targets <;>
                        simp [chargedNativeRootQueryCandidate, hcharged, hcandidate, hcoordinate, hmem]
            apply (mul_le_mul' hone le_rfl).trans
            rcases hcharged with hstructural | hencoding
            · simp [knownStructuralRootOuterCharge, hstructural]
            · simp [materializedEncodingRootOuterCharge, hencoding]
          · simp [chargedNativeRootQueryCandidate, hcharged]
  | inr message => simp [chargedNativeRootQueryCandidate, knownStructuralRootOuterCharge, materializedEncodingRootOuterCharge]

end SphincsSecurity.Concrete.OtsProbeSimulation
