import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeMaterializedRootCharge
import SphincsSecurity.Proof.OtsProbeNativeRootHistoryObserver
import SphincsSecurity.Proof.OtsProbeNativeStoredRootCutRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def ChargedNativeRootQuery (parameter : PublicParameter) (input : HashInput) (context : DeferredContext) : Prop :=
  KnownHiddenStructuralRootQuery parameter input context ∨ MaterializedHiddenEncodingRootQuery parameter input context

theorem chargedNativeRootQuery_replaceNativePosition
    (parameter : PublicParameter) (input : HashInput) (target : Position) (output : HashOutput) (context : DeferredContext) :
    ChargedNativeRootQuery parameter input (replaceNativePosition target output context) ↔ ChargedNativeRootQuery parameter input context := by
  simp only [ChargedNativeRootQuery,
    ← knownHiddenStructuralRootQuery_replaceNativePosition parameter target output context input, materializedHiddenEncodingRootQuery_replaceNativePosition]

theorem chargedNativeRootQuery_of_visible_state_eq
    (parameter : PublicParameter) (input : HashInput) (left right : DeferredContext)
    (hvalues : left.state.values = right.state.values) (hrevealed : left.state.revealed = right.state.revealed) :
    ChargedNativeRootQuery parameter input left ↔ ChargedNativeRootQuery parameter input right := by
  simp only [ChargedNativeRootQuery, KnownHiddenStructuralRootQuery, MaterializedHiddenEncodingRootQuery,
    hvalues, hrevealed, purePeekTableInput_eq_of_values_eq parameter hvalues]

def ChargedNativeRootCut (parameter : PublicParameter) (context : DeferredContext) (cut : OuterQueryCut α) : Prop :=
  ∃ input, cut.input? = some (.inl (.inr input)) ∧ ChargedNativeRootQuery parameter input context

noncomputable def chargedNativeRootCutCandidate (parameter : PublicParameter) (target : Position)
    (context : DeferredContext) (cut : OuterQueryCut α) : Option Digest :=
  if ChargedNativeRootCut parameter context cut then nativeRootCutCandidate parameter target context cut else none

theorem chargedNativeRootCutCandidate_replaceNativePosition
    (parameter : PublicParameter) (target : Position) (output : HashOutput) (context : DeferredContext) (cut : OuterQueryCut α) :
    chargedNativeRootCutCandidate parameter target (replaceNativePosition target output context) cut =
      chargedNativeRootCutCandidate parameter target context cut := by
  simp only [chargedNativeRootCutCandidate, ChargedNativeRootCut, chargedNativeRootQuery_replaceNativePosition,
    ← nativeRootCutCandidate_replaceNativePosition parameter target output context cut]

theorem nativeRootCutCandidate_of_visible_state_eq
    (parameter : PublicParameter) (target : Position) (left right : DeferredContext) (cut : OuterQueryCut α)
    (hvalues : left.state.values = right.state.values) (hrevealed : left.state.revealed = right.state.revealed) :
    nativeRootCutCandidate parameter target left cut = nativeRootCutCandidate parameter target right cut := by
  unfold nativeRootCutCandidate
  apply congrArg (fun next => cut.input?.bind next)
  funext input
  cases input with
  | inl query =>
      cases query with
      | inl n => rfl
      | inr input => simp only [nativeRootCandidate_eq_of_visible_state_eq parameter input left right hvalues hrevealed]
  | inr message => rfl

theorem chargedNativeRootCutCandidate_of_visible_state_eq
    (parameter : PublicParameter) (target : Position) (left right : DeferredContext) (cut : OuterQueryCut α)
    (hvalues : left.state.values = right.state.values) (hrevealed : left.state.revealed = right.state.revealed) :
    chargedNativeRootCutCandidate parameter target left cut = chargedNativeRootCutCandidate parameter target right cut := by
  simp only [chargedNativeRootCutCandidate, ChargedNativeRootCut,
    chargedNativeRootQuery_of_visible_state_eq parameter _ left right hvalues hrevealed,
    nativeRootCutCandidate_of_visible_state_eq parameter target left right cut hvalues hrevealed]

theorem chargedNativeRootCutCandidate_resolvePositionValue
    (parameter : PublicParameter) (target position : Position) (context : DeferredContext) (cut : OuterQueryCut α)
    (result : DeferredResolution) (hresult : some result ∈ support (resolveDeferredPositionValue position context)) :
    chargedNativeRootCutCandidate parameter target result.toDeferredContext cut = chargedNativeRootCutCandidate parameter target context cut := by
  apply chargedNativeRootCutCandidate_of_visible_state_eq parameter target result.toDeferredContext context cut
    (resolveDeferredPositionValue_preserves_state_values position context result hresult)
  rw [resolveDeferredPositionValue_state_eq_clearPending position context result hresult]
  rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
