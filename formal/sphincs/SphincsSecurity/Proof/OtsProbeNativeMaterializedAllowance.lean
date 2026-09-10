import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeCanonicalQueryTrace
import SphincsSecurity.Proof.OtsProbeNativeCandidateComponents
import SphincsSecurity.Proof.OtsProbeNativeMissingStructuralCharge
import SphincsSecurity.Proof.OtsProbeNativeQueryTraceSelection
import SphincsSecurity.Proof.OtsProbeNativeStartCharge
import SphincsSecurity.Proof.OtsProbeRiskAccumulation

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

noncomputable def nativeMaterializedCharge
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (_fuel : Nat) (_cache : SplitHashCache) : ENNReal :=
  match input with
  | .inl (.inr input) => materializedCandidateAllowance table context
      (purePlanProbingHashQuery parameter input context.state).candidate?
  | _ => 0

theorem nativeMaterializedCharge_le_hashIndicator
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    nativeMaterializedCharge parameter table input context fuel cache ≤ if IsOuterHash input then 1 else 0 := by
  cases input with
  | inl input =>
      cases input with
      | inl n => simp [nativeMaterializedCharge, IsOuterHash]
      | inr input => exact materializedCandidateAllowance_le_one table context _
  | inr message => simp [nativeMaterializedCharge, IsOuterHash]

theorem nativeMaterializedCharge_eq_zero_of_chainsPublished
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hpublic : MaterializedChainsPublished context) : nativeMaterializedCharge parameter table input context fuel cache = 0 := by
  cases input with
  | inl input =>
      cases input with
      | inl n => rfl
      | inr input => exact materializedCandidateAllowance_plan_eq_zero_of_chainsPublished parameter input table context hpublic
  | inr message => rfl

theorem nativeMaterializedTraceCharge_le_hashLength
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput) (history : List CanonicalQuerySelection) :
    canonicalTraceCharge (nativeMaterializedCharge parameter table) history ≤ (nativeHashQueryHistory history).length := by
  induction history with
  | nil => simp [canonicalTraceCharge, nativeHashQueryHistory]
  | cons head tail ih =>
      simp only [canonicalTraceCharge, List.map_cons, List.sum_cons, CanonicalQuerySelection.charge] at ih ⊢
      have hstep := add_le_add (nativeMaterializedCharge_le_hashIndicator parameter table head.input head.context head.fuel head.cache) ih
      by_cases hhash : IsOuterHash head.input <;>
        simpa [nativeHashQueryHistory, hhash, add_comm] using hstep

theorem nativeMaterializedTraceCharge_eq_zero_of_chainsPublished
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (history : List CanonicalQuerySelection) (hpublic : ∀ selection ∈ history, MaterializedChainsPublished selection.context) :
    canonicalTraceCharge (nativeMaterializedCharge parameter table) history = 0 := by
  induction history with
  | nil => rfl
  | cons head tail ih =>
      simp only [canonicalTraceCharge, List.map_cons, List.sum_cons, CanonicalQuerySelection.charge]
      rw [nativeMaterializedCharge_eq_zero_of_chainsPublished parameter table head.input head.context head.fuel head.cache
        (hpublic head (by simp)), zero_add]
      simpa only [canonicalTraceCharge, CanonicalQuerySelection.charge] using
        ih (fun selection hselection => hpublic selection (by simp [hselection]))

theorem canonicalGuessCharge_eq_native_components_of_safe
    (targets : Finset Position) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hsafe : 0 < fuel ∧ context.state.pending.card + 1 < Fintype.card Digest)
    (hcoverage : ∀ hashInput, input = .inl (.inr hashInput) → ∀ target digest,
      (purePlanProbingHashQuery parameter hashInput context.state).candidate? = some ⟨.position target, digest⟩ → target ∈ targets) :
    canonicalGuessCharge parameter table input context fuel cache =
      nativeStartCharge parameter table input context fuel cache +
        (∑ target ∈ targets, nativeMissingStructuralCharge target parameter table input context fuel cache) +
        nativeMaterializedCharge parameter table input context fuel cache := by
  simp only [canonicalGuessCharge, if_pos hsafe]
  cases input with
  | inl input =>
      cases input with
      | inl n => simp [nativeStartCharge, nativeMissingStructuralCharge, nativeMaterializedCharge]
      | inr input => exact candidateFailureAllowance_eq_native_components targets table context _ (hcoverage input rfl)
  | inr message => simp [nativeStartCharge, nativeMissingStructuralCharge, nativeMaterializedCharge]

end SphincsSecurity.Concrete.OtsProbeSimulation
