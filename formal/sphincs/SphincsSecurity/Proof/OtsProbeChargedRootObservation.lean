import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeChargedRootCut
import SphincsSecurity.Proof.OtsProbeNativeResolvedRootCutRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem DeferredCompletable.not_hitAt_of_positionValue
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hcomplete : DeferredCompletable table context) (target : Position) (output : HashOutput)
    (hknown : context.positionValue target = some output) : ¬context.state.hitAt (.position target) output := by
  obtain ⟨completion, hcompletion⟩ := hcomplete
  intro hhit
  have hnot := hcompletion.2.2.1 (.position target) (truncateHash output)
    (by simpa [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.mem_pendingAt_iff] using hhit)
  exact hnot (congrArg truncateHash (hcompletion.eq_positionValue target output hknown))

theorem DeferredCompletable.clearNativeRootPending
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hcomplete : DeferredCompletable table context) (target : Position) :
    DeferredCompletable table (clearNativeRootPending target context) := by
  obtain ⟨completion, hcompletion⟩ := hcomplete
  refine ⟨completion, hcompletion.1, hcompletion.2.1, ?_, hcompletion.2.2.2⟩
  intro coordinate candidate hmem
  exact hcompletion.2.2.1 coordinate candidate (Finset.mem_filter.mp hmem).1

theorem resolveDeferredPositionValue_eq_clearPending_of_known
    (target : Position) (context : DeferredContext) (output : HashOutput)
    (hconsistent : context.ValuesConsistent) (hknown : context.positionValue target = some output)
    (hmiss : ¬context.state.hitAt (.position target) output) :
    resolveDeferredPositionValue target context = pure (some ⟨clearNativeRootPending target context, output⟩) := by
  cases hstate : context.state.values (.position target) with
  | none =>
      have haux : context.values target = some output := by simpa [DeferredContext.positionValue, hstate] using hknown
      rw [resolveDeferredPositionValue_of_deferred_value target context output hstate haux, if_neg hmiss]
      rfl
  | some value =>
      have heq : value = output := by simpa [DeferredContext.positionValue, hstate] using hknown
      subst value
      have haux := hconsistent target output hstate
      have hinstall : context.values.install target output = context.values := by
        simp [DeferredStructuralValues.install, ← haux]
      rw [resolveDeferredPositionValue_of_state_value target context output hstate, if_neg hmiss, hinstall]
      rfl

noncomputable def observeChargedRootCut
    (parameter : PublicParameter) (target : Position) (event : HashOutput × Option Digest → Prop)
    (context : DeferredContext) (_fuel : Nat) (value : OuterQueryCut α × SplitHashCache) (history : Finset Digest) : ProbComp Bool :=
  pure (decide (¬∃ output, context.positionValue target = some output ∧ .position target ∉ context.state.revealed ∧
    truncateHash output ∉ history ∧ event (output, chargedNativeRootCutCandidate parameter target context value.1)))

theorem observeChargedRootCut_clearPending
    (parameter : PublicParameter) (target : Position) (event : HashOutput × Option Digest → Prop)
    (context : DeferredContext) (fuel : Nat) (value : OuterQueryCut α × SplitHashCache) (history : Finset Digest) :
    observeChargedRootCut parameter target event (clearNativeRootPending target context) fuel value history =
      observeChargedRootCut parameter target event context fuel value history := by
  simp only [observeChargedRootCut,
    chargedNativeRootCutCandidate_of_visible_state_eq parameter target (clearNativeRootPending target context) context value.1 rfl rfl]
  rfl

theorem observeChargedRootCut_of_known
    (parameter : PublicParameter) (target : Position) (event : HashOutput × Option Digest → Prop)
    (context : DeferredContext) (fuel : Nat) (value : OuterQueryCut α × SplitHashCache) (history : Finset Digest)
    (output : HashOutput) (hknown : context.positionValue target = some output) :
    observeChargedRootCut parameter target event context fuel value history =
      pure (decide (¬(.position target ∉ context.state.revealed ∧ truncateHash output ∉ history ∧
        event (output, chargedNativeRootCutCandidate parameter target context value.1)))) := by
  simp [observeChargedRootCut, hknown]

theorem privateResolutionObserve_chargedRootCut_of_known
    (parameter : PublicParameter) (target : Position) (table : OtsSecretIndex → HashOutput)
    (event : HashOutput × Option Digest → Prop) (history : Finset Digest)
    (context : DeferredContext) (fuel : Nat) (value : OuterQueryCut α × SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hcomplete : DeferredCompletable table context)
    (output : HashOutput) (hknown : context.positionValue target = some output) :
    privateResolutionObserve target table (fun final remaining value => observeChargedRootCut parameter target event final remaining value history)
      context fuel value = observeChargedRootCut parameter target event context fuel value history := by
  rw [privateResolutionObserve, resolveDeferredPositionValue_eq_clearPending_of_known target context output hconsistent hknown
    (hcomplete.not_hitAt_of_positionValue target output hknown)]
  simp only [pure_bind, if_pos (hcomplete.clearNativeRootPending target)]
  exact observeChargedRootCut_clearPending parameter target event context fuel value history

end SphincsSecurity.Concrete.OtsProbeSimulation
