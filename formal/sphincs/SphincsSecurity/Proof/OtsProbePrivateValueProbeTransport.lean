import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbePrivateValuePendingCleanup
import SphincsSecurity.Proof.OtsProbePrivateValueProbeRecords

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def privateResolvedSelectedCandidate (target : Position) (select : Nat → α → Option Digest) :
    Option (DeferredContext × Nat × α) → Option (HashOutput × Digest)
  | none => none
  | some (context, remaining, value) => do
      let output ← context.positionValue target
      let candidate ← select remaining value
      pure (output, candidate)

theorem privateResolutionResult_known_candidate
    (target : Position) (output : HashOutput) (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (remaining : Nat) (value : α) (select : Nat → α → Option Digest)
    (hconsistent : context.ValuesConsistent)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = some output) :
    privateResolvedSelectedCandidate target select <$> privateResolutionResult target table context remaining value =
      pure (if DeferredCompletable table context then (select remaining value).map (fun digest => (output, digest)) else none) := by
  have hknown : context.positionValue target = some output := by simp [DeferredContext.positionValue, hstate, hvalue]
  by_cases hhit : context.state.hitAt (.position target) output
  · have hdoomed : ¬DeferredCompletable table context := by
      rintro ⟨completion, hcompletion⟩
      have houtput := hcompletion.2.1 target output hvalue
      have hpending := (LazyRevealProbe.State.mem_pendingAt_iff context.state (.position target) (truncateHash output)).mp hhit
      exact hcompletion.2.2.1 _ _ hpending (by rw [houtput])
    simp [privateResolutionResult, resolveDeferredPositionValue, hstate, hvalue, hhit, hdoomed, privateResolvedSelectedCandidate]
  · have hresolve : resolveDeferredPositionValue target context = pure (some (completePrivatePosition target context output)) := by
      have hinstall : context.values.install target output = context.values := by
        unfold DeferredStructuralValues.install
        rw [← hvalue]
        exact Function.update_eq_self target context.values
      simp [resolveDeferredPositionValue, hstate, hvalue, hhit, completePrivatePosition, hinstall]
    have hsupport : some (completePrivatePosition target context output) ∈ support (resolveDeferredPositionValue target context) := by
      rw [hresolve]
      simp
    have hcomplete : DeferredCompletable table (completePrivatePosition target context output).toDeferredContext ↔
        DeferredCompletable table context := by
      constructor
      · rintro ⟨completion, hcompletion⟩
        exact ⟨completion, ((deferredCompletion_resolveDeferredPositionValue_iff target _ hconsistent hsupport completion).mp hcompletion).1⟩
      · rintro ⟨completion, hcompletion⟩
        exact ⟨completion, (deferredCompletion_resolveDeferredPositionValue_iff target _ hconsistent hsupport completion).mpr
          ⟨hcompletion, hcompletion.2.1 target output hvalue⟩⟩
    have hresolvedValue := resolveDeferredPositionValue_resolves target context (completePrivatePosition target context output) hsupport
    unfold privateResolutionResult
    rw [hresolve]
    simp only [pure_bind]
    by_cases hcompletable : DeferredCompletable table context
    · simp only [if_pos hcompletable, if_pos (hcomplete.mpr hcompletable), map_pure, privateResolvedSelectedCandidate, hresolvedValue]
      cases select remaining value <;> rfl
    · simp [hcompletable, hcomplete, privateResolvedSelectedCandidate]

theorem evalDist_privateResolvedSelectedCandidate_preloaded
    (target : Position) (output : HashOutput) (select : Nat → α → Option Digest)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (pending : Finset Digest) (bound : Nat)
    (h : PrivateTargetState target output pending context)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hsafe : computation.IsQueryBoundP (IsPrivatePositionDisclosure target) 0)
    (hcount : computation.IsQueryBoundP (IsPrivatePositionProbe target) bound) :
    evalDist (privateResolvedSelectedCandidate target select <$> runPrivateResolvedView target table context fuel computation) =
      evalDist ((fun result => result.bind (fun pair => (select pair.1 pair.2).map (fun digest => (output, digest)))) <$>
        runResolvedLiveValue table context fuel computation) := by
  unfold runPrivateResolvedView runResolvedLiveValue
  simp only [map_bind]
  apply evalDist_bind_congr
  intro result hresult
  cases result with
  | none => rfl
  | some result =>
      have hfinal := (h.history_of_mem_runResolved computation context fuel table pending bound result hsafe hcount hresult).1
      have hcore := resolvedCore_of_mem_runResolvedFromTable computation context fuel table result hconsistent hstarts hresult
      dsimp only
      rw [privateResolutionResult_known_candidate target output table result.context result.remaining result.value select hcore.2.1 hfinal.1 hfinal.2.1]
      by_cases hcomplete : DeferredCompletable table result.context <;> simp [hcomplete]

theorem evalDist_runPrivateProbeRecords_eq_none_of_initial_hit
    (target : Position) (output : HashOutput) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (hstate : context.state.values (.position target) = none) (hhidden : .position target ∉ context.state.revealed)
    (hhit : context.state.hitAt (.position target) output) :
    evalDist (runPrivateProbeRecords target computation context fuel table ordinal output) = evalDist (pure none : ProbComp (Option (ResolvedRunResult (PrivateValueCut α)))) := by
  let run := runPrivateProbeRecords target computation context fuel table ordinal output
  have honly (record) (hrecord : record ∈ support run) : record = none := by
    cases record with
    | none => rfl
    | some record =>
        have hhistory := runPrivateProbeRecords_supported_history target computation context fuel table ordinal output hstate hhidden record hrecord
        exact False.elim (hhistory.2.2 (hhistory.1 hhit))
  calc
    _ = evalDist (run >>= fun record => pure record) := by simp [run]
    _ = evalDist (run >>= fun _ => pure none) := by
      apply evalDist_bind_congr
      intro record hrecord
      rw [honly record hrecord]
    _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails run
      (by simp [run, runPrivateProbeRecords, runPrivateRecords, runResolvedFromTable]) (pure none)

end SphincsSecurity.Concrete.OtsProbeSimulation
