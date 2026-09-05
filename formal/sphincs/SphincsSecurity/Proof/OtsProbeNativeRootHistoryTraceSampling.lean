import SphincsSecurity.Proof.OtsProbeNativeRootHistoryObserver

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def finishNativeRootHistoryTrace
    (parameter : PublicParameter) (target : Position) (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → Finset Digest → ProbComp Bool)
    (history : Finset Digest) :
    Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection → ProbComp Bool
  | (none, _) => pure true
  | (some result, trace) => privateResolutionObserve target table
      (fun final remaining value => observe final remaining value (history ∪ nativeRootCandidateHistory parameter target trace))
      result.context result.remaining result.value

theorem finishNativeRootHistoryTrace_cons
    (parameter : PublicParameter) (target : Position) (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → Finset Digest → ProbComp Bool)
    (history : Finset Digest) (selection : CanonicalQuerySelection)
    (trace : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection) :
    finishNativeRootHistoryTrace parameter target table observe history (trace.1, selection :: trace.2) =
      finishNativeRootHistoryTrace parameter target table observe
        (insertNativeRootGuess (nativeRootSelectionGuess? parameter target selection) history) trace := by
  rcases trace with ⟨option, trace⟩
  cases option with
  | none => rfl
  | some result =>
      simp only [finishNativeRootHistoryTrace, nativeRootCandidateHistory_cons]
      have hhistory : history ∪ insertNativeRootGuess (nativeRootSelectionGuess? parameter target selection)
          (nativeRootCandidateHistory parameter target trace) =
          insertNativeRootGuess (nativeRootSelectionGuess? parameter target selection) history ∪
            nativeRootCandidateHistory parameter target trace := by
        cases nativeRootSelectionGuess? parameter target selection <;> simp [insertNativeRootGuess]
      rw [hhistory]

theorem evalDist_runNativeRootHistoryObserve_eq_trace
    (parameter : PublicParameter) (root : Digest) (target : Position)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → Finset Digest → ProbComp Bool)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (history : Finset Digest)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    evalDist (runNativeRootHistoryObserve parameter root target ftsSecret table observe computation context fuel cache history) =
      evalDist (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache >>=
        finishNativeRootHistoryTrace parameter target table observe history) := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache history with
  | pure value =>
      simp only [runNativeRootHistoryObserve, runNativeQueryTrace, OracleComp.construct_pure]
      split_ifs <;> simp [finishNativeRootHistoryTrace, nativeRootCandidateHistory, nativeHashQueryHistory, privateResolutionObserve]
  | query_bind input next ih =>
      rw [runNativeQueryTrace_query_bind]
      simp only [runNativeRootHistoryObserve, OracleComp.construct_query_bind]
      by_cases hcomplete : DeferredCompletable table context
      · simp only [if_pos hcomplete, runResolvedObserve, bind_assoc]
        apply evalDist_bind_congr
        intro middle hmiddle
        cases middle with
        | none => simp [finishObserve, finishNativeRootHistoryTrace]
        | some middle =>
            simp only [finishObserve, bind_assoc, pure_bind]
            have hcore := resolvedCore_of_mem_runResolvedFromTable _ context fuel table middle hconsistent hstarts hmiddle
            rw [hcore.1]
            have htail := ih middle.value.1 middle.context middle.remaining middle.value.2
              (insertNativeRootGuess (nativeRootSelectionGuess? parameter target ⟨input, context, fuel, table, cache⟩) history)
              hcore.2.1 hcore.2.2
            simpa only [runNativeRootHistoryObserve, runResolvedObserve, finishNativeRootHistoryTrace_cons] using htail
      · simp [if_neg hcomplete, finishNativeRootHistoryTrace]

theorem evalDist_resolveRoot_then_nativeHistoryTrace
    (parameter : PublicParameter) (root : Digest) (target : Position)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → Finset Digest → ProbComp Bool)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (history : Finset Digest)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : .position target ∈ context.state.ensured) :
    evalDist (do
      let resolved ← resolveDeferredPositionValue target context
      match resolved with
      | none => pure true
      | some resolved => runNativeQueryTrace parameter root ftsSecret computation resolved.toDeferredContext fuel table cache >>=
          finishNativeRootHistoryTrace parameter target table observe history) =
      evalDist (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache >>=
        finishNativeRootHistoryTrace parameter target table observe history) := by
  have hstarts := startTableAgrees_of_deferredCompletable hcomplete
  calc
    _ = evalDist (resolveDeferredPositionValue target context >>= fun resolved =>
        match resolved with
        | none => pure true
        | some resolved => runNativeRootHistoryObserve parameter root target ftsSecret table observe computation resolved.toDeferredContext fuel cache history) := by
      apply evalDist_bind_congr
      intro resolved hresolved
      cases resolved with
      | none => rfl
      | some resolved =>
          exact (evalDist_runNativeRootHistoryObserve_eq_trace parameter root target ftsSecret table observe computation
            resolved.toDeferredContext fuel cache history (hvalid.of_resolveDeferredPositionValue target resolved hresolved).valuesConsistent
            (hstarts.of_state_values_eq (resolveDeferredPositionValue_preserves_state_values target context resolved hresolved))).symm
    _ = _ := (runNativeRootHistoryObserve_neutral parameter root target ftsSecret table observe computation history
      context fuel cache hvalid hcomplete hensured).trans
      (evalDist_runNativeRootHistoryObserve_eq_trace parameter root target ftsSecret table observe computation context fuel cache history
        hvalid.valuesConsistent hstarts)

theorem evalDist_nativeHistoryTrace_eq_uniform
    (parameter : PublicParameter) (root : Digest) (target : Position)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → Finset Digest → ProbComp Bool)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (history : Finset Digest)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : .position target ∈ context.state.ensured)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = none) :
    evalDist (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache >>=
      finishNativeRootHistoryTrace parameter target table observe history) =
      evalDist (do
        let output ← LazyRevealProbe.sampleHashOutput
        if context.state.hitAt (.position target) output then pure true else
          runNativeQueryTrace parameter root ftsSecret computation (completePrivatePosition target context output).toDeferredContext fuel table cache >>=
            finishNativeRootHistoryTrace parameter target table observe history) := by
  rw [← evalDist_resolveRoot_then_nativeHistoryTrace parameter root target ftsSecret table observe computation
    context fuel cache history hvalid hcomplete hensured]
  simp only [resolveDeferredPositionValue, hstate, hvalue, bind_assoc]
  apply evalDist_bind_congr
  intro output _
  split_ifs <;> simp [completePrivatePosition]

end SphincsSecurity.Concrete.OtsProbeSimulation
