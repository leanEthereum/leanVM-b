import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeRootCandidateNormalization
import SphincsSecurity.Proof.OtsProbeNativeRootCompatibleTrace

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem nativeRootCandidate_eq_of_visible_state_eq
    (parameter : PublicParameter) (input : HashInput) (left right : DeferredContext)
    (hvalues : left.state.values = right.state.values) (hrevealed : left.state.revealed = right.state.revealed) :
    nativeRootCandidate? parameter input left = nativeRootCandidate? parameter input right := by
  have hplan := purePlanProbingHashQuery_eq_of_value_presence left.state right.state
    (fun coordinate => congrArg Option.isSome (congrFun hvalues coordinate)) parameter input
  have hstruct : KnownHiddenStructuralRootQuery parameter input left ↔ KnownHiddenStructuralRootQuery parameter input right := by
    unfold KnownHiddenStructuralRootQuery
    simp only [hrevealed, purePeekTableInput_eq_of_values_eq parameter hvalues]
  have hat (candidate : Probe) : NativeRootCandidateAt parameter input left candidate ↔ NativeRootCandidateAt parameter input right candidate := by
    simp only [NativeRootCandidateAt, hplan, hstruct]
  cases hleft : nativeRootCandidate? parameter input left with
  | none =>
      cases hright : nativeRootCandidate? parameter input right with
      | none => rfl
      | some candidate =>
          have heq := (nativeRootCandidate?_eq_some_iff parameter input left candidate).mpr
            ((hat candidate).mpr ((nativeRootCandidate?_eq_some_iff parameter input right candidate).mp hright))
          rw [hleft] at heq
          contradiction
  | some candidate =>
      exact ((nativeRootCandidate?_eq_some_iff parameter input right candidate).mpr
        ((hat candidate).mp ((nativeRootCandidate?_eq_some_iff parameter input left candidate).mp hleft))).symm

theorem nativeRootSelectionGuess_resolvePositionValue
    (parameter : PublicParameter) (target position : Position) (input : (OracleWorld + SigningSpec).Domain)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : DeferredResolution) (hresult : some result ∈ support (resolveDeferredPositionValue position context)) :
    nativeRootSelectionGuess? parameter target ⟨input, result.toDeferredContext, fuel, table, cache⟩ =
      nativeRootSelectionGuess? parameter target ⟨input, context, fuel, table, cache⟩ := by
  have hvalues := resolveDeferredPositionValue_preserves_state_values position context result hresult
  have hstate := resolveDeferredPositionValue_state_eq_clearPending position context result hresult
  have hrevealed : result.state.revealed = context.state.revealed := by rw [hstate]; rfl
  unfold nativeRootSelectionGuess? nativeRootSelectionCandidate?
  cases input with
  | inl query =>
      cases query with
      | inl n => rfl
      | inr input => simp only [nativeRootCandidate_eq_of_visible_state_eq parameter input _ _ hvalues hrevealed]
  | inr message => rfl

noncomputable def runNativeRootHistoryObserve
    (parameter : PublicParameter) (root : Digest) (target : Position)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → Finset Digest → ProbComp Bool)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    DeferredContext → Nat → SplitHashCache → Finset Digest → ProbComp Bool :=
  OracleComp.construct
    (fun value context fuel cache history =>
      if DeferredCompletable table context then
        privateResolutionObserve target table (fun final remaining value => observe final remaining (value, cache) history) context fuel value
      else pure true)
    (fun input _ next context fuel cache history =>
      if DeferredCompletable table context then
        runResolvedObserve
          (fun final remaining value => next value.1 final remaining value.2
            (insertNativeRootGuess (nativeRootSelectionGuess? parameter target ⟨input, context, fuel, table, cache⟩) history))
          context fuel table ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache)
      else pure true) computation

theorem runNativeRootHistoryObserve_of_not_completable
    (parameter : PublicParameter) (root : Digest) (target : Position)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → Finset Digest → ProbComp Bool)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (history : Finset Digest)
    (hnot : ¬DeferredCompletable table context) :
    runNativeRootHistoryObserve parameter root target ftsSecret table observe computation context fuel cache history = pure true := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [runNativeRootHistoryObserve, OracleComp.construct_pure, hnot, ↓reduceIte]
  | query_bind input next _ => simp only [runNativeRootHistoryObserve, OracleComp.construct_query_bind, hnot, ↓reduceIte]

theorem evalDist_runNativeRootHistoryObserve_query
    (parameter : PublicParameter) (root : Digest) (target : Position)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → Finset Digest → ProbComp Bool)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (history : Finset Digest)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    evalDist (runNativeRootHistoryObserve parameter root target ftsSecret table observe (OracleSpec.query input >>= next) context fuel cache history) =
      evalDist (runResolvedObserve
        (fun final remaining value => runNativeRootHistoryObserve parameter root target ftsSecret table observe (next value.1) final remaining value.2
          (insertNativeRootGuess (nativeRootSelectionGuess? parameter target ⟨input, context, fuel, table, cache⟩) history))
        context fuel table ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache)) := by
  simp only [runNativeRootHistoryObserve, OracleComp.construct_query_bind]
  by_cases hcomplete : DeferredCompletable table context
  · rw [if_pos hcomplete]
  · rw [if_neg hcomplete]
    symm
    apply evalDist_runResolvedObserve_eq_true_of_not_completable _ context fuel table _ hconsistent hstarts hcomplete
    intro final remaining value _ _ hnot
    exact congrArg evalDist (runNativeRootHistoryObserve_of_not_completable parameter root target ftsSecret table observe
      (next value.1) final remaining value.2 _ hnot)

theorem evalDist_runNativeRootHistoryObserve_pure
    (parameter : PublicParameter) (root : Digest) (target : Position)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → Finset Digest → ProbComp Bool) (value : α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (history : Finset Digest)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    evalDist (runNativeRootHistoryObserve parameter root target ftsSecret table observe (pure value) context fuel cache history) =
      evalDist (privateResolutionObserve target table (fun final remaining value => observe final remaining (value, cache) history) context fuel value) := by
  simp only [runNativeRootHistoryObserve, OracleComp.construct_pure]
  by_cases hcomplete : DeferredCompletable table context
  · rw [if_pos hcomplete]
  · rw [if_neg hcomplete]
    exact (ObserverDooms.eq_true context fuel value hconsistent hstarts hcomplete).symm

theorem runNativeRootHistoryObserve_neutral
    (parameter : PublicParameter) (root : Digest) (target : Position)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → Finset Digest → ProbComp Bool)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ history, ObserverPositionNeutralAt table target
      (fun context fuel cache => runNativeRootHistoryObserve parameter root target ftsSecret table observe computation context fuel cache history) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro history context fuel cache hvalid hcomplete hensured
      have hstarts := startTableAgrees_of_deferredCompletable hcomplete
      calc
        _ = evalDist (resolveDeferredPositionValue target context >>= fun resolved =>
            match resolved with
            | none => pure true
            | some resolved => privateResolutionObserve target table
                (fun final remaining value => observe final remaining (value, cache) history) resolved.toDeferredContext fuel value) := by
          apply evalDist_bind_congr
          intro resolved hresolved
          cases resolved with
          | none => rfl
          | some resolved =>
              exact evalDist_runNativeRootHistoryObserve_pure parameter root target ftsSecret table observe value _ fuel cache history
                (hvalid.of_resolveDeferredPositionValue target resolved hresolved).valuesConsistent
                (hstarts.of_state_values_eq (resolveDeferredPositionValue_preserves_state_values target context resolved hresolved))
        _ = _ := (privateResolutionObserve_neutral target table
          (fun final remaining value => observe final remaining (value, cache) history) context fuel value hvalid hcomplete hensured).trans
          (evalDist_runNativeRootHistoryObserve_pure parameter root target ftsSecret table observe value context fuel cache history
            hvalid.valuesConsistent hstarts).symm
  | query_bind input next ih =>
      intro history context fuel cache hvalid hcomplete hensured
      have hstarts := startTableAgrees_of_deferredCompletable hcomplete
      let nextHistory := insertNativeRootGuess (nativeRootSelectionGuess? parameter target ⟨input, context, fuel, table, cache⟩) history
      let after : DeferredContext → Nat → ((OracleWorld + SigningSpec).Range input × SplitHashCache) → ProbComp Bool :=
        fun final remaining value => runNativeRootHistoryObserve parameter root target ftsSecret table observe
          (next value.1) final remaining value.2 nextHistory
      have hneutral : ObserverPositionNeutralAt table target after := by
        intro final remaining value hvalid hcomplete hensured
        exact ih value.1 nextHistory final remaining value.2 hvalid hcomplete hensured
      letI : ObserverDooms table after := ⟨by
        intro final remaining value _ _ hnot
        exact congrArg evalDist (runNativeRootHistoryObserve_of_not_completable parameter root target ftsSecret table observe
          (next value.1) final remaining value.2 nextHistory hnot)⟩
      calc
        _ = evalDist (resolveDeferredPositionValue target context >>= fun resolved =>
            match resolved with
            | none => pure true
            | some resolved => runResolvedObserve after resolved.toDeferredContext fuel table
                ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache)) := by
          apply evalDist_bind_congr
          intro resolved hresolved
          cases resolved with
          | none => rfl
          | some resolved =>
              have hquery := evalDist_runNativeRootHistoryObserve_query parameter root target ftsSecret table observe input next
                resolved.toDeferredContext fuel cache history (hvalid.of_resolveDeferredPositionValue target resolved hresolved).valuesConsistent
                (hstarts.of_state_values_eq (resolveDeferredPositionValue_preserves_state_values target context resolved hresolved))
              simpa only [nativeRootSelectionGuess_resolvePositionValue parameter target target input context fuel table cache resolved hresolved,
                after, nextHistory] using hquery
        _ = evalDist (runResolvedObserve after context fuel table
            ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache)) :=
          evalDist_resolveDeferredPositionValue_then_runResolvedObserve_auto_at target _ context fuel table hvalid hcomplete hensured hneutral
        _ = _ := (evalDist_runNativeRootHistoryObserve_query parameter root target ftsSecret table observe input next
          context fuel cache history hvalid.valuesConsistent hstarts).symm

end SphincsSecurity.Concrete.OtsProbeSimulation
