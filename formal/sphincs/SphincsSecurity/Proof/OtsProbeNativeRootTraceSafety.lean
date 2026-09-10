import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeRootCandidateHistory

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem nativeRootSelectionGuess_mem_history
    (parameter : PublicParameter) (target : Position) (selection : CanonicalQuerySelection)
    (history : List CanonicalQuerySelection) (hmem : selection ∈ history) (guess : Digest)
    (hguess : nativeRootSelectionGuess? parameter target selection = some guess) :
    guess ∈ nativeRootCandidateHistory parameter target history := by
  have hhash : IsOuterHash selection.input := by
    cases hinput : selection.input with
    | inl query =>
        cases query with
        | inl n => simp [nativeRootSelectionGuess?, nativeRootSelectionCandidate?, hinput] at hguess
        | inr input => trivial
    | inr message => simp [nativeRootSelectionGuess?, nativeRootSelectionCandidate?, hinput] at hguess
  simp only [nativeRootCandidateHistory, List.mem_toFinset, List.mem_filterMap]
  refine ⟨selection, ?_, hguess⟩
  simpa only [nativeHashQueryHistory, List.mem_filter, decide_eq_true_eq] using And.intro hmem hhash

theorem revealed_subset_of_mem_runNativeQueryTrace
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (α × SplitHashCache)) (history : List CanonicalQuerySelection)
    (hresult : (some result, history) ∈ support (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache)) :
    context.state.revealed ⊆ result.context.state.revealed := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache history with
  | pure value =>
      simp only [runNativeQueryTrace, OracleComp.construct_pure] at hresult
      split_ifs at hresult <;> simp only [mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq] at hresult
      · obtain ⟨rfl, _⟩ := hresult
        exact Finset.Subset.refl _
      · simp at hresult
  | query_bind input next ih =>
      rw [runNativeQueryTrace_query_bind] at hresult
      by_cases hcomplete : DeferredCompletable table context
      · rw [if_pos hcomplete, mem_support_bind_iff] at hresult
        obtain ⟨middle, hmiddle, htail⟩ := hresult
        cases middle with
        | none => simp at htail
        | some middle =>
            simp only [mem_support_bind_iff] at htail
            obtain ⟨tail, htail, hresult⟩ := htail
            simp only [mem_support_pure_iff, Prod.mk.injEq] at hresult
            have htrace : (some result, tail.2) ∈ support
                (runNativeQueryTrace parameter root ftsSecret (next middle.value.1)
                  middle.context middle.remaining middle.table middle.value.2) := by
              simpa only [hresult.1] using htail
            exact (revealed_subset_of_mem_runResolvedFromTable _ context fuel table middle hmiddle).trans
              (ih middle.value.1 middle.context middle.remaining middle.table middle.value.2 tail.2 htrace)
      · rw [if_neg hcomplete] at hresult
        simp at hresult

theorem nativeRootHashSafe_of_hidden_trace_avoids
    (parameter : PublicParameter) (root : Digest) (target : Position) (hroot : IsLayerRoot target)
    (before after : HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput) (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (h : NativePositionReplaceable target before after context)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (α × SplitHashCache)) (history : List CanonicalQuerySelection)
    (hresult : (some result, history) ∈ support (runNativeQueryTrace parameter root ftsSecret
      (OracleSpec.query (spec := OracleWorld + SigningSpec) (.inl (.inr input)) >>= next) context fuel table cache))
    (hhidden : .position target ∉ result.context.state.revealed)
    (hbefore : truncateHash before ∉ nativeRootCandidateHistory parameter target history)
    (hafter : truncateHash after ∉ nativeRootCandidateHistory parameter target history) :
    NativeRootHashSafe parameter target before after input context := by
  rw [runNativeQueryTrace_query_bind] at hresult
  by_cases hcomplete : DeferredCompletable table context
  · rw [if_pos hcomplete, mem_support_bind_iff] at hresult
    obtain ⟨middle, hmiddle, htail⟩ := hresult
    cases middle with
    | none => simp at htail
    | some middle =>
        simp only [mem_support_bind_iff] at htail
        obtain ⟨tail, htail, hresult⟩ := htail
        simp only [mem_support_pure_iff, Prod.mk.injEq] at hresult
        have htrace : (some result, tail.2) ∈ support
            (runNativeQueryTrace parameter root ftsSecret (next middle.value.1)
              middle.context middle.remaining middle.table middle.value.2) := by
          simpa only [hresult.1] using htail
        have hmiddleHidden : .position target ∉ middle.context.state.revealed := fun hmem =>
          hhidden (revealed_subset_of_mem_runNativeQueryTrace parameter root ftsSecret _ _ _ _ _ result tail.2 htrace hmem)
        by_contra hunsafe
        obtain ⟨candidate, hcandidate, hcoordinate, hguess⟩ :=
          nativeRootHashSafe_failure_of_hidden_result_candidate parameter target hroot before after input context h
            fuel table cache hunsafe middle hmiddle hmiddleHidden
        have hselection : nativeRootSelectionGuess? parameter target ⟨.inl (.inr input), context, fuel, table, cache⟩ =
            some candidate.candidate := by
          simp [nativeRootSelectionGuess?, nativeRootSelectionCandidate?, hcandidate, hcoordinate]
        have hmem := nativeRootSelectionGuess_mem_history parameter target _ history
          (by rw [hresult.2]; exact List.mem_cons_self) candidate.candidate hselection
        rcases hguess with heq | heq
        · exact hbefore (heq ▸ hmem)
        · exact hafter (heq ▸ hmem)
  · rw [if_neg hcomplete] at hresult
    simp at hresult

theorem nativeRootOuterSafe_of_hidden_trace_avoids
    (parameter : PublicParameter) (root : Digest) (target : Position) (hroot : IsLayerRoot target)
    (before after : HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (h : NativePositionReplaceable target before after context)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (α × SplitHashCache)) (history : List CanonicalQuerySelection)
    (hresult : (some result, history) ∈ support (runNativeQueryTrace parameter root ftsSecret
      (OracleSpec.query input >>= next) context fuel table cache))
    (hhidden : .position target ∉ result.context.state.revealed)
    (hbefore : truncateHash before ∉ nativeRootCandidateHistory parameter target history)
    (hafter : truncateHash after ∉ nativeRootCandidateHistory parameter target history) :
    NativeRootOuterSafe parameter target before after input context := by
  cases input with
  | inl query =>
      cases query with
      | inl n => trivial
      | inr input =>
          exact nativeRootHashSafe_of_hidden_trace_avoids parameter root target hroot before after ftsSecret input next context h
            fuel table cache result history hresult hhidden hbefore hafter
  | inr message => trivial

def NativeRootTraceCompatible (parameter : PublicParameter) (target : Position) (before after : HashOutput) :
    (Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection) → Prop
  | (none, _) => False
  | (some result, history) =>
      .position target ∉ result.context.state.revealed ∧
        truncateHash before ∉ nativeRootCandidateHistory parameter target history ∧
        truncateHash after ∉ nativeRootCandidateHistory parameter target history

theorem probEvent_nativeRootTraceCompatible_eq_zero_of_unsafe
    (parameter : PublicParameter) (root : Digest) (target : Position) (hroot : IsLayerRoot target)
    (before after : HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (h : NativePositionReplaceable target before after context)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hunsafe : ¬NativeRootOuterSafe parameter target before after input context) :
    Pr[NativeRootTraceCompatible parameter target before after |
      runNativeQueryTrace parameter root ftsSecret (OracleSpec.query input >>= next) context fuel table cache] = 0 := by
  rw [probEvent_eq_zero_iff]
  rintro ⟨option, history⟩ htrace hcompatible
  cases option with
  | none => exact hcompatible
  | some result =>
      exact hunsafe (nativeRootOuterSafe_of_hidden_trace_avoids parameter root target hroot before after ftsSecret input next context h
        fuel table cache result history htrace hcompatible.1 hcompatible.2.1 hcompatible.2.2)

end SphincsSecurity.Concrete.OtsProbeSimulation
