import SphincsSecurity.Proof.OtsProbeNativeRootCandidate
import SphincsSecurity.Proof.OtsProbeNativeQueryTraceSelection
import SphincsSecurity.Proof.OtsProbePrivateValueHistoryRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def nativeRootSelectionCandidate? (parameter : PublicParameter) (selection : CanonicalQuerySelection) : Option Probe :=
  match selection.input with
  | .inl (.inr input) => nativeRootCandidate? parameter input selection.context
  | _ => none

noncomputable def nativeRootSelectionGuess? (parameter : PublicParameter) (target : Position)
    (selection : CanonicalQuerySelection) : Option Digest := do
  let candidate ← nativeRootSelectionCandidate? parameter selection
  if candidate.coordinate = .position target then some candidate.candidate else none

noncomputable def nativeRootCandidateHistory (parameter : PublicParameter) (target : Position)
    (history : List CanonicalQuerySelection) : Finset Digest :=
  ((nativeHashQueryHistory history).filterMap (nativeRootSelectionGuess? parameter target)).toFinset

theorem nativeRootCandidateHistory_card_le_hash_length
    (parameter : PublicParameter) (target : Position) (history : List CanonicalQuerySelection) :
    (nativeRootCandidateHistory parameter target history).card ≤ (nativeHashQueryHistory history).length := by
  exact (List.toFinset_card_le _).trans (List.length_filterMap_le _ _)

theorem runNativeQueryTrace_hash_length_le
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (bound : Nat) (hbound : computation.IsQueryBoundP IsOuterHash bound)
    (result : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection)
    (hresult : result ∈ support (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache)) :
    (nativeHashQueryHistory result.2).length ≤ bound := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache bound result with
  | pure value =>
      simp only [runNativeQueryTrace, OracleComp.construct_pure] at hresult
      split_ifs at hresult <;>
        simp only [mem_support_pure_iff] at hresult <;>
        subst result <;> simp [nativeHashQueryHistory]
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [runNativeQueryTrace_query_bind] at hresult
      by_cases hcomplete : DeferredCompletable table context
      · rw [if_pos hcomplete, mem_support_bind_iff] at hresult
        obtain ⟨middle, hmiddle, htail⟩ := hresult
        have hstep (history : List CanonicalQuerySelection)
            (hlength : (nativeHashQueryHistory history).length ≤ if IsOuterHash input then bound - 1 else bound) :
            (nativeHashQueryHistory (⟨input, context, fuel, table, cache⟩ :: history)).length ≤ bound := by
          by_cases hhash : IsOuterHash input
          · have hpositive := hbound.1.resolve_left (not_not.mpr hhash)
            simp only [if_pos hhash] at hlength
            simpa only [nativeHashQueryHistory, List.filter_cons, hhash, decide_true, Bool.true_eq, ↓reduceIte,
              List.length_cons] using (show (nativeHashQueryHistory history).length + 1 ≤ bound by omega)
          · simpa only [nativeHashQueryHistory, List.filter_cons, hhash, decide_false, Bool.false_eq_true, ↓reduceIte]
              using hlength
        cases middle with
        | none =>
            simp only [pure_bind, mem_support_pure_iff] at htail
            subst result
            exact hstep [] (by simp [nativeHashQueryHistory])
        | some middle =>
            simp only [mem_support_bind_iff] at htail
            obtain ⟨tail, htail, hresult⟩ := htail
            simp only [mem_support_pure_iff] at hresult
            subst result
            exact hstep tail.2 (ih middle.value.1 middle.context middle.remaining middle.table middle.value.2
              (if IsOuterHash input then bound - 1 else bound) (hbound.2 middle.value.1) tail htail)
      · rw [if_neg hcomplete, mem_support_pure_iff] at hresult
        subst result
        simp [nativeHashQueryHistory]

theorem runNativeQueryTrace_root_history_card_le
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (bound : Nat) (hbound : computation.IsQueryBoundP IsOuterHash bound)
    (result : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection)
    (hresult : result ∈ support (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache)) :
    (nativeRootCandidateHistory parameter target result.2).card ≤ bound :=
  (nativeRootCandidateHistory_card_le_hash_length parameter target result.2).trans
    (runNativeQueryTrace_hash_length_le parameter root ftsSecret computation context fuel table cache bound hbound result hresult)

theorem probEvent_uniform_avoids_native_root_history_ge_three_quarters
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (bound : Nat) (hbound : computation.IsQueryBoundP IsOuterHash bound)
    (initialHistory : Finset Digest) (hbudget : initialHistory.card + bound ≤ 2 ^ 126)
    (result : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection)
    (hresult : result ∈ support (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache)) :
    (3 / 4 : ENNReal) ≤ Pr[fun output => truncateHash output ∉
      initialHistory ∪ nativeRootCandidateHistory parameter target result.2 | LazyRevealProbe.sampleHashOutput] := by
  apply probEvent_uniform_avoids_private_history_ge_three_quarters
  exact (Finset.card_union_le _ _).trans ((Nat.add_le_add_left
    (runNativeQueryTrace_root_history_card_le parameter root ftsSecret target computation context fuel table cache bound hbound result hresult)
    initialHistory.card).trans hbudget)

end SphincsSecurity.Concrete.OtsProbeSimulation
