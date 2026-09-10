import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeRootCandidateHistory
import SphincsSecurity.Proof.OuterHashQueryCut

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec
open _root_.OracleComp.DeferredSampling

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def nativeHashHistorySelection (history : List CanonicalQuerySelection) (ordinal : Nat) :
    Option (List CanonicalQuerySelection × CanonicalQuerySelection) :=
  ((nativeHashQueryHistory history)[ordinal]?).map fun selection =>
    ((nativeHashQueryHistory history).take ordinal, selection)

noncomputable def nativeTraceHashCutHistory :
    Option (ResolvedRunResult (OuterQueryCut α × SplitHashCache)) × List CanonicalQuerySelection →
      Option (List CanonicalQuerySelection × CanonicalQuerySelection)
  | (none, _) => none
  | (some result, history) => result.value.1.input?.map fun input =>
      (nativeHashQueryHistory history, ⟨input, result.context, result.remaining, result.table, result.value.2⟩)

theorem nativeHashHistorySelection_cons_hash_zero
    (selection : CanonicalQuerySelection) (history : List CanonicalQuerySelection)
    (hhash : IsOuterHash selection.input) :
    nativeHashHistorySelection (selection :: history) 0 = some ([], selection) := by
  simp [nativeHashHistorySelection, nativeHashQueryHistory, hhash]

theorem nativeHashHistorySelection_cons_hash_succ
    (selection : CanonicalQuerySelection) (history : List CanonicalQuerySelection) (ordinal : Nat)
    (hhash : IsOuterHash selection.input) :
    nativeHashHistorySelection (selection :: history) (ordinal + 1) =
      (nativeHashHistorySelection history ordinal).map (fun pair => (selection :: pair.1, pair.2)) := by
  simp [nativeHashHistorySelection, nativeHashQueryHistory, hhash, Option.map_map, Function.comp_def]

theorem nativeHashHistorySelection_cons_not_hash
    (selection : CanonicalQuerySelection) (history : List CanonicalQuerySelection) (ordinal : Nat)
    (hhash : ¬IsOuterHash selection.input) :
    nativeHashHistorySelection (selection :: history) ordinal = nativeHashHistorySelection history ordinal := by
  simp [nativeHashHistorySelection, nativeHashQueryHistory, hhash]

theorem nativeTraceHashCutHistory_cons
    (selection : CanonicalQuerySelection)
    (trace : Option (ResolvedRunResult (OuterQueryCut α × SplitHashCache)) × List CanonicalQuerySelection) :
    nativeTraceHashCutHistory (trace.1, selection :: trace.2) =
      (nativeTraceHashCutHistory trace).map (fun pair =>
        (if IsOuterHash selection.input then selection :: pair.1 else pair.1, pair.2)) := by
  rcases trace with ⟨option, history⟩
  cases option with
  | none => rfl
  | some result =>
      by_cases hhash : IsOuterHash selection.input <;>
        simp [nativeTraceHashCutHistory, nativeHashQueryHistory, hhash, Option.map_map, Function.comp_def]

theorem runNativeQueryTrace_hashHistory_projection
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (ordinal : Nat)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    evalDist ((fun trace => nativeHashHistorySelection trace.2 ordinal) <$>
      runNativeQueryTrace parameter root ftsSecret computation context fuel table cache) =
    evalDist (nativeTraceHashCutHistory <$>
      runNativeQueryTrace parameter root ftsSecret (outerHashQueryCutAt computation ordinal) context fuel table cache) := by
  induction computation using OracleComp.inductionOn generalizing ordinal context fuel table cache with
  | pure value =>
      simp only [outerHashQueryCutAt, OracleComp.construct_pure, runNativeQueryTrace]
      split_ifs <;> simp [nativeHashHistorySelection, nativeHashQueryHistory, nativeTraceHashCutHistory, OuterQueryCut.input?]
  | query_bind input next ih =>
      rw [runNativeQueryTrace_query_bind, outerHashQueryCutAt_query_bind]
      by_cases hcomplete : DeferredCompletable table context
      · rw [if_pos hcomplete]
        by_cases hhash : IsOuterHash input
        · rw [if_pos hhash]
          cases ordinal with
          | zero =>
              simp only [map_bind]
              calc
                _ = evalDist (runResolvedFromTable context fuel table
                    ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache) >>= fun _ =>
                      pure (some ([], (⟨input, context, fuel, table, cache⟩ : CanonicalQuerySelection)))) := by
                  apply evalDist_bind_congr_left
                  intro result
                  cases result with
                  | none => simp [nativeHashHistorySelection_cons_hash_zero ⟨input, context, fuel, table, cache⟩ _ hhash]
                  | some result =>
                      simp only [map_bind, map_pure, nativeHashHistorySelection_cons_hash_zero ⟨input, context, fuel, table, cache⟩ _ hhash]
                      exact evalDist_bind_const_neverFails _ (by simp) _
                _ = _ := by
                  rw [evalDist_bind_const_neverFails _ (by simp) _]
                  simp [runNativeQueryTrace, OracleComp.construct_pure, hcomplete, nativeTraceHashCutHistory,
                    nativeHashQueryHistory, OuterQueryCut.input?]
          | succ ordinal =>
              rw [runNativeQueryTrace_query_bind, if_pos hcomplete]
              simp only [map_bind]
              apply evalDist_bind_congr_left
              intro result
              cases result with
              | none => simp [nativeHashHistorySelection, nativeHashQueryHistory, nativeTraceHashCutHistory, hhash]
              | some result =>
                  simp only [map_bind, map_pure, nativeHashHistorySelection_cons_hash_succ ⟨input, context, fuel, table, cache⟩ _ _ hhash,
                    nativeTraceHashCutHistory_cons, hhash, ↓reduceIte]
                  have hmap := evalDist_map_eq_of_evalDist_eq
                    (ih result.value.1 ordinal result.context result.remaining result.table result.value.2)
                    (Option.map (fun pair : List CanonicalQuerySelection × CanonicalQuerySelection =>
                      ((⟨input, context, fuel, table, cache⟩ : CanonicalQuerySelection) :: pair.1, pair.2)))
                  simpa only [Functor.map_map, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using hmap
        · rw [if_neg hhash, runNativeQueryTrace_query_bind, if_pos hcomplete]
          simp only [map_bind]
          apply evalDist_bind_congr_left
          intro result
          cases result with
          | none => simp [nativeHashHistorySelection, nativeHashQueryHistory, nativeTraceHashCutHistory, hhash]
          | some result =>
              simp only [map_bind, map_pure, nativeHashHistorySelection_cons_not_hash ⟨input, context, fuel, table, cache⟩ _ _ hhash,
                nativeTraceHashCutHistory_cons, hhash, ↓reduceIte]
              simpa only [Prod.mk.eta, Option.map_id_fun', id_eq, map_eq_bind_pure_comp, Function.comp_def] using
                ih result.value.1 ordinal result.context result.remaining result.table result.value.2
      · rw [if_neg hcomplete]
        by_cases hhash : IsOuterHash input
        · rw [if_pos hhash]
          cases ordinal <;> simp [runNativeQueryTrace, OracleComp.construct_pure, OracleComp.construct_query_bind,
            hcomplete, nativeHashHistorySelection, nativeHashQueryHistory, nativeTraceHashCutHistory]
        · rw [if_neg hhash, runNativeQueryTrace_query_bind, if_neg hcomplete]
          simp [nativeHashHistorySelection, nativeHashQueryHistory, nativeTraceHashCutHistory]

theorem nativeHashHistorySelection_append_hash
    (prior : List CanonicalQuerySelection) (selection : CanonicalQuerySelection) (suffix : List CanonicalQuerySelection)
    (hhash : IsOuterHash selection.input) :
    nativeHashHistorySelection (prior ++ selection :: suffix) (nativeHashQueryHistory prior).length =
      some (nativeHashQueryHistory prior, selection) := by
  simp [nativeHashHistorySelection, nativeHashQueryHistory, List.filter_append, hhash]

theorem nativeRootCandidateHistory_hashHistory
    (parameter : PublicParameter) (target : Position) (history : List CanonicalQuerySelection) :
    nativeRootCandidateHistory parameter target (nativeHashQueryHistory history) =
      nativeRootCandidateHistory parameter target history := by
  simp [nativeRootCandidateHistory, nativeHashQueryHistory, List.filter_filter]

end SphincsSecurity.Concrete.OtsProbeSimulation
