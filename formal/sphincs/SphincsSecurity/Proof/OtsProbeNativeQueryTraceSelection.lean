import SphincsSecurity.Proof.OtsProbeNativeQueryTrace
import SphincsSecurity.Proof.OtsProbeLiveHashSelection

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open _root_.OracleComp.DeferredSampling

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
theorem runNativeQueryTrace_selection_projection
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (ordinal : Nat) :
    evalDist ((fun result => result.2[ordinal]?) <$>
      runNativeQueryTrace parameter root ftsSecret computation context fuel table cache) =
      evalDist (liveNativeQuerySelection (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation ordinal context fuel table cache) := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache ordinal with
  | pure value =>
      simp only [runNativeQueryTrace, OracleComp.construct_pure, liveNativeQuerySelection_pure]
      split_ifs <;> simp
  | query_bind input next ih =>
      rw [runNativeQueryTrace_query_bind, liveNativeQuerySelection_query_bind]
      by_cases hcomplete : DeferredCompletable table context
      · simp only [hcomplete, ↓reduceIte, map_bind]
        cases ordinal with
        | zero =>
            calc
              _ = evalDist (runResolvedFromTable context fuel table
                  ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache) >>= fun _ =>
                    pure (some (⟨input, context, fuel, table, cache⟩ : CanonicalQuerySelection))) := by
                apply evalDist_bind_congr_left
                intro result
                cases result with
                | none => simp
                | some result =>
                    simp only [map_bind, map_pure, List.getElem?_cons_zero]
                    exact evalDist_bind_const_neverFails _ (by simp) _
              _ = _ := evalDist_bind_const_neverFails _ (by simp) _
        | succ ordinal =>
            apply evalDist_bind_congr_left
            intro result
            cases result with
            | none => simp
            | some result =>
                simp only [map_bind, map_pure, List.getElem?_cons_succ]
                simpa only [map_eq_bind_pure_comp, Function.comp_def] using
                  ih result.value.1 result.context result.remaining result.table result.value.2 ordinal
      · simp [hcomplete]

noncomputable def nativeHashQueryHistory (history : List CanonicalQuerySelection) : List CanonicalQuerySelection :=
  history.filter fun selection => IsOuterHash selection.input

theorem runNativeQueryTrace_hashSelection_projection
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (ordinal : Nat) :
    evalDist ((fun result => (nativeHashQueryHistory result.2)[ordinal]?) <$>
      runNativeQueryTrace parameter root ftsSecret computation context fuel table cache) =
      evalDist (liveNativeHashQuerySelection (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        computation ordinal context fuel table cache) := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache ordinal with
  | pure value =>
      simp only [runNativeQueryTrace, OracleComp.construct_pure, liveNativeHashQuerySelection_pure]
      split_ifs <;> simp [nativeHashQueryHistory]
  | query_bind input next ih =>
      rw [runNativeQueryTrace_query_bind, liveNativeHashQuerySelection_query_bind]
      by_cases hcomplete : DeferredCompletable table context
      · simp only [hcomplete, ↓reduceIte, map_bind]
        by_cases hhash : IsOuterHash input
        · cases ordinal with
          | zero =>
              simp only [hhash, and_self, ↓reduceIte]
              calc
                _ = evalDist (runResolvedFromTable context fuel table
                    ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache) >>= fun _ =>
                      pure (some (⟨input, context, fuel, table, cache⟩ : CanonicalQuerySelection))) := by
                  apply evalDist_bind_congr_left
                  intro result
                  cases result with
                  | none => simp [nativeHashQueryHistory, hhash]
                  | some result =>
                      simp only [map_bind, map_pure, nativeHashQueryHistory, List.filter_cons,
                        hhash, decide_true, Bool.true_eq, ↓reduceIte, List.getElem?_cons_zero]
                      exact evalDist_bind_const_neverFails _ (by simp) _
                _ = _ := evalDist_bind_const_neverFails _ (by simp [runResolvedFromTable]) _
          | succ ordinal =>
              simp only [hhash, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
                Nat.add_sub_cancel]
              apply evalDist_bind_congr_left
              intro result
              cases result with
              | none => simp [nativeHashQueryHistory, hhash]
              | some result =>
                  simp only [map_bind, map_pure, nativeHashQueryHistory, List.filter_cons,
                    hhash, decide_true, Bool.true_eq, ↓reduceIte, List.getElem?_cons_succ]
                  simpa only [nativeHashQueryHistory, map_eq_bind_pure_comp, Function.comp_def] using
                    ih result.value.1 result.context result.remaining result.table result.value.2 ordinal
        · simp only [hhash, false_and, ↓reduceIte]
          apply evalDist_bind_congr_left
          intro result
          cases result with
          | none => simp [nativeHashQueryHistory, hhash]
          | some result =>
              simp only [map_bind, map_pure, nativeHashQueryHistory, List.filter_cons,
                hhash, decide_false, Bool.false_eq_true, ↓reduceIte]
              simpa only [nativeHashQueryHistory, map_eq_bind_pure_comp, Function.comp_def] using
                ih result.value.1 result.context result.remaining result.table result.value.2 ordinal
      · simp [hcomplete, nativeHashQueryHistory]

end SphincsSecurity.Concrete.OtsProbeSimulation
