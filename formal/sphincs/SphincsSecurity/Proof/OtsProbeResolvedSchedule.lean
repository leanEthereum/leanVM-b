import SphincsSecurity.Proof.OtsProbeResolvedSampling

/-!
# Concrete one-time layer scheduling

The chronological signer resolves a selected layer before selecting the next one. The ordinary
signer selects all three layers first. This file permutes those operations without changing their
joint distribution.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp

abbrev DeferredLayerEncoding := Counter × (ChainIndex → Digit)

structure DeferredLayerStore where
  selected : Layer → Option DeferredLayerEncoding
  resolved : Layer → Option LayerPart
  cache : SplitHashCache

noncomputable def selectDeferredLayer
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay : Layer) (result : ResolvedRunResult DeferredLayerStore) :
    ProbComp (Option (ResolvedRunResult DeferredLayerStore)) := do
  let selected ← runResolvedFromTable result.context result.remaining table
    ((maskedSignLayer parameter ftsSecret index lay).run result.value.cache)
  match selected with
  | none => pure none
  | some selected => pure (some ⟨selected.context, selected.remaining,
      { selected := Function.update result.value.selected lay selected.value.1
        resolved := result.value.resolved
        cache := selected.value.2 }, table⟩)

noncomputable def resolveDeferredLayer
    (table : OtsSecretIndex → HashOutput) (index : Index) (lay : Layer)
    (result : ResolvedRunResult DeferredLayerStore) :
    ProbComp (Option (ResolvedRunResult DeferredLayerStore)) :=
  match result.value.selected lay with
  | none => pure (some ⟨result.context, result.remaining,
      { result.value with resolved := Function.update result.value.resolved lay none },
      table⟩)
  | some (counter, encoding) => do
      let resolved ← resolveDeferredLayerValues table index lay encoding result.context
      match resolved with
      | none => pure none
      | some (context, values) =>
          let part : LayerPart := (counter, values.1, values.2)
          pure (some ⟨context, result.remaining,
            { result.value with
              resolved := Function.update result.value.resolved lay (some part) }, table⟩)

def mapResolvedLayerSchedule
    (table : OtsSecretIndex → HashOutput)
    (resolvedLay selectedLay : Layer) (counter : Counter)
    (store : DeferredLayerStore) :
    Option (ResolvedRunResult (DeferredLayerValues × DeferredLayerSelection)) →
      Option (ResolvedRunResult DeferredLayerStore)
  | none => none
  | some result => some ⟨result.context, result.remaining,
      { selected := Function.update store.selected selectedLay result.value.2.1
        resolved := Function.update store.resolved resolvedLay
          (some (counter, result.value.1.1, result.value.1.2))
        cache := result.value.2.2 }, table⟩

theorem evalDist_resolveDeferredLayer_then_selectDeferredLayer_eq
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (resolvedLay selectedLay : Layer) (hlt : resolvedLay.val < selectedLay.val)
    (result : ResolvedRunResult DeferredLayerStore) :
    evalDist (resolveDeferredLayer table index resolvedLay result >>= fun resolved =>
      match resolved with
      | none => pure none
      | some resolved => selectDeferredLayer parameter table ftsSecret index selectedLay resolved) =
    evalDist (selectDeferredLayer parameter table ftsSecret index selectedLay result >>=
      fun selected =>
      match selected with
      | none => pure none
      | some selected => resolveDeferredLayer table index resolvedLay selected) := by
  classical
  have hne : selectedLay ≠ resolvedLay := by
    intro heq
    subst selectedLay
    omega
  have hne' : resolvedLay ≠ selectedLay := Ne.symm hne
  cases hselected : result.value.selected resolvedLay with
  | none =>
      rw [resolveDeferredLayer]
      simp only [hselected, pure_bind]
      unfold selectDeferredLayer
      simp only [bind_assoc]
      apply congrArg evalDist
      apply bind_congr
      intro selectedOption
      cases selectedOption with
      | none => rfl
      | some selected =>
          simp only [pure_bind]
          rw [resolveDeferredLayer]
          simp [Function.update, hne', hselected]
  | some selected =>
      rcases selected with ⟨counter, encoding⟩
      have hleft :
          (resolveDeferredLayer table index resolvedLay result >>= fun resolved =>
            match resolved with
            | none => pure none
            | some resolved =>
                selectDeferredLayer parameter table ftsSecret index selectedLay resolved) =
          (mapResolvedLayerSchedule table resolvedLay selectedLay counter result.value <$>
            resolveThenSelectLayer parameter table ftsSecret index resolvedLay selectedLay
              encoding result.context result.remaining result.value.cache) := by
        unfold resolveDeferredLayer resolveThenSelectLayer selectDeferredLayer
        simp only [hselected, map_eq_bind_pure_comp, bind_assoc]
        apply bind_congr
        intro resolvedOption
        cases resolvedOption with
        | none => simp [mapResolvedLayerSchedule]
        | some resolved =>
            rcases resolved with ⟨resolvedContext, values⟩
            simp only [pure_bind]
            rw [bind_assoc]
            apply bind_congr
            intro selectedOption
            cases selectedOption <;> rfl
      have hright :
          (selectDeferredLayer parameter table ftsSecret index selectedLay result >>=
            fun selected =>
            match selected with
            | none => pure none
            | some selected => resolveDeferredLayer table index resolvedLay selected) =
          (mapResolvedLayerSchedule table resolvedLay selectedLay counter result.value <$>
            selectThenResolveLayer parameter table ftsSecret index resolvedLay selectedLay
              encoding result.context result.remaining result.value.cache) := by
        unfold selectDeferredLayer selectThenResolveLayer
        simp only [map_eq_bind_pure_comp, bind_assoc]
        apply bind_congr
        intro selectedOption
        cases selectedOption with
        | none => simp [mapResolvedLayerSchedule]
        | some selected =>
            simp only [pure_bind]
            rw [resolveDeferredLayer]
            simp [Function.update, hne', hselected]
            apply bind_congr
            intro resolvedOption
            cases resolvedOption <;> rfl
      rw [hleft, hright]
      rw [evalDist_map, evalDist_map,
        evalDist_resolveThenSelectLayer_eq_selectThenResolveLayer_of_lt parameter table
          ftsSecret index resolvedLay selectedLay hlt encoding result.context result.remaining
          result.value.cache]

inductive DeferredLayerOperation where
  | select (lay : Layer)
  | resolve (lay : Layer)

noncomputable def runDeferredLayerOperation
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (operation : DeferredLayerOperation) :
    Option (ResolvedRunResult DeferredLayerStore) →
      ProbComp (Option (ResolvedRunResult DeferredLayerStore))
  | none => pure none
  | some result =>
      match operation with
      | .select lay => selectDeferredLayer parameter table ftsSecret index lay result
      | .resolve lay => resolveDeferredLayer table index lay result

noncomputable def runDeferredLayerSchedule
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) :
    List DeferredLayerOperation → Option (ResolvedRunResult DeferredLayerStore) →
      ProbComp (Option (ResolvedRunResult DeferredLayerStore))
  | [], input => pure input
  | operation :: remaining, input => do
      let result ← runDeferredLayerOperation parameter table ftsSecret index operation input
      runDeferredLayerSchedule parameter table ftsSecret index remaining result

theorem evalDist_runDeferredLayerSchedule_adjacent
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (resolvedLay selectedLay : Layer) (hlt : resolvedLay.val < selectedLay.val)
    (remaining : List DeferredLayerOperation)
    (input : Option (ResolvedRunResult DeferredLayerStore)) :
    evalDist (runDeferredLayerSchedule parameter table ftsSecret index
      (.resolve resolvedLay :: .select selectedLay :: remaining) input) =
    evalDist (runDeferredLayerSchedule parameter table ftsSecret index
      (.select selectedLay :: .resolve resolvedLay :: remaining) input) := by
  cases input with
  | none => simp [runDeferredLayerSchedule, runDeferredLayerOperation]
  | some result =>
      simp only [runDeferredLayerSchedule, runDeferredLayerOperation]
      simp only [← bind_assoc]
      have hswap := evalDist_resolveDeferredLayer_then_selectDeferredLayer_eq parameter table
        ftsSecret index resolvedLay selectedLay hlt result
      rw [evalDist_bind, evalDist_bind] at hswap
      rw [evalDist_bind, evalDist_bind, hswap]
      rw [evalDist_bind]
      rw [evalDist_bind]

theorem evalDist_runDeferredLayerSchedule_swap
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (resolvedLay selectedLay : Layer) (hlt : resolvedLay.val < selectedLay.val)
    (before remaining : List DeferredLayerOperation)
    (input : Option (ResolvedRunResult DeferredLayerStore)) :
    evalDist (runDeferredLayerSchedule parameter table ftsSecret index
      (before ++ .resolve resolvedLay :: .select selectedLay :: remaining) input) =
    evalDist (runDeferredLayerSchedule parameter table ftsSecret index
      (before ++ .select selectedLay :: .resolve resolvedLay :: remaining) input) := by
  induction before generalizing input with
  | nil =>
      simpa using evalDist_runDeferredLayerSchedule_adjacent parameter table ftsSecret index
        resolvedLay selectedLay hlt remaining input
  | cons operation before ih =>
      simp only [List.cons_append, runDeferredLayerSchedule]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro result
      exact ih result

def chronologicalLayerSchedule : List DeferredLayerOperation :=
  [.select topLayer, .resolve topLayer,
    .select middleLayer, .resolve middleLayer,
    .select bottomLayer, .resolve bottomLayer]

def deferredLayerSchedule : List DeferredLayerOperation :=
  [.select topLayer, .select middleLayer, .select bottomLayer,
    .resolve topLayer, .resolve middleLayer, .resolve bottomLayer]

theorem evalDist_chronologicalLayerSchedule_eq_deferred
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (input : Option (ResolvedRunResult DeferredLayerStore)) :
    evalDist (runDeferredLayerSchedule parameter table ftsSecret index
      chronologicalLayerSchedule input) =
    evalDist (runDeferredLayerSchedule parameter table ftsSecret index
      deferredLayerSchedule input) := by
  have h01 : topLayer.val < middleLayer.val := by decide
  have h12 : middleLayer.val < bottomLayer.val := by decide
  have h02 : topLayer.val < bottomLayer.val := by decide
  calc
    _ = evalDist (runDeferredLayerSchedule parameter table ftsSecret index
        [.select topLayer, .select middleLayer, .resolve topLayer,
          .resolve middleLayer, .select bottomLayer, .resolve bottomLayer] input) := by
      simpa [chronologicalLayerSchedule] using
        evalDist_runDeferredLayerSchedule_swap parameter table ftsSecret index topLayer
          middleLayer h01 [.select topLayer]
          [.resolve middleLayer, .select bottomLayer, .resolve bottomLayer] input
    _ = evalDist (runDeferredLayerSchedule parameter table ftsSecret index
        [.select topLayer, .select middleLayer, .resolve topLayer,
          .select bottomLayer, .resolve middleLayer, .resolve bottomLayer] input) := by
      simpa using
        evalDist_runDeferredLayerSchedule_swap parameter table ftsSecret index middleLayer
          bottomLayer h12 [.select topLayer, .select middleLayer, .resolve topLayer]
          [.resolve bottomLayer] input
    _ = evalDist (runDeferredLayerSchedule parameter table ftsSecret index
        deferredLayerSchedule input) := by
      simpa [deferredLayerSchedule] using
        evalDist_runDeferredLayerSchedule_swap parameter table ftsSecret index topLayer
          bottomLayer h02 [.select topLayer, .select middleLayer]
          [.resolve middleLayer, .resolve bottomLayer] input

end SphincsSecurity.Concrete.OtsProbeSimulation
