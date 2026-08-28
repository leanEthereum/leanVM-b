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

def emptyDeferredLayerStore (cache : SplitHashCache) : DeferredLayerStore :=
  { selected := fun _ => none
    resolved := fun _ => none
    cache := cache }

def projectDeferredLayerStore
    (result : ResolvedRunResult DeferredLayerStore) :
    ResolvedRunResult ((Layer → Option LayerPart) × SplitHashCache) :=
  { result with value := (result.value.resolved, result.value.cache) }

theorem DeferredCompletion.materializeResolvedPosition
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput} (position : Position)
    (result : DeferredResolution)
    (hstateValues : result.state.values = context.state.values)
    (hpending : result.state.pending =
      context.state.pendingAway (.position position))
    (hresolved : result.toDeferredContext.positionValue position = some result.output)
    (hcompletion : DeferredCompletion table result.toDeferredContext completion) :
    DeferredCompletion table
      (materializeResolvedPosition context position result) completion := by
  refine ⟨?_, hcompletion.2.1, ?_, hcompletion.2.2.2⟩
  · intro coordinate output hvalue
    by_cases heq : coordinate = .position position
    · subst coordinate
      change (context.state.materialize (.position position) result.output).values
        (.position position) = some output at hvalue
      have hsame : result.output = output := by
        exact Option.some.inj (by simpa [LazyRevealProbe.State.materialize] using hvalue)
      rw [← hsame]
      exact hcompletion.eq_positionValue position result.output hresolved
    · apply hcompletion.1 coordinate output
      rw [hstateValues]
      change (context.state.materialize (.position position) result.output).values
        coordinate = some output at hvalue
      simpa [LazyRevealProbe.State.materialize, Function.update_of_ne heq] using hvalue
  · intro coordinate candidate hmember
    apply hcompletion.2.2.1 coordinate candidate
    rw [hpending]
    change (coordinate, candidate) ∈
      (context.state.materialize (.position position) result.output).pending at hmember
    simpa [LazyRevealProbe.State.materialize] using hmember

theorem deferredCompletion_materializeResolvedPosition_iff
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput} (position : Position)
    (result : DeferredResolution)
    (hstateValues : result.state.values = context.state.values)
    (hpending : result.state.pending =
      context.state.pendingAway (.position position))
    (hresolved : result.toDeferredContext.positionValue position = some result.output) :
    DeferredCompletion table
        (materializeResolvedPosition context position result) completion ↔
      DeferredCompletion table result.toDeferredContext completion := by
  constructor
  · exact fun hcompletion => hcompletion.of_materializeResolvedPosition position result
      hstateValues (by rw [hpending]) hresolved
  · exact fun hcompletion => hcompletion.materializeResolvedPosition position result
      hstateValues hpending hresolved

theorem deferredCompletion_materializeResolvedChainStart_iff
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput} (index : OtsSecretIndex)
    (result : DeferredResolution)
    (hstarts : StartTableAgrees context.state table)
    (houtput : result.output = table index)
    (hstateValues : result.state.values = context.state.values)
    (hdeferredValues : result.values = context.values)
    (hpending : result.state.pending = context.state.pendingAway index.coordinate) :
    DeferredCompletion table
        (materializeResolvedChainStart context index result) completion ↔
      DeferredCompletion table result.toDeferredContext completion := by
  constructor
  · intro hcompletion
    refine ⟨?_, ?_, ?_, hcompletion.2.2.2⟩
    · intro coordinate output hvalue
      rw [hstateValues] at hvalue
      by_cases heq : coordinate = index.coordinate
      · subst coordinate
        have hcompletionTable := hcompletion.2.2.2 index
        have hsame : output = table index := hstarts index output hvalue
        rw [hsame]
        exact hcompletionTable
      · apply hcompletion.1 coordinate output
        simpa [materializeResolvedChainStart, LazyRevealProbe.State.materialize,
          Function.update_of_ne heq] using hvalue
    · intro position output hvalue
      apply hcompletion.2.1 position output
      simpa [materializeResolvedChainStart, hdeferredValues] using hvalue
    · intro coordinate candidate hmember
      apply hcompletion.2.2.1 coordinate candidate
      rw [hpending] at hmember
      simpa [materializeResolvedChainStart, LazyRevealProbe.State.materialize] using hmember
  · intro hcompletion
    refine ⟨?_, ?_, ?_, hcompletion.2.2.2⟩
    · intro coordinate output hvalue
      by_cases heq : coordinate = index.coordinate
      · subst coordinate
        have hsame : output = result.output := by
          change (context.state.materialize index.coordinate result.output).values
            index.coordinate = some output at hvalue
          exact (Option.some.inj (by
            simpa [LazyRevealProbe.State.materialize] using hvalue)).symm
        rw [hsame, houtput]
        exact hcompletion.2.2.2 index
      · apply hcompletion.1 coordinate output
        rw [hstateValues]
        change (context.state.materialize index.coordinate result.output).values coordinate =
          some output at hvalue
        simpa [LazyRevealProbe.State.materialize, Function.update_of_ne heq] using hvalue
    · intro position output hvalue
      apply hcompletion.2.1 position output
      simpa [materializeResolvedChainStart, hdeferredValues] using hvalue
    · intro coordinate candidate hmember
      apply hcompletion.2.2.1 coordinate candidate
      rw [hpending]
      change (coordinate, candidate) ∈
        (context.state.materialize index.coordinate result.output).pending at hmember
      simpa [LazyRevealProbe.State.materialize] using hmember

theorem deferredCompletion_materializeResolvedReveal_iff
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput} (position : Position)
    (result : DeferredResolution) (hvalid : context.Valid)
    (hstarts : StartTableAgrees context.state table)
    (hresult : some result ∈ support
      (resolveDeferredReveal table position context)) :
    DeferredCompletion table
        (materializeResolvedPosition context position result) completion ↔
      DeferredCompletion table result.toDeferredContext completion := by
  have hstateValues := resolveDeferredReveal_preserves_state_values table position context result
    hresult
  have hpending := resolveDeferredReveal_pendingAway_subset table position context result hresult
  have hresolved := resolveDeferredReveal_resolves table position context result hresult
  constructor
  · exact fun hcompletion => hcompletion.of_materializeResolvedPosition position result
      hstateValues hpending hresolved
  · intro hcompletion
    have hbase := hcompletion.of_resolveDeferredReveal hvalid.valuesConsistent hstarts position
      result hresult
    refine ⟨?_, hcompletion.2.1, ?_, hcompletion.2.2.2⟩
    · intro coordinate output hvalue
      by_cases heq : coordinate = .position position
      · subst coordinate
        change (context.state.materialize (.position position) result.output).values
          (.position position) = some output at hvalue
        have hsame : output = result.output := by
          exact (Option.some.inj (by
            simpa [LazyRevealProbe.State.materialize] using hvalue)).symm
        rw [hsame]
        exact hcompletion.eq_positionValue position result.output hresolved
      · apply hbase.1 coordinate output
        change (context.state.materialize (.position position) result.output).values
          coordinate = some output at hvalue
        simpa [LazyRevealProbe.State.materialize, Function.update_of_ne heq] using hvalue
    · intro coordinate candidate hmember
      apply hbase.2.2.1 coordinate candidate
      change (coordinate, candidate) ∈
        (context.state.materialize (.position position) result.output).pending at hmember
      have haway : (coordinate, candidate) ∈
          context.state.pendingAway (.position position) := by
        simpa [LazyRevealProbe.State.materialize] using hmember
      exact (Finset.mem_filter.1 haway).1

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

@[simp] theorem runDeferredLayerSchedule_none
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) :
    ∀ operations : List DeferredLayerOperation,
      runDeferredLayerSchedule parameter table ftsSecret index operations none = pure none
  | [] => rfl
  | _ :: operations => by
      simp [runDeferredLayerSchedule, runDeferredLayerOperation,
        runDeferredLayerSchedule_none parameter table ftsSecret index operations]

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

theorem runDeferredLayerSchedule_append
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (before after : List DeferredLayerOperation)
    (input : Option (ResolvedRunResult DeferredLayerStore)) :
    runDeferredLayerSchedule parameter table ftsSecret index (before ++ after) input =
      (runDeferredLayerSchedule parameter table ftsSecret index before input >>= fun result =>
        runDeferredLayerSchedule parameter table ftsSecret index after result) := by
  induction before generalizing input with
  | nil => simp [runDeferredLayerSchedule]
  | cons operation before ih =>
      simp only [List.cons_append, runDeferredLayerSchedule, bind_assoc]
      apply bind_congr
      intro result
      exact ih result

def chronologicalLayerSchedule : List DeferredLayerOperation :=
  [.select topLayer, .resolve topLayer,
    .select middleLayer, .resolve middleLayer,
    .select bottomLayer, .resolve bottomLayer]

def deferredLayerSchedule : List DeferredLayerOperation :=
  [.select topLayer, .select middleLayer, .select bottomLayer,
    .resolve topLayer, .resolve middleLayer, .resolve bottomLayer]

def deferredLayerSelections : List DeferredLayerOperation :=
  [topLayer, middleLayer, bottomLayer].map DeferredLayerOperation.select

def deferredLayerResolutions : List DeferredLayerOperation :=
  [topLayer, middleLayer, bottomLayer].map DeferredLayerOperation.resolve

theorem deferredLayerSchedule_eq_append :
    deferredLayerSchedule = deferredLayerSelections ++ deferredLayerResolutions := by
  simp [deferredLayerSchedule, deferredLayerSelections, deferredLayerResolutions]

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

theorem evalDist_chronologicalLayerSchedule_bind_eq_deferred
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (input : Option (ResolvedRunResult DeferredLayerStore))
    (next : Option (ResolvedRunResult DeferredLayerStore) → ProbComp α) :
    evalDist (runDeferredLayerSchedule parameter table ftsSecret index
        chronologicalLayerSchedule input >>= next) =
      evalDist (runDeferredLayerSchedule parameter table ftsSecret index
        deferredLayerSchedule input >>= next) := by
  rw [evalDist_bind, evalDist_bind,
    evalDist_chronologicalLayerSchedule_eq_deferred parameter table ftsSecret index input]

noncomputable def finalizeDeferredLayerSchedule
    (coordinates : List Coordinate) :
    Option (ResolvedRunResult DeferredLayerStore) →
      ProbComp (Option (LazyRevealProbe.State Coordinate))
  | none => pure none
  | some result => projectDeferredState <$>
      finalizeResolvedCoordinates coordinates result.context result.table

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredLayerSchedule_then_finalize
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (coordinates : List Coordinate) :
    ∀ (layers : List Layer) (result : ResolvedRunResult DeferredLayerStore),
      result.table = table → result.context.Valid →
      PendingCovered coordinates result.context →
      evalDist (runDeferredLayerSchedule parameter table ftsSecret index
          (layers.map DeferredLayerOperation.resolve) (some result) >>=
        finalizeDeferredLayerSchedule coordinates) =
      evalDist (projectDeferredState <$>
        finalizeResolvedCoordinates coordinates result.context result.table)
  | [], result, htable, hvalid, hcovered => by
      simp [runDeferredLayerSchedule, finalizeDeferredLayerSchedule]
  | lay :: layers, result, htable, hvalid, hcovered => by
      subst table
      simp only [List.map_cons, runDeferredLayerSchedule, runDeferredLayerOperation]
      rw [resolveDeferredLayer]
      cases hselected : result.value.selected lay with
      | none =>
          simp only [pure_bind]
          exact evalDist_resolveDeferredLayerSchedule_then_finalize parameter result.table ftsSecret
            index coordinates layers
            { result with
              value :=
                { result.value with
                  resolved := Function.update result.value.resolved lay none } }
            rfl hvalid hcovered
      | some selected =>
          rcases selected with ⟨counter, encoding⟩
          simp only [bind_assoc]
          calc
            _ = evalDist (resolveDeferredLayerValues result.table index lay encoding result.context >>=
                fun resolved =>
                  match resolved with
                  | none => pure none
                  | some (finalContext, _) => projectDeferredState <$>
                      finalizeResolvedCoordinates coordinates finalContext result.table) := by
              apply evalDist_bind_congr
              intro resolved hresolved
              cases resolved with
              | none =>
                  simp [finalizeDeferredLayerSchedule]
              | some resolved =>
                  rcases resolved with ⟨finalContext, values⟩
                  simp only [pure_bind]
                  have hfinalValid := hvalid.of_resolveDeferredLayerValues result.table index lay
                    encoding finalContext values hresolved
                  have hfinalCovered := hcovered.of_resolveDeferredLayerValues result.table index lay
                    encoding finalContext values hresolved
                  simpa only using
                    (evalDist_resolveDeferredLayerSchedule_then_finalize parameter result.table
                      ftsSecret index coordinates layers
                      { context := finalContext
                        remaining := result.remaining
                        value :=
                          { result.value with
                            resolved := Function.update result.value.resolved lay
                              (some (counter, values.1, values.2)) }
                        table := result.table }
                      rfl hfinalValid hfinalCovered)
            _ = _ := evalDist_map_resolveDeferredLayerValues_then_finalize result.table index lay
              encoding coordinates result.context hvalid hcovered

theorem valid_pendingCovered_of_mem_selectDeferredLayer
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay : Layer) (coordinates : List Coordinate)
    (result output : ResolvedRunResult DeferredLayerStore)
    (hvalid : result.context.Valid) (hcovered : PendingCovered coordinates result.context)
    (houtput : some output ∈ support
      (selectDeferredLayer parameter table ftsSecret index lay result)) :
    output.table = table ∧ output.context.Valid ∧
      PendingCovered coordinates output.context := by
  unfold selectDeferredLayer at houtput
  rw [mem_support_bind_iff] at houtput
  obtain ⟨selectedOption, hselected, hreturn⟩ := houtput
  cases selectedOption with
  | none => simp at hreturn
  | some selected =>
      simp only [support_pure, Set.mem_singleton_iff] at hreturn
      have houtputEq := Option.some.inj hreturn
      subst output
      have hinvariants := valid_pendingCovered_of_mem_runResolvedFromTable_of_probeFree
        ((maskedSignLayer parameter ftsSecret index lay).run result.value.cache)
        result.context result.remaining table selected coordinates
        (maskedSignLayer_probeFree parameter ftsSecret index lay result.value.cache)
        hvalid hcovered hselected
      exact ⟨rfl, hinvariants⟩

theorem valid_pendingCovered_of_mem_runDeferredLayerSelections
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (coordinates : List Coordinate) :
    ∀ (layers : List Layer) (result output : ResolvedRunResult DeferredLayerStore),
      result.table = table → result.context.Valid →
      PendingCovered coordinates result.context →
      some output ∈ support
        (runDeferredLayerSchedule parameter table ftsSecret index
          (layers.map DeferredLayerOperation.select) (some result)) →
      output.table = table ∧ output.context.Valid ∧
        PendingCovered coordinates output.context
  | [], result, output, htable, hvalid, hcovered, houtput => by
      simp [runDeferredLayerSchedule] at houtput
      subst output
      exact ⟨htable, hvalid, hcovered⟩
  | lay :: layers, result, output, htable, hvalid, hcovered, houtput => by
      simp only [List.map_cons, runDeferredLayerSchedule, runDeferredLayerOperation,
        mem_support_bind_iff] at houtput
      obtain ⟨selectedOption, hselected, htail⟩ := houtput
      cases selectedOption with
      | none => simp at htail
      | some selected =>
          have hinvariants := valid_pendingCovered_of_mem_selectDeferredLayer parameter table
            ftsSecret index lay coordinates result selected hvalid hcovered hselected
          exact valid_pendingCovered_of_mem_runDeferredLayerSelections parameter table ftsSecret
            index coordinates layers selected output hinvariants.1 hinvariants.2.1
            hinvariants.2.2 htail

set_option maxRecDepth 100000 in
theorem evalDist_selectThenResolveDeferredLayerSchedule_then_finalize
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (coordinates : List Coordinate) (layers : List Layer)
    (result : ResolvedRunResult DeferredLayerStore)
    (htable : result.table = table) (hvalid : result.context.Valid)
    (hcovered : PendingCovered coordinates result.context) :
    evalDist (runDeferredLayerSchedule parameter table ftsSecret index
        ((layers.map DeferredLayerOperation.select) ++
          layers.map DeferredLayerOperation.resolve) (some result) >>=
        finalizeDeferredLayerSchedule coordinates) =
      evalDist (runDeferredLayerSchedule parameter table ftsSecret index
        (layers.map DeferredLayerOperation.select) (some result) >>=
        finalizeDeferredLayerSchedule coordinates) := by
  rw [runDeferredLayerSchedule_append, bind_assoc]
  apply evalDist_bind_congr
  intro selectedOption hselected
  cases selectedOption with
  | none => simp [finalizeDeferredLayerSchedule]
  | some selected =>
      have hinvariants : selected.table = table ∧ selected.context.Valid ∧
          PendingCovered coordinates selected.context :=
        valid_pendingCovered_of_mem_runDeferredLayerSelections parameter table ftsSecret index
          coordinates layers result selected htable hvalid hcovered hselected
      exact evalDist_resolveDeferredLayerSchedule_then_finalize parameter table ftsSecret index
        coordinates layers selected hinvariants.1
        hinvariants.2.1 hinvariants.2.2

set_option maxRecDepth 100000 in
theorem evalDist_deferredLayerSchedule_then_finalize_eq_selections
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (coordinates : List Coordinate) (result : ResolvedRunResult DeferredLayerStore)
    (htable : result.table = table) (hvalid : result.context.Valid)
    (hcovered : PendingCovered coordinates result.context) :
    evalDist (runDeferredLayerSchedule parameter table ftsSecret index
        deferredLayerSchedule (some result) >>= finalizeDeferredLayerSchedule coordinates) =
      evalDist (runDeferredLayerSchedule parameter table ftsSecret index
        deferredLayerSelections (some result) >>= finalizeDeferredLayerSchedule coordinates) := by
  rw [deferredLayerSchedule_eq_append]
  exact evalDist_selectThenResolveDeferredLayerSchedule_then_finalize parameter table ftsSecret
    index coordinates [topLayer, middleLayer, bottomLayer] result htable hvalid hcovered

end SphincsSecurity.Concrete.OtsProbeSimulation
