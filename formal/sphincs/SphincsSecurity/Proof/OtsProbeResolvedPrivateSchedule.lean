import SphincsSecurity.Proof.OtsProbeResolvedPrivateSelection

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp

attribute [local irreducible] maskedSignLayer

def selectedChronologicalPartsOfStore (store : DeferredLayerStore) :
    Layer → Option ChronologicalLayerPart := fun lay =>
  match store.selected lay with
  | none => none
  | some (counter, encoding) =>
      some
        { counter := counter
          encoding := encoding
          chainValue := fun _ => 0
          authPath := fun _ => 0 }

noncomputable def publishSelectedChronologicalSignature
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (selected : Layer → Option DeferredLayerEncoding) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Signature) :=
  match traverseOption selected with
  | none => pure none
  | some parts => do
      let published ← sequenceFin fun lay =>
        revealLayerValues index lay (parts lay).2
      pure (some
        { randomness := randomness
          ftsSecret := fun tree => ftsSecret index tree (leaves (ftsIndexOf tree))
          ftsPath := ftsPath
          counter := fun lay => (parts lay).1
          chainValue := fun lay => (published lay).1
          authPath := flattenPaths fun lay => (published lay).2 })

theorem publishChronologicalSignature_eq_selected
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (layers : Layer → Option ChronologicalLayerPart) :
    publishChronologicalSignature ftsSecret randomness index leaves ftsPath layers =
      publishSelectedChronologicalSignature ftsSecret randomness index leaves ftsPath
        (fun lay => (layers lay).map fun part => (part.counter, part.encoding)) := by
  unfold publishChronologicalSignature publishSelectedChronologicalSignature
  rw [traverseOption_map]
  cases hparts : traverseOption layers with
  | none => rfl
  | some parts => rfl

def ResolutionPresenceAgrees (store : DeferredLayerStore) : Prop :=
  ∀ lay, (store.resolved lay).isSome = (store.selected lay).isSome

theorem chronologicalPartsOfStore_selection_eq
    (store : DeferredLayerStore) (hagrees : ResolutionPresenceAgrees store) :
    (fun lay => (chronologicalPartsOfStore store lay).map fun part =>
      (part.counter, part.encoding)) = store.selected := by
  funext lay
  unfold chronologicalPartsOfStore
  cases hselected : store.selected lay with
  | none => simp
  | some selected =>
      cases hresolved : store.resolved lay with
      | none =>
          have := hagrees lay
          simp [hselected, hresolved] at this
      | some resolved =>
          rcases selected with ⟨counter, encoding⟩
          rcases resolved with ⟨resolvedCounter, chainValue, authPath⟩
          simp

theorem publishChronologicalSignature_store_eq_selected
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (store : DeferredLayerStore) (hagrees : ResolutionPresenceAgrees store) :
    publishChronologicalSignature ftsSecret randomness index leaves ftsPath
        (chronologicalPartsOfStore store) =
      publishSelectedChronologicalSignature ftsSecret randomness index leaves ftsPath
        store.selected := by
  rw [publishChronologicalSignature_eq_selected,
    chronologicalPartsOfStore_selection_eq store hagrees]

noncomputable def publishSelectedDeferredSignature
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) :
    Option (ResolvedRunResult DeferredLayerStore) →
      ProbComp (Option (ResolvedRunResult (Option Signature × SplitHashCache)))
  | none => pure none
  | some result =>
      runResolvedFromTable result.context result.remaining result.table
        ((publishSelectedChronologicalSignature ftsSecret randomness index leaves ftsPath
          result.value.selected).run result.value.cache)

theorem publishDeferredChronologicalSignature_eq_selected
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (result : ResolvedRunResult DeferredLayerStore)
    (hagrees : ResolutionPresenceAgrees result.value) :
    publishDeferredChronologicalSignature ftsSecret randomness index leaves ftsPath
        (some result) =
      publishSelectedDeferredSignature ftsSecret randomness index leaves ftsPath
        (some result) := by
  unfold publishDeferredChronologicalSignature publishSelectedDeferredSignature
  simp only
  rw [publishChronologicalSignature_store_eq_selected ftsSecret randomness index leaves
    ftsPath result.value hagrees]

theorem valid_completable_of_mem_runResolvedFromTable_of_finalizationMaterializedCouples
    (table : OtsSecretIndex → HashOutput)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcouples : FinalizationMaterializedCouples table computation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (result : ResolvedRunResult (α × SplitHashCache))
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table (computation.run cache))) :
    result.context.Valid ∧ DeferredCompletable table result.context := by
  have hstarts := startTableAgrees_of_deferredCompletable hcompletable
  have hview := finalizationViewEq_of_deferredCompletion_iff hvalid hvalid hstarts hstarts
    rfl hcompletable (fun _ => Iff.rfl)
  have hrelation := hcouples context context fuel cache cache
    ⟨hview, hvalid, hvalid, hcompletable⟩ rfl rfl
  obtain ⟨rightResult, _hright, hresultRelation⟩ :=
    exists_right_of_relTriple_of_mem_support hrelation hresult
  cases rightResult with
  | none => simp [FinalizationMaterializedRunEq] at hresultRelation
  | some rightResult =>
      rcases hresultRelation with
        ⟨_value, hcontexts, _fuel, _leftTable, _rightTable, _cache, _revealed⟩
      exact ⟨hcontexts.2.1, hcontexts.2.2.2⟩

theorem LayerValuesEnsured.of_privateStateAgrees
    {index : Index} {lay : Layer} {encoding : ChainIndex → Digit}
    {left right : DeferredContext}
    (hensured : LayerValuesEnsured index lay encoding right)
    (hagrees : PrivateStateAgrees left right) :
    LayerValuesEnsured index lay encoding left := by
  rcases hagrees with ⟨_values, _revealed, hstateEnsured⟩
  constructor
  · simpa [hstateEnsured] using hensured.1
  · intro level hlevel
    apply (treeNodeEnsured_congr_ensured lay (treeIndexAt index lay) level.val
      (Nat.xor ((leafIndexAt index lay).val / 2 ^ level.val) 1)
        right left hstateEnsured.symm).mp
    exact hensured.2 level hlevel

theorem LayerValuesEnsured.mono
    {index : Index} {lay : Layer} {encoding : ChainIndex → Digit}
    {left right : DeferredContext}
    (hensured : LayerValuesEnsured index lay encoding left)
    (hle : LazyRevealProbe.EnsuredLE left.state right.state) :
    LayerValuesEnsured index lay encoding right := by
  refine ⟨fun chainIdx step hstep => hle (hensured.1 chainIdx step hstep), ?_⟩
  intro level hlevel
  exact (hensured.2 level hlevel).mono hle

theorem DeferredCompletable.of_resolveDeferredLayerValues
    {table : OtsSecretIndex → HashOutput} {index : Index} {lay : Layer}
    {encoding : ChainIndex → Digit} {context finalContext : DeferredContext}
    {values : (ChainIndex → Digest) × (Fin maxLayerHeight → Digest)}
    (hcompletable : DeferredCompletable table context) (hvalid : context.Valid)
    (hresult : some (finalContext, values) ∈ support
      (resolveDeferredLayerValues table index lay encoding context)) :
    DeferredCompletable table finalContext := by
  rw [resolveDeferredLayerValues, mem_support_bind_iff] at hresult
  obtain ⟨chainsOption, hchains, hrest⟩ := hresult
  cases chainsOption with
  | none => simp at hrest
  | some chains =>
      rcases chains with ⟨afterChains, chainValues⟩
      rw [mem_support_bind_iff] at hrest
      obtain ⟨pathOption, hpath, hreturn⟩ := hrest
      cases pathOption with
      | none => simp at hreturn
      | some path =>
          rcases path with ⟨afterPath, pathValues⟩
          simp only [support_pure, Set.mem_singleton_iff] at hreturn
          have hreturn' : finalContext = afterPath := by
            exact congrArg (fun result => result.1) (Option.some.inj hreturn)
          rw [hreturn']
          have hchainsCompletable :=
            hcompletable.of_resolveDeferredSelectedChainFamily hvalid
              (fun chainIdx : ChainIndex => chainIdx) encoding afterChains chainValues hchains
          have hchainsValid := hvalid.of_resolveDeferredSelectedChainFamily table lay
            (treeIndexAt index lay) (leafIndexAt index lay)
              (fun chainIdx : ChainIndex => chainIdx) encoding afterChains chainValues hchains
          exact hchainsCompletable.of_resolveDeferredLayerPathFamily hchainsValid
            (fun level : Fin maxLayerHeight => level) afterPath pathValues hpath

noncomputable def resolveSelectedLayerValuesList
    (table : OtsSecretIndex → HashOutput) (index : Index)
    (selected : Layer → Option DeferredLayerEncoding) :
    List Layer → DeferredContext → ProbComp (Option DeferredContext)
  | [], context => pure (some context)
  | lay :: layers, context =>
      match selected lay with
      | none => resolveSelectedLayerValuesList table index selected layers context
      | some (_, encoding) => do
          let resolved ← resolveDeferredLayerValues table index lay encoding context
          match resolved with
          | none => pure none
          | some (afterLayer, _) =>
              resolveSelectedLayerValuesList table index selected layers afterLayer

theorem evalDist_resolveSelectedLayerValuesList_then_runResolvedFinishIsNone
    (table : OtsSecretIndex → HashOutput) (index : Index)
    (selected : Layer → Option DeferredLayerEncoding)
    (fuel : Nat) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    ∀ (layers : List Layer) (context : DeferredContext),
      context.Valid → DeferredCompletable table context →
      (∀ lay, lay ∈ layers → ∀ counter encoding,
        selected lay = some (counter, encoding) →
          LayerValuesEnsured index lay encoding context) →
      evalDist (do
        let resolved ← resolveSelectedLayerValuesList table index selected layers context
        match resolved with
        | none => pure true
        | some finalContext =>
            runResolvedFinishIsNone finalContext fuel table computation) =
        evalDist (runResolvedFinishIsNone context fuel table computation)
  | [], context, hvalid, hcompletable, hensured => by
      simp [resolveSelectedLayerValuesList]
  | lay :: layers, context, hvalid, hcompletable, hensured => by
      rw [resolveSelectedLayerValuesList]
      cases hselection : selected lay with
      | none =>
          exact evalDist_resolveSelectedLayerValuesList_then_runResolvedFinishIsNone table index
            selected fuel computation layers context hvalid hcompletable
              (fun other hother counter encoding hselected =>
                hensured other (List.mem_cons_of_mem lay hother) counter encoding hselected)
      | some selection =>
          rcases selection with ⟨counter, encoding⟩
          simp only [bind_assoc]
          calc
            _ = evalDist (resolveDeferredLayerValues table index lay encoding context >>= fun
                resolved =>
                  match resolved with
                  | none => pure true
                  | some (afterLayer, _) =>
                      runResolvedFinishIsNone afterLayer fuel table computation) := by
                apply evalDist_bind_congr
                intro resolved hresolved
                cases resolved with
                | none => rfl
                | some resolved =>
                    rcases resolved with ⟨afterLayer, values⟩
                    have hafterValid := hvalid.of_resolveDeferredLayerValues table index lay
                      encoding afterLayer values hresolved
                    have hafterCompletable := hcompletable.of_resolveDeferredLayerValues hvalid
                      hresolved
                    have hagrees := privateStateAgrees_resolveDeferredLayerValues table index lay
                      encoding context afterLayer values hresolved
                    exact evalDist_resolveSelectedLayerValuesList_then_runResolvedFinishIsNone
                      table index selected fuel computation layers afterLayer hafterValid
                        hafterCompletable
                        (fun other hother otherCounter otherEncoding hselected =>
                          (hensured other (List.mem_cons_of_mem lay hother) otherCounter
                            otherEncoding hselected).of_privateStateAgrees hagrees)
            _ = _ :=
              evalDist_resolveDeferredLayerValues_then_runResolvedFinishIsNone table index lay
                encoding context fuel computation hvalid hcompletable
                  (hensured lay (by simp) counter encoding hselection)

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredLayerSchedule_publish_finish_eq_selectedList
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput) (index : Index)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) :
    ∀ (layers : List Layer) (result : ResolvedRunResult DeferredLayerStore),
      result.table = table →
      (∀ lay, lay ∉ layers →
        (result.value.resolved lay).isSome =
          (result.value.selected lay).isSome) →
      evalDist (runDeferredLayerSchedule parameter table ftsSecret index
          (layers.map DeferredLayerOperation.resolve) (some result) >>=
        publishDeferredChronologicalSignature ftsSecret randomness index leaves ftsPath >>=
        finishResolvedRunIsNone) =
      evalDist (do
        let resolved ← resolveSelectedLayerValuesList table index
          result.value.selected layers result.context
        match resolved with
        | none => pure true
        | some finalContext =>
            runResolvedFinishIsNone finalContext result.remaining table
              ((publishSelectedChronologicalSignature ftsSecret randomness index leaves
                ftsPath result.value.selected).run result.value.cache))
  | [], result, htable, hagrees => by
      have hpresence : ResolutionPresenceAgrees result.value := by
        intro lay
        exact hagrees lay (by simp)
      simp only [List.map_nil, runDeferredLayerSchedule, pure_bind,
        resolveSelectedLayerValuesList]
      rw [publishDeferredChronologicalSignature_eq_selected ftsSecret randomness index leaves
        ftsPath result hpresence]
      simp only [publishSelectedDeferredSignature]
      unfold runResolvedFinishIsNone
      rw [htable]
  | lay :: layers, result, htable, hagrees => by
      simp only [List.map_cons, runDeferredLayerSchedule, runDeferredLayerOperation]
      rw [resolveDeferredLayer]
      cases hselection : result.value.selected lay with
      | none =>
          simp only [pure_bind, resolveSelectedLayerValuesList, hselection]
          have hrecursive :=
            evalDist_resolveDeferredLayerSchedule_publish_finish_eq_selectedList parameter
              table index ftsSecret randomness leaves ftsPath layers
              { context := result.context
                remaining := result.remaining
                value :=
                  { result.value with
                    resolved := Function.update result.value.resolved lay none }
                table := table }
                rfl (by
                  intro observed hnotMem
                  by_cases heq : observed = lay
                  · subst observed
                    simp [Function.update, hselection]
                  · simpa [Function.update, heq] using
                      hagrees observed (by simp [heq, hnotMem]))
          simpa only [bind_assoc] using hrecursive
      | some selection =>
          rcases selection with ⟨counter, encoding⟩
          simp only [bind_assoc, resolveSelectedLayerValuesList, hselection]
          apply evalDist_bind_congr
          intro resolvedOption hresolved
          cases resolvedOption with
          | none =>
              simp [publishDeferredChronologicalSignature, finishResolvedRunIsNone,
                finishResolvedRun]
          | some resolved =>
              rcases resolved with ⟨afterLayer, values⟩
              simpa only [pure_bind, bind_assoc] using
                (evalDist_resolveDeferredLayerSchedule_publish_finish_eq_selectedList parameter
                  table index ftsSecret randomness leaves ftsPath layers
                    { context := afterLayer
                      remaining := result.remaining
                      value :=
                        { result.value with
                          resolved := Function.update result.value.resolved lay
                            (some (counter, values.1, values.2)) }
                      table := table }
                    rfl (by
                      intro observed hnotMem
                      by_cases heq : observed = lay
                      · subst observed
                        simp [Function.update, hselection]
                      · simpa [Function.update, heq] using
                          hagrees observed (by simp [heq, hnotMem])))

theorem ensuredLE_of_mem_selectDeferredLayer
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay : Layer) (input output : ResolvedRunResult DeferredLayerStore)
    (houtput : some output ∈ support
      (selectDeferredLayer parameter table ftsSecret index lay input)) :
    LazyRevealProbe.EnsuredLE input.context.state output.context.state := by
  unfold selectDeferredLayer at houtput
  rw [mem_support_bind_iff] at houtput
  obtain ⟨selectedOption, hselected, hreturn⟩ := houtput
  cases selectedOption with
  | none => simp at hreturn
  | some selected =>
      simp only [support_pure, Set.mem_singleton_iff] at hreturn
      have houtputEq := Option.some.inj hreturn
      subst output
      exact ensuredLE_of_mem_runResolvedFromTable
        ((maskedSignLayer parameter ftsSecret index lay).run input.value.cache)
          input.context input.remaining table selected hselected

theorem selected_eq_of_mem_selectDeferredLayer_of_ne
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay observed : Layer) (hne : observed ≠ lay)
    (input output : ResolvedRunResult DeferredLayerStore)
    (houtput : some output ∈ support
      (selectDeferredLayer parameter table ftsSecret index lay input)) :
    output.value.selected observed = input.value.selected observed := by
  unfold selectDeferredLayer at houtput
  rw [mem_support_bind_iff] at houtput
  obtain ⟨selectedOption, _hselected, hreturn⟩ := houtput
  cases selectedOption with
  | none => simp at hreturn
  | some selected =>
      simp only [support_pure, Set.mem_singleton_iff] at hreturn
      have houtputEq := Option.some.inj hreturn
      subst output
      simp [Function.update, hne]

set_option maxHeartbeats 800000 in
theorem selectedLayersEnsured_of_mem_deferredLayerSelections
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (output : ResolvedRunResult DeferredLayerStore)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (houtput : some output ∈ support
      (runDeferredLayerSchedule parameter table ftsSecret index deferredLayerSelections
        (some ⟨context, fuel, emptyDeferredLayerStore cache, table⟩))) :
    output.table = table ∧ output.context.Valid ∧
      DeferredCompletable table output.context ∧
      ∀ lay counter encoding,
        output.value.selected lay = some (counter, encoding) →
          LayerValuesEnsured index lay encoding output.context := by
  simp only [deferredLayerSelections, List.map_cons, List.map_nil,
    runDeferredLayerSchedule, runDeferredLayerOperation, mem_support_bind_iff] at houtput
  obtain ⟨topOption, htop, hafterTop⟩ := houtput
  cases topOption with
  | none => simp at hafterTop
  | some topResult =>
      obtain ⟨middleOption, hmiddle, hafterMiddle⟩ := hafterTop
      cases middleOption with
      | none => simp at hafterMiddle
      | some middleResult =>
          obtain ⟨bottomOption, hbottom, hreturn⟩ := hafterMiddle
          cases bottomOption with
          | none => simp at hreturn
          | some bottomResult =>
              simp only [support_pure, Set.mem_singleton_iff] at hreturn
              have houtputEq := Option.some.inj hreturn
              rw [houtputEq]
              have htopInv := valid_pendingCovered_of_mem_selectDeferredLayer parameter table
                ftsSecret index topLayer context.state.coordinates.toList
                  ⟨context, fuel, emptyDeferredLayerStore cache, table⟩ topResult hvalid
                    (pendingCovered_coordinates_toList context) htop
              have htopCompletable := deferredCompletable_of_mem_selectDeferredLayer parameter
                table ftsSecret index topLayer
                  ⟨context, fuel, emptyDeferredLayerStore cache, table⟩ topResult hvalid
                    hcompletable htop
              have hmiddleInv := valid_pendingCovered_of_mem_selectDeferredLayer parameter table
                ftsSecret index middleLayer context.state.coordinates.toList topResult
                  middleResult htopInv.2.1 htopInv.2.2 hmiddle
              have hmiddleCompletable := deferredCompletable_of_mem_selectDeferredLayer parameter
                table ftsSecret index middleLayer topResult middleResult htopInv.2.1
                  htopCompletable hmiddle
              have hbottomInv := valid_pendingCovered_of_mem_selectDeferredLayer parameter table
                ftsSecret index bottomLayer context.state.coordinates.toList middleResult
                  bottomResult hmiddleInv.2.1 hmiddleInv.2.2 hbottom
              have hbottomCompletable := deferredCompletable_of_mem_selectDeferredLayer parameter
                table ftsSecret index bottomLayer middleResult bottomResult hmiddleInv.2.1
                  hmiddleCompletable hbottom
              refine ⟨hbottomInv.1, hbottomInv.2.1, hbottomCompletable, ?_⟩
              intro lay counter encoding hselected
              fin_cases lay
              · have htopSelected : topResult.value.selected topLayer =
                    some (counter, encoding) := by
                  rw [← selected_eq_of_mem_selectDeferredLayer_of_ne parameter table ftsSecret
                    index middleLayer topLayer (by decide) topResult middleResult hmiddle,
                    ← selected_eq_of_mem_selectDeferredLayer_of_ne parameter table ftsSecret
                      index bottomLayer topLayer (by decide) middleResult bottomResult hbottom]
                  exact hselected
                have htopEnsured := selectedLayerValuesEnsured_of_mem_selectDeferredLayer
                  parameter table ftsSecret index topLayer
                    ⟨context, fuel, emptyDeferredLayerStore cache, table⟩ topResult
                      counter encoding htop htopSelected
                exact (htopEnsured.mono
                  (ensuredLE_of_mem_selectDeferredLayer parameter table ftsSecret index
                    middleLayer topResult middleResult hmiddle)).mono
                      (ensuredLE_of_mem_selectDeferredLayer parameter table ftsSecret index
                        bottomLayer middleResult bottomResult hbottom)
              · have hmiddleSelected : middleResult.value.selected middleLayer =
                    some (counter, encoding) := by
                  rw [← selected_eq_of_mem_selectDeferredLayer_of_ne parameter table ftsSecret
                    index bottomLayer middleLayer (by decide) middleResult bottomResult hbottom]
                  exact hselected
                have hmiddleEnsured := selectedLayerValuesEnsured_of_mem_selectDeferredLayer
                  parameter table ftsSecret index middleLayer topResult middleResult
                    counter encoding hmiddle hmiddleSelected
                exact hmiddleEnsured.mono
                  (ensuredLE_of_mem_selectDeferredLayer parameter table ftsSecret index
                    bottomLayer middleResult bottomResult hbottom)
              · have hbottomSelected : bottomResult.value.selected bottomLayer =
                    some (counter, encoding) := by
                  simpa [bottomLayer, numLayers] using hselected
                exact selectedLayerValuesEnsured_of_mem_selectDeferredLayer
                  parameter table ftsSecret index bottomLayer middleResult bottomResult
                    counter encoding hbottom hbottomSelected

noncomputable def runSelectionOnlyLayersAndPublish
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    ProbComp (Option (ResolvedRunResult (Option Signature × SplitHashCache))) :=
  runDeferredLayerSchedule parameter table ftsSecret index deferredLayerSelections
      (some ⟨context, fuel, emptyDeferredLayerStore cache, table⟩) >>=
    publishSelectedDeferredSignature ftsSecret randomness index leaves ftsPath

set_option maxRecDepth 100000 in
theorem evalDist_runDeferredLayersAndPublish_finish_eq_selectionOnly
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    evalDist (runDeferredLayersAndPublish parameter table ftsSecret randomness index leaves
        ftsPath deferredLayerSchedule context fuel cache >>= finishResolvedRunIsNone) =
      evalDist (runSelectionOnlyLayersAndPublish parameter table ftsSecret randomness index
        leaves ftsPath context fuel cache >>= finishResolvedRunIsNone) := by
  unfold runDeferredLayersAndPublish runSelectionOnlyLayersAndPublish
  rw [deferredLayerSchedule_eq_append, runDeferredLayerSchedule_append]
  simp only [bind_assoc]
  apply evalDist_bind_congr
  intro selectedOption hselected
  cases selectedOption with
  | none =>
      simp [publishDeferredChronologicalSignature, publishSelectedDeferredSignature,
        finishResolvedRunIsNone, finishResolvedRun]
  | some selected =>
      have hinvariants := selectedLayersEnsured_of_mem_deferredLayerSelections parameter table
        ftsSecret index context fuel cache selected hvalid hcompletable hselected
      have hschedule :=
        evalDist_resolveDeferredLayerSchedule_publish_finish_eq_selectedList parameter table
          index ftsSecret randomness leaves ftsPath [topLayer, middleLayer, bottomLayer]
            selected hinvariants.1 (by
              intro lay hnotMem
              fin_cases lay <;>
                simp [topLayer, middleLayer, bottomLayer, numLayers] at hnotMem)
      simp only [deferredLayerResolutions, publishSelectedDeferredSignature]
      rw [← bind_assoc]
      rw [hschedule]
      rw [hinvariants.1]
      exact evalDist_resolveSelectedLayerValuesList_then_runResolvedFinishIsNone table index
        selected.value.selected selected.remaining
          ((publishSelectedChronologicalSignature ftsSecret randomness index leaves ftsPath
            selected.value.selected).run selected.value.cache)
          [topLayer, middleLayer, bottomLayer] selected.context hinvariants.2.1
            hinvariants.2.2.1 (by
              intro lay hlay counter encoding hselection
              exact hinvariants.2.2.2 lay counter encoding hselection)

noncomputable def runSelectionOnlySignAfterDigest
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    ProbComp (Option (ResolvedRunResult (Option Signature × SplitHashCache))) := do
  let ftsPath ← runResolvedFromTable context fuel table
    ((simulateQ ordinaryHashImpl
      (ftsOpen parameter index leaves (ftsSecret index))).run cache)
  match ftsPath with
  | none => pure none
  | some ftsPath =>
      runSelectionOnlyLayersAndPublish parameter table ftsSecret randomness index leaves
        ftsPath.value.1 ftsPath.context ftsPath.remaining ftsPath.value.2

set_option maxRecDepth 100000 in
theorem evalDist_runDeferredChronologicalSignAfterDigest_finish_eq_selectionOnly
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    evalDist (runDeferredChronologicalSignAfterDigest parameter table ftsSecret randomness
        index leaves context fuel cache >>= finishResolvedRunIsNone) =
      evalDist (runSelectionOnlySignAfterDigest parameter table ftsSecret randomness index
        leaves context fuel cache >>= finishResolvedRunIsNone) := by
  unfold runDeferredChronologicalSignAfterDigest runSelectionOnlySignAfterDigest
  simp only [bind_assoc]
  apply evalDist_bind_congr
  intro ftsOption hfts
  cases ftsOption with
  | none => simp [finishResolvedRunIsNone, finishResolvedRun]
  | some ftsResult =>
      have hftsInvariants :=
        valid_completable_of_mem_runResolvedFromTable_of_finalizationMaterializedCouples table
          (simulateQ ordinaryHashImpl
            (ftsOpen parameter index leaves (ftsSecret index)))
          (finalizationMaterializedCouples_simulateQ ordinaryHashImpl
            (finalizationMaterializedCouples_ordinaryHashImpl table)
            (ftsOpen parameter index leaves (ftsSecret index)))
          context fuel cache ftsResult hvalid hcompletable hfts
      calc
        _ = evalDist (runDeferredLayersAndPublish parameter table ftsSecret randomness index
              leaves ftsResult.value.1 deferredLayerSchedule ftsResult.context
                ftsResult.remaining ftsResult.value.2 >>= finishResolvedRunIsNone) :=
          evalDist_runDeferredChronologicalLayersAndPublish_finish_eq_deferred parameter table
            ftsSecret randomness index leaves ftsResult.value.1 ftsResult.context
              ftsResult.remaining ftsResult.value.2
        _ = _ := evalDist_runDeferredLayersAndPublish_finish_eq_selectionOnly parameter table
          ftsSecret randomness index leaves ftsResult.value.1 ftsResult.context
            ftsResult.remaining ftsResult.value.2 hftsInvariants.1 hftsInvariants.2

noncomputable def continueResolvedRunIsNone
    (next : σ → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) :
    Option (ResolvedRunResult (σ × SplitHashCache)) → ProbComp Bool
  | none => pure true
  | some result =>
      runResolvedFinishIsNone result.context result.remaining result.table
        ((next result.value.1).run result.value.2)

theorem evalDist_runResolvedFromTable_then_continue
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) σ)
    (next : σ → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) :
    evalDist (runResolvedFromTable context fuel table (computation.run cache) >>=
        continueResolvedRunIsNone next) =
      evalDist (runResolvedFinishIsNone context fuel table
        ((computation >>= next).run cache)) := by
  unfold runResolvedFinishIsNone
  rw [StateT.run_bind, runResolvedFromTable_bind, bind_assoc]
  apply evalDist_bind_congr
  intro resultOption _hresult
  cases resultOption with
  | none => simp [continueResolvedRunIsNone, finishResolvedRunIsNone, finishResolvedRun]
  | some result => rfl

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredLayerSchedule_continue_eq_selectedList
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput) (index : Index)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (next : Option Signature → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) :
    ∀ (layers : List Layer) (result : ResolvedRunResult DeferredLayerStore),
      result.table = table →
      (∀ lay, lay ∉ layers →
        (result.value.resolved lay).isSome =
          (result.value.selected lay).isSome) →
      evalDist (runDeferredLayerSchedule parameter table ftsSecret index
          (layers.map DeferredLayerOperation.resolve) (some result) >>=
        publishDeferredChronologicalSignature ftsSecret randomness index leaves ftsPath >>=
        continueResolvedRunIsNone next) =
      evalDist (do
        let resolved ← resolveSelectedLayerValuesList table index
          result.value.selected layers result.context
        match resolved with
        | none => pure true
        | some finalContext =>
            runResolvedFinishIsNone finalContext result.remaining table
              ((publishSelectedChronologicalSignature ftsSecret randomness index leaves
                ftsPath result.value.selected >>= next).run result.value.cache))
  | [], result, htable, hagrees => by
      have hpresence : ResolutionPresenceAgrees result.value := by
        intro lay
        exact hagrees lay (by simp)
      simp only [List.map_nil, runDeferredLayerSchedule, pure_bind,
        resolveSelectedLayerValuesList]
      rw [publishDeferredChronologicalSignature_eq_selected ftsSecret randomness index leaves
        ftsPath result hpresence]
      simp only [publishSelectedDeferredSignature]
      rw [htable]
      exact evalDist_runResolvedFromTable_then_continue result.context result.remaining table
        result.value.cache
          (publishSelectedChronologicalSignature ftsSecret randomness index leaves ftsPath
            result.value.selected) next
  | lay :: layers, result, htable, hagrees => by
      simp only [List.map_cons, runDeferredLayerSchedule, runDeferredLayerOperation]
      rw [resolveDeferredLayer]
      cases hselection : result.value.selected lay with
      | none =>
          simp only [pure_bind, resolveSelectedLayerValuesList, hselection]
          have hrecursive :=
            evalDist_resolveDeferredLayerSchedule_continue_eq_selectedList parameter table index
              ftsSecret randomness leaves ftsPath next layers
              { context := result.context
                remaining := result.remaining
                value :=
                  { result.value with
                    resolved := Function.update result.value.resolved lay none }
                table := table }
                rfl (by
                  intro observed hnotMem
                  by_cases heq : observed = lay
                  · subst observed
                    simp [Function.update, hselection]
                  · simpa [Function.update, heq] using
                      hagrees observed (by simp [heq, hnotMem]))
          simpa only [bind_assoc] using hrecursive
      | some selection =>
          rcases selection with ⟨counter, encoding⟩
          simp only [bind_assoc, resolveSelectedLayerValuesList, hselection]
          apply evalDist_bind_congr
          intro resolvedOption hresolved
          cases resolvedOption with
          | none =>
              simp [publishDeferredChronologicalSignature, continueResolvedRunIsNone,
                runResolvedFinishIsNone]
          | some resolved =>
              rcases resolved with ⟨afterLayer, values⟩
              simpa only [pure_bind, bind_assoc] using
                (evalDist_resolveDeferredLayerSchedule_continue_eq_selectedList parameter table
                  index ftsSecret randomness leaves ftsPath next layers
                    { context := afterLayer
                      remaining := result.remaining
                      value :=
                        { result.value with
                          resolved := Function.update result.value.resolved lay
                            (some (counter, values.1, values.2)) }
                      table := table }
                    rfl (by
                      intro observed hnotMem
                      by_cases heq : observed = lay
                      · subst observed
                        simp [Function.update, hselection]
                      · simpa [Function.update, heq] using
                          hagrees observed (by simp [heq, hnotMem])))

set_option maxRecDepth 100000 in
theorem evalDist_runDeferredLayersAndPublish_continue_eq_selectionOnly
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (next : Option Signature → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    evalDist (runDeferredLayersAndPublish parameter table ftsSecret randomness index leaves
        ftsPath deferredLayerSchedule context fuel cache >>=
          continueResolvedRunIsNone next) =
      evalDist (runSelectionOnlyLayersAndPublish parameter table ftsSecret randomness index
        leaves ftsPath context fuel cache >>= continueResolvedRunIsNone next) := by
  unfold runDeferredLayersAndPublish runSelectionOnlyLayersAndPublish
  rw [deferredLayerSchedule_eq_append, runDeferredLayerSchedule_append]
  simp only [bind_assoc]
  apply evalDist_bind_congr
  intro selectedOption hselected
  cases selectedOption with
  | none =>
      rw [runDeferredLayerSchedule_none]
      simp only [pure_bind]
      rw [publishDeferredChronologicalSignature.eq_def, publishSelectedDeferredSignature]
  | some selected =>
      have hinvariants := selectedLayersEnsured_of_mem_deferredLayerSelections parameter table
        ftsSecret index context fuel cache selected hvalid hcompletable hselected
      have hschedule :=
        evalDist_resolveDeferredLayerSchedule_continue_eq_selectedList parameter table index
          ftsSecret randomness leaves ftsPath next [topLayer, middleLayer, bottomLayer]
            selected hinvariants.1 (by
              intro lay hnotMem
              fin_cases lay <;>
                simp [topLayer, middleLayer, bottomLayer, numLayers] at hnotMem)
      simp only [deferredLayerResolutions]
      rw [← bind_assoc, hschedule]
      simp only [publishSelectedDeferredSignature]
      rw [evalDist_runResolvedFromTable_then_continue selected.context selected.remaining
        selected.table selected.value.cache
          (publishSelectedChronologicalSignature ftsSecret randomness index leaves ftsPath
            selected.value.selected) next, hinvariants.1]
      exact evalDist_resolveSelectedLayerValuesList_then_runResolvedFinishIsNone table index
        selected.value.selected selected.remaining
          ((publishSelectedChronologicalSignature ftsSecret randomness index leaves ftsPath
            selected.value.selected >>= next).run selected.value.cache)
          [topLayer, middleLayer, bottomLayer] selected.context hinvariants.2.1
            hinvariants.2.2.1 (by
              intro lay hlay counter encoding hselection
              exact hinvariants.2.2.2 lay counter encoding hselection)

theorem evalDist_runDeferredChronologicalLayersAndPublish_continue_eq_selectionOnly
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (next : Option Signature → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    evalDist (runDeferredChronologicalLayersAndPublish parameter table ftsSecret randomness
        index leaves ftsPath context fuel cache >>= continueResolvedRunIsNone next) =
      evalDist (runSelectionOnlyLayersAndPublish parameter table ftsSecret randomness index
        leaves ftsPath context fuel cache >>= continueResolvedRunIsNone next) := by
  calc
    _ = evalDist (runDeferredLayersAndPublish parameter table ftsSecret randomness index leaves
          ftsPath deferredLayerSchedule context fuel cache >>=
            continueResolvedRunIsNone next) := by
      rw [evalDist_bind, evalDist_bind,
        evalDist_runDeferredChronologicalLayersAndPublish_eq_deferred parameter table ftsSecret
          randomness index leaves ftsPath context fuel cache]
    _ = _ := evalDist_runDeferredLayersAndPublish_continue_eq_selectionOnly parameter table
      ftsSecret randomness index leaves ftsPath context fuel cache next hvalid hcompletable

set_option maxRecDepth 100000 in
theorem evalDist_runDeferredChronologicalSignAfterDigest_continue_eq_selectionOnly
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (next : Option Signature → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    evalDist (runDeferredChronologicalSignAfterDigest parameter table ftsSecret randomness
        index leaves context fuel cache >>= continueResolvedRunIsNone next) =
      evalDist (runSelectionOnlySignAfterDigest parameter table ftsSecret randomness index
        leaves context fuel cache >>= continueResolvedRunIsNone next) := by
  unfold runDeferredChronologicalSignAfterDigest runSelectionOnlySignAfterDigest
  simp only [bind_assoc]
  apply evalDist_bind_congr
  intro ftsOption hfts
  cases ftsOption with
  | none => simp [continueResolvedRunIsNone]
  | some ftsResult =>
      have hftsInvariants :=
        valid_completable_of_mem_runResolvedFromTable_of_finalizationMaterializedCouples table
          (simulateQ ordinaryHashImpl
            (ftsOpen parameter index leaves (ftsSecret index)))
          (finalizationMaterializedCouples_simulateQ ordinaryHashImpl
            (finalizationMaterializedCouples_ordinaryHashImpl table)
            (ftsOpen parameter index leaves (ftsSecret index)))
          context fuel cache ftsResult hvalid hcompletable hfts
      exact
        evalDist_runDeferredChronologicalLayersAndPublish_continue_eq_selectionOnly parameter
          table ftsSecret randomness index leaves ftsResult.value.1 ftsResult.context
            ftsResult.remaining ftsResult.value.2 next hftsInvariants.1 hftsInvariants.2

noncomputable def runSelectionOnlySign
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    ProbComp (Option (ResolvedRunResult (Option Signature × SplitHashCache))) := do
  let secretKey : SecretKey :=
    ⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩
  let selected ← runResolvedFromTable context fuel table
    ((simulateQ ordinaryRomImpl
      (signDigestLoop digestAttemptLimit secretKey message)).run cache)
  match selected with
  | none => pure none
  | some selected =>
      match selected.value.1 with
      | none => pure (some ⟨selected.context, selected.remaining,
          (none, selected.value.2), table⟩)
      | some (randomness, index, leaves) =>
          runSelectionOnlySignAfterDigest parameter table ftsSecret randomness index leaves
            selected.context selected.remaining selected.value.2

set_option maxRecDepth 100000 in
theorem evalDist_runDeferredChronologicalSign_continue_eq_selectionOnly
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (next : Option Signature → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    evalDist (runDeferredChronologicalSign parameter root table ftsSecret message context fuel
        cache >>= continueResolvedRunIsNone next) =
      evalDist (runSelectionOnlySign parameter root table ftsSecret message context fuel cache >>=
        continueResolvedRunIsNone next) := by
  unfold runDeferredChronologicalSign runSelectionOnlySign
  simp only [bind_assoc]
  apply evalDist_bind_congr
  intro selectedOption hselected
  cases selectedOption with
  | none => simp [continueResolvedRunIsNone]
  | some selected =>
      cases hvalue : selected.value.1 with
      | none => simp [hvalue, continueResolvedRunIsNone]
      | some digestResult =>
          rcases digestResult with ⟨randomness, index, leaves⟩
          simp only [hvalue]
          let secretKey : SecretKey :=
            ⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩
          have hselectedInvariants :=
            valid_completable_of_mem_runResolvedFromTable_of_finalizationMaterializedCouples table
              (simulateQ ordinaryRomImpl
                (signDigestLoop digestAttemptLimit secretKey message))
              (finalizationMaterializedCouples_simulateQ ordinaryRomImpl
                (finalizationMaterializedCouples_ordinaryRomImpl table)
                (signDigestLoop digestAttemptLimit secretKey message))
              context fuel cache selected hvalid hcompletable (by
                simpa only [secretKey] using hselected)
          exact evalDist_runDeferredChronologicalSignAfterDigest_continue_eq_selectionOnly
            parameter table ftsSecret randomness index leaves selected.context
              selected.remaining selected.value.2 next hselectedInvariants.1
                hselectedInvariants.2

noncomputable def maskedSelectionOnlyLayersAndPublish
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Signature) := do
  let layers ← sequenceFin fun lay : Layer =>
    maskedSignLayer parameter ftsSecret index lay
  publishSelectedChronologicalSignature ftsSecret randomness index leaves ftsPath layers

noncomputable def maskedScheduledSelectionOnlyLayersAndPublish
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Signature) := do
  let top ← maskedSignLayer parameter ftsSecret index topLayer
  let middle ← maskedSignLayer parameter ftsSecret index middleLayer
  let bottom ← maskedSignLayer parameter ftsSecret index bottomLayer
  let selected := Function.update
    (Function.update
      (Function.update (fun _ : Layer => none) topLayer top)
      middleLayer middle)
    bottomLayer bottom
  publishSelectedChronologicalSignature ftsSecret randomness index leaves ftsPath selected

set_option maxRecDepth 100000 in
theorem evalDist_runSelectionOnlyLayersAndPublish_eq_sequence
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table) :
    evalDist (runSelectionOnlyLayersAndPublish parameter table ftsSecret randomness index
        leaves ftsPath context fuel cache) =
      evalDist (runResolvedFromTable context fuel table
        ((maskedScheduledSelectionOnlyLayersAndPublish parameter ftsSecret randomness index
          leaves ftsPath).run cache)) := by
  unfold runSelectionOnlyLayersAndPublish maskedScheduledSelectionOnlyLayersAndPublish
  simp only [deferredLayerSelections, List.map_cons, List.map_nil,
    runDeferredLayerSchedule, runDeferredLayerOperation, selectDeferredLayer,
    bind_assoc, StateT.run_bind, runResolvedFromTable_bind]
  apply evalDist_bind_congr
  intro topOption htop
  cases topOption with
  | none => simp [publishSelectedDeferredSignature]
  | some topResult =>
      have htopCore := resolvedCore_of_mem_runResolvedFromTable
        ((maskedSignLayer parameter ftsSecret index topLayer).run
          (emptyDeferredLayerStore cache).cache)
          context fuel table topResult hconsistent hstarts htop
      simp only [pure_bind]
      rw [htopCore.1]
      simp only [bind_assoc]
      apply evalDist_bind_congr
      intro middleOption hmiddle
      cases middleOption with
      | none => simp [publishSelectedDeferredSignature]
      | some middleResult =>
          have hmiddleCore := resolvedCore_of_mem_runResolvedFromTable
                ((maskedSignLayer parameter ftsSecret index middleLayer).run topResult.value.2)
              topResult.context topResult.remaining table middleResult htopCore.2.1
                htopCore.2.2 (by simpa using hmiddle)
          simp only [pure_bind]
          rw [hmiddleCore.1]
          simp only [bind_assoc]
          apply evalDist_bind_congr
          intro bottomOption hbottom
          cases bottomOption with
          | none => simp [publishSelectedDeferredSignature]
          | some bottomResult =>
              have hbottomCore := resolvedCore_of_mem_runResolvedFromTable
                ((maskedSignLayer parameter ftsSecret index bottomLayer).run middleResult.value.2)
                  middleResult.context middleResult.remaining table bottomResult
                    hmiddleCore.2.1 hmiddleCore.2.2 (by simpa using hbottom)
              simp only [pure_bind, publishSelectedDeferredSignature]
              rw [hbottomCore.1]
              congr 2

theorem maskedScheduledSelectionOnlyLayersAndPublish_eq
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) :
    maskedScheduledSelectionOnlyLayersAndPublish parameter ftsSecret randomness index leaves
        ftsPath =
      maskedSelectionOnlyLayersAndPublish parameter ftsSecret randomness index leaves
        ftsPath := by
  unfold maskedScheduledSelectionOnlyLayersAndPublish maskedSelectionOnlyLayersAndPublish
  simp only [sequenceFin, numLayers, topLayer, middleLayer, bottomLayer, bind_assoc,
    pure_bind]
  apply bind_congr
  intro top
  apply bind_congr
  intro middle
  apply bind_congr
  intro bottom
  congr 1
  funext lay
  fin_cases lay <;>
    simp [Function.update, numLayers]
  all_goals rfl

set_option maxRecDepth 100000 in
theorem evalDist_runSelectionOnlyLayersAndPublish_eq_resolved
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table) :
    evalDist (runSelectionOnlyLayersAndPublish parameter table ftsSecret randomness index
        leaves ftsPath context fuel cache) =
      evalDist (runResolvedFromTable context fuel table
        ((maskedSelectionOnlyLayersAndPublish parameter ftsSecret randomness index leaves
          ftsPath).run cache)) := by
  calc
    _ = evalDist (runResolvedFromTable context fuel table
          ((maskedScheduledSelectionOnlyLayersAndPublish parameter ftsSecret randomness index
            leaves ftsPath).run cache)) :=
      evalDist_runSelectionOnlyLayersAndPublish_eq_sequence parameter table ftsSecret
        randomness index leaves ftsPath context fuel cache hconsistent hstarts
    _ = _ := by
      rw [maskedScheduledSelectionOnlyLayersAndPublish_eq]

theorem maskedSignAfterDigest_eq_selectionOnly
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    maskedSignAfterDigest parameter ftsSecret randomness index leaves = (do
      let ftsPath ← simulateQ ordinaryHashImpl
        (ftsOpen parameter index leaves (ftsSecret index))
      maskedSelectionOnlyLayersAndPublish parameter ftsSecret randomness index leaves
        ftsPath) := by
  unfold maskedSignAfterDigest maskedSelectionOnlyLayersAndPublish
    publishSelectedChronologicalSignature
  rfl

set_option maxRecDepth 100000 in
theorem evalDist_runSelectionOnlySignAfterDigest_eq_resolved
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table) :
    evalDist (runSelectionOnlySignAfterDigest parameter table ftsSecret randomness index leaves
        context fuel cache) =
      evalDist (runResolvedFromTable context fuel table
        ((maskedSignAfterDigest parameter ftsSecret randomness index leaves).run cache)) := by
  rw [maskedSignAfterDigest_eq_selectionOnly]
  unfold runSelectionOnlySignAfterDigest
  rw [StateT.run_bind, runResolvedFromTable_bind]
  apply evalDist_bind_congr
  intro ftsOption hfts
  cases ftsOption with
  | none => rfl
  | some ftsResult =>
      have hftsCore := resolvedCore_of_mem_runResolvedFromTable
        ((simulateQ ordinaryHashImpl
          (ftsOpen parameter index leaves (ftsSecret index))).run cache)
        context fuel table ftsResult hconsistent hstarts hfts
      simp only
      rw [hftsCore.1]
      exact evalDist_runSelectionOnlyLayersAndPublish_eq_resolved parameter table ftsSecret
        randomness index leaves ftsResult.value.1 ftsResult.context ftsResult.remaining
          ftsResult.value.2 hftsCore.2.1 hftsCore.2.2

set_option maxRecDepth 100000 in
theorem evalDist_runSelectionOnlySign_eq_resolved
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table) :
    evalDist (runSelectionOnlySign parameter root table ftsSecret message context fuel cache) =
      evalDist (runResolvedFromTable context fuel table
        ((maskedSign parameter root ftsSecret message).run cache)) := by
  unfold runSelectionOnlySign maskedSign
  rw [StateT.run_bind, runResolvedFromTable_bind]
  apply evalDist_bind_congr
  intro selectedOption hselected
  cases selectedOption with
  | none => rfl
  | some selected =>
      have hselectedCore := resolvedCore_of_mem_runResolvedFromTable
        ((simulateQ ordinaryRomImpl
          (signDigestLoop digestAttemptLimit
            ⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩ message)).run cache)
        context fuel table selected hconsistent hstarts hselected
      cases hvalue : selected.value.1 with
      | none =>
          simp only [hvalue]
          simp [runResolvedFromTable, hselectedCore.1]
      | some digestResult =>
          rcases digestResult with ⟨randomness, selectedIndex, leaves⟩
          simp only [hvalue]
          rw [hselectedCore.1]
          exact evalDist_runSelectionOnlySignAfterDigest_eq_resolved parameter table ftsSecret
            randomness selectedIndex leaves selected.context selected.remaining
              selected.value.2 hselectedCore.2.1 hselectedCore.2.2

set_option maxRecDepth 100000 in
theorem evalDist_runDeferredChronologicalSign_continue_eq_maskedSign
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (next : Option Signature → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    evalDist (runDeferredChronologicalSign parameter root table ftsSecret message context fuel
        cache >>= continueResolvedRunIsNone next) =
      evalDist (runResolvedFinishIsNone context fuel table
        ((maskedSign parameter root ftsSecret message >>= next).run cache)) := by
  calc
    _ = evalDist (runSelectionOnlySign parameter root table ftsSecret message context fuel cache >>=
          continueResolvedRunIsNone next) :=
      evalDist_runDeferredChronologicalSign_continue_eq_selectionOnly parameter root table
        ftsSecret message context fuel cache next hvalid hcompletable
    _ = evalDist (runResolvedFromTable context fuel table
          ((maskedSign parameter root ftsSecret message).run cache) >>=
            continueResolvedRunIsNone next) := by
      rw [evalDist_bind, evalDist_bind,
        evalDist_runSelectionOnlySign_eq_resolved parameter root table ftsSecret message context
          fuel cache hvalid.valuesConsistent
            (startTableAgrees_of_deferredCompletable hcompletable)]
    _ = _ := evalDist_runResolvedFromTable_then_continue context fuel table cache
      (maskedSign parameter root ftsSecret message) next

end SphincsSecurity.Concrete.OtsProbeSimulation
