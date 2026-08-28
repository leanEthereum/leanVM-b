import SphincsSecurity.Proof.OtsProbeResolvedSelectionFinalization

/-!
# Finalization equivalence for the chronological signer

This file carries the layer-schedule coupling through the delayed publication pass and the complete
signer.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem FinalizationViewEq.publish
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewEq table left right) (coordinate : Coordinate) :
    FinalizationViewEq table
      { left with state := left.state.publish coordinate }
      { right with state := right.state.publish coordinate } := by
  refine ⟨hview.leftConsistent.publish coordinate,
    hview.rightConsistent.publish coordinate, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hview.leftStarts
  · exact hview.rightStarts
  · exact hview.valueEq
  · exact hview.leftClean
  · exact hview.rightClean
  · exact hview.pendingEq

theorem DeferredCompletable.publish
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hcompletable : DeferredCompletable table context) (coordinate : Coordinate) :
    DeferredCompletable table
      { context with state := context.state.publish coordinate } := by
  rcases hcompletable with ⟨completion, hcompletion⟩
  exact ⟨completion, hcompletion⟩

theorem finalizationMaterializedCouples_publishCoordinate
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) :
    FinalizationMaterializedCouples table (publishCoordinate coordinate) := by
  intro left right fuel leftCache rightCache hcontext hcache hrevealed
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  unfold publishCoordinate
  rw [StateT.run_liftM, StateT.run_liftM,
    LazyRevealProbe.publishQuery,
    runResolvedFromTable_publish_query_bind,
    runResolvedFromTable_publish_query_bind]
  apply relTriple_pure_pure
  exact ⟨rfl,
    ⟨hview.publish coordinate, hleftValid.publish coordinate,
      hrightValid.publish coordinate, hleftCompletable.publish coordinate⟩,
    rfl, rfl, rfl, hcache, by
      simpa [LazyRevealProbe.State.publish] using congrArg (insert coordinate) hrevealed⟩

theorem finalizationMaterializedCouples_splitUniformImpl
    (table : OtsSecretIndex → HashOutput) (n : Nat) :
    FinalizationMaterializedCouples table (splitUniformImpl n) := by
  intro left right fuel leftCache rightCache hcontext hcache hrevealed
  unfold splitUniformImpl
  rw [StateT.run_liftM, StateT.run_liftM, LazyRevealProbe.uniformQuery,
    runResolvedFromTable_uniform_query_bind,
    runResolvedFromTable_uniform_query_bind]
  apply relTriple_bind (relTriple_refl
    (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
  intro leftOutput rightOutput houtput
  subst rightOutput
  apply relTriple_pure_pure
  exact ⟨rfl, hcontext, rfl, rfl, rfl, hcache, hrevealed⟩

theorem finalizationMaterializedCouples_ordinaryRomImpl
    (table : OtsSecretIndex → HashOutput) (query : OracleWorld.Domain) :
    FinalizationMaterializedCouples table (ordinaryRomImpl query) := by
  cases query with
  | inl n => exact finalizationMaterializedCouples_splitUniformImpl table n
  | inr input => exact finalizationMaterializedCouples_ordinaryHashImpl table input

set_option maxRecDepth 100000 in
theorem finalizationMaterializedCouples_revealChainStart
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex) :
    FinalizationMaterializedCouples table
      (revealChainStart index.lay index.tree index.leafIdx index.chainIdx) := by
  intro left right fuel leftCache rightCache hcontext hcache hrevealed
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  rw [revealChainStart, runResolvedFromTable_revealCoordinate,
    runResolvedFromTable_revealCoordinate]
  have hresolved := relTriple_resolveDeferredChainStart_of_finalizationViewEq table index left
    right hview hleftValid hrightValid hleftCompletable
  have hresolvedLeft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hresolved
      (fun result => result ∈ support
        (pure (resolveDeferredChainStart table index left) :
          ProbComp (Option DeferredResolution)))
      (fun result hresult => hresult)
  have hresolvedBoth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hresolvedLeft
  apply relTriple_bind hresolvedBoth
  intro leftResolved rightResolved hrelation
  rcases hrelation with ⟨⟨hrelation, hleftSupport⟩, hrightSupport⟩
  cases leftResolved with
  | none =>
      cases rightResolved with
      | none => simp [FinalizationMaterializedRunEq]
      | some rightResolved => simp [FinalizationResolutionEq] at hrelation
  | some leftResolved =>
      cases rightResolved with
      | none => simp [FinalizationResolutionEq] at hrelation
      | some rightResolved =>
          have hleftResult :
              resolveDeferredChainStart table index left = some leftResolved := by
            simpa using hleftSupport.symm
          have hrightResult :
              resolveDeferredChainStart table index right = some rightResolved := by
            simpa using hrightSupport.symm
          have hleftMaterializedCompletable :=
            hleftCompletable.materializeResolvedChainStart hview.leftStarts index leftResolved
              hleftResult
          have hrightCompletable : DeferredCompletable table right := by
            rcases hleftCompletable with ⟨completion, hcompletion⟩
            exact ⟨completion, (hview.deferredCompletion_iff completion).mp hcompletion⟩
          have hrightMaterializedCompletable :=
            hrightCompletable.materializeResolvedChainStart hview.rightStarts index
              rightResolved hrightResult
          have hleftMaterializedView :=
            finalizationViewEq_materializeResolvedChainStart index leftResolved hleftValid
              hview.leftStarts hleftResult hleftMaterializedCompletable
          have hrightMaterializedView :=
            finalizationViewEq_materializeResolvedChainStart index rightResolved hrightValid
              hview.rightStarts hrightResult hrightMaterializedCompletable
          have hleftMaterializedValid :
              (materializeResolvedChainStart left index leftResolved).Valid := by
            unfold materializeResolvedChainStart
            rw [resolveDeferredChainStart_deferred_values_eq table index left leftResolved
              hleftResult]
            rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
            exact hleftValid.materialize_chainStart lay tree leafIdx chainIdx leftResolved.output
          have hrightMaterializedValid :
              (materializeResolvedChainStart right index rightResolved).Valid := by
            unfold materializeResolvedChainStart
            rw [resolveDeferredChainStart_deferred_values_eq table index right rightResolved
              hrightResult]
            rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
            exact hrightValid.materialize_chainStart lay tree leafIdx chainIdx
              rightResolved.output
          apply relTriple_pure_pure
          refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
          · simpa using congrArg truncateHash hrelation.1
          · exact ⟨hleftMaterializedView.trans
                (hrelation.2.1.trans hrightMaterializedView.symm),
              hleftMaterializedValid, hrightMaterializedValid,
              hleftMaterializedCompletable⟩
          · rw [ordinaryQueryCache_update_hidden, ordinaryQueryCache_update_hidden,
              hcache]
          · simpa [materializeResolvedChainStart, LazyRevealProbe.State.materialize]
              using hrevealed

theorem finalizationMaterializedCouples_revealCoordinate
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) :
    FinalizationMaterializedCouples table (revealCoordinate coordinate) := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      exact finalizationMaterializedCouples_revealChainStart table
        ⟨lay, tree, leafIdx, chainIdx⟩
  | position position =>
      exact finalizationMaterializedCouples_revealPosition table position

theorem finalizationMaterializedCouples_revealPublishedCoordinate
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) :
    FinalizationMaterializedCouples table (revealPublishedCoordinate coordinate) := by
  unfold revealPublishedCoordinate
  exact (finalizationMaterializedCouples_revealCoordinate table coordinate).bind fun value =>
    (finalizationMaterializedCouples_publishCoordinate table coordinate).bind fun _ =>
      finalizationMaterializedCouples_pure table value

set_option maxRecDepth 100000 in
theorem finalizationMaterializedCouples_revealLayerValues
    (table : OtsSecretIndex → HashOutput) (index : Index) (lay : Layer)
    (encoding : ChainIndex → Digit) :
    FinalizationMaterializedCouples table (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  apply (finalizationMaterializedCouples_sequenceFin
    (fun chainIdx : ChainIndex =>
      revealPublishedCoordinate
        (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay)
          chainIdx (encoding chainIdx)))
    (fun chainIdx => finalizationMaterializedCouples_revealPublishedCoordinate table
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay)
        chainIdx (encoding chainIdx)))).bind
  intro values
  apply (finalizationMaterializedCouples_sequenceFin
    (fun level : Fin maxLayerHeight =>
      if level.val < layerHeight lay then
        match level.val with
        | 0 => revealPublishedCoordinate (.position (.leaf lay (treeIndexAt index lay)
            (leafOfNat (Nat.xor (leafIndexAt index lay).val 1))))
        | current + 1 =>
            if hcurrent : current < maxLayerHeight then
              revealPublishedCoordinate (.position (.node lay (treeIndexAt index lay)
                ⟨current, hcurrent⟩ (leafOfNat
                  (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
            else pure 0
      else pure 0)
    (fun level => by
      by_cases hinLayer : level.val < layerHeight lay
      · rw [if_pos hinLayer]
        cases hvalue : level.val with
        | zero =>
            exact finalizationMaterializedCouples_revealPublishedCoordinate table
              (.position (.leaf lay (treeIndexAt index lay)
                (leafOfNat (Nat.xor (leafIndexAt index lay).val 1))))
        | succ current =>
            have hcurrent : current < maxLayerHeight := by
              have := level.isLt
              omega
            simp only
            rw [dif_pos hcurrent]
            exact finalizationMaterializedCouples_revealPublishedCoordinate table
              (.position (.node lay (treeIndexAt index lay) ⟨current, hcurrent⟩
                (leafOfNat
                  (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
      · rw [if_neg hinLayer]
        exact finalizationMaterializedCouples_pure table 0)).bind
  intro path
  exact finalizationMaterializedCouples_pure table (values, path)

set_option maxRecDepth 100000 in
theorem finalizationMaterializedCouples_publishChronologicalSignature
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (layers : Layer → Option ChronologicalLayerPart) :
    FinalizationMaterializedCouples table
      (publishChronologicalSignature ftsSecret randomness index leaves ftsPath layers) := by
  unfold publishChronologicalSignature
  cases hparts : traverseOption layers with
  | none => exact finalizationMaterializedCouples_pure table none
  | some parts =>
      apply (finalizationMaterializedCouples_sequenceFin
        (fun lay : Layer => revealLayerValues index lay (parts lay).encoding)
        (fun lay => finalizationMaterializedCouples_revealLayerValues table index lay
          (parts lay).encoding)).bind
      intro published
      let signature : Signature :=
        { randomness := randomness
          ftsSecret := fun tree => ftsSecret index tree (leaves (ftsIndexOf tree))
          ftsPath := ftsPath
          counter := fun lay => (parts lay).counter
          chainValue := fun lay => (published lay).1
          authPath := flattenPaths fun lay => (published lay).2 }
      exact finalizationMaterializedCouples_pure table (some signature)

def chronologicalPartsOfStore (store : DeferredLayerStore) :
    Layer → Option ChronologicalLayerPart := fun lay =>
  match store.selected lay, store.resolved lay with
  | some (counter, encoding), some (_, chainValue, authPath) =>
      some ⟨counter, encoding, chainValue, authPath⟩
  | _, _ => none

theorem chronologicalSelectedAfter_layers_empty
    (parts : Layer → Option ChronologicalLayerPart) (cache : SplitHashCache) :
    chronologicalSelectedAfter (fun lay : Layer => lay) parts
        (emptyDeferredLayerStore cache).selected =
      fun lay => (parts lay).map fun part => (part.counter, part.encoding) := by
  funext lay
  fin_cases lay <;> rfl

theorem chronologicalResolvedAfter_layers_empty
    (parts : Layer → Option ChronologicalLayerPart) (cache : SplitHashCache) :
    chronologicalResolvedAfter (fun lay : Layer => lay) parts
        (emptyDeferredLayerStore cache).resolved =
      fun lay => (parts lay).map ChronologicalLayerPart.toLayerPart := by
  funext lay
  fin_cases lay <;> rfl

theorem chronologicalPartsOfStore_eq
    (store : DeferredLayerStore) (parts : Layer → Option ChronologicalLayerPart)
    (hselected : store.selected =
      fun lay => (parts lay).map fun part => (part.counter, part.encoding))
    (hresolved : store.resolved =
      fun lay => (parts lay).map ChronologicalLayerPart.toLayerPart) :
    chronologicalPartsOfStore store = parts := by
  funext lay
  rw [chronologicalPartsOfStore, hselected, hresolved]
  cases hpart : parts lay with
  | none => simp [hpart]
  | some part =>
      rcases part with ⟨counter, encoding, chainValue, authPath⟩
      simp [hpart, ChronologicalLayerPart.toLayerPart]

noncomputable def publishDeferredChronologicalSignature
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) :
    Option (ResolvedRunResult DeferredLayerStore) →
      ProbComp (Option (ResolvedRunResult (Option Signature × SplitHashCache)))
  | none => pure none
  | some result =>
      runResolvedFromTable result.context result.remaining result.table
        ((publishChronologicalSignature ftsSecret randomness index leaves ftsPath
          (chronologicalPartsOfStore result.value)).run result.value.cache)

noncomputable def runResolvedChronologicalLayersAndPublish
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    ProbComp (Option (ResolvedRunResult (Option Signature × SplitHashCache))) := do
  let layers ← runResolvedSequenceFin
    (fun lay : Layer => maskedChronologicalSignLayer parameter ftsSecret index lay)
    context fuel table cache
  match layers with
  | none => pure none
  | some layers =>
      runResolvedFromTable layers.context layers.remaining layers.table
        ((publishChronologicalSignature ftsSecret randomness index leaves ftsPath
          layers.value.1).run layers.value.2)

noncomputable def runDeferredChronologicalLayersAndPublish
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    ProbComp (Option (ResolvedRunResult (Option Signature × SplitHashCache))) :=
  runDeferredLayerSchedule parameter table ftsSecret index chronologicalLayerSchedule
      (some ⟨context, fuel, emptyDeferredLayerStore cache, table⟩) >>=
    publishDeferredChronologicalSignature ftsSecret randomness index leaves ftsPath

set_option maxRecDepth 100000 in
theorem relTriple_runResolvedChronologicalLayersAndPublish_finalization
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (left right : DeferredContext) (fuel : Nat) (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed) :
    RelTriple
      (runResolvedChronologicalLayersAndPublish parameter table ftsSecret randomness index
        leaves ftsPath left fuel leftCache)
      (runDeferredChronologicalLayersAndPublish parameter table ftsSecret randomness index
        leaves ftsPath right fuel rightCache)
      (FinalizationMaterializedRunEq table) := by
  unfold runResolvedChronologicalLayersAndPublish
    runDeferredChronologicalLayersAndPublish
  have hlayers :=
    relTriple_runResolvedSequenceFin_maskedChronologicalSignLayers_schedule_finalization
      parameter table ftsSecret index left right fuel leftCache
      (emptyDeferredLayerStore rightCache) hcontext hcache hrevealed
  apply relTriple_bind hlayers
  intro leftLayers rightLayers hlayersRelation
  cases leftLayers with
  | none =>
      cases rightLayers with
      | none => simp [publishDeferredChronologicalSignature,
          FinalizationMaterializedRunEq]
      | some rightLayers =>
          simp [FinalizationChronologicalFamilyEq] at hlayersRelation
  | some leftLayers =>
      cases rightLayers with
      | none => simp [FinalizationChronologicalFamilyEq] at hlayersRelation
      | some rightLayers =>
          rcases leftLayers with
            ⟨leftContext, leftRemaining, ⟨leftParts, leftCache⟩, leftTable⟩
          rcases rightLayers with
            ⟨rightContext, rightRemaining, rightStore, rightTable⟩
          simp only [FinalizationChronologicalFamilyEq] at hlayersRelation
          rcases hlayersRelation with
            ⟨hcontext, hremaining, hleftTable, hrightTable, hselected, hresolved,
              hcache, hrevealed⟩
          subst leftRemaining
          subst leftTable
          subst rightTable
          simp only [publishDeferredChronologicalSignature]
          have hselected' : rightStore.selected =
              fun lay => (leftParts lay).map fun part =>
                (part.counter, part.encoding) := by
            rw [hselected, chronologicalSelectedAfter_layers_empty]
          have hresolved' : rightStore.resolved =
              fun lay => (leftParts lay).map ChronologicalLayerPart.toLayerPart := by
            rw [hresolved, chronologicalResolvedAfter_layers_empty]
          have hparts := chronologicalPartsOfStore_eq rightStore leftParts
            hselected' hresolved'
          rw [hparts]
          exact finalizationMaterializedCouples_publishChronologicalSignature table ftsSecret
            randomness index leaves ftsPath leftParts leftContext rightContext rightRemaining
              leftCache rightStore.cache hcontext hcache hrevealed

set_option maxHeartbeats 400000 in
theorem evalDist_runResolvedChronologicalLayersAndPublish_eq
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table) :
    evalDist (runResolvedChronologicalLayersAndPublish parameter table ftsSecret randomness
        index leaves ftsPath context fuel cache) =
      evalDist (runResolvedFromTable context fuel table
        ((do
          let layers ← maskedChronologicalSignLayers parameter ftsSecret index
          publishChronologicalSignature ftsSecret randomness index leaves ftsPath layers).run
            cache)) := by
  unfold runResolvedChronologicalLayersAndPublish maskedChronologicalSignLayers
  rw [StateT.run_bind, runResolvedFromTable_bind, evalDist_bind, evalDist_bind,
    evalDist_runResolvedSequenceFin_eq
      (fun lay : Layer => maskedChronologicalSignLayer parameter ftsSecret index lay)
      context fuel table cache hconsistent hstarts]
  apply bind_congr
  intro result
  cases result <;> rfl

noncomputable def runDeferredLayersAndPublish
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (schedule : List DeferredLayerOperation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    ProbComp (Option (ResolvedRunResult (Option Signature × SplitHashCache))) :=
  runDeferredLayerSchedule parameter table ftsSecret index schedule
      (some ⟨context, fuel, emptyDeferredLayerStore cache, table⟩) >>=
    publishDeferredChronologicalSignature ftsSecret randomness index leaves ftsPath

theorem evalDist_runDeferredChronologicalLayersAndPublish_eq_deferred
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    evalDist (runDeferredChronologicalLayersAndPublish parameter table ftsSecret randomness
        index leaves ftsPath context fuel cache) =
      evalDist (runDeferredLayersAndPublish parameter table ftsSecret randomness index leaves
        ftsPath deferredLayerSchedule context fuel cache) := by
  unfold runDeferredChronologicalLayersAndPublish runDeferredLayersAndPublish
  exact evalDist_chronologicalLayerSchedule_bind_eq_deferred parameter table ftsSecret index
    (some ⟨context, fuel, emptyDeferredLayerStore cache, table⟩)
    (publishDeferredChronologicalSignature ftsSecret randomness index leaves ftsPath)

noncomputable def finishResolvedRunIsNone
    (input : Option (ResolvedRunResult α)) : ProbComp Bool :=
  Option.isNone <$> finishResolvedRun input

set_option maxRecDepth 100000 in
theorem evalDist_finishResolvedRunIsNone_eq_of_finalizationMaterializedRunEq
    (table : OtsSecretIndex → HashOutput)
    (left right : Option (ResolvedRunResult (α × SplitHashCache)))
    (hrelation : FinalizationMaterializedRunEq table left right) :
    evalDist (finishResolvedRunIsNone left) =
      evalDist (finishResolvedRunIsNone right) := by
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some right => simp [FinalizationMaterializedRunEq] at hrelation
  | some left =>
      cases right with
      | none => simp [FinalizationMaterializedRunEq] at hrelation
      | some right =>
          rcases hrelation with
            ⟨hvalue, hcontext, hremaining, hleftTable, hrightTable, hcache, _hrevealed⟩
          rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
          have hrightCompletable : DeferredCompletable table right.context := by
            rcases hleftCompletable with ⟨completion, hcompletion⟩
            exact ⟨completion, (hview.deferredCompletion_iff completion).mp hcompletion⟩
          simp only [finishResolvedRunIsNone, finishResolvedRun, hleftTable, hrightTable,
            hleftCompletable, hrightCompletable, ↓reduceIte, map_bind]
          have hfinalize := evalDist_map_isNone_finalizeResolvedCoordinates_congr_covered table
            left.context.state.coordinates.toList right.context.state.coordinates.toList
            left.context right.context hview (Finset.nodup_toList _)
              (Finset.nodup_toList _) (pendingCovered_coordinates_toList left.context)
              (pendingCovered_coordinates_toList right.context)
          have hleftFinish :
              evalDist (do
                let finalized ← finalizeResolvedCoordinates
                  left.context.state.coordinates.toList left.context table
                Option.isNone <$> match finalized with
                | none => pure none
                | some context => pure (some
                    (ResolvedRunResult.mk context left.remaining left.value table))) =
                evalDist (Option.isNone <$>
                  finalizeResolvedCoordinates left.context.state.coordinates.toList
                    left.context table) := by
            rw [map_eq_bind_pure_comp]
            apply evalDist_bind_congr
            intro finalized _
            cases finalized <;> simp
          have hrightFinish :
              evalDist (do
                let finalized ← finalizeResolvedCoordinates
                  right.context.state.coordinates.toList right.context table
                Option.isNone <$> match finalized with
                | none => pure none
                | some context => pure (some
                    (ResolvedRunResult.mk context right.remaining right.value table))) =
                evalDist (Option.isNone <$>
                  finalizeResolvedCoordinates right.context.state.coordinates.toList
                    right.context table) := by
            rw [map_eq_bind_pure_comp]
            apply evalDist_bind_congr
            intro finalized _
            cases finalized <;> simp
          exact hleftFinish.trans (hfinalize.trans hrightFinish.symm)

theorem relTriple_finishResolvedRunIsNone_of_finalizationMaterializedRunEq
    (table : OtsSecretIndex → HashOutput)
    (left right : Option (ResolvedRunResult (α × SplitHashCache)))
    (hrelation : FinalizationMaterializedRunEq table left right) :
    RelTriple (finishResolvedRunIsNone left) (finishResolvedRunIsNone right) (EqRel Bool) :=
  relTriple_eqRel_of_evalDist_eq
    (evalDist_finishResolvedRunIsNone_eq_of_finalizationMaterializedRunEq table left right
      hrelation)

theorem evalDist_runResolvedChronologicalLayersAndPublish_finish_eq_deferred
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (left right : DeferredContext) (fuel : Nat) (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed) :
    evalDist (runResolvedChronologicalLayersAndPublish parameter table ftsSecret randomness
        index leaves ftsPath left fuel leftCache >>= finishResolvedRunIsNone) =
      evalDist (runDeferredChronologicalLayersAndPublish parameter table ftsSecret randomness
        index leaves ftsPath right fuel rightCache >>= finishResolvedRunIsNone) := by
  apply evalDist_eq_of_relTriple_eqRel
  apply relTriple_bind
    (relTriple_runResolvedChronologicalLayersAndPublish_finalization parameter table ftsSecret
      randomness index leaves ftsPath left right fuel leftCache rightCache hcontext hcache hrevealed)
  intro leftResult rightResult hrelation
  exact relTriple_finishResolvedRunIsNone_of_finalizationMaterializedRunEq table leftResult
    rightResult hrelation

theorem evalDist_runDeferredChronologicalLayersAndPublish_finish_eq_deferred
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    evalDist (runDeferredChronologicalLayersAndPublish parameter table ftsSecret randomness
        index leaves ftsPath context fuel cache >>= finishResolvedRunIsNone) =
      evalDist (runDeferredLayersAndPublish parameter table ftsSecret randomness index leaves
        ftsPath deferredLayerSchedule context fuel cache >>= finishResolvedRunIsNone) := by
  rw [evalDist_bind, evalDist_bind,
    evalDist_runDeferredChronologicalLayersAndPublish_eq_deferred parameter table ftsSecret
      randomness index leaves ftsPath context fuel cache]

noncomputable def runDeferredChronologicalSignAfterDigest
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
      runDeferredChronologicalLayersAndPublish parameter table ftsSecret randomness index
        leaves ftsPath.value.1 ftsPath.context ftsPath.remaining ftsPath.value.2

set_option maxRecDepth 100000 in
theorem relTriple_runResolvedFromTable_maskedPublishedChronologicalSignAfterDigest_finalization
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (left right : DeferredContext) (fuel : Nat) (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed) :
    RelTriple
      (runResolvedFromTable left fuel table
        ((maskedPublishedChronologicalSignAfterDigest parameter ftsSecret randomness index
          leaves).run leftCache))
      (runDeferredChronologicalSignAfterDigest parameter table ftsSecret randomness index leaves
        right fuel rightCache)
      (FinalizationMaterializedRunEq table) := by
  rw [maskedPublishedChronologicalSignAfterDigest_eq, StateT.run_bind,
    runResolvedFromTable_bind]
  unfold runDeferredChronologicalSignAfterDigest
  have hfts := finalizationMaterializedCouples_simulateQ ordinaryHashImpl
    (finalizationMaterializedCouples_ordinaryHashImpl table)
    (ftsOpen parameter index leaves (ftsSecret index))
    left right fuel leftCache rightCache hcontext hcache hrevealed
  apply relTriple_bind hfts
  intro leftFts rightFts hftsRelation
  cases leftFts with
  | none =>
      cases rightFts with
      | none => simp [FinalizationMaterializedRunEq]
      | some rightFts => simp [FinalizationMaterializedRunEq] at hftsRelation
  | some leftFts =>
      cases rightFts with
      | none => simp [FinalizationMaterializedRunEq] at hftsRelation
      | some rightFts =>
          rcases leftFts with
            ⟨leftContext, leftRemaining, ⟨leftFtsPath, leftCache⟩, leftTable⟩
          rcases rightFts with
            ⟨rightContext, rightRemaining, ⟨rightFtsPath, rightCache⟩, rightTable⟩
          rcases hftsRelation with
            ⟨hftsPath, hcontext, hremaining, hleftTable, hrightTable, hcache, hrevealed⟩
          simp only at hftsPath hcontext hremaining hleftTable hrightTable hcache hrevealed
          subst rightFtsPath
          subst leftRemaining
          subst leftTable
          subst rightTable
          simp only
          have hlayers :=
            relTriple_runResolvedChronologicalLayersAndPublish_finalization parameter table
              ftsSecret randomness index leaves leftFtsPath leftContext rightContext
                rightRemaining leftCache rightCache hcontext hcache hrevealed
          apply relTriple_of_evalDist_eq_left _ hlayers
          exact (evalDist_runResolvedChronologicalLayersAndPublish_eq parameter table ftsSecret
            randomness index leaves leftFtsPath leftContext rightRemaining leftCache
              hcontext.2.1.1 hcontext.1.leftStarts).symm

noncomputable def runDeferredChronologicalSign
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
          runDeferredChronologicalSignAfterDigest parameter table ftsSecret randomness index
            leaves selected.context selected.remaining selected.value.2

set_option maxRecDepth 100000 in
theorem relTriple_runResolvedFromTable_maskedPublishedChronologicalSign_finalization
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (left right : DeferredContext) (fuel : Nat) (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed) :
    RelTriple
      (runResolvedFromTable left fuel table
        ((maskedPublishedChronologicalSign parameter root ftsSecret message).run leftCache))
      (runDeferredChronologicalSign parameter root table ftsSecret message right fuel rightCache)
      (FinalizationMaterializedRunEq table) := by
  unfold maskedPublishedChronologicalSign runDeferredChronologicalSign
  let secretKey : SecretKey :=
    ⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩
  rw [StateT.run_bind, runResolvedFromTable_bind]
  have hselected := finalizationMaterializedCouples_simulateQ ordinaryRomImpl
    (finalizationMaterializedCouples_ordinaryRomImpl table)
    (signDigestLoop digestAttemptLimit secretKey message)
    left right fuel leftCache rightCache hcontext hcache hrevealed
  apply relTriple_bind hselected
  intro leftSelected rightSelected hselectedRelation
  cases leftSelected with
  | none =>
      cases rightSelected with
      | none => simp [FinalizationMaterializedRunEq]
      | some rightSelected =>
          simp [FinalizationMaterializedRunEq] at hselectedRelation
  | some leftSelected =>
      cases rightSelected with
      | none => simp [FinalizationMaterializedRunEq] at hselectedRelation
      | some rightSelected =>
          rcases leftSelected with
            ⟨leftContext, leftRemaining, ⟨leftValue, leftCache⟩, leftTable⟩
          rcases rightSelected with
            ⟨rightContext, rightRemaining, ⟨rightValue, rightCache⟩, rightTable⟩
          simp only [FinalizationMaterializedRunEq] at hselectedRelation
          rcases hselectedRelation with
            ⟨hvalue, hcontext, hremaining, hleftTable, hrightTable, hcache, hrevealed⟩
          subst rightValue
          subst leftRemaining
          subst leftTable
          subst rightTable
          simp only
          cases leftValue with
          | none =>
              apply relTriple_pure_pure
              exact ⟨rfl, hcontext, rfl, rfl, rfl, hcache, hrevealed⟩
          | some selected =>
              rcases selected with ⟨randomness, index, leaves⟩
              exact
                relTriple_runResolvedFromTable_maskedPublishedChronologicalSignAfterDigest_finalization
                  parameter table ftsSecret randomness index leaves leftContext rightContext
                    rightRemaining leftCache rightCache hcontext hcache hrevealed

end SphincsSecurity.Concrete.OtsProbeSimulation
