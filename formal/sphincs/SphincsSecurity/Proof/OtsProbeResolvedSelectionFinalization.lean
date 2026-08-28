import SphincsSecurity.Proof.OtsProbeResolvedFinalization

/-!
# Finalization equivalence through one-time layer selection

Layer selection may materialize the lower layer root before selecting a counter. This file lifts
the finalization view through those materializing computations while retaining exact public outputs
and ordinary-cache behavior.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def FinalizationMaterializedRunEq (table : OtsSecretIndex → HashOutput) :
    Option (ResolvedRunResult (α × SplitHashCache)) →
      Option (ResolvedRunResult (α × SplitHashCache)) → Prop
  | none, none => True
  | some left, some right =>
      left.value.1 = right.value.1 ∧
        FinalizationContextEq table (some left.context) (some right.context) ∧
        left.remaining = right.remaining ∧
        left.table = table ∧ right.table = table ∧
        ordinaryQueryCache left.value.2 = ordinaryQueryCache right.value.2 ∧
        left.context.state.revealed = right.context.state.revealed
  | _, _ => False

def FinalizationMaterializedCouples (table : OtsSecretIndex → HashOutput)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ left right fuel leftCache rightCache,
    FinalizationContextEq table (some left) (some right) →
    ordinaryQueryCache leftCache = ordinaryQueryCache rightCache →
    left.state.revealed = right.state.revealed →
    RelTriple
      (runResolvedFromTable left fuel table (computation.run leftCache))
      (runResolvedFromTable right fuel table (computation.run rightCache))
      (FinalizationMaterializedRunEq table)

theorem finalizationMaterializedCouples_pure
    (table : OtsSecretIndex → HashOutput) (value : α) :
    FinalizationMaterializedCouples table
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) α) := by
  intro left right fuel leftCache rightCache hcontext hcache hrevealed
  simp [StateT.run_pure, runResolvedFromTable, FinalizationMaterializedRunEq,
    hcontext, hcache, hrevealed]

theorem FinalizationMaterializedCouples.bind
    {table : OtsSecretIndex → HashOutput}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hleft : FinalizationMaterializedCouples table left)
    (hnext : ∀ value, FinalizationMaterializedCouples table (next value)) :
    FinalizationMaterializedCouples table (left >>= next) := by
  intro leftContext rightContext fuel leftCache rightCache hcontext hcache hrevealed
  rw [StateT.run_bind, StateT.run_bind, runResolvedFromTable_bind,
    runResolvedFromTable_bind]
  apply relTriple_bind
    (hleft leftContext rightContext fuel leftCache rightCache hcontext hcache hrevealed)
  intro leftResult rightResult hresult
  cases leftResult with
  | none =>
      cases rightResult with
      | none => simp [FinalizationMaterializedRunEq]
      | some rightResult => simp [FinalizationMaterializedRunEq] at hresult
  | some leftResult =>
      cases rightResult with
      | none => simp [FinalizationMaterializedRunEq] at hresult
      | some rightResult =>
          rcases leftResult with ⟨leftContext, leftFuel, leftValue, leftTable⟩
          rcases rightResult with ⟨rightContext, rightFuel, rightValue, rightTable⟩
          rcases leftValue with ⟨leftOutput, leftCache⟩
          rcases rightValue with ⟨rightOutput, rightCache⟩
          simp only [FinalizationMaterializedRunEq] at hresult
          rcases hresult with
            ⟨houtput, hcontext, hfuel, hleftTable, hrightTable, hcache, hrevealed⟩
          subst rightOutput
          subst rightFuel
          subst leftTable
          subst rightTable
          exact hnext leftOutput leftContext rightContext leftFuel leftCache
            rightCache hcontext hcache hrevealed

theorem FinalizationViewEq.ensure
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewEq table left right) (coordinate : Coordinate) :
    FinalizationViewEq table
      { left with state := left.state.ensure coordinate }
      { right with state := right.state.ensure coordinate } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change left.ValuesConsistent
    exact hview.leftConsistent
  · change right.ValuesConsistent
    exact hview.rightConsistent
  · change StartTableAgrees left.state table
    exact hview.leftStarts
  · change StartTableAgrees right.state table
    exact hview.rightStarts
  · change resolvedCompletionValue table left = resolvedCompletionValue table right
    exact hview.valueEq
  · intro other output hvalue
    change ¬left.state.hitAt other output
    apply hview.leftClean other output
    change resolvedCompletionValue table left other = some output at hvalue
    exact hvalue
  · intro other output hvalue
    change ¬right.state.hitAt other output
    apply hview.rightClean other output
    change resolvedCompletionValue table right other = some output at hvalue
    exact hvalue
  · intro other hvalue
    change left.state.pendingAt other = right.state.pendingAt other
    apply hview.pendingEq other
    change resolvedCompletionValue table left other = none at hvalue
    exact hvalue

theorem DeferredCompletable.ensure
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hcompletable : DeferredCompletable table context) (coordinate : Coordinate) :
    DeferredCompletable table
      { context with state := context.state.ensure coordinate } := by
  rcases hcompletable with ⟨completion, hcompletion⟩
  rcases hcompletion with ⟨hstate, hprivate, hpending, htable⟩
  exact ⟨completion, ⟨hstate, hprivate, hpending, htable⟩⟩

theorem finalizationMaterializedCouples_ensureCoordinate
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) :
    FinalizationMaterializedCouples table (ensureCoordinate coordinate) := by
  intro left right fuel leftCache rightCache hcontext hcache hrevealed
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  unfold ensureCoordinate
  simp only [StateT.run_liftM, LazyRevealProbe.ensureQuery, runResolvedFromTable]
  apply relTriple_pure_pure
  exact ⟨rfl,
    ⟨hview.ensure coordinate, hleftValid.ensure coordinate,
      hrightValid.ensure coordinate, hleftCompletable.ensure coordinate⟩,
    rfl, rfl, rfl, hcache, hrevealed⟩

theorem finalizationMaterializedCouples_sequenceFin
    {table : OtsSecretIndex → HashOutput} {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcomponent : ∀ position,
      FinalizationMaterializedCouples table (computation position)) :
    FinalizationMaterializedCouples table (sequenceFin computation) := by
  induction n with
  | zero =>
      simpa [sequenceFin] using
        (finalizationMaterializedCouples_pure table Fin.elim0 :
          FinalizationMaterializedCouples table
            (pure Fin.elim0 : StateT SplitHashCache
              (OracleComp (LazyRevealProbe.World Coordinate)) (Fin 0 → α)))
  | succ n ih =>
      rw [sequenceFin]
      apply (hcomponent 0).bind
      intro head
      apply (ih (fun position : Fin n => computation position.succ)
        (fun position => hcomponent position.succ)).bind
      intro tail
      exact finalizationMaterializedCouples_pure table
        (Fin.cases head tail : Fin (n + 1) → α)

theorem finalizationMaterializedCouples_splitHashQuery_ordinary
    (table : OtsSecretIndex → HashOutput) (input : HashInput) :
    FinalizationMaterializedCouples table
      (splitHashQuery (.ordinary input)) := by
  intro left right fuel leftCache rightCache hcontext hcache hrevealed
  rw [splitHashQuery_run_eq, splitHashQuery_run_eq]
  have hcacheAt : leftCache (.ordinary input) = rightCache (.ordinary input) :=
    congrFun hcache input
  cases hlookup : leftCache (.ordinary input) with
  | some output =>
      have hright : rightCache (.ordinary input) = some output := by
        rw [← hcacheAt]
        exact hlookup
      simp only [hright]
      simp [runResolvedFromTable, FinalizationMaterializedRunEq, hcontext, hcache, hrevealed]
  | none =>
      have hright : rightCache (.ordinary input) = none := by
        rw [← hcacheAt]
        exact hlookup
      simp only [hright]
      rw [LazyRevealProbe.hashOutputQuery,
        runResolvedFromTable_hashOutput_query_bind,
        runResolvedFromTable_hashOutput_query_bind]
      apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
      intro leftOutput rightOutput houtput
      subst rightOutput
      simp only [runResolvedFromTable]
      apply relTriple_pure_pure
      refine ⟨rfl, hcontext, rfl, rfl, rfl, ?_, hrevealed⟩
      rw [ordinaryQueryCache_update, ordinaryQueryCache_update, hcache]

theorem finalizationMaterializedCouples_ordinaryHashImpl
    (table : OtsSecretIndex → HashOutput) (input : HashInput) :
    FinalizationMaterializedCouples table (ordinaryHashImpl input) :=
  finalizationMaterializedCouples_splitHashQuery_ordinary table input

theorem finalizationMaterializedCouples_simulateQ
    {table : OtsSecretIndex → HashOutput} {spec : OracleSpec ι}
    (impl : QueryImpl spec
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))))
    (hquery : ∀ query, FinalizationMaterializedCouples table (impl query))
    (computation : OracleComp spec α) :
    FinalizationMaterializedCouples table (simulateQ impl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure]
      exact finalizationMaterializedCouples_pure table value
  | query_bind query next ih =>
      rw [simulateQ_query_bind]
      exact (hquery query).bind fun output => ih output

set_option maxRecDepth 100000 in
theorem finalizationMaterializedCouples_revealPosition
    (table : OtsSecretIndex → HashOutput) (position : Position) :
    FinalizationMaterializedCouples table (revealPosition position) := by
  intro left right fuel leftCache rightCache hcontext hcache hrevealed
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  rw [runResolvedFromTable_revealPosition, runResolvedFromTable_revealPosition]
  have hresolved := relTriple_resolveDeferredReveal_of_finalizationViewEq table position left
    right hview hleftValid hrightValid hleftCompletable
  have hresolvedLeft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hresolved
      (fun result => result ∈ support (resolveDeferredReveal table position left))
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
          have hleftMaterializedCompletable : DeferredCompletable table
              (materializeResolvedPosition left position leftResolved) := by
            rcases hrelation.2.2.2.2 with ⟨completion, hcompletion⟩
            exact ⟨completion,
              (deferredCompletion_materializeResolvedReveal_iff position leftResolved
                hleftValid hview.leftStarts hleftSupport).mpr hcompletion⟩
          have hrightRawCompletable :
              DeferredCompletable table rightResolved.toDeferredContext := by
            rcases hrelation.2.2.2.2 with ⟨completion, hcompletion⟩
            exact ⟨completion,
              (hrelation.2.1.deferredCompletion_iff completion).mp hcompletion⟩
          have hrightMaterializedCompletable : DeferredCompletable table
              (materializeResolvedPosition right position rightResolved) := by
            rcases hrightRawCompletable with ⟨completion, hcompletion⟩
            exact ⟨completion,
              (deferredCompletion_materializeResolvedReveal_iff position rightResolved
                hrightValid hview.rightStarts hrightSupport).mpr hcompletion⟩
          have hleftMaterializedView := finalizationViewEq_materializeResolvedReveal position
            leftResolved hleftValid hview.leftStarts hleftSupport
              hleftMaterializedCompletable
          have hrightMaterializedView := finalizationViewEq_materializeResolvedReveal position
            rightResolved hrightValid hview.rightStarts hrightSupport
              hrightMaterializedCompletable
          have hleftResultValid := hleftValid.of_resolveDeferredReveal table position
            leftResolved hleftSupport
          have hrightResultValid := hrightValid.of_resolveDeferredReveal table position
            rightResolved hrightSupport
          have hleftStateValues := resolveDeferredReveal_preserves_state_values table position
            left leftResolved hleftSupport
          have hrightStateValues := resolveDeferredReveal_preserves_state_values table position
            right rightResolved hrightSupport
          have hleftResolvedValue := resolveDeferredReveal_resolves table position left
            leftResolved hleftSupport
          have hrightResolvedValue := resolveDeferredReveal_resolves table position right
            rightResolved hrightSupport
          have hleftMaterializedValid :
              (materializeResolvedPosition left position leftResolved).Valid :=
            hleftValid.materializeResolvedPosition_of position leftResolved hleftResultValid
              hleftStateValues hleftResolvedValue
          have hrightMaterializedValid :
              (materializeResolvedPosition right position rightResolved).Valid :=
            hrightValid.materializeResolvedPosition_of position rightResolved hrightResultValid
              hrightStateValues hrightResolvedValue
          apply relTriple_pure_pure
          refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
          · simpa using congrArg truncateHash hrelation.1
          · exact ⟨hleftMaterializedView.trans
                (hrelation.2.1.trans hrightMaterializedView.symm),
              hleftMaterializedValid, hrightMaterializedValid,
              hleftMaterializedCompletable⟩
          · rw [ordinaryQueryCache_update_hidden, ordinaryQueryCache_update_hidden,
              hcache]
          · simpa [materializeResolvedPosition, LazyRevealProbe.State.materialize]
              using hrevealed

theorem finalizationMaterializedCouples_ensureFullChain
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    FinalizationMaterializedCouples table
      (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  apply (finalizationMaterializedCouples_sequenceFin
    (fun step : ChainStep =>
      ensureCoordinate (.position (.chain lay tree leafIdx chainIdx step)))
    (fun step => finalizationMaterializedCouples_ensureCoordinate table
      (.position (.chain lay tree leafIdx chainIdx step)))).bind
  intro _
  exact finalizationMaterializedCouples_pure table ()

theorem finalizationMaterializedCouples_ensureOtsLeaf
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    FinalizationMaterializedCouples table (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  apply (finalizationMaterializedCouples_sequenceFin
    (fun chainIdx : ChainIndex => ensureFullChain lay tree leafIdx chainIdx)
    (fun chainIdx => finalizationMaterializedCouples_ensureFullChain table lay tree leafIdx
      chainIdx)).bind
  intro _
  exact finalizationMaterializedCouples_ensureCoordinate table
    (.position (.leaf lay tree leafIdx))

theorem finalizationMaterializedCouples_ensureTreeNode
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx,
      FinalizationMaterializedCouples table (ensureTreeNode lay tree level nodeIdx)
  | 0, nodeIdx =>
      finalizationMaterializedCouples_ensureOtsLeaf table lay tree (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      apply (finalizationMaterializedCouples_ensureTreeNode table lay tree level
        (2 * nodeIdx)).bind
      intro _
      apply (finalizationMaterializedCouples_ensureTreeNode table lay tree level
        (2 * nodeIdx + 1)).bind
      intro _
      by_cases hlevel : level < maxLayerHeight
      · rw [dif_pos hlevel]
        exact finalizationMaterializedCouples_ensureCoordinate table
          (.position (.node lay tree ⟨level, hlevel⟩ (leafOfNat nodeIdx)))
      · rw [dif_neg hlevel]
        exact finalizationMaterializedCouples_pure table ()

theorem finalizationMaterializedCouples_maskedTreeNode
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (level nodeIdx : Nat) :
    FinalizationMaterializedCouples table (maskedTreeNode lay tree level nodeIdx) := by
  unfold maskedTreeNode
  apply (finalizationMaterializedCouples_ensureTreeNode table lay tree level nodeIdx).bind
  intro _
  cases level with
  | zero =>
      exact finalizationMaterializedCouples_revealPosition table
        (.leaf lay tree (leafOfNat nodeIdx))
  | succ current =>
      by_cases hlevel : current < maxLayerHeight
      · simp only [hlevel, ↓reduceDIte]
        exact finalizationMaterializedCouples_revealPosition table
          (.node lay tree ⟨current, hlevel⟩ (leafOfNat nodeIdx))
      · simp only [hlevel, ↓reduceDIte]
        exact finalizationMaterializedCouples_pure table 0

theorem finalizationMaterializedCouples_maskedTreeRoot
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) :
    FinalizationMaterializedCouples table (maskedTreeRoot lay tree) := by
  unfold maskedTreeRoot
  exact finalizationMaterializedCouples_maskedTreeNode table lay tree (layerHeight lay) 0

theorem finalizationMaterializedCouples_ensureChainPrefix
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (digit : Digit) :
    FinalizationMaterializedCouples table
      (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  unfold ensureChainPrefix
  apply (finalizationMaterializedCouples_sequenceFin
    (fun step : ChainStep =>
      if step.val < digit.val then
        ensureCoordinate (.position (.chain lay tree leafIdx chainIdx step))
      else pure ())
    (fun step => by
      by_cases hstep : step.val < digit.val
      · rw [if_pos hstep]
        exact finalizationMaterializedCouples_ensureCoordinate table
          (.position (.chain lay tree leafIdx chainIdx step))
      · rw [if_neg hstep]
        exact finalizationMaterializedCouples_pure table ())).bind
  intro _
  exact finalizationMaterializedCouples_pure table ()

theorem finalizationMaterializedCouples_ensureTreePath
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    FinalizationMaterializedCouples table (ensureTreePath lay tree leafIdx) := by
  unfold ensureTreePath
  apply (finalizationMaterializedCouples_sequenceFin
    (fun level : Fin maxLayerHeight =>
      if level.val < layerHeight lay then
        ensureTreeNode lay tree level.val
          (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
      else pure ())
    (fun level => by
      by_cases hlevel : level.val < layerHeight lay
      · rw [if_pos hlevel]
        exact finalizationMaterializedCouples_ensureTreeNode table lay tree level.val
          (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
      · rw [if_neg hlevel]
        exact finalizationMaterializedCouples_pure table ())).bind
  intro _
  exact finalizationMaterializedCouples_pure table ()

theorem finalizationMaterializedCouples_maskedOtsSignFrom
    (table : OtsSecretIndex → HashOutput) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    ∀ attempts counter,
      FinalizationMaterializedCouples table
        (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
  | 0, counter => by
      rw [maskedOtsSignFrom]
      exact finalizationMaterializedCouples_pure table none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom]
      have hencoded := finalizationMaterializedCouples_simulateQ ordinaryHashImpl
        (finalizationMaterializedCouples_ordinaryHashImpl table)
        (encode parameter lay tree leafIdx message
          (BitVec.ofNat counterBits counter))
      apply hencoded.bind
      intro encoded
      cases encoded with
      | none =>
          exact finalizationMaterializedCouples_maskedOtsSignFrom table parameter lay tree
            leafIdx message attempts (counter + 1)
      | some encoding =>
          apply (finalizationMaterializedCouples_sequenceFin
            (fun chainIdx => ensureChainPrefix lay tree leafIdx chainIdx
              (encoding chainIdx))
            (fun chainIdx => finalizationMaterializedCouples_ensureChainPrefix table lay tree
              leafIdx chainIdx (encoding chainIdx))).bind
          intro _
          exact finalizationMaterializedCouples_pure table
            (some (BitVec.ofNat counterBits counter, encoding))

theorem finalizationMaterializedCouples_maskedOtsSign
    (table : OtsSecretIndex → HashOutput) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    FinalizationMaterializedCouples table
      (maskedOtsSign parameter lay tree leafIdx message) :=
  finalizationMaterializedCouples_maskedOtsSignFrom table parameter lay tree leafIdx message
    encodingAttemptLimit 0

theorem finalizationMaterializedCouples_maskedLayerMessage
    (table : OtsSecretIndex → HashOutput) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay : Layer) :
    FinalizationMaterializedCouples table
      (maskedLayerMessage parameter ftsSecret index lay) := by
  unfold maskedLayerMessage
  by_cases hbelow : lay.val + 1 < numLayers
  · rw [dif_pos hbelow]
    exact finalizationMaterializedCouples_maskedTreeRoot table ⟨lay.val + 1, hbelow⟩
      (treeIndexAt index ⟨lay.val + 1, hbelow⟩)
  · rw [dif_neg hbelow]
    exact finalizationMaterializedCouples_simulateQ ordinaryHashImpl
      (finalizationMaterializedCouples_ordinaryHashImpl table)
      (ftsKey parameter index (ftsSecret index))

theorem finalizationMaterializedCouples_maskedSignLayer
    (table : OtsSecretIndex → HashOutput) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay : Layer) :
    FinalizationMaterializedCouples table
      (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayer
  apply (finalizationMaterializedCouples_maskedLayerMessage table parameter ftsSecret index
    lay).bind
  intro message
  apply (finalizationMaterializedCouples_maskedOtsSign table parameter lay
    (treeIndexAt index lay) (leafIndexAt index lay) message).bind
  intro selected
  cases selected with
  | none => exact finalizationMaterializedCouples_pure table none
  | some selected =>
      apply (finalizationMaterializedCouples_ensureTreePath table lay
        (treeIndexAt index lay) (leafIndexAt index lay)).bind
      intro _
      exact finalizationMaterializedCouples_pure table (some selected)

noncomputable def privateChronologicalSignLayer
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay : Layer) (context : DeferredContext) (fuel : Nat)
    (store : DeferredLayerStore) :
    ProbComp (Option (ResolvedRunResult DeferredLayerStore)) := do
  let selected ← runResolvedFromTable context fuel table
    ((maskedSignLayer parameter ftsSecret index lay).run store.cache)
  match selected with
  | none => pure none
  | some selected =>
      match selected.value.1 with
      | none => pure (some ⟨selected.context, selected.remaining,
          { selected := Function.update store.selected lay none
            resolved := Function.update store.resolved lay none
            cache := selected.value.2 }, table⟩)
      | some (counter, encoding) => do
          let resolved ← resolveDeferredLayerValues table index lay encoding
            selected.context
          match resolved with
          | none => pure none
          | some (finalContext, values) =>
              pure (some ⟨finalContext, selected.remaining,
                { selected := Function.update store.selected lay
                    (some (counter, encoding))
                  resolved := Function.update store.resolved lay
                    (some (counter, values.1, values.2))
                  cache := selected.value.2 }, table⟩)

def FinalizationChronologicalLayerEq
    (table : OtsSecretIndex → HashOutput) (lay : Layer)
    (initialStore : DeferredLayerStore) :
    Option (ResolvedRunResult (Option ChronologicalLayerPart × SplitHashCache)) →
      Option (ResolvedRunResult DeferredLayerStore) → Prop
  | none, none => True
  | some left, some right =>
      FinalizationContextEq table (some left.context) (some right.context) ∧
        left.remaining = right.remaining ∧ left.table = table ∧ right.table = table ∧
        right.value.selected = Function.update initialStore.selected lay
          (left.value.1.map fun part => (part.counter, part.encoding)) ∧
        right.value.resolved = Function.update initialStore.resolved lay
          (left.value.1.map ChronologicalLayerPart.toLayerPart) ∧
        ordinaryQueryCache left.value.2 = ordinaryQueryCache right.value.cache ∧
        left.context.state.revealed = right.context.state.revealed
  | _, _ => False

set_option maxRecDepth 100000 in
theorem relTriple_runResolvedFromTable_maskedChronologicalSignLayer_finalization
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay : Layer) (left right : DeferredContext) (fuel : Nat)
    (leftCache : SplitHashCache) (store : DeferredLayerStore)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache store.cache)
    (hrevealed : left.state.revealed = right.state.revealed) :
    RelTriple
      (runResolvedFromTable left fuel table
        ((maskedChronologicalSignLayer parameter ftsSecret index lay).run leftCache))
      (privateChronologicalSignLayer parameter table ftsSecret index lay right fuel store)
      (FinalizationChronologicalLayerEq table lay store) := by
  rw [maskedChronologicalSignLayer, StateT.run_bind, runResolvedFromTable_bind]
  unfold privateChronologicalSignLayer
  have hselected := finalizationMaterializedCouples_maskedSignLayer table parameter ftsSecret
    index lay left right fuel leftCache store.cache hcontext hcache hrevealed
  apply relTriple_bind hselected
  intro leftSelected rightSelected hselectedRelation
  cases leftSelected with
  | none =>
      cases rightSelected with
      | none => simp [FinalizationChronologicalLayerEq]
      | some rightSelected => simp [FinalizationMaterializedRunEq] at hselectedRelation
  | some leftSelected =>
      cases rightSelected with
      | none => simp [FinalizationMaterializedRunEq] at hselectedRelation
      | some rightSelected =>
          rcases hselectedRelation with
            ⟨hselection, hselectedContext, hremaining, hleftTable, hrightTable,
              hselectedCache, hselectedRevealed⟩
          simp only
          rw [← hselection]
          cases selected : leftSelected.value.1 with
          | none =>
              simp only
              apply relTriple_pure_pure
              simp [FinalizationChronologicalLayerEq, hselectedContext, hremaining,
                hleftTable, hselectedCache, hselectedRevealed]
          | some selectedPart =>
              rcases selectedPart with ⟨counter, encoding⟩
              simp only
              rw [hremaining, hleftTable]
              rw [StateT.run_bind, runResolvedFromTable_bind]
              have hvaluesBase :=
                relTriple_runResolvedFromTable_revealPrivateLayerValues_of_finalizationViewEq
                  table index lay encoding leftSelected.context rightSelected.context
                  rightSelected.remaining leftSelected.value.2 hselectedContext.1
                  hselectedContext.2.1 hselectedContext.2.2.1 hselectedContext.2.2.2
              have hvaluesLeft :=
                SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support
                  hvaluesBase
                  (fun result => result ∈ support
                    (runResolvedFromTable leftSelected.context rightSelected.remaining table
                      ((revealPrivateLayerValues index lay encoding).run
                        leftSelected.value.2)))
                  (fun result hresult => hresult)
              have hvalues :=
                SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hvaluesLeft
              apply relTriple_bind hvalues
              intro leftValues rightValues hvaluesRelation
              rcases hvaluesRelation with
                ⟨⟨hvaluesRelation, hleftValuesSupport⟩, hrightValuesSupport⟩
              cases leftValues with
              | none =>
                  cases rightValues with
                  | none => simp [FinalizationChronologicalLayerEq]
                  | some rightValues =>
                      simp [FinalizationRunContextValueEq] at hvaluesRelation
              | some leftValues =>
                  cases rightValues with
                  | none => simp [FinalizationRunContextValueEq] at hvaluesRelation
                  | some rightValues =>
                      apply relTriple_pure_pure
                      refine ⟨hvaluesRelation.2.1, hvaluesRelation.2.2.1,
                        hvaluesRelation.2.2.2.1, rfl, ?_, ?_, ?_, ?_⟩
                      · funext selectedLay
                        by_cases heq : selectedLay = lay
                        · subst selectedLay
                          simp
                        · simp [Function.update_of_ne heq]
                      · funext resolvedLay
                        by_cases heq : resolvedLay = lay
                        · subst resolvedLay
                          simp [ChronologicalLayerPart.toLayerPart,
                            hvaluesRelation.1]
                        · simp [Function.update_of_ne heq]
                      · exact hvaluesRelation.2.2.2.2.trans hselectedCache
                      · have hleftValuesRevealed :=
                          revealed_eq_of_mem_runResolvedFromTable_of_noPublish
                            ((revealPrivateLayerValues index lay encoding).run
                              leftSelected.value.2)
                            leftSelected.context rightSelected.remaining table leftValues
                            (noPublish_revealPrivateLayerValues index lay encoding
                              leftSelected.value.2)
                            hleftValuesSupport
                        have hrightValuesRevealed :=
                          (privateStateAgrees_resolveDeferredLayerValues table index lay encoding
                            rightSelected.context rightValues.1 rightValues.2
                            hrightValuesSupport).2.1
                        exact hleftValuesRevealed.trans
                          (hselectedRevealed.trans hrightValuesRevealed.symm)

theorem privateChronologicalSignLayer_eq_schedule
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay : Layer) (context : DeferredContext) (fuel : Nat)
    (store : DeferredLayerStore) :
    privateChronologicalSignLayer parameter table ftsSecret index lay context fuel store =
      runDeferredLayerSchedule parameter table ftsSecret index
        [.select lay, .resolve lay] (some ⟨context, fuel, store, table⟩) := by
  unfold privateChronologicalSignLayer
  simp only [runDeferredLayerSchedule, runDeferredLayerOperation, selectDeferredLayer,
    bind_assoc]
  apply bind_congr
  intro selectedOption
  cases selectedOption with
  | none => rfl
  | some selected =>
      simp only [pure_bind]
      cases hselected : selected.value.1 with
      | none => simp [resolveDeferredLayer]
      | some selectedPart =>
          rcases selectedPart with ⟨counter, encoding⟩
          simp only [resolveDeferredLayer, Function.update_self, bind_assoc]
          apply bind_congr
          intro resolvedOption
          cases resolvedOption <;> rfl

def chronologicalSelectedAfter : ∀ {n : Nat}, (Fin n → Layer) →
    (Fin n → Option ChronologicalLayerPart) →
    (Layer → Option DeferredLayerEncoding) →
      Layer → Option DeferredLayerEncoding
  | 0, _, _, selected => selected
  | n + 1, family, parts, selected =>
      chronologicalSelectedAfter
        (fun position : Fin n => family position.succ)
        (fun position : Fin n => parts position.succ)
        (Function.update selected (family 0)
          ((parts 0).map fun part => (part.counter, part.encoding)))

def chronologicalResolvedAfter : ∀ {n : Nat}, (Fin n → Layer) →
    (Fin n → Option ChronologicalLayerPart) →
    (Layer → Option LayerPart) → Layer → Option LayerPart
  | 0, _, _, resolved => resolved
  | n + 1, family, parts, resolved =>
      chronologicalResolvedAfter
        (fun position : Fin n => family position.succ)
        (fun position : Fin n => parts position.succ)
        (Function.update resolved (family 0)
          ((parts 0).map ChronologicalLayerPart.toLayerPart))

noncomputable def privateChronologicalLayerFamily
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) :
    ∀ {n : Nat}, (Fin n → Layer) →
      Option (ResolvedRunResult DeferredLayerStore) →
        ProbComp (Option (ResolvedRunResult DeferredLayerStore))
  | 0, _, input => pure input
  | n + 1, family, input =>
      match input with
      | none => pure none
      | some result => do
          let head ← privateChronologicalSignLayer parameter table ftsSecret index
            (family 0) result.context result.remaining result.value
          privateChronologicalLayerFamily parameter table ftsSecret index
            (fun position : Fin n => family position.succ) head

def FinalizationChronologicalFamilyEq
    (table : OtsSecretIndex → HashOutput) (family : Fin n → Layer)
    (initialStore : DeferredLayerStore) :
    Option (ResolvedRunResult ((Fin n → Option ChronologicalLayerPart) ×
      SplitHashCache)) → Option (ResolvedRunResult DeferredLayerStore) → Prop
  | none, none => True
  | some left, some right =>
      FinalizationContextEq table (some left.context) (some right.context) ∧
        left.remaining = right.remaining ∧ left.table = table ∧ right.table = table ∧
        right.value.selected =
          chronologicalSelectedAfter family left.value.1 initialStore.selected ∧
        right.value.resolved =
          chronologicalResolvedAfter family left.value.1 initialStore.resolved ∧
        ordinaryQueryCache left.value.2 = ordinaryQueryCache right.value.cache ∧
        left.context.state.revealed = right.context.state.revealed
  | _, _ => False

set_option maxRecDepth 100000 in
theorem relTriple_runResolvedSequenceFin_maskedChronologicalLayerFamily_finalization
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) :
    ∀ {n : Nat} (family : Fin n → Layer) (left right : DeferredContext)
      (fuel : Nat) (leftCache : SplitHashCache) (store : DeferredLayerStore),
      FinalizationContextEq table (some left) (some right) →
      ordinaryQueryCache leftCache = ordinaryQueryCache store.cache →
      left.state.revealed = right.state.revealed →
      RelTriple
        (runResolvedSequenceFin
          (fun position => maskedChronologicalSignLayer parameter ftsSecret index
            (family position)) left fuel table leftCache)
        (privateChronologicalLayerFamily parameter table ftsSecret index family
          (some ⟨right, fuel, store, table⟩))
        (FinalizationChronologicalFamilyEq table family store)
  | 0, family, left, right, fuel, leftCache, store, hcontext, hcache, hrevealed => by
      simp [runResolvedSequenceFin, privateChronologicalLayerFamily,
        FinalizationChronologicalFamilyEq, chronologicalSelectedAfter,
        chronologicalResolvedAfter, hcontext, hcache, hrevealed]
  | n + 1, family, left, right, fuel, leftCache, store, hcontext, hcache, hrevealed => by
      rw [runResolvedSequenceFin, privateChronologicalLayerFamily]
      have hhead :=
        relTriple_runResolvedFromTable_maskedChronologicalSignLayer_finalization parameter table
          ftsSecret index (family 0) left right fuel leftCache store hcontext hcache hrevealed
      apply relTriple_bind hhead
      intro leftHead rightHead hheadRelation
      cases leftHead with
      | none =>
          cases rightHead with
          | none =>
              simp only
              have hnone :
                  privateChronologicalLayerFamily parameter table ftsSecret index
                    (fun position : Fin n => family position.succ) none = pure none := by
                cases n <;> rfl
              rw [hnone]
              apply relTriple_pure_pure
              simp [FinalizationChronologicalFamilyEq]
          | some rightHead => simp [FinalizationChronologicalLayerEq] at hheadRelation
      | some leftHead =>
          cases rightHead with
          | none => simp [FinalizationChronologicalLayerEq] at hheadRelation
          | some rightHead =>
              rcases leftHead with
                ⟨leftContext, leftRemaining, ⟨leftPart, leftCache⟩, leftTable⟩
              rcases rightHead with
                ⟨rightContext, rightRemaining, rightStore, rightTable⟩
              simp only [FinalizationChronologicalLayerEq] at hheadRelation
              rcases hheadRelation with
                ⟨hcontext, hremaining, hleftTable, hrightTable, hselected,
                  hresolved, hcache, hrevealed⟩
              subst leftRemaining
              subst leftTable
              subst rightTable
              simp only
              have htail :=
                relTriple_runResolvedSequenceFin_maskedChronologicalLayerFamily_finalization
                  parameter table ftsSecret index
                  (fun position : Fin n => family position.succ) leftContext
                  rightContext rightRemaining leftCache rightStore hcontext hcache hrevealed
              rw [← bind_pure
                (privateChronologicalLayerFamily parameter table ftsSecret index
                  (fun position : Fin n => family position.succ)
                  (some ⟨rightContext, rightRemaining, rightStore, table⟩))]
              apply relTriple_bind htail
              intro leftTail rightTail htailRelation
              cases leftTail with
              | none =>
                  cases rightTail with
                  | none => simp [FinalizationChronologicalFamilyEq]
                  | some rightTail =>
                      simp [FinalizationChronologicalFamilyEq] at htailRelation
              | some leftTail =>
                  cases rightTail with
                  | none => simp [FinalizationChronologicalFamilyEq] at htailRelation
                  | some rightTail =>
                      apply relTriple_pure_pure
                      refine ⟨htailRelation.1, htailRelation.2.1,
                        rfl, htailRelation.2.2.2.1, ?_, ?_,
                        htailRelation.2.2.2.2.2.2.1,
                        htailRelation.2.2.2.2.2.2.2⟩
                      · simpa [chronologicalSelectedAfter, hselected] using
                          htailRelation.2.2.2.2.1
                      · simpa [chronologicalResolvedAfter, hresolved] using
                          htailRelation.2.2.2.2.2.1

def chronologicalFamilySchedule : ∀ {n : Nat},
    (Fin n → Layer) → List DeferredLayerOperation
  | 0, _ => []
  | n + 1, family =>
      [.select (family 0), .resolve (family 0)] ++
        chronologicalFamilySchedule (fun position : Fin n => family position.succ)

theorem privateChronologicalLayerFamily_eq_schedule
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) :
    ∀ {n : Nat} (family : Fin n → Layer)
      (input : Option (ResolvedRunResult DeferredLayerStore)),
      privateChronologicalLayerFamily parameter table ftsSecret index family input =
        runDeferredLayerSchedule parameter table ftsSecret index
          (chronologicalFamilySchedule family) input
  | 0, family, input => by
      simp [privateChronologicalLayerFamily, chronologicalFamilySchedule,
        runDeferredLayerSchedule]
  | n + 1, family, input => by
      cases input with
      | none =>
          simp [privateChronologicalLayerFamily, chronologicalFamilySchedule,
            runDeferredLayerSchedule_none]
      | some result =>
          rw [privateChronologicalLayerFamily, chronologicalFamilySchedule,
            runDeferredLayerSchedule_append,
            privateChronologicalSignLayer_eq_schedule]
          apply bind_congr
          intro head
          exact privateChronologicalLayerFamily_eq_schedule parameter table ftsSecret index
            (fun position : Fin n => family position.succ) head

theorem chronologicalFamilySchedule_layers :
    chronologicalFamilySchedule (fun lay : Layer => lay) = chronologicalLayerSchedule := by
  rfl

theorem relTriple_runResolvedSequenceFin_maskedChronologicalSignLayers_schedule_finalization
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (left right : DeferredContext) (fuel : Nat) (leftCache : SplitHashCache)
    (store : DeferredLayerStore)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache store.cache)
    (hrevealed : left.state.revealed = right.state.revealed) :
    RelTriple
      (runResolvedSequenceFin
        (fun lay : Layer => maskedChronologicalSignLayer parameter ftsSecret index lay)
        left fuel table leftCache)
      (runDeferredLayerSchedule parameter table ftsSecret index chronologicalLayerSchedule
        (some ⟨right, fuel, store, table⟩))
      (FinalizationChronologicalFamilyEq table (fun lay : Layer => lay) store) := by
  rw [← chronologicalFamilySchedule_layers,
    ← privateChronologicalLayerFamily_eq_schedule parameter table ftsSecret index]
  exact relTriple_runResolvedSequenceFin_maskedChronologicalLayerFamily_finalization
    parameter table ftsSecret index (fun lay : Layer => lay) left right fuel leftCache store
      hcontext hcache hrevealed

end SphincsSecurity.Concrete.OtsProbeSimulation
