import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveNormalizedSigner

/-!
# Exact reverse signer coupling

A probe-free signer preserves the full finalization view between a deferred execution and its
materialized shadow. Successful runs agree on outputs, caches, revealed coordinates and materialized
values while retaining both independent probe-fuel counters exactly.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def DeferredStructuralValuesLE
    (left right : DeferredStructuralValues) : Prop :=
  ∀ position output, left position = some output → right position = some output

theorem DeferredStructuralValuesLE.refl (values : DeferredStructuralValues) :
    DeferredStructuralValuesLE values values := by
  intro position output hvalue
  exact hvalue

theorem DeferredStructuralValuesLE.trans
    {left middle right : DeferredStructuralValues}
    (hleft : DeferredStructuralValuesLE left middle)
    (hright : DeferredStructuralValuesLE middle right) :
    DeferredStructuralValuesLE left right := by
  intro position output hvalue
  exact hright position output (hleft position output hvalue)

theorem DeferredStructuralValuesLE.install_of_none
    {values : DeferredStructuralValues} {position : Position} {installed : HashOutput}
    (hmissing : values position = none) :
    DeferredStructuralValuesLE values (values.install position installed) := by
  intro other output hvalue
  have hne : other ≠ position := by
    intro heq
    subst other
    rw [hmissing] at hvalue
    contradiction
  simpa [DeferredStructuralValues.install, hne] using hvalue

def DirectWitnessFinalizationMaterializedRunEq
    (table : OtsSecretIndex → HashOutput) (initialValues : DeferredStructuralValues)
    (leftInitialFuel rightInitialFuel : Nat) :
    DirectWitnessResult (α × SplitHashCache) →
      DirectDetailedResult (α × SplitHashCache) → Prop
  | .done left, .done right =>
      left.value.1 = right.value.1 ∧
        FinalizationContextEq table (some left.context) (some right.context) ∧
        left.remaining = leftInitialFuel ∧ right.remaining = rightInitialFuel ∧
        left.table = table ∧ right.table = table ∧
        left.value.2 = right.value.2 ∧
        left.context.state.revealed = right.context.state.revealed ∧
        (materializedDeferredState left.context).values = right.context.state.values ∧
        DeferredStructuralValuesLE initialValues left.context.values ∧
        right.context = directDeferredContext right.context.state
  | .done _, .stopped _ => False
  | _, _ => True

def DirectWitnessFinalizationMaterializedCouples
    (table : OtsSecretIndex → HashOutput)
  (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ left right leftFuel rightFuel leftCache rightCache,
    FinalizationContextEq table (some left) (some right) →
    leftCache = rightCache →
    left.state.revealed = right.state.revealed →
    (materializedDeferredState left).values = right.state.values →
    right = directDeferredContext right.state →
    RelTriple
      (runDirectResolvedWitnessFromTable left leftFuel table (computation.run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table (computation.run rightCache))
      (DirectWitnessFinalizationMaterializedRunEq table left.values leftFuel rightFuel)

theorem materializedDeferredState_ensure
    (context : DeferredContext) (coordinate : Coordinate) :
    materializedDeferredState
        { context with state := context.state.ensure coordinate } =
      (materializedDeferredState context).ensure coordinate := by
  rcases context with ⟨state, values⟩
  rcases state with ⟨pending, stateValues, revealed, ensured⟩
  simp [materializedDeferredState, DeferredContext.positionValue,
    LazyRevealProbe.State.ensure]

theorem materializedDeferredState_publish
    (context : DeferredContext) (coordinate : Coordinate) :
    materializedDeferredState
        { context with state := context.state.publish coordinate } =
      (materializedDeferredState context).publish coordinate := by
  rcases context with ⟨state, values⟩
  rcases state with ⟨pending, stateValues, revealed, ensured⟩
  simp [materializedDeferredState, DeferredContext.positionValue,
    LazyRevealProbe.State.publish]

@[simp] theorem materializedDeferredState_directDeferredContext
    (state : LazyRevealProbe.State Coordinate) :
    materializedDeferredState (directDeferredContext state) = state := by
  rcases state with ⟨pending, values, revealed, ensured⟩
  simp only [materializedDeferredState, directDeferredContext,
    directDeferredValues, DeferredContext.positionValue]
  congr
  funext coordinate
  cases coordinate with
  | chainStart => rfl
  | position position =>
      change (match values (.position position) with
        | some output => some output
        | none => values (.position position)) = values (.position position)
      cases values (.position position) <;> rfl

theorem materializedDeferredState_values_materialize_position_of_private
    (context : DeferredContext) (position : Position) (output : HashOutput)
    (hconsistent : context.ValuesConsistent)
    (hprivate : context.values position = some output) :
    (materializedDeferredState
      { context with state := context.state.materialize (.position position) output }).values =
      (materializedDeferredState context).values := by
  funext coordinate
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      simp [materializedDeferredState, LazyRevealProbe.State.materialize,
        Function.update_of_ne]
  | position other =>
      by_cases heq : other = position
      · subst other
        cases hvalue : context.state.values (.position position) with
        | none =>
            simp [materializedDeferredState, DeferredContext.positionValue,
              LazyRevealProbe.State.materialize, hprivate, hvalue]
        | some cached =>
            have hcached := hconsistent position cached hvalue
            rw [hprivate] at hcached
            have hsame : output = cached := Option.some.inj hcached
            subst cached
            simp [materializedDeferredState, DeferredContext.positionValue,
              LazyRevealProbe.State.materialize, hprivate, hvalue]
      · simp [materializedDeferredState, DeferredContext.positionValue,
          LazyRevealProbe.State.materialize, Function.update_of_ne,
          show Coordinate.position other ≠ Coordinate.position position by simpa using heq,
          heq]

theorem materializedDeferredState_values_materialize_position_install
    (context : DeferredContext) (position : Position) (output : HashOutput) :
    (materializedDeferredState
      { state := context.state.materialize (.position position) output
        values := context.values.install position output }).values =
      Function.update (materializedDeferredState context).values
        (.position position) (some output) := by
  funext coordinate
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      simp [materializedDeferredState, LazyRevealProbe.State.materialize,
        Function.update_of_ne]
  | position other =>
      by_cases heq : other = position
      · subst other
        simp [materializedDeferredState, DeferredContext.positionValue,
          LazyRevealProbe.State.materialize, DeferredStructuralValues.install]
      · simp [materializedDeferredState, DeferredContext.positionValue,
          LazyRevealProbe.State.materialize, Function.update_of_ne,
          show Coordinate.position other ≠ Coordinate.position position by simpa using heq,
          DeferredStructuralValues.install, heq]

theorem materializedDeferredState_values_materialize_chainStart
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (index : OtsSecretIndex) :
    (materializedDeferredState
      { context with state := context.state.materialize index.coordinate (table index) }).values =
      Function.update (materializedDeferredState context).values index.coordinate
        (some (table index)) := by
  rcases index with ⟨indexLay, indexTree, indexLeaf, indexChain⟩
  change
    (materializedDeferredState
      { context with state := (context.state.materialize
          (.chainStart indexLay indexTree indexLeaf indexChain)
          (table ⟨indexLay, indexTree, indexLeaf, indexChain⟩)) }).values =
      Function.update (materializedDeferredState context).values
        (.chainStart indexLay indexTree indexLeaf indexChain)
        (some (table ⟨indexLay, indexTree, indexLeaf, indexChain⟩))
  funext coordinate
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      by_cases heq : Coordinate.chainStart lay tree leafIdx chainIdx =
          Coordinate.chainStart indexLay indexTree indexLeaf indexChain
      · rw [heq]
        simp [materializedDeferredState, LazyRevealProbe.State.materialize]
      · simp [materializedDeferredState, LazyRevealProbe.State.materialize,
          Function.update_of_ne heq]
  | position position =>
      simp [materializedDeferredState, DeferredContext.positionValue,
        LazyRevealProbe.State.materialize, OtsSecretIndex.coordinate]

set_option maxRecDepth 100000 in
theorem FinalizationContextEq.materialize_position_left_of_right_value
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextEq table (some left) (some right))
    (position : Position) (output : HashOutput)
    (hleftHidden : left.state.values (.position position) = none)
    (hleftPrivate : left.values position = some output) :
    FinalizationContextEq table
      (some { left with state := left.state.materialize (.position position) output })
      (some right) := by
  have hle := (FinalizationContextLE.of_eq hcontext).materialize_position_left
    position output hleftHidden hleftPrivate
  refine ⟨{
    leftConsistent := hle.view.leftConsistent
    rightConsistent := hle.view.rightConsistent
    leftStarts := hle.view.leftStarts
    rightStarts := hle.view.rightStarts
    valueEq := hle.view.valueEq
    leftClean := hle.view.leftClean
    rightClean := hle.view.rightClean
    pendingEq := ?_ }, hle.leftValid, hle.rightValid, hle.leftCompletable⟩
  intro coordinate hnone
  have hne : coordinate ≠ .position position := by
    intro heq
    subst coordinate
    simp [resolvedCompletionValue, DeferredContext.positionValue,
      LazyRevealProbe.State.materialize] at hnone
  have hrightNone : resolvedCompletionValue table right coordinate = none := by
    rw [← hle.view.valueEq]
    exact hnone
  have hleftNone : resolvedCompletionValue table left coordinate = none := by
    rw [hcontext.1.valueEq]
    exact hrightNone
  change (left.state.clearPending (.position position)).pendingAt coordinate =
    right.state.pendingAt coordinate
  rw [pendingAt_clearPending_of_ne left.state (.position position) coordinate hne]
  exact hcontext.1.pendingEq coordinate hleftNone

set_option maxRecDepth 100000 in
theorem FinalizationContextEq.materialize_position_both
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextEq table (some left) (some right))
    (position : Position) (output : HashOutput) :
    FinalizationContextEq table
      (some { state := left.state.materialize (.position position) output
              values := left.values.install position output })
      (some { state := right.state.materialize (.position position) output
              values := right.values.install position output }) := by
  have hle := (FinalizationContextLE.of_eq hcontext).materialize_position_both position output
  refine ⟨{
    leftConsistent := hle.view.leftConsistent
    rightConsistent := hle.view.rightConsistent
    leftStarts := hle.view.leftStarts
    rightStarts := hle.view.rightStarts
    valueEq := hle.view.valueEq
    leftClean := hle.view.leftClean
    rightClean := hle.view.rightClean
    pendingEq := ?_ }, hle.leftValid, hle.rightValid, hle.leftCompletable⟩
  intro coordinate hnone
  have hne : coordinate ≠ .position position := by
    intro heq
    subst coordinate
    simp [resolvedCompletionValue, DeferredContext.positionValue,
      LazyRevealProbe.State.materialize] at hnone
  change (left.state.clearPending (.position position)).pendingAt coordinate =
    (right.state.clearPending (.position position)).pendingAt coordinate
  rw [pendingAt_clearPending_of_ne left.state (.position position) coordinate hne,
    pendingAt_clearPending_of_ne right.state (.position position) coordinate hne]
  have hleftNone : resolvedCompletionValue table left coordinate = none := by
    cases coordinate with
    | chainStart => exact hnone
    | position other =>
        have hother : other ≠ position := by simpa using hne
        simpa [resolvedCompletionValue, DeferredContext.positionValue,
          LazyRevealProbe.State.materialize, Function.update_of_ne,
          show Coordinate.position other ≠ Coordinate.position position by simpa using hother,
          DeferredStructuralValues.install, hother] using hnone
  exact hcontext.1.pendingEq coordinate hleftNone

set_option maxRecDepth 100000 in
theorem FinalizationContextEq.materialize_chainStart_left
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextEq table (some left) (some right))
    (index : OtsSecretIndex) :
    FinalizationContextEq table
      (some { left with state := left.state.materialize index.coordinate (table index) })
      (some right) := by
  have hle := (FinalizationContextLE.of_eq hcontext).materialize_chainStart_left index
  refine ⟨{
    leftConsistent := hle.view.leftConsistent
    rightConsistent := hle.view.rightConsistent
    leftStarts := hle.view.leftStarts
    rightStarts := hle.view.rightStarts
    valueEq := hle.view.valueEq
    leftClean := hle.view.leftClean
    rightClean := hle.view.rightClean
    pendingEq := ?_ }, hle.leftValid, hle.rightValid, hle.leftCompletable⟩
  intro coordinate hnone
  have hne : coordinate ≠ index.coordinate := by
    intro heq
    subst coordinate
    rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
    simp [resolvedCompletionValue, OtsSecretIndex.coordinate] at hnone
  have hrightNone : resolvedCompletionValue table right coordinate = none := by
    rw [← hle.view.valueEq]
    exact hnone
  have hleftNone : resolvedCompletionValue table left coordinate = none := by
    rw [hcontext.1.valueEq]
    exact hrightNone
  change (left.state.clearPending index.coordinate).pendingAt coordinate =
    right.state.pendingAt coordinate
  rw [pendingAt_clearPending_of_ne left.state index.coordinate coordinate hne]
  exact hcontext.1.pendingEq coordinate hleftNone

set_option maxRecDepth 100000 in
theorem FinalizationContextEq.materialize_chainStart_right
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextEq table (some left) (some right))
    (index : OtsSecretIndex) :
    FinalizationContextEq table
      (some left)
      (some { right with state := right.state.materialize index.coordinate (table index) }) := by
  have hle := (FinalizationContextLE.of_eq hcontext).materialize_chainStart_right index
  refine ⟨{
    leftConsistent := hle.view.leftConsistent
    rightConsistent := hle.view.rightConsistent
    leftStarts := hle.view.leftStarts
    rightStarts := hle.view.rightStarts
    valueEq := hle.view.valueEq
    leftClean := hle.view.leftClean
    rightClean := hle.view.rightClean
    pendingEq := ?_ }, hle.leftValid, hle.rightValid, hle.leftCompletable⟩
  intro coordinate hnone
  have hne : coordinate ≠ index.coordinate := by
    intro heq
    subst coordinate
    rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
    simp [resolvedCompletionValue, OtsSecretIndex.coordinate] at hnone
  change left.state.pendingAt coordinate =
    (right.state.clearPending index.coordinate).pendingAt coordinate
  rw [pendingAt_clearPending_of_ne right.state index.coordinate coordinate hne]
  exact hcontext.1.pendingEq coordinate hnone

set_option maxRecDepth 100000 in
theorem FinalizationContextEq.materialize_chainStart_both
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextEq table (some left) (some right))
    (index : OtsSecretIndex) :
    FinalizationContextEq table
      (some { left with state := left.state.materialize index.coordinate (table index) })
      (some { right with state := right.state.materialize index.coordinate (table index) }) := by
  have hle := (FinalizationContextLE.of_eq hcontext).materialize_chainStart_both index
  refine ⟨{
    leftConsistent := hle.view.leftConsistent
    rightConsistent := hle.view.rightConsistent
    leftStarts := hle.view.leftStarts
    rightStarts := hle.view.rightStarts
    valueEq := hle.view.valueEq
    leftClean := hle.view.leftClean
    rightClean := hle.view.rightClean
    pendingEq := ?_ }, hle.leftValid, hle.rightValid, hle.leftCompletable⟩
  intro coordinate hnone
  have hne : coordinate ≠ index.coordinate := by
    intro heq
    subst coordinate
    rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
    simp [resolvedCompletionValue, OtsSecretIndex.coordinate] at hnone
  change (left.state.clearPending index.coordinate).pendingAt coordinate =
    (right.state.clearPending index.coordinate).pendingAt coordinate
  rw [pendingAt_clearPending_of_ne left.state index.coordinate coordinate hne,
    pendingAt_clearPending_of_ne right.state index.coordinate coordinate hne]
  have hleftNone : resolvedCompletionValue table left coordinate = none := by
    cases coordinate with
    | chainStart => exact hnone
    | position position =>
        simpa [resolvedCompletionValue, DeferredContext.positionValue,
          LazyRevealProbe.State.materialize, OtsSecretIndex.coordinate] using hnone
  exact hcontext.1.pendingEq coordinate hleftNone

theorem completionSafeStateEq_materialized_right_of_finalizationContextEq
    (table : OtsSecretIndex → HashOutput) (left right : DeferredContext)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hvalues : (materializedDeferredState left).values = right.state.values)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hright : right = directDeferredContext right.state) :
    CompletionSafeStateEq table (materializedDeferredState left) right.state := by
  have hforward := completionSafeStateLE_materialized_of_finalizationContextLE table left right
    (FinalizationContextLE.of_eq hcontext) hrevealed hvalues
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  have hrightCompletable : DeferredCompletable table right := by
    obtain ⟨completion, hcompletion⟩ := hleftCompletable
    exact ⟨completion, (hview.deferredCompletion_iff completion).mp hcompletion⟩
  have hleftMaterialized :=
    finalizationContextLE_materializedDeferredContext hleftValid hleftCompletable
  have hreverse : FinalizationContextEq table (some right) (some left) :=
    ⟨hview.symm, hrightValid, hleftValid, hrightCompletable⟩
  have hbackwardContext : FinalizationContextLE table right
      (materializedDeferredContext left) :=
    { view := (FinalizationContextLE.of_eq hreverse).view.trans hleftMaterialized.view
      leftValid := hrightValid
      rightValid := hleftMaterialized.rightValid
      rightCompletable := hleftMaterialized.rightCompletable }
  have hrightMaterialized : materializedDeferredState right = right.state := by
    rw [hright]
    exact materializedDeferredState_directDeferredContext right.state
  have hbackwardValues : (materializedDeferredState right).values =
      (materializedDeferredState left).values := by
    rw [hrightMaterialized, ← hvalues]
  have hbackwardRevealed : right.state.revealed =
      (materializedDeferredContext left).state.revealed := by
    change right.state.revealed = (materializedDeferredState left).revealed
    simpa using hrevealed.symm
  have hbackward := completionSafeStateLE_materialized_of_finalizationContextLE table right
    (materializedDeferredContext left) hbackwardContext hbackwardRevealed (by
      change (materializedDeferredState right).values =
        (materializedDeferredState left).values
      exact hbackwardValues)
  refine ⟨hforward, ?_⟩
  rw [hrightMaterialized] at hbackward
  exact hbackward

theorem directWitnessFinalizationMaterializedCouples_pure
    (table : OtsSecretIndex → HashOutput) (value : α) :
    DirectWitnessFinalizationMaterializedCouples table
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) α) := by
  intro left right leftFuel rightFuel leftCache rightCache hcontext hcache hrevealed hmaterialized
    hright
  rw [StateT.run_pure, StateT.run_pure, runDirectResolvedDetailedFromTable_pure]
  simp only [runDirectResolvedWitnessFromTable]
  exact relTriple_pure_pure
    ⟨rfl, hcontext, rfl, rfl, rfl, rfl, hcache, hrevealed, hmaterialized,
      DeferredStructuralValuesLE.refl left.values, hright⟩

theorem DirectWitnessFinalizationMaterializedCouples.bind
    {table : OtsSecretIndex → HashOutput}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hleft : DirectWitnessFinalizationMaterializedCouples table left)
    (hnext : ∀ value, DirectWitnessFinalizationMaterializedCouples table (next value)) :
    DirectWitnessFinalizationMaterializedCouples table (left >>= next) := by
  intro leftContext rightContext leftFuel rightFuel leftCache rightCache hcontext hcache hrevealed
    hmaterialized hright
  rw [StateT.run_bind, StateT.run_bind, runDirectResolvedWitnessFromTable_bind,
    runDirectResolvedDetailedFromTable_bind]
  apply relTriple_bind
    (hleft leftContext rightContext leftFuel rightFuel leftCache rightCache hcontext hcache hrevealed
      hmaterialized hright)
  intro leftResult rightResult hresult
  cases leftResult with
  | stoppedFuel =>
      cases rightResult with
      | stopped reason => exact relTriple_pure_pure trivial
      | done rightResult =>
          have hbase := relTriple_true
            (pure (.stoppedFuel : DirectWitnessResult (β × SplitHashCache)) :
              ProbComp (DirectWitnessResult (β × SplitHashCache)))
            (runDirectResolvedDetailedFromTable rightResult.context rightResult.remaining
              rightResult.table ((next rightResult.value.1).run rightResult.value.2))
          have hsupported :=
            SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
              (fun result ↦ result = .stoppedFuel) (by intro result hresult; simpa using hresult)
          apply relTriple_post_mono hsupported
          intro left _right hrelation
          rw [hrelation.2]
          trivial
  | stoppedOrdinary =>
      cases rightResult with
      | stopped reason => exact relTriple_pure_pure trivial
      | done rightResult =>
          have hbase := relTriple_true
            (pure (.stoppedOrdinary : DirectWitnessResult (β × SplitHashCache)) :
              ProbComp (DirectWitnessResult (β × SplitHashCache)))
            (runDirectResolvedDetailedFromTable rightResult.context rightResult.remaining
              rightResult.table ((next rightResult.value.1).run rightResult.value.2))
          have hsupported :=
            SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
              (fun result ↦ result = .stoppedOrdinary)
              (by intro result hresult; simpa using hresult)
          apply relTriple_post_mono hsupported
          intro left _right hrelation
          rw [hrelation.2]
          trivial
  | stoppedPrivate witness =>
      cases rightResult with
      | stopped reason => exact relTriple_pure_pure trivial
      | done rightResult =>
          have hbase := relTriple_true
            (pure (.stoppedPrivate witness : DirectWitnessResult (β × SplitHashCache)) :
              ProbComp (DirectWitnessResult (β × SplitHashCache)))
            (runDirectResolvedDetailedFromTable rightResult.context rightResult.remaining
              rightResult.table ((next rightResult.value.1).run rightResult.value.2))
          have hsupported :=
            SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
              (fun result ↦ result = .stoppedPrivate witness)
              (by intro result hresult; simpa using hresult)
          apply relTriple_post_mono hsupported
          intro left _right hrelation
          rw [hrelation.2]
          trivial
  | done leftResult =>
      cases rightResult with
      | stopped reason => simp [DirectWitnessFinalizationMaterializedRunEq] at hresult
      | done rightResult =>
          rcases leftResult with ⟨leftContext, leftRemaining, leftValue, leftTable⟩
          rcases rightResult with ⟨rightContext, rightRemaining, rightValue, rightTable⟩
          rcases leftValue with ⟨leftOutput, leftCache⟩
          rcases rightValue with ⟨rightOutput, rightCache⟩
          simp only [DirectWitnessFinalizationMaterializedRunEq] at hresult
          rcases hresult with
            ⟨houtput, hcontext, hleftRemaining, hrightRemaining, hleftTable, hrightTable, hcache,
              hrevealed,
              hmaterialized, hprivateValues, hright⟩
          subst rightOutput
          subst leftRemaining
          subst rightRemaining
          subst leftTable
          subst rightTable
          have htail := hnext leftOutput leftContext rightContext leftFuel rightFuel leftCache rightCache
            hcontext hcache hrevealed hmaterialized hright
          apply relTriple_post_mono htail
          intro finalLeft finalRight hfinal
          cases finalLeft with
          | stoppedFuel => trivial
          | stoppedOrdinary => trivial
          | stoppedPrivate witness => trivial
          | done finalLeft =>
              cases finalRight with
              | stopped reason =>
                  simp [DirectWitnessFinalizationMaterializedRunEq] at hfinal
              | done finalRight =>
                  simp only [DirectWitnessFinalizationMaterializedRunEq] at hfinal ⊢
                  rcases hfinal with
                    ⟨houtput, hcontext, hleftRemaining, hrightRemaining, hleftTable, hrightTable,
                      hcache,
                      hrevealed, hmaterialized, htailValues, hright⟩
                  exact ⟨houtput, hcontext, hleftRemaining, hrightRemaining, hleftTable,
                    hrightTable, hcache,
                    hrevealed, hmaterialized, hprivateValues.trans htailValues, hright⟩

theorem directWitnessFinalizationMaterializedCouples_ensureCoordinate
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) :
    DirectWitnessFinalizationMaterializedCouples table (ensureCoordinate coordinate) := by
  intro left right leftFuel rightFuel leftCache rightCache hcontext hcache hrevealed hmaterialized
    hright
  unfold ensureCoordinate
  rw [StateT.run_liftM, StateT.run_liftM, LazyRevealProbe.ensureQuery,
    runDirectResolvedWitnessFromTable_ensure_query_bind,
    runDirectResolvedDetailedFromTable_ensure_query_bind,
    runDirectResolvedDetailedFromTable_pure]
  simp only [runDirectResolvedWitnessFromTable]
  apply relTriple_pure_pure
  refine ⟨rfl, ⟨hcontext.1.ensure coordinate, hcontext.2.1.ensure coordinate,
    hcontext.2.2.1.ensure coordinate, hcontext.2.2.2.ensure coordinate⟩,
    rfl, rfl, rfl, rfl, hcache, ?_, ?_, ?_, ?_⟩
  · simpa [LazyRevealProbe.State.ensure] using hrevealed
  · simpa [materializedDeferredState, DeferredContext.positionValue,
      LazyRevealProbe.State.ensure] using hmaterialized
  · exact DeferredStructuralValuesLE.refl left.values
  · rw [hright]
    simp [directDeferredContext, directDeferredValues_ensure]

set_option maxRecDepth 100000 in
theorem directWitnessFinalizationMaterializedCouples_revealCoordinateOutput_position
    (table : OtsSecretIndex → HashOutput) (position : Position) :
    DirectWitnessFinalizationMaterializedCouples table
      (revealCoordinateOutput (.position position)) := by
  intro left right leftFuel rightFuel leftCache rightCache hcontext hcache hrevealed hmaterialized
    hright
  cases hleftValue : left.state.values (.position position) with
  | some output =>
      have hleftResolved : resolvedCompletionValue table left (.position position) =
          some output := by
        simp [resolvedCompletionValue, DeferredContext.positionValue, hleftValue]
      have hrightResolved : resolvedCompletionValue table right (.position position) =
          some output := by
        rw [← hcontext.1.valueEq]
        exact hleftResolved
      have hrightValue : right.state.values (.position position) = some output := by
        have hvalue := congrFun hmaterialized (.position position)
        simpa [materializedDeferredState_position, DeferredContext.positionValue,
          hleftValue] using hvalue.symm
      rw [runDirectResolvedWitnessFromTable_revealCoordinateOutput_of_value table
          (.position position) left leftFuel leftCache output hleftValue,
        runDirectResolvedDetailedFromTable_revealCoordinateOutput_of_value table
          (.position position) right rightFuel rightCache output hrightValue]
      apply relTriple_pure_pure
      refine ⟨rfl, hcontext, rfl, rfl, rfl, rfl, ?_, hrevealed, hmaterialized,
        DeferredStructuralValuesLE.refl left.values, hright⟩
      simpa [hcache]
  | none =>
      cases hrightValue : right.state.values (.position position) with
      | some output =>
          have hprivate := (FinalizationContextLE.of_eq hcontext).view
            |>.privateValue_of_left_hidden_of_right_materialized
              position output hleftValue hrightValue
          rw [runDirectResolvedWitnessFromTable_revealCoordinateOutput_position_of_private
              table position left leftFuel leftCache output hleftValue hprivate,
            runDirectResolvedDetailedFromTable_revealCoordinateOutput_of_value table
              (.position position) right rightFuel rightCache output hrightValue]
          have hresolved : resolvedCompletionValue table left (.position position) =
              some output := by
            simp [resolvedCompletionValue, DeferredContext.positionValue, hleftValue, hprivate]
          have hmiss := hcontext.1.leftClean (.position position) output hresolved
          simp only [hmiss, ↓reduceIte]
          apply relTriple_pure_pure
          refine ⟨rfl,
            hcontext.materialize_position_left_of_right_value position output
              hleftValue hprivate,
            rfl, rfl, rfl, rfl, ?_, ?_, ?_, DeferredStructuralValuesLE.refl left.values,
              hright⟩
          · simpa [hcache]
          · simpa [LazyRevealProbe.State.materialize] using hrevealed
          · rw [materializedDeferredState_values_materialize_position_of_private
              left position output hcontext.2.1.valuesConsistent hprivate]
            exact hmaterialized
      | none =>
          have hrightPrivate : right.values position = none := by
            rw [hright]
            simpa [directDeferredContext, directDeferredValues] using hrightValue
          have hleftPositionValue : left.positionValue position = none := by
            change resolvedCompletionValue table left (.position position) = none
            rw [hcontext.1.valueEq]
            simp [resolvedCompletionValue, DeferredContext.positionValue, hrightValue,
              hrightPrivate]
          have hleftPrivate : left.values position = none := by
            simpa [DeferredContext.positionValue, hleftValue] using hleftPositionValue
          rw [runDirectResolvedWitnessFromTable_revealCoordinateOutput_position_of_fresh
              table position left leftFuel leftCache hleftValue hleftPrivate,
            runDirectResolvedDetailedFromTable_revealCoordinateOutput_position_of_fresh
              table position right rightFuel rightCache hrightValue hrightPrivate]
          apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
          intro leftOutput rightOutput houtput
          subst rightOutput
          have hresolvedNone : resolvedCompletionValue table left (.position position) = none := by
            simpa [resolvedCompletionValue] using hleftPositionValue
          have hpending := hcontext.1.pendingEq (.position position) hresolvedNone
          have hhit : left.state.hitAt (.position position) leftOutput ↔
              right.state.hitAt (.position position) leftOutput := by
            change truncateHash leftOutput ∈ left.state.pendingAt (.position position) ↔
              truncateHash leftOutput ∈ right.state.pendingAt (.position position)
            rw [hpending]
          by_cases hleftHit : left.state.hitAt (.position position) leftOutput
          · have hrightHit := hhit.mp hleftHit
            simp only [hleftHit, hrightHit, ↓reduceIte]
            exact relTriple_pure_pure trivial
          · have hrightHit := hhit.not.mp hleftHit
            simp only [hleftHit, hrightHit, ↓reduceIte]
            apply relTriple_pure_pure
            refine ⟨rfl, hcontext.materialize_position_both position leftOutput,
              rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
            · simpa [hcache]
            · simpa [LazyRevealProbe.State.materialize] using hrevealed
            · rw [materializedDeferredState_values_materialize_position_install]
              simpa [LazyRevealProbe.State.materialize] using
                congrArg (fun values : Coordinate → Option HashOutput =>
                  Function.update values (.position position)
                  (some leftOutput)) hmaterialized
            · exact DeferredStructuralValuesLE.install_of_none hleftPrivate
            · rw [hright]
              simp [directDeferredContext, directDeferredValues_materialize_position]

theorem directWitnessFinalizationMaterializedCouples_revealPosition
    (table : OtsSecretIndex → HashOutput) (position : Position) :
    DirectWitnessFinalizationMaterializedCouples table (revealPosition position) := by
  unfold revealPosition revealCoordinate
  exact (directWitnessFinalizationMaterializedCouples_revealCoordinateOutput_position
    table position).bind fun output ↦
      directWitnessFinalizationMaterializedCouples_pure table (truncateHash output)

set_option maxRecDepth 100000 in
theorem directWitnessFinalizationMaterializedCouples_revealCoordinateOutput_chainStart
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex) :
    DirectWitnessFinalizationMaterializedCouples table
      (revealCoordinateOutput index.coordinate) := by
  intro left right leftFuel rightFuel leftCache rightCache hcontext hcache hrevealed hmaterialized
    hright
  have hrightCompletable := (FinalizationContextLE.of_eq hcontext).rightCompletable
  cases hleftValue : left.state.values index.coordinate with
  | some output =>
      have houtput := hcontext.1.leftStarts index output hleftValue
      subst output
      rw [runDirectResolvedWitnessFromTable_revealCoordinateOutput_of_value table
        index.coordinate left leftFuel leftCache (table index) hleftValue]
      cases hrightValue : right.state.values index.coordinate with
      | some output =>
          have houtput := hcontext.1.rightStarts index output hrightValue
          subst output
          rw [runDirectResolvedDetailedFromTable_revealCoordinateOutput_of_value table
            index.coordinate right rightFuel rightCache (table index) hrightValue]
          apply relTriple_pure_pure
          refine ⟨rfl, hcontext, rfl, rfl, rfl, rfl, ?_, hrevealed, hmaterialized,
            DeferredStructuralValuesLE.refl left.values, hright⟩
          simpa [hcache]
      | none =>
          have hvalue := congrFun hmaterialized index.coordinate
          rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
          change left.state.values (.chainStart lay tree leafIdx chainIdx) =
            some (table ⟨lay, tree, leafIdx, chainIdx⟩) at hleftValue
          change right.state.values (.chainStart lay tree leafIdx chainIdx) = none at hrightValue
          have hvalue' : left.state.values (.chainStart lay tree leafIdx chainIdx) =
              right.state.values (.chainStart lay tree leafIdx chainIdx) := by
            simpa [materializedDeferredState, OtsSecretIndex.coordinate] using hvalue
          rw [hleftValue, hrightValue] at hvalue'
          contradiction
  | none =>
      have hleftMiss : ¬left.state.hitAt index.coordinate (table index) :=
        hcontext.2.2.2.not_hitAt_chainStart index
      rw [runDirectResolvedWitnessFromTable_revealCoordinateOutput_chainStart_of_missing
        table index left leftFuel leftCache hleftValue, if_neg hleftMiss]
      cases hrightValue : right.state.values index.coordinate with
      | some output =>
          have hvalue := congrFun hmaterialized index.coordinate
          rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
          change left.state.values (.chainStart lay tree leafIdx chainIdx) = none at hleftValue
          change right.state.values (.chainStart lay tree leafIdx chainIdx) = some output at hrightValue
          have hvalue' : left.state.values (.chainStart lay tree leafIdx chainIdx) =
              right.state.values (.chainStart lay tree leafIdx chainIdx) := by
            simpa [materializedDeferredState, OtsSecretIndex.coordinate] using hvalue
          rw [hleftValue, hrightValue] at hvalue'
          contradiction
      | none =>
          have hrightMiss : ¬right.state.hitAt index.coordinate (table index) :=
            hrightCompletable.not_hitAt_chainStart index
          rw [runDirectResolvedDetailedFromTable_revealCoordinateOutput_chainStart_of_missing
            table index right rightFuel rightCache hrightValue, if_neg hrightMiss]
          apply relTriple_pure_pure
          refine ⟨rfl, hcontext.materialize_chainStart_both index,
            rfl, rfl, rfl, rfl, ?_, ?_, ?_, DeferredStructuralValuesLE.refl left.values, ?_⟩
          · simpa [hcache]
          · simpa [LazyRevealProbe.State.materialize] using hrevealed
          · rw [materializedDeferredState_values_materialize_chainStart table]
            simpa [LazyRevealProbe.State.materialize] using
              congrArg (fun values : Coordinate → Option HashOutput =>
                Function.update values index.coordinate
                (some (table index))) hmaterialized
          · rw [hright]
            simp [directDeferredContext, directDeferredValues_materialize_chainStart]

theorem directWitnessFinalizationMaterializedCouples_revealCoordinateOutput
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) :
    DirectWitnessFinalizationMaterializedCouples table
      (revealCoordinateOutput coordinate) := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      exact directWitnessFinalizationMaterializedCouples_revealCoordinateOutput_chainStart table
        ⟨lay, tree, leafIdx, chainIdx⟩
  | position position =>
      exact directWitnessFinalizationMaterializedCouples_revealCoordinateOutput_position
        table position

theorem directWitnessFinalizationMaterializedCouples_revealCoordinate
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) :
    DirectWitnessFinalizationMaterializedCouples table (revealCoordinate coordinate) := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      unfold revealCoordinate
      exact (directWitnessFinalizationMaterializedCouples_revealCoordinateOutput_chainStart table
        ⟨lay, tree, leafIdx, chainIdx⟩).bind fun output ↦
          directWitnessFinalizationMaterializedCouples_pure table (truncateHash output)
  | position position =>
      exact directWitnessFinalizationMaterializedCouples_revealPosition table position

theorem directWitnessFinalizationMaterializedCouples_publishCoordinate
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) :
    DirectWitnessFinalizationMaterializedCouples table (publishCoordinate coordinate) := by
  intro left right leftFuel rightFuel leftCache rightCache hcontext hcache hrevealed hmaterialized
    hright
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  unfold publishCoordinate
  rw [StateT.run_liftM, StateT.run_liftM, LazyRevealProbe.publishQuery,
    runDirectResolvedWitnessFromTable_publish_query_bind,
    runDirectResolvedDetailedFromTable_publish_query_bind,
    runDirectResolvedDetailedFromTable_pure]
  simp only [runDirectResolvedWitnessFromTable]
  apply relTriple_pure_pure
  refine ⟨rfl,
    ⟨hview.publish coordinate, hleftValid.publish coordinate,
      hrightValid.publish coordinate, hleftCompletable.publish coordinate⟩,
    rfl, rfl, rfl, rfl, hcache, ?_, ?_, DeferredStructuralValuesLE.refl left.values, ?_⟩
  · simpa [LazyRevealProbe.State.publish] using congrArg (insert coordinate) hrevealed
  · rw [materializedDeferredState_publish]
    simpa [LazyRevealProbe.State.publish] using hmaterialized
  · rw [hright]
    simp [directDeferredContext, directDeferredValues_publish]

theorem directWitnessFinalizationMaterializedCouples_revealPublishedCoordinate
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) :
    DirectWitnessFinalizationMaterializedCouples table
      (revealPublishedCoordinate coordinate) := by
  unfold revealPublishedCoordinate revealCoordinate
  simp only [bind_assoc, pure_bind]
  apply (directWitnessFinalizationMaterializedCouples_revealCoordinateOutput
    table coordinate).bind
  intro output
  apply (directWitnessFinalizationMaterializedCouples_publishCoordinate
    table coordinate).bind
  intro _
  exact directWitnessFinalizationMaterializedCouples_pure table (truncateHash output)

set_option maxRecDepth 100000 in
theorem directWitnessFinalizationMaterializedCouples_sequenceFin
    {table : OtsSecretIndex → HashOutput} {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcomponent : ∀ index,
      DirectWitnessFinalizationMaterializedCouples table (computation index)) :
    DirectWitnessFinalizationMaterializedCouples table (sequenceFin computation) := by
  induction n with
  | zero =>
      simpa [sequenceFin] using
        (directWitnessFinalizationMaterializedCouples_pure table Fin.elim0 :
          DirectWitnessFinalizationMaterializedCouples table
            (pure Fin.elim0 : StateT SplitHashCache
              (OracleComp (LazyRevealProbe.World Coordinate)) (Fin 0 → α)))
  | succ n ih =>
      rw [sequenceFin]
      apply (hcomponent 0).bind
      intro head
      apply (ih (fun index : Fin n ↦ computation index.succ)
        (fun index ↦ hcomponent index.succ)).bind
      intro tail
      exact directWitnessFinalizationMaterializedCouples_pure table
        (Fin.cases head tail : Fin (n + 1) → α)

set_option maxRecDepth 100000 in
theorem directWitnessFinalizationMaterializedCouples_splitHashQuery_ordinary
    (table : OtsSecretIndex → HashOutput) (input : HashInput) :
    DirectWitnessFinalizationMaterializedCouples table
      (splitHashQuery (.ordinary input)) := by
  intro left right leftFuel rightFuel leftCache rightCache hcontext hcache hrevealed hmaterialized
    hright
  rw [splitHashQuery_run_eq, splitHashQuery_run_eq]
  have hcacheAt : leftCache (.ordinary input) = rightCache (.ordinary input) :=
    congrFun hcache (.ordinary input)
  cases hlookup : leftCache (.ordinary input) with
  | some output =>
      have hrightLookup : rightCache (.ordinary input) = some output := by
        rw [← hcacheAt]
        exact hlookup
      simp only [hrightLookup]
      exact directWitnessFinalizationMaterializedCouples_pure table output left right leftFuel
        rightFuel leftCache rightCache hcontext hcache hrevealed hmaterialized hright
  | none =>
      have hrightLookup : rightCache (.ordinary input) = none := by
        rw [← hcacheAt]
        exact hlookup
      simp only [hrightLookup]
      rw [LazyRevealProbe.hashOutputQuery,
        runDirectResolvedWitnessFromTable_hashOutput_query_bind,
        runDirectResolvedDetailedFromTable_hashOutput_query_bind]
      apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
      intro leftOutput rightOutput houtput
      subst rightOutput
      simp only [runDirectResolvedWitnessFromTable, runDirectResolvedDetailedFromTable]
      apply relTriple_pure_pure
      refine ⟨rfl, hcontext, rfl, rfl, rfl, rfl, ?_, hrevealed, hmaterialized,
        DeferredStructuralValuesLE.refl left.values, hright⟩
      simpa [hcache]

theorem directWitnessFinalizationMaterializedCouples_ordinaryHashImpl
    (table : OtsSecretIndex → HashOutput) (input : HashInput) :
    DirectWitnessFinalizationMaterializedCouples table (ordinaryHashImpl input) :=
  directWitnessFinalizationMaterializedCouples_splitHashQuery_ordinary table input

theorem directWitnessFinalizationMaterializedCouples_splitUniformImpl
    (table : OtsSecretIndex → HashOutput) (n : unifSpec.Domain) :
    DirectWitnessFinalizationMaterializedCouples table (splitUniformImpl n) := by
  intro left right leftFuel rightFuel leftCache rightCache hcontext hcache hrevealed hmaterialized
    hright
  unfold splitUniformImpl
  rw [StateT.run_liftM, StateT.run_liftM, LazyRevealProbe.uniformQuery,
    runDirectResolvedWitnessFromTable_uniform_query_bind,
    runDirectResolvedDetailedFromTable_uniform_query_bind]
  apply relTriple_bind (relTriple_refl
    (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
  intro leftOutput rightOutput houtput
  subst rightOutput
  exact directWitnessFinalizationMaterializedCouples_pure table leftOutput left right leftFuel
    rightFuel leftCache rightCache hcontext hcache hrevealed hmaterialized hright

theorem directWitnessFinalizationMaterializedCouples_simulateQ
    {table : OtsSecretIndex → HashOutput} {spec : OracleSpec ι}
    (impl : QueryImpl spec
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))))
    (hquery : ∀ query,
      DirectWitnessFinalizationMaterializedCouples table (impl query))
    (computation : OracleComp spec α) :
    DirectWitnessFinalizationMaterializedCouples table (simulateQ impl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure]
      exact directWitnessFinalizationMaterializedCouples_pure table value
  | query_bind query next ih =>
      rw [simulateQ_query_bind]
      exact (hquery query).bind fun output ↦ ih output

theorem directWitnessFinalizationMaterializedCouples_ordinaryRomImpl
    (table : OtsSecretIndex → HashOutput) (query : OracleWorld.Domain) :
    DirectWitnessFinalizationMaterializedCouples table (ordinaryRomImpl query) := by
  cases query with
  | inl n => exact directWitnessFinalizationMaterializedCouples_splitUniformImpl table n
  | inr input => exact directWitnessFinalizationMaterializedCouples_ordinaryHashImpl table input

theorem directWitnessFinalizationMaterializedCouples_ensureFullChain
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    DirectWitnessFinalizationMaterializedCouples table
      (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  apply (directWitnessFinalizationMaterializedCouples_sequenceFin
    (fun step : ChainStep =>
      ensureCoordinate (.position (.chain lay tree leafIdx chainIdx step)))
    (fun step => directWitnessFinalizationMaterializedCouples_ensureCoordinate table
      (.position (.chain lay tree leafIdx chainIdx step)))).bind
  intro _
  exact directWitnessFinalizationMaterializedCouples_pure table ()

theorem directWitnessFinalizationMaterializedCouples_ensureOtsLeaf
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    DirectWitnessFinalizationMaterializedCouples table (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  apply (directWitnessFinalizationMaterializedCouples_sequenceFin
    (fun chainIdx : ChainIndex => ensureFullChain lay tree leafIdx chainIdx)
    (fun chainIdx => directWitnessFinalizationMaterializedCouples_ensureFullChain table lay tree
      leafIdx chainIdx)).bind
  intro _
  exact directWitnessFinalizationMaterializedCouples_ensureCoordinate table
    (.position (.leaf lay tree leafIdx))

theorem directWitnessFinalizationMaterializedCouples_ensureTreeNode
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx,
      DirectWitnessFinalizationMaterializedCouples table (ensureTreeNode lay tree level nodeIdx)
  | 0, nodeIdx =>
      directWitnessFinalizationMaterializedCouples_ensureOtsLeaf table lay tree
        (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      apply (directWitnessFinalizationMaterializedCouples_ensureTreeNode table lay tree level
        (2 * nodeIdx)).bind
      intro _
      apply (directWitnessFinalizationMaterializedCouples_ensureTreeNode table lay tree level
        (2 * nodeIdx + 1)).bind
      intro _
      by_cases hlevel : level < maxLayerHeight
      · rw [dif_pos hlevel]
        exact directWitnessFinalizationMaterializedCouples_ensureCoordinate table
          (.position (.node lay tree ⟨level, hlevel⟩ (leafOfNat nodeIdx)))
      · rw [dif_neg hlevel]
        exact directWitnessFinalizationMaterializedCouples_pure table ()

theorem directWitnessFinalizationMaterializedCouples_maskedTreeNode
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (level nodeIdx : Nat) :
    DirectWitnessFinalizationMaterializedCouples table
      (maskedTreeNode lay tree level nodeIdx) := by
  unfold maskedTreeNode
  apply (directWitnessFinalizationMaterializedCouples_ensureTreeNode table lay tree level
    nodeIdx).bind
  intro _
  cases level with
  | zero =>
      exact directWitnessFinalizationMaterializedCouples_revealPosition table
        (.leaf lay tree (leafOfNat nodeIdx))
  | succ current =>
      by_cases hlevel : current < maxLayerHeight
      · simp only [hlevel, ↓reduceDIte]
        exact directWitnessFinalizationMaterializedCouples_revealPosition table
          (.node lay tree ⟨current, hlevel⟩ (leafOfNat nodeIdx))
      · simp only [hlevel, ↓reduceDIte]
        exact directWitnessFinalizationMaterializedCouples_pure table 0

theorem directWitnessFinalizationMaterializedCouples_maskedTreeRoot
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) :
    DirectWitnessFinalizationMaterializedCouples table (maskedTreeRoot lay tree) := by
  unfold maskedTreeRoot
  exact directWitnessFinalizationMaterializedCouples_maskedTreeNode table lay tree
    (layerHeight lay) 0

theorem directWitnessFinalizationMaterializedCouples_ensureChainPrefix
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (digit : Digit) :
    DirectWitnessFinalizationMaterializedCouples table
      (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  unfold ensureChainPrefix
  apply (directWitnessFinalizationMaterializedCouples_sequenceFin
    (fun step : ChainStep =>
      if step.val < digit.val then
        ensureCoordinate (.position (.chain lay tree leafIdx chainIdx step))
      else pure ())
    (fun step => by
      by_cases hstep : step.val < digit.val
      · rw [if_pos hstep]
        exact directWitnessFinalizationMaterializedCouples_ensureCoordinate table
          (.position (.chain lay tree leafIdx chainIdx step))
      · rw [if_neg hstep]
        exact directWitnessFinalizationMaterializedCouples_pure table ())).bind
  intro _
  exact directWitnessFinalizationMaterializedCouples_pure table ()

theorem directWitnessFinalizationMaterializedCouples_ensureTreePath
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    DirectWitnessFinalizationMaterializedCouples table (ensureTreePath lay tree leafIdx) := by
  unfold ensureTreePath
  apply (directWitnessFinalizationMaterializedCouples_sequenceFin
    (fun level : Fin maxLayerHeight =>
      if level.val < layerHeight lay then
        ensureTreeNode lay tree level.val (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
      else pure ())
    (fun level => by
      by_cases hlevel : level.val < layerHeight lay
      · rw [if_pos hlevel]
        exact directWitnessFinalizationMaterializedCouples_ensureTreeNode table lay tree
          level.val (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
      · rw [if_neg hlevel]
        exact directWitnessFinalizationMaterializedCouples_pure table ())).bind
  intro _
  exact directWitnessFinalizationMaterializedCouples_pure table ()

theorem directWitnessFinalizationMaterializedCouples_maskedOtsSignFrom
    (table : OtsSecretIndex → HashOutput) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    ∀ attempts counter,
      DirectWitnessFinalizationMaterializedCouples table
        (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
  | 0, counter => by
      rw [maskedOtsSignFrom]
      exact directWitnessFinalizationMaterializedCouples_pure table none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom]
      have hencoded := directWitnessFinalizationMaterializedCouples_simulateQ ordinaryHashImpl
        (directWitnessFinalizationMaterializedCouples_ordinaryHashImpl table)
        (encode parameter lay tree leafIdx message (BitVec.ofNat counterBits counter))
      apply hencoded.bind
      intro encoded
      cases encoded with
      | none =>
          exact directWitnessFinalizationMaterializedCouples_maskedOtsSignFrom table parameter
            lay tree leafIdx message attempts (counter + 1)
      | some encoding =>
          apply (directWitnessFinalizationMaterializedCouples_sequenceFin
            (fun chainIdx => ensureChainPrefix lay tree leafIdx chainIdx (encoding chainIdx))
            (fun chainIdx =>
              directWitnessFinalizationMaterializedCouples_ensureChainPrefix table lay tree
                leafIdx chainIdx (encoding chainIdx))).bind
          intro _
          exact directWitnessFinalizationMaterializedCouples_pure table
            (some (BitVec.ofNat counterBits counter, encoding))

theorem directWitnessFinalizationMaterializedCouples_maskedOtsSign
    (table : OtsSecretIndex → HashOutput) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    DirectWitnessFinalizationMaterializedCouples table
      (maskedOtsSign parameter lay tree leafIdx message) :=
  directWitnessFinalizationMaterializedCouples_maskedOtsSignFrom table parameter lay tree
    leafIdx message encodingAttemptLimit 0

theorem directWitnessFinalizationMaterializedCouples_maskedLayerMessage
    (table : OtsSecretIndex → HashOutput) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    DirectWitnessFinalizationMaterializedCouples table
      (maskedLayerMessage parameter ftsSecret index lay) := by
  unfold maskedLayerMessage
  by_cases hbelow : lay.val + 1 < numLayers
  · rw [dif_pos hbelow]
    exact directWitnessFinalizationMaterializedCouples_maskedTreeRoot table
      ⟨lay.val + 1, hbelow⟩ (treeIndexAt index ⟨lay.val + 1, hbelow⟩)
  · rw [dif_neg hbelow]
    exact directWitnessFinalizationMaterializedCouples_simulateQ ordinaryHashImpl
      (directWitnessFinalizationMaterializedCouples_ordinaryHashImpl table)
      (ftsKey parameter index (ftsSecret index))

theorem directWitnessFinalizationMaterializedCouples_maskedSignLayer
    (table : OtsSecretIndex → HashOutput) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    DirectWitnessFinalizationMaterializedCouples table
      (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayer
  apply (directWitnessFinalizationMaterializedCouples_maskedLayerMessage table parameter
    ftsSecret index lay).bind
  intro message
  apply (directWitnessFinalizationMaterializedCouples_maskedOtsSign table parameter lay
    (treeIndexAt index lay) (leafIndexAt index lay) message).bind
  intro selected
  cases selected with
  | none => exact directWitnessFinalizationMaterializedCouples_pure table none
  | some selected =>
      apply (directWitnessFinalizationMaterializedCouples_ensureTreePath table lay
        (treeIndexAt index lay) (leafIndexAt index lay)).bind
      intro _
      exact directWitnessFinalizationMaterializedCouples_pure table (some selected)

set_option maxRecDepth 100000 in
theorem directWitnessFinalizationMaterializedCouples_revealLayerValues
    (table : OtsSecretIndex → HashOutput) (index : Index) (lay : Layer)
    (encoding : ChainIndex → Digit) :
    DirectWitnessFinalizationMaterializedCouples table
      (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  apply (directWitnessFinalizationMaterializedCouples_sequenceFin
    (fun chainIdx : ChainIndex =>
      revealPublishedCoordinate
        (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay)
          chainIdx (encoding chainIdx)))
    (fun chainIdx => directWitnessFinalizationMaterializedCouples_revealPublishedCoordinate table
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay)
        chainIdx (encoding chainIdx)))).bind
  intro values
  apply (directWitnessFinalizationMaterializedCouples_sequenceFin
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
            exact directWitnessFinalizationMaterializedCouples_revealPublishedCoordinate table
              (.position (.leaf lay (treeIndexAt index lay)
                (leafOfNat (Nat.xor (leafIndexAt index lay).val 1))))
        | succ current =>
            have hcurrent : current < maxLayerHeight := by
              have := level.isLt
              omega
            simp only
            rw [dif_pos hcurrent]
            exact directWitnessFinalizationMaterializedCouples_revealPublishedCoordinate table
              (.position (.node lay (treeIndexAt index lay) ⟨current, hcurrent⟩
                (leafOfNat
                  (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
      · rw [if_neg hinLayer]
        exact directWitnessFinalizationMaterializedCouples_pure table 0)).bind
  intro path
  exact directWitnessFinalizationMaterializedCouples_pure table (values, path)

set_option maxRecDepth 100000 in
theorem directWitnessFinalizationMaterializedCouples_maskedSignAfterDigest
    (table : OtsSecretIndex → HashOutput) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    DirectWitnessFinalizationMaterializedCouples table
      (maskedSignAfterDigest parameter ftsSecret randomness index leaves) := by
  unfold maskedSignAfterDigest
  apply (directWitnessFinalizationMaterializedCouples_simulateQ ordinaryHashImpl
    (directWitnessFinalizationMaterializedCouples_ordinaryHashImpl table)
    (ftsOpen parameter index leaves (ftsSecret index))).bind
  intro ftsPath
  apply (directWitnessFinalizationMaterializedCouples_sequenceFin
    (fun lay : Layer => maskedSignLayer parameter ftsSecret index lay)
    (fun lay => directWitnessFinalizationMaterializedCouples_maskedSignLayer table parameter
      ftsSecret index lay)).bind
  intro layers
  cases hparts : traverseOption layers with
  | none => exact directWitnessFinalizationMaterializedCouples_pure table none
  | some parts =>
      apply (directWitnessFinalizationMaterializedCouples_sequenceFin
        (fun lay : Layer => revealLayerValues index lay (parts lay).2)
        (fun lay => directWitnessFinalizationMaterializedCouples_revealLayerValues table index lay
          (parts lay).2)).bind
      intro revealed
      let signature : Signature :=
        { randomness := randomness
          ftsSecret := fun tree => ftsSecret index tree (leaves (ftsIndexOf tree))
          ftsPath := ftsPath
          counter := fun lay => (parts lay).1
          chainValue := fun lay => (revealed lay).1
          authPath := flattenPaths fun lay => (revealed lay).2 }
      exact directWitnessFinalizationMaterializedCouples_pure table (some signature)

set_option maxRecDepth 100000 in
theorem directWitnessFinalizationMaterializedCouples_maskedSign
    (table : OtsSecretIndex → HashOutput) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message) :
    DirectWitnessFinalizationMaterializedCouples table
      (maskedSign parameter root ftsSecret message) := by
  unfold maskedSign
  apply (directWitnessFinalizationMaterializedCouples_simulateQ ordinaryRomImpl
    (directWitnessFinalizationMaterializedCouples_ordinaryRomImpl table)
    (signDigestLoop digestAttemptLimit
      ⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩ message)).bind
  intro selected
  cases selected with
  | none => exact directWitnessFinalizationMaterializedCouples_pure table none
  | some data =>
      exact directWitnessFinalizationMaterializedCouples_maskedSignAfterDigest table parameter
        ftsSecret data.1 data.2.1 data.2.2

set_option maxRecDepth 100000 in
theorem evalDist_runDirectDetailed_finish_eq_runObservedClean_finish
    (computation : OracleComp (LazyRevealProbe.World Coordinate) (α × SplitHashCache))
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (continuation : LazyRevealProbe.State Coordinate → Nat → α → SplitHashCache →
      List CleanProbeObservation → ProbComp Bool)
    (hprobeFree : computation.IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 0) :
    evalDist
        (runDirectResolvedDetailedFromTable (directDeferredContext state) fuel table computation >>=
          fun result => match result with
          | .stopped _ => pure false
          | .done result => continuation result.context.state result.remaining
              result.value.1 result.value.2 observations) =
      evalDist
        (runObservedCleanFromTable observations state fuel table computation >>= fun result =>
          match result with
          | none => pure false
          | some result => continuation result.state result.remaining result.value.1
              result.value.2 result.observations) := by
  let finishClean : Option (CleanRunResult (α × SplitHashCache)) → ProbComp Bool
    | none => pure false
    | some result => continuation result.state result.remaining result.value.1
        result.value.2 observations
  let finishObserved : Option (ObservedCleanRunResult (α × SplitHashCache)) → ProbComp Bool
    | none => pure false
    | some result => continuation result.state result.remaining result.value.1
        result.value.2 result.observations
  have hdirect := map_projectDirectDetailedClean_run_eq_clean computation state fuel table
  have hobserved := map_attachCleanProbeObservations_runCleanFromTable_of_probeFree computation
    observations state fuel table hprobeFree
  calc
    _ = evalDist
        ((projectDirectDetailedClean <$>
            runDirectResolvedDetailedFromTable (directDeferredContext state) fuel table
              computation) >>= finishClean) := by
          rw [map_eq_bind_pure_comp, bind_assoc]
          apply evalDist_bind_congr
          intro result _hresult
          cases result <;> rfl
    _ = evalDist (runCleanFromTable state fuel table computation >>= finishClean) := by
          rw [hdirect]
    _ = evalDist
        ((attachCleanProbeObservations observations <$>
            runCleanFromTable state fuel table computation) >>= finishObserved) := by
          rw [map_eq_bind_pure_comp, bind_assoc]
          apply evalDist_bind_congr
          intro result _hresult
          cases result <;> rfl
    _ = _ := by rw [hobserved]

theorem runDirectDetailed_finish_eq_runObservedClean_finish
    (computation : OracleComp (LazyRevealProbe.World Coordinate) (α × SplitHashCache))
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (continuation : LazyRevealProbe.State Coordinate → Nat → α → SplitHashCache →
      List CleanProbeObservation → ProbComp Bool)
    (hprobeFree : computation.IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 0) :
    (runDirectResolvedDetailedFromTable (directDeferredContext state) fuel table computation >>=
        fun result => match result with
        | .stopped _ => pure false
        | .done result => continuation result.context.state result.remaining
            result.value.1 result.value.2 observations) =
      (runObservedCleanFromTable observations state fuel table computation >>= fun result =>
        match result with
        | none => pure false
        | some result => continuation result.state result.remaining result.value.1
            result.value.2 result.observations) := by
  let finishClean : Option (CleanRunResult (α × SplitHashCache)) → ProbComp Bool
    | none => pure false
    | some result => continuation result.state result.remaining result.value.1
        result.value.2 observations
  let finishObserved : Option (ObservedCleanRunResult (α × SplitHashCache)) → ProbComp Bool
    | none => pure false
    | some result => continuation result.state result.remaining result.value.1
        result.value.2 result.observations
  have hdirect := map_projectDirectDetailedClean_run_eq_clean computation state fuel table
  have hobserved := map_attachCleanProbeObservations_runCleanFromTable_of_probeFree computation
    observations state fuel table hprobeFree
  calc
    _ = (projectDirectDetailedClean <$>
          runDirectResolvedDetailedFromTable (directDeferredContext state) fuel table
            computation) >>= finishClean := by
        rw [map_eq_bind_pure_comp, bind_assoc]
        apply bind_congr
        intro result
        cases result <;> rfl
    _ = runCleanFromTable state fuel table computation >>= finishClean := by rw [hdirect]
    _ = (attachCleanProbeObservations observations <$>
          runCleanFromTable state fuel table computation) >>= finishObserved := by
        rw [map_eq_bind_pure_comp, bind_assoc]
        apply bind_congr
        intro result
        cases result <;> rfl
    _ = _ := by rw [hobserved]

theorem relTriple_finishDirectWitness_directDetailed
    (table : OtsSecretIndex → HashOutput) (initialValues : DeferredStructuralValues)
    (leftInitialFuel rightInitialFuel : Nat)
    (leftRun : ProbComp (DirectWitnessResult (α × SplitHashCache)))
    (rightRun : ProbComp (DirectDetailedResult (α × SplitHashCache)))
    (leftObserve : DeferredContext → Nat → (α × SplitHashCache) →
      List PlannedProbeSnapshot → List CleanProbeObservation → ProbComp Bool)
    (rightObserve : LazyRevealProbe.State Coordinate → Nat → α → SplitHashCache →
      List CleanProbeObservation → ProbComp Bool)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (hstep : RelTriple leftRun rightRun
      (DirectWitnessFinalizationMaterializedRunEq table initialValues leftInitialFuel
        rightInitialFuel))
    (hnext : ∀ left right,
      DirectWitnessResult.done left ∈ support leftRun →
      DirectDetailedResult.done right ∈ support rightRun →
      DirectWitnessFinalizationMaterializedRunEq table initialValues leftInitialFuel
          rightInitialFuel (.done left) (.done right) →
      RelTriple
        (leftObserve left.context left.remaining left.value snapshots observations)
        (rightObserve right.context.state right.remaining right.value.1 right.value.2
          observations)
      BoolImp) :
    RelTriple
      (leftRun >>= finishDirectDelayedSelectedRootIndicator leftObserve snapshots observations)
      (rightRun >>= fun result => match result with
        | .stopped _ => pure false
        | .done result => rightObserve result.context.state result.remaining result.value.1
            result.value.2 observations)
      BoolImp := by
  have hleftSupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hstep
      (fun result => result ∈ support leftRun) (fun _ hresult => hresult)
  have hbothSupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleftSupported
  apply relTriple_bind hbothSupported
  intro left right hrelation
  rcases hrelation with ⟨⟨hrelation, hleftSupport⟩, hrightSupport⟩
  cases left with
  | stoppedFuel =>
      simp only [finishDirectDelayedSelectedRootIndicator]
      exact relTriple_false_any _
  | stoppedOrdinary =>
      simp only [finishDirectDelayedSelectedRootIndicator]
      exact relTriple_false_any _
  | stoppedPrivate witness =>
      simp only [finishDirectDelayedSelectedRootIndicator]
      exact relTriple_false_any _
  | done left =>
      cases right with
      | stopped reason => simp [DirectWitnessFinalizationMaterializedRunEq] at hrelation
      | done right => exact hnext left right hleftSupport hrightSupport hrelation
end SphincsSecurity.Concrete.OtsProbeSimulation
