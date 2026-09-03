import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveRootAwarePrivateStrong

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace ScratchLocal

theorem relTriple_of_not_true_mem_support
    (left right : ProbComp Bool) (hfalse : true ∉ support left) :
    RelTriple left right BoolImp := by
  have hbase := relTriple_true left right
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun value ↦ value ∈ support left) (fun _ hvalue ↦ hvalue)
  apply relTriple_post_mono hsupported
  intro leftValue _rightValue hrelation htrue
  exact (hfalse (by simpa [htrue] using hrelation.2)).elim

set_option maxRecDepth 100000 in
theorem finalizationMaterializedCouples_maskedSignAfterDigest_scratch
    (table : OtsSecretIndex → HashOutput) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    FinalizationMaterializedCouples table
      (maskedSignAfterDigest parameter ftsSecret randomness index leaves) := by
  unfold maskedSignAfterDigest
  apply (finalizationMaterializedCouples_simulateQ ordinaryHashImpl
    (finalizationMaterializedCouples_ordinaryHashImpl table)
    (ftsOpen parameter index leaves (ftsSecret index))).bind
  intro ftsPath
  apply (finalizationMaterializedCouples_sequenceFin
    (fun lay : Layer ↦ maskedSignLayer parameter ftsSecret index lay)
    (fun lay ↦ finalizationMaterializedCouples_maskedSignLayer table parameter ftsSecret
      index lay)).bind
  intro layers
  cases hparts : traverseOption layers with
  | none => exact finalizationMaterializedCouples_pure table none
  | some parts =>
      apply (finalizationMaterializedCouples_sequenceFin
        (fun lay : Layer ↦ revealLayerValues index lay (parts lay).2)
        (fun lay ↦ finalizationMaterializedCouples_revealLayerValues table index lay
          (parts lay).2)).bind
      intro revealed
      let signature : Signature :=
        { randomness := randomness
          ftsSecret := fun tree ↦ ftsSecret index tree (leaves (ftsIndexOf tree))
          ftsPath := ftsPath
          counter := fun lay ↦ (parts lay).1
          chainValue := fun lay ↦ (revealed lay).1
          authPath := flattenPaths fun lay ↦ (revealed lay).2 }
      exact finalizationMaterializedCouples_pure table (some signature)

set_option maxRecDepth 100000 in
theorem finalizationMaterializedCouples_maskedSign_scratch
    (table : OtsSecretIndex → HashOutput) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message) :
    FinalizationMaterializedCouples table
      (maskedSign parameter root ftsSecret message) := by
  unfold maskedSign
  apply (finalizationMaterializedCouples_simulateQ ordinaryRomImpl
    (finalizationMaterializedCouples_ordinaryRomImpl table)
    (signDigestLoop digestAttemptLimit
      ⟨parameter, root, fun _ _ _ _ ↦ 0, ftsSecret⟩ message)).bind
  intro selected
  cases selected with
  | none => exact finalizationMaterializedCouples_pure table none
  | some data =>
      exact finalizationMaterializedCouples_maskedSignAfterDigest_scratch table parameter ftsSecret
        data.1 data.2.1 data.2.2

theorem finalizationContextEq_materializedDeferredContext_scratch
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    FinalizationContextEq table (some context)
      (some (materializedDeferredContext context)) := by
  have hle := finalizationContextLE_materializedDeferredContext hvalid hcompletable
  refine ⟨{
    leftConsistent := hle.view.leftConsistent
    rightConsistent := hle.view.rightConsistent
    leftStarts := hle.view.leftStarts
    rightStarts := hle.view.rightStarts
    valueEq := hle.view.valueEq
    leftClean := hle.view.leftClean
    rightClean := hle.view.rightClean
    pendingEq := ?_ }, hvalid, hle.rightValid, hcompletable⟩
  intro coordinate _hnone
  rfl

theorem materializedDeferredState_canonicalize_direct_eq_scratch
    (table : OtsSecretIndex → HashOutput)
    (state : LazyRevealProbe.State Coordinate)
    (hstarts : StartTableAgrees state table)
    (hchainValid : ChainState.ValidFor (fun _ ↦ True) state) :
    materializedDeferredState
        (canonicalizeMaterializedValues table (directDeferredContext state)) = state := by
  cases state with
  | mk pending values revealed ensured =>
    simp only [materializedDeferredState, canonicalizeMaterializedValues,
      directDeferredContext]
    congr
    funext coordinate
    cases coordinate with
    | chainStart lay tree leafIdx chainIdx =>
        by_cases hrevealed : Coordinate.chainStart lay tree leafIdx chainIdx ∈ revealed
        · have hvalue := (hchainValid (.chainStart lay tree leafIdx chainIdx)
            (by simp [IsChainCoordinate])).2.1 hrevealed
          obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hvalue
          have htable := hstarts ⟨lay, tree, leafIdx, chainIdx⟩ output houtput
          simp only [publicMaterializedValues, hrevealed, ↓reduceIte,
            resolvedCompletionValue]
          have houtput' : values (.chainStart lay tree leafIdx chainIdx) = some output := by
            simpa using houtput
          exact (congrArg some htable).symm.trans houtput'.symm
        · have hvalue : values (.chainStart lay tree leafIdx chainIdx) = none := by
            by_contra hne
            exact hrevealed ((hchainValid (.chainStart lay tree leafIdx chainIdx)
              (by simp [IsChainCoordinate])).1 hne)
          simp [publicMaterializedValues, hrevealed, hvalue]
    | position position =>
        by_cases hrevealed : Coordinate.position position ∈ revealed
        · simp only [publicMaterializedValues, hrevealed, ↓reduceIte,
            resolvedCompletionValue, DeferredContext.positionValue, directDeferredValues]
          cases values (.position position) <;> simp
        · simp only [publicMaterializedValues, hrevealed, ↓reduceIte,
            DeferredContext.positionValue, directDeferredValues]

theorem materializedDeferredState_canonicalize_direct_eq_of_chainStarts
    (table : OtsSecretIndex → HashOutput)
    (state : LazyRevealProbe.State Coordinate)
    (hstarts : StartTableAgrees state table)
    (hchainStarts : ∀ lay tree leafIdx chainIdx,
      (state.values (.chainStart lay tree leafIdx chainIdx) ≠ none →
          .chainStart lay tree leafIdx chainIdx ∈ state.revealed) ∧
        (.chainStart lay tree leafIdx chainIdx ∈ state.revealed →
          state.values (.chainStart lay tree leafIdx chainIdx) ≠ none)) :
    materializedDeferredState
        (canonicalizeMaterializedValues table (directDeferredContext state)) = state := by
  cases state with
  | mk pending values revealed ensured =>
    simp only [materializedDeferredState, canonicalizeMaterializedValues,
      directDeferredContext]
    congr
    funext coordinate
    cases coordinate with
    | chainStart lay tree leafIdx chainIdx =>
        by_cases hrevealed : Coordinate.chainStart lay tree leafIdx chainIdx ∈ revealed
        · have hvalue := (hchainStarts lay tree leafIdx chainIdx).2 hrevealed
          obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hvalue
          have htable := hstarts ⟨lay, tree, leafIdx, chainIdx⟩ output houtput
          simp only [publicMaterializedValues, hrevealed, ↓reduceIte,
            resolvedCompletionValue]
          have houtput' : values (.chainStart lay tree leafIdx chainIdx) = some output := by
            simpa using houtput
          exact (congrArg some htable).symm.trans houtput'.symm
        · have hvalue : values (.chainStart lay tree leafIdx chainIdx) = none := by
            by_contra hne
            exact hrevealed ((hchainStarts lay tree leafIdx chainIdx).1 hne)
          simp [publicMaterializedValues, hrevealed, hvalue]
    | position position =>
        by_cases hrevealed : Coordinate.position position ∈ revealed
        · simp only [publicMaterializedValues, hrevealed, ↓reduceIte,
            resolvedCompletionValue, DeferredContext.positionValue, directDeferredValues]
          cases values (.position position) <;> simp
        · simp only [publicMaterializedValues, hrevealed, ↓reduceIte,
            DeferredContext.positionValue, directDeferredValues]

theorem materializedDeferredState_canonicalize_eq
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hstarts : StartTableAgrees context.state table)
    (hchainValid : ChainState.ValidFor (fun _ ↦ True) context.state)
    (hconsistent : context.ValuesConsistent) :
    materializedDeferredState (canonicalizeMaterializedValues table context) =
      materializedDeferredState context := by
  cases hstate : context.state with
  | mk pending values revealed ensured =>
    simp only [materializedDeferredState, canonicalizeMaterializedValues, hstate]
    congr
    funext coordinate
    cases coordinate with
    | chainStart lay tree leafIdx chainIdx =>
        have hvalue := canonicalizeMaterializedValues_chain_value table context hstarts
          hchainValid (.chainStart lay tree leafIdx chainIdx) (by simp [IsChainCoordinate])
        unfold canonicalizeMaterializedValues at hvalue
        rw [hstate] at hvalue
        exact hvalue
    | position position =>
        have hvalue := canonicalizeMaterializedValues_positionValue table context hconsistent
          position
        unfold canonicalizeMaterializedValues at hvalue
        rw [hstate] at hvalue
        exact hvalue

theorem evalDist_negatedCanonicalizeDirectDelayedObserve_eq_of_finalizationContextEq_published_scratch
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      List CleanProbeObservation → ProbComp Bool)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (left right : DeferredContext) (fuel : Nat) (value : α)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hrevealed : left.state.revealed = right.state.revealed)
    (hleftPublished : PublishedValues left.state)
    (hrightPublished : PublishedValues right.state)
    [ObserverSynchronized table
      (negatedDirectDelayedObserve observe snapshots observations)] :
    evalDist
        (negatedDirectDelayedObserve
          (canonicalizeDirectDelayedSelectedRootIndicator table observe)
          snapshots observations left fuel value) =
      evalDist
        (negatedDirectDelayedObserve
          (canonicalizeDirectDelayedSelectedRootIndicator table observe)
          snapshots observations right fuel value) := by
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  have hrightCompletable : DeferredCompletable table right := by
    obtain ⟨completion, hcompletion⟩ := hleftCompletable
    exact ⟨completion, (hview.deferredCompletion_iff completion).mp hcompletion⟩
  have hleftCanonical := valid_completable_canonicalizeMaterializedValues table left
    hleftValid hleftCompletable
  have hrightCanonical := valid_completable_canonicalizeMaterializedValues table right
    hrightValid hrightCompletable
  have hleftNoHit : ¬PrivateStructuralHit (canonicalizeMaterializedValues table left) :=
    not_privateStructuralHit_of_deferredCompletable hleftCanonical.2
  have hrightNoHit : ¬PrivateStructuralHit (canonicalizeMaterializedValues table right) :=
    not_privateStructuralHit_of_deferredCompletable hrightCanonical.2
  unfold negatedDirectDelayedObserve canonicalizeDirectDelayedSelectedRootIndicator
  simp only [hleftNoHit, hrightNoHit, hleftPublished, hrightPublished,
    hleftCanonical.2, hrightCanonical.2, ↓reduceIte]
  have hcanonical := canonicalizedFinalizationContextEq
    (⟨hview, hleftValid, hrightValid, hleftCompletable⟩ :
      FinalizationContextEq table (some left) (some right)) hrevealed
  exact ObserverSynchronized.eq_of_synchronized
    (table := table)
    (observe := negatedDirectDelayedObserve observe snapshots observations)
    (canonicalizeMaterializedValues table left)
    (canonicalizeMaterializedValues table right) fuel value hcanonical.1 hcanonical.2 hrevealed

theorem relTriple_finishObserve_reverse_of_finalizationMaterialized_scratch
    (table : OtsSecretIndex → HashOutput)
    (leftRun rightRun : ProbComp
      (Option (ResolvedRunResult (α × SplitHashCache))))
    (leftObserve rightObserve : DeferredContext → Nat →
      (α × SplitHashCache) → ProbComp Bool)
    (hstep : RelTriple leftRun rightRun (FinalizationMaterializedRunEq table))
    (hrecursive : ∀ left right,
      FinalizationMaterializedRunEq table (some left) (some right) →
      RelTriple
        (rightObserve right.context right.remaining right.value)
        (leftObserve left.context left.remaining left.value)
        BoolImp) :
    RelTriple
      (rightRun >>= finishObserve rightObserve)
      (leftRun >>= finishObserve leftObserve)
      BoolImp := by
  apply relTriple_bind (relTriple_symm hstep)
  intro right left hrelation
  cases right with
  | none =>
      cases left with
      | none => exact relTriple_pure_pure (by simp [BoolImp])
      | some left => simp [FinalizationMaterializedRunEq] at hrelation
  | some right =>
      cases left with
      | none => simp [FinalizationMaterializedRunEq] at hrelation
      | some left => exact hrecursive left right hrelation

set_option maxRecDepth 100000 in
theorem evalDist_complement_observed_probeFree_eq_runDirectResolvedObserve_scratch
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (continuation : LazyRevealProbe.State Coordinate → Nat → α → ProbComp Bool)
    (hprobeFree : computation.IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 0) :
    evalDist (Bool.not <$> (runObservedCleanFromTable observations state fuel table computation >>=
      fun result ↦ match result with
      | none => pure false
      | some result => continuation result.state result.remaining result.value)) =
      evalDist (runDirectResolvedObserve
        (fun context remaining value ↦
          Bool.not <$> continuation context.state remaining value)
        (directDeferredContext state) fuel table computation) := by
  rw [map_bind]
  have hobserved := map_attachCleanProbeObservations_runCleanFromTable_of_probeFree computation
    observations state fuel table hprobeFree
  rw [← hobserved, map_eq_bind_pure_comp, bind_assoc]
  have hclean := map_projectResolvedRunResult_runDirect_eq_runClean computation state fuel table
  rw [← hclean, map_eq_bind_pure_comp, bind_assoc]
  unfold runDirectResolvedObserve
  apply evalDist_bind_congr
  intro result _hresult
  cases result <;> rfl

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

end ScratchLocal

open ScratchLocal

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem goodForRoots_of_true_mem_directDelayed_selected_hash
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (targetOutput : HashOutput) (input : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) RetainedRestResult)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (candidate : Probe)
    (hcandidate : rootAwareCandidateForPlan? parameter input
      (purePlanProbingHashQuery parameter input context.state) = some candidate)
    (hordinal : snapshots.length = ordinal)
    (hobservationLength : observations.length = ordinal)
    (hvalid : context.Valid)
    (hcompletable : DeferredCompletable table context)
    (hpublished : PublishedValues context.state)
    (hcanonical : CanonicalMaterializedValues table context)
    (hprivate : context.values target = some targetOutput)
    (htrue : true ∈ support
      (directDelayedSelectedRootIndicator ordinal parameter publicRoot ftsSecret table target
        rightRoot
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inr input))) >>= next)
        snapshots observations context fuel cache)) :
    let selection : PrivateOrdinalSelection :=
      ⟨candidate, context,
        (snapshots ++ [(⟨candidate, context⟩ : PlannedProbeSnapshot)]).map
          PlannedProbeSnapshot.toProbe⟩
    selection.GoodForRoots target targetOutput rightRoot ordinal := by
  dsimp only
  have hnotSelected : ¬ordinal < snapshots.length := by omega
  have hselected : ordinal <
      (appendPlannedSnapshot snapshots (some candidate) context).length := by
    simp [appendPlannedSnapshot, hordinal]
  rw [directDelayedSelectedRootIndicator_hash_eq_selected ordinal parameter publicRoot
    ftsSecret table target rightRoot input next snapshots observations context fuel cache
    hnotSelected (by simpa [hcandidate] using hselected)] at htrue
  have hget :
      (appendPlannedSnapshot snapshots
        (rootAwareCandidateForPlan? parameter input
          (purePlanProbingHashQuery parameter input context.state)) context).get
          ⟨ordinal, by simpa [hcandidate] using hselected⟩ =
        (⟨candidate, context⟩ : PlannedProbeSnapshot) := by
    subst ordinal
    simp [appendPlannedSnapshot, hcandidate, List.get_eq_getElem]
  rw [hget] at htrue
  unfold delayedSelectedRootIndicator at htrue
  rw [mem_support_bind_iff] at htrue
  obtain ⟨resolvedOption, hresolvedOption, hrest⟩ := htrue
  cases resolvedOption with
  | none => simp at hrest
  | some resolved =>
      simp only at hrest
      have houtput :=
        resolveDeferredPositionValue_output_eq_of_private_of_deferredCompletable table target
          context targetOutput hprivate hcompletable resolved hresolvedOption
      have happend :
          appendPlannedSnapshot snapshots
              (rootAwareCandidateForPlan? parameter input
                (purePlanProbingHashQuery parameter input context.state)) context =
            snapshots ++ [(⟨candidate, context⟩ : PlannedProbeSnapshot)] := by
        simp [hcandidate, appendPlannedSnapshot]
      rw [happend] at hrest
      have hsafe : CandidatesAvoidRoots target (truncateHash targetOutput) rightRoot
          ((snapshots ++ [(⟨candidate, context⟩ : PlannedProbeSnapshot)]).map
            PlannedProbeSnapshot.toProbe |>.take ordinal) := by
        rw [houtput] at hrest
        by_cases hsafe : CandidatesAvoidRoots target (truncateHash targetOutput) rightRoot
            ((snapshots ++ [(⟨candidate, context⟩ : PlannedProbeSnapshot)]).map
              PlannedProbeSnapshot.toProbe |>.take ordinal)
        · exact hsafe
        · rw [if_neg hsafe] at hrest
          simp at hrest
      rw [houtput] at hrest
      simp only [hsafe, ↓reduceIte] at hrest
      rw [support_map] at hrest
      obtain ⟨observed, hobserved, hindicator⟩ := hrest
      have hgood : ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
          table ordinal target rightRoot observed := by
        change successfulObservedRootComparisonIndicator table ordinal target
          (observed, rightRoot) = true at hindicator
        rw [successfulObservedRootComparisonIndicator_eq_true_iff] at hindicator
        exact hindicator
      cases observed with
      | none =>
          simp [ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
            ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
            ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt] at hgood
      | some result =>
          have hresolvedValid := hvalid.of_resolveDeferredPositionValue target resolved
            hresolvedOption
          have hresolvedCompletable :=
            hcompletable.of_resolveDeferredPositionValue hvalid target resolved hresolvedOption
          have hresolvedCanonical := canonicalMaterializedValues_of_resolveDeferredPositionValue
            table target context resolved hpublished hcanonical hresolvedOption
          have hcontextLE := finalizationContextLE_materializedDeferredContext hresolvedValid
            hresolvedCompletable
          have hvalues :
              (materializedCanonicalContext table
                (materializedDeferredState resolved.toDeferredContext)).state.values =
                resolved.state.values :=
            canonicalized_right_values_eq_of_finalizationContextLE hcontextLE rfl
              hresolvedCanonical
          have hpreserved := resolveDeferredPositionValue_preserves_state_values target context
            resolved hresolvedOption
          have hqueryCandidate : rootAwareCandidateForPlan? parameter input
              (purePlanProbingHashQuery parameter input
                (materializedCanonicalContext table
                  (materializedDeferredState resolved.toDeferredContext)).state) =
                some candidate := by
            rw [purePlanProbingHashQuery_eq_of_values_eq hvalues parameter input,
              purePlanProbingHashQuery_eq_of_values_eq hpreserved parameter input]
            exact hcandidate
          obtain ⟨⟨⟨⟨_finalResult, _hfinish⟩, _hdoomed,
            selected, hselectedOrdinal, hfirst, _hroot⟩, hposition⟩, _hcomparison⟩ := hgood
          have hobservation :=
            selected_observation_eq_of_mem_observedMaterializedBoundary_hash_query ordinal
              parameter publicRoot ftsSecret input next observations
              (materializedDeferredState resolved.toDeferredContext) fuel table cache candidate
              hobservationLength hqueryCandidate result hobserved selected hselectedOrdinal
          obtain ⟨first, hfirstOrdinal, hfirstHit, _hbeforeFirst⟩ := hfirst
          have hfirstSelected : first = selected :=
            Fin.ext (hfirstOrdinal.trans hselectedOrdinal.symm)
          subst first
          have hselectedLt : ordinal < result.observations.length := by
            rw [← hselectedOrdinal]
            exact selected.isLt
          have hselectedIndex :
              (⟨ordinal, hselectedLt⟩ : Fin result.observations.length) = selected :=
            Fin.ext hselectedOrdinal.symm
          have htargetData :
              (result.observations.get selected).coordinate = .position target := by
            simp only [observedFirstLayerRootPosition?, hselectedLt, ↓reduceDIte] at hposition
            rw [candidateLayerRootPosition?_eq_some_iff, hselectedIndex] at hposition
            exact hposition.1
          have hcandidateCoordinate : candidate.coordinate = .position target := by
            rw [hobservation] at htargetData
            simpa [cleanProbeObservation] using htargetData
          rw [ExistingHiddenHitAtOrdinal, hobservation] at hfirstHit
          obtain ⟨hselectedHidden, existing, hselectedValue, hselectedCandidate⟩ := hfirstHit
          have hresolvedValue :
              (materializedDeferredState resolved.toDeferredContext).values
                  (.position target) = some targetOutput := by
            simp only [materializedDeferredState_position]
            have hpositionValue := resolveDeferredPositionValue_resolves target context resolved
              hresolvedOption
            simpa [houtput] using hpositionValue
          have hexisting : existing = targetOutput := by
            have : (materializedDeferredState resolved.toDeferredContext).values
                candidate.coordinate = some existing := by
              simpa [cleanProbeObservation] using hselectedValue
            rw [hcandidateCoordinate, hresolvedValue] at this
            exact Option.some.inj this.symm
          have hcandidateDigest : truncateHash targetOutput = candidate.candidate := by
            simpa [cleanProbeObservation, hexisting] using hselectedCandidate
          have hcandidateEq : candidate = ⟨.position target, truncateHash targetOutput⟩ := by
            cases candidate
            simp only [Probe.mk.injEq]
            exact ⟨hcandidateCoordinate, hcandidateDigest.symm⟩
          have hresolvedHidden : Coordinate.position target ∉ resolved.state.revealed := by
            rw [← hcandidateCoordinate]
            simpa [cleanProbeObservation, decide_eq_false_iff_not] using hselectedHidden
          have hcontextHidden : Coordinate.position target ∉ context.state.revealed := by
            rw [resolveDeferredPositionValue_state_eq_clearPending target context resolved
              hresolvedOption] at hresolvedHidden
            simpa [LazyRevealProbe.State.clearPending] using hresolvedHidden
          refine ⟨hcandidateEq,
            canonical_value_none_of_not_revealed hcanonical hcontextHidden,
            hcontextHidden, hprivate, ?_⟩
          simpa [hordinal] using hsafe

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 1000000 in
theorem relTriple_directDelayed_observed_shadow
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (targetOutput : HashOutput)
    (hroot : IsLayerRoot target)
    (computation : OracleComp (OracleWorld + SigningSpec) RetainedRestResult)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (leftFuel rightFuel q bound : Nat)
    (cache : SplitHashCache)
    (hbound : computation.IsQueryBoundP IsOuterHash bound)
    (hvalid : context.Valid)
    (hcompletable : DeferredCompletable table context)
    (hpublished : PublishedValues context.state)
    (hcanonical : CanonicalMaterializedValues table context)
    (hchainValid : ChainState.ValidFor (fun _ ↦ True) context.state)
    (hprivate : context.values target = some targetOutput)
    (haligned : SnapshotsObservedAt table snapshots observations)
    (hbefore : SnapshotsBefore snapshots context)
    (htracked : CleanProbeObservationsTrackedBy observations
      (materializedDeferredState context))
    (hcovered : CleanProbeObservationsCoverPending observations
      (materializedDeferredState context))
    (hnoHit : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit)
    (hpending : PendingCoveredBy
      (snapshots.map PlannedProbeSnapshot.toProbe) context)
    (hlength : snapshots.length ≤ ordinal)
    (hleftLower : bound ≤ leftFuel) (hleftUpper : leftFuel ≤ q)
    (hrightLower : q + bound ≤ rightFuel)
    (hbudget : rightFuel + (materializedDeferredState context).pending.card <
      Fintype.card Digest) :
    RelTriple
      (directDelayedSelectedRootIndicator ordinal parameter publicRoot ftsSecret table target
        rightRoot computation snapshots observations context leftFuel cache)
      ((successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed ↦ (observed, rightRoot)) <$>
        observedMaterializedBoundary parameter publicRoot ftsSecret computation observations
          (materializedDeferredState context) rightFuel table cache)
      SuccessfulObservedIndicatorRel := by
  induction computation using OracleComp.inductionOn generalizing
      snapshots observations context leftFuel rightFuel bound cache with
  | pure value =>
      have hselected : ¬ordinal < snapshots.length := by omega
      rw [directDelayedSelectedRootIndicator, OracleComp.construct_pure]
      simp only [hselected, ↓reduceDIte]
      exact relTriple_false_any _
  | query_bind query next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      have hnotSelected : ¬ordinal < snapshots.length := by omega
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              apply relTriple_directDelayed_uniform_observed ordinal parameter publicRoot
                rightRoot ftsSecret table target n next snapshots observations context leftFuel
                rightFuel cache hnotSelected hcompletable hpublished hcanonical
              intro output
              exact ih output snapshots observations context leftFuel rightFuel bound
                cache (by simpa [IsOuterHash] using hbound.2 output) hvalid hcompletable hpublished
                hcanonical hchainValid hprivate haligned hbefore htracked hcovered hnoHit hpending hlength
                hleftLower hleftUpper hrightLower hbudget
          | inr input =>
              change HashOutput → OracleComp (OracleWorld + SigningSpec)
                RetainedRestResult at next
              let plan := purePlanProbingHashQuery parameter input context.state
              let candidate? := rootAwareCandidateForPlan? parameter input plan
              let nextSnapshots := appendPlannedSnapshot snapshots candidate? context
              by_cases hnowSelected : ordinal < nextSnapshots.length
              · obtain ⟨candidate, hcandidate⟩ : ∃ candidate, candidate? = some candidate := by
                  cases hcandidate : candidate? with
                  | none =>
                      exfalso
                      apply hnotSelected
                      simpa [nextSnapshots, appendPlannedSnapshot, hcandidate] using hnowSelected
                  | some candidate => exact ⟨candidate, rfl⟩
                have hsnapshotLength : snapshots.length = ordinal := by
                  simp [nextSnapshots, appendPlannedSnapshot, hcandidate] at hnowSelected
                  omega
                let selection : PrivateOrdinalSelection :=
                  ⟨candidate, context,
                    (snapshots ++ [(⟨candidate, context⟩ : PlannedProbeSnapshot)]).map
                      PlannedProbeSnapshot.toProbe⟩
                have hselectionCovered : PendingCoveredBy
                    (selection.candidates.take ordinal) selection.context := by
                  simpa [selection, hsnapshotLength] using hpending
                by_cases hselectionGood :
                    selection.GoodForRoots target targetOutput rightRoot ordinal
                · let selectedComputation :=
                    liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
                      (Sum.inl (Sum.inr input))) >>= next
                  have hsame :=
                    relTriple_directDelayed_selected_hash_observed_of_good ordinal
                      parameter publicRoot rightRoot ftsSecret table target targetOutput hroot input
                      next snapshots observations context leftFuel cache hsnapshotLength
                      (by simpa [plan, candidate?, hcandidate] using hselectionGood.1)
                      hselectionGood.2.1 hselectionGood.2.2.1 hselectionGood.2.2.2.1
                      (by simpa [selection, hsnapshotLength] using hselectionGood.2.2.2.2)
                      hpending hvalid hcompletable hpublished hcanonical
                      (by rw [← haligned.length_eq]; exact hsnapshotLength)
                      haligned.map_toProbe_eq.symm hnoHit
                  have hfuel :=
                    relTriple_indicator_observedMaterializedBoundary_fuel_of_isQueryBoundP
                      ordinal parameter publicRoot rightRoot ftsSecret table target
                      selectedComputation observations (materializedDeferredState context)
                      leftFuel rightFuel bound cache (by
                        dsimp only [selectedComputation]
                        rw [OracleComp.isQueryBoundP_query_bind_iff]
                        exact hbound)
                      hleftLower (by omega)
                  have hglued := SphincsSecurity.relTriple_trans_exists hsame hfuel
                  apply relTriple_post_mono hglued
                  intro source actual hrelation
                  obtain ⟨middle, hfirst, hsecond⟩ := hrelation
                  exact fun htrue ↦ hsecond (hfirst htrue)
                · apply relTriple_of_not_true_mem_support
                  intro htrue
                  apply hselectionGood
                  simpa [selection, plan, candidate?, hcandidate] using
                    goodForRoots_of_true_mem_directDelayed_selected_hash ordinal parameter
                      publicRoot rightRoot ftsSecret table target targetOutput input next snapshots
                      observations context leftFuel cache candidate
                      (by simpa [plan, candidate?] using hcandidate)
                      hsnapshotLength (haligned.length_eq.symm.trans hsnapshotLength) hvalid
                      hcompletable hpublished hcanonical hprivate htrue
              · rw [directDelayedSelectedRootIndicator_hash_eq_not_selected ordinal parameter
                  publicRoot ftsSecret table target rightRoot input next snapshots observations
                  context leftFuel cache hnotSelected (by
                    simpa [nextSnapshots] using hnowSelected)]
                rw [observedMaterializedBoundary_hash_query_bind]
                simp only [map_bind]
                let rightContext := materializedDeferredContext context
                have hcontextEq : FinalizationContextEq table (some context)
                    (some rightContext) :=
                  finalizationContextEq_materializedDeferredContext hvalid hcompletable
                have hcontextDirect : FinalizationContextLE table context rightContext :=
                  FinalizationContextLE.of_eq hcontextEq
                have hrightValues :
                    (materializedCanonicalContext table
                        (materializedDeferredState context)).state.values =
                      context.state.values := by
                  change (canonicalizeMaterializedValues table rightContext).state.values =
                    context.state.values
                  exact canonicalized_right_values_eq_of_finalizationContextLE hcontextDirect rfl
                    hcanonical
                have hplanEq :
                    purePlanProbingHashQuery parameter input
                        (materializedCanonicalContext table
                          (materializedDeferredState context)).state = plan := by
                  exact purePlanProbingHashQuery_eq_of_values_eq hrightValues parameter input
                rw [hplanEq]
                have hpublicExecutor :
                    probingHashQueryAfterRootAwarePublicPlan parameter input
                        (materializedCanonicalContext table
                          (materializedDeferredState context)).state plan =
                      probingHashQueryAfterRootAwarePublicPlan parameter input context.state plan :=
                  probingHashQueryAfterRootAwarePublicPlan_eq_of_values_eq parameter input
                    hrightValues plan
                rw [hpublicExecutor]
                let nextObservations := observationsAfterCandidate observations
                  (materializedDeferredState context) candidate?
                let leftStep : ProbComp
                    (DirectWitnessResult (HashOutput × SplitHashCache)) :=
                  runDirectResolvedWitnessFromTable context leftFuel table
                    ((probingHashQueryAfterRootAwarePlan parameter input plan).run cache)
                let rightStep : ProbComp
                    (Option (ObservedCleanRunResult (HashOutput × SplitHashCache))) :=
                  runObservedCleanFromTable observations (materializedDeferredState context)
                    rightFuel table
                    ((probingHashQueryAfterRootAwarePublicPlan parameter input context.state plan).run
                      cache)
                let observe : DeferredContext → Nat →
                    (HashOutput × SplitHashCache) → List PlannedProbeSnapshot →
                      List CleanProbeObservation → ProbComp Bool :=
                  fun nextContext remaining value laterSnapshots laterObservations ↦
                    directDelayedSelectedRootIndicator ordinal parameter publicRoot ftsSecret table
                      target rightRoot (next value.1) laterSnapshots laterObservations nextContext
                      remaining value.2
                let rightObserve : LazyRevealProbe.State Coordinate → Nat → HashOutput →
                    SplitHashCache → List CleanProbeObservation → ProbComp Bool :=
                  fun state remaining output nextCache laterObservations ↦
                    (successfulObservedRootComparisonIndicator table ordinal target ∘
                        fun observed ↦ (observed, rightRoot)) <$>
                      observedMaterializedBoundary parameter publicRoot ftsSecret (next output)
                        laterObservations state remaining table nextCache
                change RelTriple
                  (leftStep >>= finishDirectDelayedSelectedRootIndicator
                    (canonicalizeDirectDelayedSelectedRootIndicator table observe) nextSnapshots
                    nextObservations)
                  (rightStep >>= fun result ↦
                    (successfulObservedRootComparisonIndicator table ordinal target ∘
                        fun observed ↦ (observed, rightRoot)) <$> match result with
                    | none => pure none
                    | some result =>
                        observedMaterializedBoundary parameter publicRoot ftsSecret
                          (next result.value.1) result.observations result.state result.remaining
                          table result.value.2)
                  SuccessfulObservedIndicatorRel
                change RelTriple _ _ BoolImp
                have houter : IsOuterHash (.inl (.inr input)) := by simp [IsOuterHash]
                have hboundPositive : 0 < bound := by
                  rcases hbound.1 with hnot | hpositive
                  · exact (hnot houter).elim
                  · exact hpositive
                have hleftPositive : 0 < leftFuel := by omega
                have hnextLength : nextSnapshots.length ≤ ordinal :=
                  Nat.le_of_not_gt hnowSelected
                have hcontinue
                    (hcandidateCompletable : ∀ candidate,
                      candidate? = some candidate →
                      candidate.coordinate ∉ context.state.revealed →
                      DeferredCompletable table
                        { context with state :=
                            (context.state.addPending candidate.coordinate candidate.candidate) })
                    (hnextAligned : SnapshotsObservedAt table nextSnapshots nextObservations)
                    (hnextNoHit : ∀ observation ∈ nextObservations,
                      ¬observation.ExistingHiddenHit) :
                    RelTriple
                      (leftStep >>= finishDirectDelayedSelectedRootIndicator
                        (canonicalizeDirectDelayedSelectedRootIndicator table observe)
                        nextSnapshots nextObservations)
                      (rightStep >>= fun result ↦
                        match result with
                        | none => pure false
                        | some result =>
                            rightObserve result.state result.remaining result.value.1
                              result.value.2 result.observations)
                      BoolImp := by
                  have hstep :=
                    relTriple_runDirectResolvedWitness_rootAwarePrivate_observedFinalizationMaterialized
                      table parameter input context.state plan observations context rightContext
                      leftFuel rightFuel cache cache rfl hleftPositive (by omega) hcontextEq rfl rfl
                      rfl (by rfl) (by
                        intro candidate hcandidate hhidden
                        exact hcandidateCompletable candidate (by simpa [candidate?] using hcandidate)
                          hhidden)
                  have hfinished :=
                    relTriple_bind_finishDirectDelayed_observed_of_spent table context.values
                      leftFuel rightFuel (if candidate?.isSome then 1 else 0) nextObservations
                      leftStep rightStep
                      (canonicalizeDirectDelayedSelectedRootIndicator table observe) rightObserve
                      nextSnapshots nextObservations
                      (by simpa [leftStep, rightStep, candidate?, rightContext,
                        materializedDeferredContext, directDeferredContext] using hstep) (by
                        intro leftResult rightResult hleftSupport hrightSupport hrelation
                        rcases hrelation with
                          ⟨houtput, hfinal, hleftSpent, hrightSpent, hleftTable,
                            hrightTable, hcache, hrevealed, hmaterialized, hprivateValues,
                            hrightDirect⟩
                        have hinitialPublished :
                            PublishedValues (materializedDeferredState context) := by
                          intro coordinate hcoordinate
                          cases coordinate with
                          | chainStart lay tree leafIdx chainIdx =>
                              exact hpublished _ (by simpa using hcoordinate)
                          | position position =>
                              have hvalue := hpublished (.position position) (by simpa using hcoordinate)
                              obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hvalue
                              simp [materializedDeferredState, DeferredContext.positionValue,
                                houtput]
                        have hrightDetailed : DirectDetailedResult.done rightResult ∈ support
                            (runDirectResolvedDetailedFromTable rightContext rightFuel table
                              ((probingHashQueryAfterRootAwarePublicPlan parameter input context.state
                                plan).run cache)) := by
                          have hsupported := hrightSupport
                          dsimp only [rightStep] at hsupported
                          rw [← map_projectDirectDetailedObserved_rootAwarePublic parameter input
                            context.state plan observations (materializedDeferredState context)
                            rightFuel table cache, support_map] at hsupported
                          obtain ⟨detailed, hdetailed, heq⟩ := hsupported
                          cases detailed with
                          | stopped reason =>
                              simp [projectDirectDetailedObserved] at heq
                          | done found =>
                              simp [projectDirectDetailedObserved, observedResolvedResult] at heq
                              have hfoundSupport : some found ∈ support
                                  (runDirectResolvedFromTable
                                    (directDeferredContext (materializedDeferredState context))
                                    rightFuel table
                                    ((probingHashQueryAfterRootAwarePublicPlan parameter input
                                      context.state plan).run cache)) :=
                                mem_support_runDirectResolvedFromTable_of_done_detailed
                                  ((probingHashQueryAfterRootAwarePublicPlan parameter input
                                    context.state plan).run cache)
                                  (directDeferredContext (materializedDeferredState context))
                                  rightFuel table found hdetailed
                              have hfoundDirect := direct_context_of_mem_runDirectResolvedFromTable
                                ((probingHashQueryAfterRootAwarePublicPlan parameter input
                                  context.state plan).run cache)
                                (materializedDeferredState context) rightFuel table found
                                hfoundSupport
                              have hcontextFound : found.context = rightResult.context := by
                                rw [hfoundDirect, hrightDirect, heq.1]
                              cases found with
                              | mk foundContext foundRemaining foundValue foundTable =>
                                  cases rightResult with
                                  | mk resultContext resultRemaining resultValue resultTable =>
                                      simp only at hcontextFound
                                      subst resultContext
                                      simp only at heq
                                      rcases heq with
                                        ⟨_stateEq, rfl, rfl, rfl, _observationsEq⟩
                                      simpa [rightContext, materializedDeferredContext] using
                                        hdetailed
                        have hrightPublished : PublishedValues rightResult.context.state :=
                          publishedValues_of_done_runDirectResolvedDetailedFromTable
                            (probingHashQueryAfterRootAwarePublicPlan parameter input context.state
                              plan)
                            (preservesPublishedValues_probingHashQueryAfterRootAwarePublicPlan
                              parameter input context.state plan)
                            rightContext rightFuel table cache rightResult
                            (by simpa [rightContext, materializedDeferredContext,
                              directDeferredContext] using hinitialPublished)
                            hrightDetailed
                        have hrightTracked : CleanProbeObservationsTrackedBy nextObservations
                            rightResult.context.state := by
                          simpa [rightStep, observedResolvedResult] using
                            cleanProbeObservationsTrackedBy_of_mem_runObservedCleanFromTable
                              ((probingHashQueryAfterRootAwarePublicPlan parameter input context.state
                                plan).run cache)
                              observations (materializedDeferredState context) rightFuel table
                              htracked (observedResolvedResult nextObservations rightResult)
                              hrightSupport
                        have hrightCovered : CleanProbeObservationsCoverPending nextObservations
                            rightResult.context.state := by
                          simpa [rightStep, observedResolvedResult] using
                            cleanProbeObservationsCoverPending_of_mem_runObservedCleanFromTable
                              ((probingHashQueryAfterRootAwarePublicPlan parameter input context.state
                                plan).run cache)
                              observations (materializedDeferredState context) rightFuel table
                              hcovered (observedResolvedResult nextObservations rightResult)
                              hrightSupport
                        have hrightBudget : rightResult.remaining +
                            rightResult.context.state.pending.card < Fintype.card Digest := by
                          have hremaining :=
                            remaining_add_pending_card_le_of_mem_runObservedCleanFromTable
                              ((probingHashQueryAfterRootAwarePublicPlan parameter input context.state
                                plan).run cache)
                              observations (materializedDeferredState context) rightFuel table
                              (observedResolvedResult nextObservations rightResult) hrightSupport
                          simpa [observedResolvedResult] using hremaining.trans_lt hbudget
                        have hleftDetailed : DirectDetailedResult.done leftResult ∈ support
                            (runDirectResolvedDetailedFromTable context leftFuel table
                              ((probingHashQueryAfterRootAwarePlan parameter input plan).run cache)) := by
                          rw [← map_erase_runDirectResolvedWitnessFromTable
                            ((probingHashQueryAfterRootAwarePlan parameter input plan).run cache)
                            context leftFuel table, support_map]
                          exact ⟨.done leftResult, by simpa [leftStep] using hleftSupport, rfl⟩
                        have hleftDirect : some leftResult ∈ support
                            (runDirectResolvedFromTable context leftFuel table
                              ((probingHashQueryAfterRootAwarePlan parameter input plan).run cache)) :=
                          mem_support_runDirectResolvedFromTable_of_done_detailed
                            ((probingHashQueryAfterRootAwarePlan parameter input plan).run cache)
                            context leftFuel table leftResult hleftDetailed
                        have hpreservesLeft : PreservesChainValid (fun _ ↦ True)
                            (probingHashQueryAfterRootAwarePlan parameter input plan) := by
                          have hclosed : ChainForwardClosed (fun _ ↦ True) := by
                            intro candidate _hallowed _houtput
                            trivial
                          unfold probingHashQueryAfterRootAwarePlan
                          cases hcandidateRoot : rootAwareCandidateForPlan? parameter input plan with
                          | none =>
                              simp only [executeCandidate?, pure_bind]
                              cases plan.action with
                              | ordinary =>
                                  exact preservesChainValid_splitHashQuery_ordinary (fun _ ↦ True)
                                    input
                              | resolve coordinate =>
                                  exact preservesChainValid_resolveKnownInput (fun _ ↦ True) hclosed
                                    parameter coordinate input
                          | some candidate =>
                              apply (preservesChainValid_probe (fun _ ↦ True) candidate).bind
                              intro _
                              cases plan.action with
                              | ordinary =>
                                  exact preservesChainValid_splitHashQuery_ordinary (fun _ ↦ True)
                                    input
                              | resolve coordinate =>
                                  exact preservesChainValid_resolveKnownInput (fun _ ↦ True) hclosed
                                    parameter coordinate input
                        have hleftChainValid : ChainState.ValidFor (fun _ ↦ True)
                            leftResult.context.state :=
                          chainValid_of_mem_runDirectResolvedFromTable (fun _ ↦ True)
                            (probingHashQueryAfterRootAwarePlan parameter input plan) context
                            leftFuel table cache leftResult hpreservesLeft hchainValid hleftDirect
                        have hrightChainStarts : ∀ lay tree leafIdx chainIdx,
                            (rightResult.context.state.values
                                  (.chainStart lay tree leafIdx chainIdx) ≠ none →
                                .chainStart lay tree leafIdx chainIdx ∈
                                  rightResult.context.state.revealed) ∧
                              (.chainStart lay tree leafIdx chainIdx ∈
                                  rightResult.context.state.revealed →
                                rightResult.context.state.values
                                  (.chainStart lay tree leafIdx chainIdx) ≠ none) := by
                          intro lay tree leafIdx chainIdx
                          have hleft := hleftChainValid (.chainStart lay tree leafIdx chainIdx)
                            (by simp [IsChainCoordinate])
                          have hvalue := congrFun hmaterialized
                            (.chainStart lay tree leafIdx chainIdx)
                          have hvalue' : leftResult.context.state.values
                              (.chainStart lay tree leafIdx chainIdx) =
                                rightResult.context.state.values
                                  (.chainStart lay tree leafIdx chainIdx) := by
                            simpa using hvalue
                          constructor
                          · intro hsome
                            have hleftSome : leftResult.context.state.values
                                (.chainStart lay tree leafIdx chainIdx) ≠ none := by
                              rw [hvalue']
                              exact hsome
                            rw [← hrevealed]
                            exact hleft.1 hleftSome
                          · intro hrightRevealed
                            have hleftRevealed : .chainStart lay tree leafIdx chainIdx ∈
                                leftResult.context.state.revealed := by
                              simpa [hrevealed] using hrightRevealed
                            have hleftSome := hleft.2.1 hleftRevealed
                            rw [← hvalue']
                            exact hleftSome
                        let canonical := canonicalizeMaterializedValues table rightResult.context
                        have hrightCompletable : DeferredCompletable table rightResult.context :=
                          (FinalizationContextLE.of_eq hfinal).rightCompletable
                        have hcanonicalFacts := valid_completable_canonicalizeMaterializedValues
                          table rightResult.context hfinal.2.2.1 hrightCompletable
                        have hcanonicalPublished : PublishedValues canonical.state :=
                          hrightPublished.to_canonicalizedMaterializedValues
                        have hcanonicalCanonical : CanonicalMaterializedValues table canonical :=
                          canonicalizeMaterializedValues_canonical table rightResult.context
                            hfinal.1.rightConsistent
                        have hcanonicalState : materializedDeferredState canonical =
                            rightResult.context.state := by
                          have heq := materializedDeferredState_canonicalize_direct_eq_of_chainStarts
                            table rightResult.context.state hfinal.1.rightStarts hrightChainStarts
                          dsimp only [canonical]
                          rw [hrightDirect]
                          exact heq
                        have hcanonicalChainValid : ChainState.ValidFor (fun _ ↦ True)
                            canonical.state := by
                          intro coordinate hcoordinate
                          constructor
                          · intro hsome
                            by_contra hhidden
                            have hhiddenRight : coordinate ∉ rightResult.context.state.revealed := by
                              simpa [canonical, canonicalizeMaterializedValues_revealed] using hhidden
                            change publicMaterializedValues table rightResult.context coordinate ≠ none
                              at hsome
                            simp [publicMaterializedValues, hhiddenRight] at hsome
                          · exact ⟨hcanonicalPublished coordinate, fun _ ↦ trivial⟩
                        have hleftPrivate : leftResult.context.values target =
                            some targetOutput :=
                          hprivateValues target targetOutput hprivate
                        have hleftMaterializedTarget :
                            (materializedDeferredState leftResult.context).values
                                (.position target) = some targetOutput := by
                          rw [materializedDeferredState_position]
                          unfold DeferredContext.positionValue
                          cases hstate : leftResult.context.state.values (.position target) with
                          | none => simp [hstate, hleftPrivate]
                          | some existing =>
                              have hagrees := hfinal.1.leftConsistent target existing hstate
                              rw [hleftPrivate] at hagrees
                              cases Option.some.inj hagrees
                              simp [hstate]
                        have hrightTarget : rightResult.context.state.values (.position target) =
                            some targetOutput := by
                          rw [← congrFun hmaterialized (.position target)]
                          exact hleftMaterializedTarget
                        have hcanonicalPrivate : canonical.values target = some targetOutput := by
                          change rightResult.context.values target = some targetOutput
                          rw [hrightDirect]
                          simpa [directDeferredContext, directDeferredValues] using hrightTarget
                        have hcanonicalPending : PendingCoveredBy
                            (nextSnapshots.map PlannedProbeSnapshot.toProbe) canonical := by
                          intro entry hentry
                          have hentryRight : entry ∈ rightResult.context.state.pending := by
                            simpa [canonical, canonicalizeMaterializedValues_pending] using hentry
                          obtain ⟨observation, hobservation, hcoordinate, hcand, _hhidden⟩ :=
                            hrightCovered entry hentryRight
                          refine ⟨observation.toProbe, ?_, hcoordinate, hcand⟩
                          rw [hnextAligned.map_toProbe_eq]
                          exact List.mem_map.mpr ⟨observation, hobservation, rfl⟩
                        have hcontextMaterialized : PrivateValuesLE context rightContext := by
                          intro position output hvalue
                          change context.positionValue position = some output
                          unfold DeferredContext.positionValue
                          cases hstate : context.state.values (.position position) with
                          | none => simp [hstate, hvalue]
                          | some existing =>
                              have hagrees := hvalid.valuesConsistent position existing hstate
                              rw [hvalue] at hagrees
                              cases Option.some.inj hagrees
                              simp [hstate]
                        have hmaterializedToRight : PrivateValuesLE rightContext
                            rightResult.context :=
                          privateValuesLE_of_done_runDirectResolvedDetailedFromTable
                            ((probingHashQueryAfterRootAwarePublicPlan parameter input context.state
                              plan).run cache)
                            rightContext rightFuel table rightResult hrightDetailed
                        have hrightRevealedSubset : context.state.revealed ⊆
                            rightResult.context.state.revealed := by
                          have hsubset := revealed_subset_of_mem_runObservedCleanFromTable
                            ((probingHashQueryAfterRootAwarePublicPlan parameter input context.state
                              plan).run cache)
                            observations (materializedDeferredState context) rightFuel table
                            (observedResolvedResult nextObservations rightResult) hrightSupport
                          simpa [observedResolvedResult] using hsubset
                        have hcanonicalBefore : SnapshotsBefore nextSnapshots canonical := by
                          simpa [nextSnapshots] using
                            (((hbefore.appendPlannedSnapshot candidate?).trans
                              hrightRevealedSubset
                              (hcontextMaterialized.trans hmaterializedToRight)).canonicalize_right
                                table)
                        have hleftPublished : PublishedValues leftResult.context.state :=
                          publishedValues_of_done_runDirectResolvedWitnessFromTable
                            (probingHashQueryAfterRootAwarePlan parameter input plan)
                            (preservesPublishedValues_probingHashQueryAfterRootAwarePlan parameter
                              input plan)
                            context leftFuel table cache leftResult hpublished
                            (by simpa [leftStep] using hleftSupport)
                        letI : ObserverSynchronized table
                            (negatedDirectDelayedObserve observe nextSnapshots nextObservations) :=
                          ⟨by
                            intro nextLeft nextRight remaining value hnextContext hnextValues
                              hnextRevealed
                            have hlaws := negatedDirectDelayedComputationObserve_observerLaws
                              ordinal parameter publicRoot ftsSecret table target rightRoot
                              (next value.1) nextSnapshots nextObservations hnextLength
                              hnextAligned.map_toProbe_eq.symm hnextNoHit
                            letI : ObserverSynchronized table
                                (negatedDirectDelayedComputationObserve ordinal parameter publicRoot
                                  ftsSecret table target rightRoot (next value.1) nextSnapshots
                                  nextObservations) := hlaws.1
                            simpa [observe, negatedDirectDelayedObserve,
                              negatedDirectDelayedComputationObserve] using
                              ObserverSynchronized.eq_of_synchronized
                                (table := table)
                                (observe := negatedDirectDelayedComputationObserve ordinal parameter
                                  publicRoot ftsSecret table target rightRoot (next value.1)
                                  nextSnapshots nextObservations)
                                nextLeft nextRight remaining value.2 hnextContext hnextValues
                                hnextRevealed⟩
                        let leftCanonicalRun :=
                          canonicalizeDirectDelayedSelectedRootIndicator table observe
                            leftResult.context leftResult.remaining leftResult.value nextSnapshots
                            nextObservations
                        let rightCanonicalRun :=
                          canonicalizeDirectDelayedSelectedRootIndicator table observe
                            rightResult.context leftResult.remaining leftResult.value nextSnapshots
                            nextObservations
                        have hnegatedEq : evalDist (Bool.not <$> leftCanonicalRun) =
                            evalDist (Bool.not <$> rightCanonicalRun) :=
                          evalDist_negatedCanonicalizeDirectDelayedObserve_eq_of_finalizationContextEq_published
                            table observe nextSnapshots nextObservations leftResult.context
                            rightResult.context leftResult.remaining leftResult.value hfinal hrevealed
                            hleftPublished hrightPublished
                        have hnegatedRel : RelTriple (Bool.not <$> rightCanonicalRun)
                            (Bool.not <$> leftCanonicalRun) (EqRel Bool) := by
                          apply relTriple_of_evalDist_eq_right hnegatedEq.symm
                          exact relTriple_refl _
                        have hnegatedImp : RelTriple (Bool.not <$> rightCanonicalRun)
                            (Bool.not <$> leftCanonicalRun) BoolImp := by
                          apply relTriple_post_mono hnegatedRel
                          intro rightNot leftNot heq htrue
                          rw [heq] at htrue
                          exact htrue
                        have hcanonicalBridge : RelTriple leftCanonicalRun rightCanonicalRun
                            BoolImp :=
                          relTriple_boolImp_of_not_reverse leftCanonicalRun rightCanonicalRun
                            hnegatedImp
                        have hnotPrivate : ¬PrivateStructuralHit canonical :=
                          not_privateStructuralHit_of_deferredCompletable hcanonicalFacts.2
                        have hrightCanonicalEq : rightCanonicalRun =
                            directDelayedSelectedRootIndicator ordinal parameter publicRoot ftsSecret
                              table target rightRoot (next leftResult.value.1) nextSnapshots
                              nextObservations canonical leftResult.remaining leftResult.value.2 := by
                          unfold rightCanonicalRun
                            canonicalizeDirectDelayedSelectedRootIndicator
                          simp only [canonical, hnotPrivate, hrightPublished, hcanonicalFacts.2,
                            ↓reduceIte]
                          rfl
                        rw [hrightCanonicalEq, houtput, hcache] at hcanonicalBridge
                        have hspentLe : (if candidate?.isSome then 1 else 0) ≤ 1 := by
                          split <;> omega
                        have hrecursive := ih rightResult.value.1 nextSnapshots nextObservations
                          canonical leftResult.remaining rightResult.remaining (bound - 1)
                          rightResult.value.2
                          (by simpa [IsOuterHash] using hbound.2 rightResult.value.1)
                          hcanonicalFacts.1 hcanonicalFacts.2 hcanonicalPublished
                          hcanonicalCanonical hcanonicalChainValid hcanonicalPrivate hnextAligned
                          hcanonicalBefore
                          (by rw [hcanonicalState]; exact hrightTracked)
                          (by rw [hcanonicalState]; exact hrightCovered)
                          hnextNoHit hcanonicalPending hnextLength
                          (by omega) (by omega) (by omega)
                          (by rw [hcanonicalState]; exact hrightBudget)
                        have hrecursive' : RelTriple
                            (directDelayedSelectedRootIndicator ordinal parameter publicRoot
                              ftsSecret table target rightRoot (next rightResult.value.1)
                              nextSnapshots nextObservations canonical leftResult.remaining
                              rightResult.value.2)
                            (rightObserve rightResult.context.state rightResult.remaining
                              rightResult.value.1 rightResult.value.2 nextObservations) BoolImp := by
                          change RelTriple _ _ BoolImp at hrecursive
                          simpa [rightObserve, hcanonicalState] using hrecursive
                        have hglued := SphincsSecurity.relTriple_trans_exists hcanonicalBridge
                          hrecursive'
                        apply relTriple_post_mono hglued
                        intro leftValue rightValue hrelation
                        obtain ⟨middle, hleftMiddle, hmiddleRight⟩ := hrelation
                        exact fun htrue ↦ hmiddleRight (hleftMiddle htrue))
                  refine relTriple_of_evalDist_eq_right ?_ hfinished
                  apply congrArg evalDist
                  apply bind_congr
                  intro result
                  cases result <;> rfl
                have htoGoal
                    (hbase : RelTriple
                      (leftStep >>= finishDirectDelayedSelectedRootIndicator
                        (canonicalizeDirectDelayedSelectedRootIndicator table observe)
                        nextSnapshots nextObservations)
                      (rightStep >>= fun result ↦
                        match result with
                        | none => pure false
                        | some result =>
                            rightObserve result.state result.remaining result.value.1
                              result.value.2 result.observations)
                      BoolImp) :
                    RelTriple
                      (leftStep >>= finishDirectDelayedSelectedRootIndicator
                        (canonicalizeDirectDelayedSelectedRootIndicator table observe)
                        nextSnapshots nextObservations)
                      (rightStep >>= fun result ↦
                        (successfulObservedRootComparisonIndicator table ordinal target ∘
                            fun observed ↦ (observed, rightRoot)) <$> match result with
                        | none => pure none
                        | some result =>
                            observedMaterializedBoundary parameter publicRoot ftsSecret
                              (next result.value.1) result.observations result.state
                              result.remaining table result.value.2)
                      BoolImp := by
                  refine relTriple_of_evalDist_eq_right ?_ hbase
                  apply congrArg evalDist
                  apply bind_congr
                  intro result
                  cases result with
                  | none =>
                      simp [rightObserve, successfulObservedRootComparisonIndicator,
                        ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
                        ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
                        ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt]
                  | some result => rfl
                cases hcandidate : candidate? with
                | none =>
                    have hnextSnapshotsEq : nextSnapshots = snapshots := by
                      simp [nextSnapshots, hcandidate, appendPlannedSnapshot]
                    have hnextObservationsEq : nextObservations = observations := by
                      simp [nextObservations, hcandidate, observationsAfterCandidate]
                    apply htoGoal
                    apply hcontinue
                    · intro candidate hsome _hhidden
                      simp [hcandidate] at hsome
                    · simpa [hnextSnapshotsEq, hnextObservationsEq] using haligned
                    · simpa [hnextObservationsEq] using hnoHit
                | some candidate =>
                    let actualNextObservations := observations ++
                      [cleanProbeObservation (materializedDeferredState context)
                        candidate.coordinate candidate.candidate]
                    have hnextObservationsEq : nextObservations = actualNextObservations := by
                      simp [nextObservations, candidate?, hcandidate, actualNextObservations,
                        observationsAfterCandidate]
                    have hnextAligned : SnapshotsObservedAt table nextSnapshots
                        nextObservations := by
                      rw [hnextObservationsEq]
                      simpa [actualNextObservations, nextSnapshots, candidate?, hcandidate,
                        observationsAfterCandidate, appendPlannedSnapshot] using
                        (haligned.appendCandidate (some candidate) hcontextDirect rfl hpublished
                          hcanonical)
                    by_cases hcandidateRevealed :
                        candidate.coordinate ∈ context.state.revealed
                    · have hnewNoHit :
                          ¬(cleanProbeObservation (materializedDeferredState context)
                            candidate.coordinate candidate.candidate).ExistingHiddenHit := by
                        rintro ⟨hhidden, _output, _hvalue, _hcandidate⟩
                        simp [cleanProbeObservation, hcandidateRevealed] at hhidden
                      have hnextNoHit : ∀ observation ∈ nextObservations,
                          ¬observation.ExistingHiddenHit := by
                        rw [hnextObservationsEq]
                        intro observation hobservation
                        simp only [actualNextObservations, List.mem_append,
                          List.mem_singleton] at hobservation
                        rcases hobservation with hold | rfl
                        · exact hnoHit observation hold
                        · exact hnewNoHit
                      apply htoGoal
                      apply hcontinue
                      · intro other hother hhidden
                        have heq : other = candidate := by
                          apply Option.some.inj
                          exact hother.symm.trans (by simpa [candidate?] using hcandidate)
                        subst other
                        exact (hhidden hcandidateRevealed).elim
                      · exact hnextAligned
                      · exact hnextNoHit
                    · let postContext : DeferredContext :=
                        { context with state :=
                            context.state.addPending candidate.coordinate candidate.candidate }
                      by_cases hpostCompletable : DeferredCompletable table postContext
                      · have hrightPostCompletable : DeferredCompletable table
                            { rightContext with state :=
                                (rightContext.state.addPending candidate.coordinate
                                  candidate.candidate) } := by
                          exact (deferredCompletable_addPending_iff_of_finalizationViewEq
                            hcontextEq.1 candidate.coordinate candidate.candidate).mp
                              (by simpa [postContext] using hpostCompletable)
                        have hnewNoHit :
                            ¬(cleanProbeObservation (materializedDeferredState context)
                              candidate.coordinate candidate.candidate).ExistingHiddenHit := by
                          simpa [rightContext, materializedDeferredContext,
                            directDeferredContext] using
                            (not_existingHiddenHit_cleanProbeObservation_of_addPending_completable
                              table rightContext candidate hrightPostCompletable)
                        have hnextNoHit : ∀ observation ∈ nextObservations,
                            ¬observation.ExistingHiddenHit := by
                          rw [hnextObservationsEq]
                          intro observation hobservation
                          simp only [actualNextObservations, List.mem_append,
                            List.mem_singleton] at hobservation
                          rcases hobservation with hold | rfl
                          · exact hnoHit observation hold
                          · exact hnewNoHit
                        apply htoGoal
                        apply hcontinue
                        · intro other hother _hhidden
                          have heq : other = candidate := by
                            apply Option.some.inj
                            exact hother.symm.trans (by simpa [candidate?] using hcandidate)
                          subst other
                          simpa [postContext] using hpostCompletable
                        · exact hnextAligned
                        · exact hnextNoHit
                      · apply relTriple_of_not_true_mem_support
                        intro htrue
                        rw [mem_support_bind_iff] at htrue
                        obtain ⟨step, hstepSupport, hfinishSupport⟩ := htrue
                        cases step with
                        | stoppedFuel =>
                            simp [finishDirectDelayedSelectedRootIndicator] at hfinishSupport
                        | stoppedOrdinary =>
                            simp [finishDirectDelayedSelectedRootIndicator] at hfinishSupport
                        | stoppedPrivate witness =>
                            simp [finishDirectDelayedSelectedRootIndicator] at hfinishSupport
                        | done result =>
                            cases leftFuel with
                            | zero => omega
                            | succ remaining =>
                                have hcandidateRoot : rootAwareCandidateForPlan? parameter input
                                    plan = some candidate := by
                                  simpa [candidate?] using hcandidate
                                have hpostSupport : DirectWitnessResult.done result ∈ support
                                    (runDirectResolvedWitnessFromTable postContext remaining table
                                      ((probingHashQueryPublicAction parameter input context.state
                                        plan.action).run cache)) := by
                                  dsimp only [leftStep] at hstepSupport
                                  rw [runDirectResolvedWitnessFromTable_rootAwarePrivate_eq_public
                                    parameter input plan context (remaining + 1) table cache]
                                    at hstepSupport
                                  unfold probingHashQueryAfterRootAwarePublicPlan at hstepSupport
                                  rw [StateT.run_bind, runDirectResolvedWitnessFromTable_bind]
                                    at hstepSupport
                                  simp only [hcandidateRoot, executeCandidate?, probe,
                                    StateT.run_liftM, LazyRevealProbe.probeQuery,
                                    runDirectResolvedWitnessFromTable_probe_query_bind,
                                    hcandidateRevealed, ↓reduceIte] at hstepSupport
                                  rw [show
                                    runDirectResolvedWitnessFromTable postContext remaining table
                                        (pure ((), cache)) =
                                      pure (.done ⟨postContext, remaining, ((), cache), table⟩) by
                                    simp [runDirectResolvedWitnessFromTable]] at hstepSupport
                                  simp only [pure_bind] at hstepSupport
                                  simpa [postContext] using hstepSupport
                                have hpostDetailed : DirectDetailedResult.done result ∈ support
                                    (runDirectResolvedDetailedFromTable postContext remaining table
                                      ((probingHashQueryPublicAction parameter input context.state
                                        plan.action).run cache)) := by
                                  rw [← map_erase_runDirectResolvedWitnessFromTable
                                    ((probingHashQueryPublicAction parameter input context.state
                                      plan.action).run cache)
                                    postContext remaining table, support_map]
                                  exact ⟨.done result, hpostSupport, rfl⟩
                                have hpostDirect : some result ∈ support
                                    (runDirectResolvedFromTable postContext remaining table
                                      ((probingHashQueryPublicAction parameter input context.state
                                        plan.action).run cache)) :=
                                  mem_support_runDirectResolvedFromTable_of_done_detailed
                                    ((probingHashQueryPublicAction parameter input context.state
                                      plan.action).run cache)
                                    postContext remaining table result hpostDetailed
                                have hpostConsistent : postContext.ValuesConsistent := by
                                  intro position output hvalue
                                  exact hvalid.1 position output (by
                                    simpa [postContext, LazyRevealProbe.State.addPending] using
                                      hvalue)
                                have hpostStarts : StartTableAgrees postContext.state table := by
                                  intro index output hvalue
                                  exact hcontextEq.1.leftStarts index output (by
                                    simpa [postContext, LazyRevealProbe.State.addPending] using
                                      hvalue)
                                have hresultCore := resolvedCore_of_mem_runDirectResolvedFromTable
                                  ((probingHashQueryPublicAction parameter input context.state
                                    plan.action).run cache)
                                  postContext remaining table result hpostConsistent
                                  hpostStarts hpostDirect
                                have hresultNotCompletable :
                                    ¬DeferredCompletable table result.context :=
                                  not_deferredCompletable_of_mem_runDirectResolvedFromTable
                                    ((probingHashQueryPublicAction parameter input context.state
                                      plan.action).run cache)
                                    postContext remaining table result hpostConsistent
                                    hpostStarts hpostDirect (by
                                      simpa [postContext] using hpostCompletable)
                                have hcanonicalDoomed :=
                                  doomedResolvedContext_canonicalizeMaterializedValues
                                    (⟨hresultCore.2.1, hresultCore.2.2,
                                      hresultNotCompletable⟩ : DoomedResolvedContext table
                                        result.context)
                                simp [finishDirectDelayedSelectedRootIndicator,
                                  canonicalizeDirectDelayedSelectedRootIndicator,
                                  hcanonicalDoomed.2.2] at hfinishSupport
      | inr message =>
          change Option Signature → OracleComp (OracleWorld + SigningSpec)
            RetainedRestResult at next
          rw [directDelayedSelectedRootIndicator_signing_eq ordinal parameter publicRoot
            ftsSecret table target rightRoot message next snapshots observations context leftFuel
            cache hnotSelected]
          rw [observedMaterializedBoundary_sign_query_bind]
          simp only [map_bind]
          let rightContext := materializedDeferredContext context
          have hcontextEq : FinalizationContextEq table (some context) (some rightContext) := by
            exact finalizationContextEq_materializedDeferredContext hvalid hcompletable
          have hstep :=
            (directWitnessFinalizationMaterializedCouples_maskedSign table parameter publicRoot
              ftsSecret message) context rightContext leftFuel rightFuel cache cache hcontextEq rfl
                rfl rfl (by rfl)
          let observe : DeferredContext → Nat →
              (Option Signature × SplitHashCache) → List PlannedProbeSnapshot →
                List CleanProbeObservation → ProbComp Bool :=
            fun nextContext remaining value laterSnapshots laterObservations =>
              directDelayedSelectedRootIndicator ordinal parameter publicRoot ftsSecret table
                target rightRoot (next value.1) laterSnapshots laterObservations nextContext
                remaining value.2
          let rightObserve : LazyRevealProbe.State Coordinate → Nat → Option Signature →
              SplitHashCache → List CleanProbeObservation → ProbComp Bool :=
            fun state remaining signature nextCache laterObservations =>
              (successfulObservedRootComparisonIndicator table ordinal target ∘
                  fun observed => (observed, rightRoot)) <$>
                observedMaterializedBoundary parameter publicRoot ftsSecret (next signature)
                  laterObservations state remaining table nextCache
          have hfinishProgram := runDirectDetailed_finish_eq_runObservedClean_finish
            ((maskedSign parameter publicRoot ftsSecret message).run cache) observations
            (materializedDeferredState context) rightFuel table rightObserve
            (maskedSign_probeFree parameter publicRoot ftsSecret message cache)
          have hrightProgram :
              (runObservedCleanFromTable observations (materializedDeferredState context)
                    rightFuel table ((maskedSign parameter publicRoot ftsSecret message).run cache) >>=
                fun result => match result with
                | none => pure false
                | some result => rightObserve result.state result.remaining result.value.1
                    result.value.2 result.observations) =
              (runObservedCleanFromTable observations (materializedDeferredState context)
                    rightFuel table ((maskedSign parameter publicRoot ftsSecret message).run cache) >>=
                fun result =>
                  (successfulObservedRootComparisonIndicator table ordinal target ∘
                      fun observed => (observed, rightRoot)) <$> match result with
                  | none => pure none
                  | some result =>
                      observedMaterializedBoundary parameter publicRoot ftsSecret
                        (next result.value.1) result.observations result.state result.remaining
                        table result.value.2) := by
            apply bind_congr
            intro result
            cases result with
            | none =>
                simp [rightObserve, successfulObservedRootComparisonIndicator,
                  ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
                  ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
                  ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt]
            | some result => rfl
          dsimp only [rightContext, materializedDeferredContext] at hstep
          change RelTriple _
            (runObservedCleanFromTable observations (materializedDeferredState context)
                rightFuel table ((maskedSign parameter publicRoot ftsSecret message).run cache) >>=
              fun result =>
                (successfulObservedRootComparisonIndicator table ordinal target ∘
                    fun observed => (observed, rightRoot)) <$> match result with
                | none => pure none
                | some result =>
                    observedMaterializedBoundary parameter publicRoot ftsSecret
                      (next result.value.1) result.observations result.state result.remaining table
                      result.value.2)
            SuccessfulObservedIndicatorRel
          change RelTriple _ _ BoolImp
          have hcoupled := relTriple_finishDirectWitness_directDetailed table context.values
            leftFuel rightFuel
            (runDirectResolvedWitnessFromTable context leftFuel table
              ((maskedSign parameter publicRoot ftsSecret message).run cache))
            (runDirectResolvedDetailedFromTable
              (directDeferredContext (materializedDeferredState context)) rightFuel table
              ((maskedSign parameter publicRoot ftsSecret message).run cache))
            (canonicalizeDirectDelayedSelectedRootIndicator table observe) rightObserve snapshots
              observations hstep
          have hbase := hcoupled (by
            intro leftResult rightResult hleftSupport hrightSupport hrelation
            rcases hrelation with
              ⟨houtput, hfinal, hleftRemaining, hrightRemaining, hleftTable,
                hrightTable, hcache, hrevealed, hmaterialized, hprivateValues,
                hrightDirect⟩
            have hrightObserved : some (observedResolvedResult observations rightResult) ∈
                support (runObservedCleanFromTable observations
                  (materializedDeferredState context) rightFuel table
                  ((maskedSign parameter publicRoot ftsSecret message).run cache)) := by
              rw [← map_observedResultOfDetailed_run_eq_observed_of_probeFree
                ((maskedSign parameter publicRoot ftsSecret message).run cache) observations
                (materializedDeferredState context) rightFuel table
                (maskedSign_probeFree parameter publicRoot ftsSecret message cache), support_map]
              exact ⟨.done rightResult, hrightSupport, rfl⟩
            have hinitialPublished : PublishedValues (materializedDeferredState context) := by
              intro coordinate hcoordinate
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  exact hpublished _ (by simpa using hcoordinate)
              | position position =>
                  have hvalue := hpublished (.position position) (by simpa using hcoordinate)
                  obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hvalue
                  simp [materializedDeferredState, DeferredContext.positionValue, houtput]
            have hrightPublished : PublishedValues rightResult.context.state :=
              publishedValues_of_done_runDirectResolvedDetailedFromTable
                (maskedSign parameter publicRoot ftsSecret message)
                (preservesPublishedValues_maskedSign parameter publicRoot ftsSecret message)
                (directDeferredContext (materializedDeferredState context)) rightFuel table cache
                rightResult (by simpa [directDeferredContext] using hinitialPublished)
                hrightSupport
            have hrightTracked : CleanProbeObservationsTrackedBy observations
                rightResult.context.state := by
              simpa [observedResolvedResult] using
                cleanProbeObservationsTrackedBy_of_mem_runObservedCleanFromTable
                  ((maskedSign parameter publicRoot ftsSecret message).run cache) observations
                  (materializedDeferredState context) rightFuel table htracked
                  (observedResolvedResult observations rightResult) hrightObserved
            have hrightCovered : CleanProbeObservationsCoverPending observations
                rightResult.context.state := by
              simpa [observedResolvedResult] using
                cleanProbeObservationsCoverPending_of_mem_runObservedCleanFromTable
                  ((maskedSign parameter publicRoot ftsSecret message).run cache) observations
                  (materializedDeferredState context) rightFuel table hcovered
                  (observedResolvedResult observations rightResult) hrightObserved
            have hrightBudget : rightResult.remaining +
                rightResult.context.state.pending.card < Fintype.card Digest := by
              have hremaining := remaining_add_pending_card_le_of_mem_runObservedCleanFromTable
                ((maskedSign parameter publicRoot ftsSecret message).run cache) observations
                (materializedDeferredState context) rightFuel table
                (observedResolvedResult observations rightResult) hrightObserved
              simpa [observedResolvedResult] using hremaining.trans_lt hbudget
            have hleftDetailed : DirectDetailedResult.done leftResult ∈ support
                (runDirectResolvedDetailedFromTable context leftFuel table
                  ((maskedSign parameter publicRoot ftsSecret message).run cache)) := by
              rw [← map_erase_runDirectResolvedWitnessFromTable
                ((maskedSign parameter publicRoot ftsSecret message).run cache) context leftFuel
                table, support_map]
              exact ⟨.done leftResult, hleftSupport, rfl⟩
            have hleftDirect : some leftResult ∈ support
                (runDirectResolvedFromTable context leftFuel table
                  ((maskedSign parameter publicRoot ftsSecret message).run cache)) :=
              mem_support_runDirectResolvedFromTable_of_done_detailed
                ((maskedSign parameter publicRoot ftsSecret message).run cache) context leftFuel
                table leftResult hleftDetailed
            have hleftChainValid : ChainState.ValidFor (fun _ ↦ True)
                leftResult.context.state :=
              chainValid_of_mem_runDirectResolvedFromTable (fun _ ↦ True)
                (maskedSign parameter publicRoot ftsSecret message) context leftFuel table cache
                leftResult
                (preservesChainValid_maskedSign_true parameter publicRoot ftsSecret message)
                hchainValid hleftDirect
            have hrightChainStarts : ∀ lay tree leafIdx chainIdx,
                (rightResult.context.state.values (.chainStart lay tree leafIdx chainIdx) ≠ none →
                    .chainStart lay tree leafIdx chainIdx ∈ rightResult.context.state.revealed) ∧
                  (.chainStart lay tree leafIdx chainIdx ∈ rightResult.context.state.revealed →
                    rightResult.context.state.values (.chainStart lay tree leafIdx chainIdx) ≠
                      none) := by
              intro lay tree leafIdx chainIdx
              have hleft := hleftChainValid (.chainStart lay tree leafIdx chainIdx)
                (by simp [IsChainCoordinate])
              have hvalue := congrFun hmaterialized (.chainStart lay tree leafIdx chainIdx)
              have hvalue' : leftResult.context.state.values
                  (.chainStart lay tree leafIdx chainIdx) =
                    rightResult.context.state.values
                      (.chainStart lay tree leafIdx chainIdx) := by
                simpa using hvalue
              constructor
              · intro hsome
                have hleftSome : leftResult.context.state.values
                    (.chainStart lay tree leafIdx chainIdx) ≠ none := by
                  rw [hvalue']
                  exact hsome
                rw [← hrevealed]
                exact hleft.1 hleftSome
              · intro hrightRevealed
                have hleftRevealed : .chainStart lay tree leafIdx chainIdx ∈
                    leftResult.context.state.revealed := by simpa [hrevealed] using hrightRevealed
                have hleftSome := hleft.2.1 hleftRevealed
                rw [← hvalue']
                exact hleftSome
            let canonical := canonicalizeMaterializedValues table rightResult.context
            have hrightCompletable : DeferredCompletable table rightResult.context :=
              (FinalizationContextLE.of_eq hfinal).rightCompletable
            have hcanonicalFacts := valid_completable_canonicalizeMaterializedValues table
              rightResult.context hfinal.2.2.1 hrightCompletable
            have hcanonicalPublished : PublishedValues canonical.state := by
              exact hrightPublished.to_canonicalizedMaterializedValues
            have hcanonicalCanonical : CanonicalMaterializedValues table canonical := by
              exact canonicalizeMaterializedValues_canonical table rightResult.context
                hfinal.1.rightConsistent
            have hcanonicalState : materializedDeferredState canonical =
                rightResult.context.state := by
              have heq := materializedDeferredState_canonicalize_direct_eq_of_chainStarts table
                rightResult.context.state hfinal.1.rightStarts hrightChainStarts
              dsimp only [canonical]
              rw [hrightDirect]
              exact heq
            have hcanonicalChainValid : ChainState.ValidFor (fun _ ↦ True)
                canonical.state := by
              intro coordinate hcoordinate
              constructor
              · intro hsome
                by_contra hhidden
                have hhiddenRight : coordinate ∉ rightResult.context.state.revealed := by
                  simpa [canonical, canonicalizeMaterializedValues_revealed] using hhidden
                change publicMaterializedValues table rightResult.context coordinate ≠ none at hsome
                simp [publicMaterializedValues, hhiddenRight] at hsome
              · exact ⟨hcanonicalPublished coordinate, fun _ ↦ trivial⟩
            have hleftPrivate : leftResult.context.values target = some targetOutput :=
              hprivateValues target targetOutput hprivate
            have hleftMaterializedTarget :
                (materializedDeferredState leftResult.context).values (.position target) =
                  some targetOutput := by
              rw [materializedDeferredState_position]
              unfold DeferredContext.positionValue
              cases hstate : leftResult.context.state.values (.position target) with
              | none => simp [hstate, hleftPrivate]
              | some existing =>
                  have hagrees := hfinal.1.leftConsistent target existing hstate
                  rw [hleftPrivate] at hagrees
                  cases Option.some.inj hagrees
                  simp [hstate]
            have hrightTarget : rightResult.context.state.values (.position target) =
                some targetOutput := by
              rw [← congrFun hmaterialized (.position target)]
              exact hleftMaterializedTarget
            have hcanonicalPrivate : canonical.values target = some targetOutput := by
              change rightResult.context.values target = some targetOutput
              rw [hrightDirect]
              simpa [directDeferredContext, directDeferredValues] using hrightTarget
            have hrightPendingSubset : rightResult.context.state.pending ⊆
                (directDeferredContext (materializedDeferredState context)).state.pending :=
              pending_subset_of_done_runDirectResolvedDetailedFromTable_of_probeFree
                ((maskedSign parameter publicRoot ftsSecret message).run cache)
                (directDeferredContext (materializedDeferredState context)) rightFuel table
                rightResult (maskedSign_probeFree parameter publicRoot ftsSecret message cache)
                hrightSupport
            have hcanonicalPending : PendingCoveredBy
                (snapshots.map PlannedProbeSnapshot.toProbe) canonical := by
              apply (pendingCoveredBy_canonicalize_iff table
                (snapshots.map PlannedProbeSnapshot.toProbe) rightResult.context).2
              apply hpending.of_subset
              intro entry hentry
              have := hrightPendingSubset hentry
              simpa [directDeferredContext, materializedDeferredState] using this
            have hcontextMaterialized : PrivateValuesLE context
                (directDeferredContext (materializedDeferredState context)) := by
              intro position output hvalue
              change context.positionValue position = some output
              unfold DeferredContext.positionValue
              cases hstate : context.state.values (.position position) with
              | none => simp [hstate, hvalue]
              | some existing =>
                  have hagrees := hvalid.valuesConsistent position existing hstate
                  rw [hvalue] at hagrees
                  cases Option.some.inj hagrees
                  simp [hstate]
            have hmaterializedToRight : PrivateValuesLE
                (directDeferredContext (materializedDeferredState context))
                rightResult.context :=
              privateValuesLE_of_done_runDirectResolvedDetailedFromTable
                ((maskedSign parameter publicRoot ftsSecret message).run cache)
                (directDeferredContext (materializedDeferredState context)) rightFuel table
                rightResult hrightSupport
            have hrightRevealedSubset : context.state.revealed ⊆
                rightResult.context.state.revealed := by
              have hsubset := revealed_subset_of_mem_runObservedCleanFromTable
                ((maskedSign parameter publicRoot ftsSecret message).run cache) observations
                (materializedDeferredState context) rightFuel table
                (observedResolvedResult observations rightResult) hrightObserved
              simpa [observedResolvedResult] using hsubset
            have hcanonicalBefore : SnapshotsBefore snapshots canonical :=
              (hbefore.trans hrightRevealedSubset
                (hcontextMaterialized.trans hmaterializedToRight)).canonicalize_right table
            have hleftPublished : PublishedValues leftResult.context.state :=
              publishedValues_of_done_runDirectResolvedWitnessFromTable
                (maskedSign parameter publicRoot ftsSecret message)
                (preservesPublishedValues_maskedSign parameter publicRoot ftsSecret message)
                context leftFuel table cache leftResult hpublished hleftSupport
            letI : ObserverSynchronized table
                (negatedDirectDelayedObserve observe snapshots observations) := ⟨by
              intro nextLeft nextRight remaining value hnextContext hnextValues hnextRevealed
              have hlaws := negatedDirectDelayedComputationObserve_observerLaws ordinal parameter
                publicRoot ftsSecret table target rightRoot (next value.1) snapshots observations
                hlength haligned.map_toProbe_eq.symm hnoHit
              letI : ObserverSynchronized table
                  (negatedDirectDelayedComputationObserve ordinal parameter publicRoot ftsSecret
                    table target rightRoot (next value.1) snapshots observations) := hlaws.1
              simpa [observe, negatedDirectDelayedObserve,
                negatedDirectDelayedComputationObserve] using
                ObserverSynchronized.eq_of_synchronized
                  (table := table)
                  (observe := negatedDirectDelayedComputationObserve ordinal parameter
                    publicRoot ftsSecret table target rightRoot (next value.1)
                    snapshots observations)
                  nextLeft nextRight remaining value.2 hnextContext hnextValues hnextRevealed⟩
            let leftCanonicalRun := canonicalizeDirectDelayedSelectedRootIndicator table observe
              leftResult.context leftResult.remaining leftResult.value snapshots observations
            let rightCanonicalRun := canonicalizeDirectDelayedSelectedRootIndicator table observe
              rightResult.context leftResult.remaining leftResult.value snapshots observations
            have hnegatedEq : evalDist (Bool.not <$> leftCanonicalRun) =
                evalDist (Bool.not <$> rightCanonicalRun) := by
              exact evalDist_negatedCanonicalizeDirectDelayedObserve_eq_of_finalizationContextEq_published
                table observe snapshots observations leftResult.context rightResult.context
                leftResult.remaining leftResult.value hfinal hrevealed hleftPublished
                hrightPublished
            have hnegatedRel : RelTriple (Bool.not <$> rightCanonicalRun)
                (Bool.not <$> leftCanonicalRun) (EqRel Bool) := by
              apply relTriple_of_evalDist_eq_right hnegatedEq.symm
              exact relTriple_refl _
            have hnegatedImp : RelTriple (Bool.not <$> rightCanonicalRun)
                (Bool.not <$> leftCanonicalRun) BoolImp := by
              apply relTriple_post_mono hnegatedRel
              intro rightNot leftNot heq
              intro htrue
              rw [heq] at htrue
              exact htrue
            have hcanonicalBridge : RelTriple leftCanonicalRun rightCanonicalRun BoolImp :=
              relTriple_boolImp_of_not_reverse leftCanonicalRun rightCanonicalRun hnegatedImp
            have hnotPrivate : ¬PrivateStructuralHit canonical :=
              not_privateStructuralHit_of_deferredCompletable hcanonicalFacts.2
            have hrightCanonicalEq : rightCanonicalRun =
                directDelayedSelectedRootIndicator ordinal parameter publicRoot ftsSecret table
                  target rightRoot (next leftResult.value.1) snapshots observations canonical
                  leftResult.remaining leftResult.value.2 := by
              unfold rightCanonicalRun canonicalizeDirectDelayedSelectedRootIndicator
              simp only [canonical, hnotPrivate, hrightPublished, hcanonicalFacts.2, ↓reduceIte]
              rfl
            rw [hrightCanonicalEq, houtput, hcache] at hcanonicalBridge
            have hrecursive := ih rightResult.value.1 snapshots observations canonical
              leftResult.remaining rightResult.remaining bound rightResult.value.2
              (by simpa [IsOuterHash] using hbound.2 rightResult.value.1)
              hcanonicalFacts.1 hcanonicalFacts.2 hcanonicalPublished hcanonicalCanonical
              hcanonicalChainValid hcanonicalPrivate haligned hcanonicalBefore
              (by rw [hcanonicalState]; exact hrightTracked)
              (by rw [hcanonicalState]; exact hrightCovered)
              hnoHit hcanonicalPending hlength
              (by omega) (by omega) (by omega)
              (by rw [hcanonicalState]; exact hrightBudget)
            have hrecursive' : RelTriple
                (directDelayedSelectedRootIndicator ordinal parameter publicRoot ftsSecret table
                  target rightRoot (next rightResult.value.1) snapshots observations canonical
                  leftResult.remaining rightResult.value.2)
                (rightObserve rightResult.context.state rightResult.remaining
                  rightResult.value.1 rightResult.value.2 observations) BoolImp := by
              change RelTriple _ _ BoolImp at hrecursive
              simpa [rightObserve, hcanonicalState] using hrecursive
            have hglued := SphincsSecurity.relTriple_trans_exists hcanonicalBridge hrecursive'
            apply relTriple_post_mono hglued
            intro leftValue rightValue hrelation
            obtain ⟨middle, hleftMiddle, hmiddleRight⟩ := hrelation
            exact fun htrue ↦ hmiddleRight (hleftMiddle htrue))
          have hfinishEval := congrArg evalDist hfinishProgram
          dsimp only [rightObserve] at hfinishEval
          refine relTriple_of_evalDist_eq_right ?_ hbase
          rw [hfinishEval]
          apply congrArg evalDist
          apply bind_congr
          intro result
          cases result with
          | none =>
              simp [successfulObservedRootComparisonIndicator,
                ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
                ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
                ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt]
          | some result => rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
