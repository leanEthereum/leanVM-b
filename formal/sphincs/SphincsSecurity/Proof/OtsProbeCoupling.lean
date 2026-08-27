import SphincsSecurity.Proof.OtsProbeTrace
import SphincsSecurity.Proof.FtsProbeProbability

/-!
# Retained one-time game coupling

The ordinary side of the split probing oracle is exactly the real lazy random oracle. This module
packages that distributional identity as the relational kernel used by the retained-game lift.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def RawOrdinaryResultRel :
    LazyRevealProbe.RawResult Coordinate (alpha × SplitHashCache) →
      (alpha × QueryCache HashSpec) → Prop
  | .stopped _, _ => False
  | .done _ _ (value, cache), ordinaryResult =>
      ordinaryResult = (value, ordinaryQueryCache cache)

def RawOrdinaryResultRelAt
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) :
    LazyRevealProbe.RawResult Coordinate (alpha × SplitHashCache) →
      (alpha × QueryCache HashSpec) → Prop
  | .stopped _, _ => False
  | .done finalState remaining (value, cache), ordinaryResult =>
      finalState = state ∧ remaining = fuel ∧
        ordinaryResult = (value, ordinaryQueryCache cache)

theorem exists_right_mem_support_of_relTriple
    {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    [IsUniformSpec spec₁] [IsUniformSpec spec₂]
    {left : OracleComp spec₁ alpha} {right : OracleComp spec₂ beta}
    {relation : alpha → beta → Prop}
    (hrel : RelTriple left right relation) {leftResult : alpha}
    (hleft : leftResult ∈ support left) :
    ∃ rightResult ∈ support right, relation leftResult rightResult := by
  rw [relTriple_iff_relWP, relWP_iff_couplingPost] at hrel
  obtain ⟨coupling, hcoupled⟩ := hrel
  have hleftEval : leftResult ∈ support 𝒟[left] := by
    rw [mem_support_iff_evalDist_apply_ne_zero] at hleft ⊢
    exact hleft
  have hleftMapped : leftResult ∈ support (Prod.fst <$> coupling.1) := by
    rw [coupling.2.map_fst]
    exact hleftEval
  rw [support_map] at hleftMapped
  obtain ⟨jointResult, hjoint, hfst⟩ := hleftMapped
  rcases jointResult with ⟨coupledLeft, coupledRight⟩
  simp only at hfst
  subst coupledLeft
  refine ⟨coupledRight, ?_, hcoupled (leftResult, coupledRight) hjoint⟩
  have hrightMapped : coupledRight ∈ support (Prod.snd <$> coupling.1) := by
    rw [support_map]
    exact ⟨(leftResult, coupledRight), hjoint, rfl⟩
  rw [coupling.2.map_snd] at hrightMapped
  rw [mem_support_iff_evalDist_apply_ne_zero] at hrightMapped ⊢
  exact hrightMapped

theorem probingHashQuery_eq_splitHashQuery_of_stable
    (parameter : PublicParameter) (input : HashInput)
    (hstable : StableOrdinaryInput parameter input) :
    probingHashQuery parameter input = splitHashQuery (.ordinary input) := by
  unfold probingHashQuery
  rw [hstable.1]
  cases hposition : decodePosition? parameter input with
  | none => rfl
  | some position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          exact (hstable.2 _ hposition (by trivial)).elim
      | leaf lay tree leafIdx =>
          exact (hstable.2 _ hposition (by trivial)).elim
      | node lay tree level nodeIdx =>
          exact (hstable.2 _ hposition (by trivial)).elim
      | ftsLeaf | ftsNode | ftsRoots => rfl

theorem probingHashImpl_eq_ordinaryHashImpl_of_stable
    (parameter : PublicParameter) (input : HashInput)
    (hstable : StableOrdinaryInput parameter input) :
    probingHashImpl parameter input = ordinaryHashImpl input :=
  probingHashQuery_eq_splitHashQuery_of_stable parameter input hstable

theorem tableAnswer_eq_fallback_of_stable
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (fallback : QueryImpl HashSpec Id) (input : HashInput)
    (hstable : StableOrdinaryInput parameter input) :
    tableAnswer parameter table fallback input = fallback input := by
  unfold tableAnswer
  cases hposition : decodePosition? parameter input with
  | none => rfl
  | some position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          exact (hstable.2 _ hposition (by trivial)).elim
      | leaf lay tree leafIdx =>
          exact (hstable.2 _ hposition (by trivial)).elim
      | node lay tree level nodeIdx =>
          exact (hstable.2 _ hposition (by trivial)).elim
      | ftsLeaf | ftsNode | ftsRoots => rfl

theorem stableCacheAgreesWithFn_tableAnswer
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (cache : SplitHashCache) :
    StableCacheAgreesWithFn parameter cache
      (tableAnswer parameter table (splitFallback cache)) := by
  intro input output hstable hcached
  rw [tableAnswer_eq_fallback_of_stable parameter table _ input hstable]
  simp [splitFallback, hcached]

theorem tableAnswer_realizes_otsPositions
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (fallback : QueryImpl HashSpec Id) :
    ∀ position : Position, IsOtsPosition position →
      tableAnswer parameter table fallback
          (tableInput parameter table (.position position)) =
        table (.position position) := by
  intro position hposition
  exact tableAnswer_tableInput parameter table fallback position hposition

theorem mergedCache_extendTable_agreesWith_tableAnswer
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate)
    (base : Coordinate → HashOutput) (cache : SplitHashCache)
    (hconsistent : HiddenConsistent state cache) :
    (mergedCache parameter (extendTable state base) state.ensured cache).AgreesWithFn
      (tableAnswer parameter (extendTable state base) (splitFallback cache)) := by
  apply mergedCache_agreesWith_tableAnswer
  exact completedSplitHashCache_extendTable_consistent state cache base hconsistent

private theorem attach_flatMap_val {α β : Type*} (xs : List α) (g : α → List β) :
    xs.attach.flatMap (fun x => g x.1) = xs.flatMap g := by
  calc
    _ = (xs.attach.map Subtype.val).flatMap g := by rw [List.flatMap_map]
    _ = xs.flatMap g := by rw [List.attach_map_subtype_val]

private theorem positionDepth_wf :
    WellFounded (fun child parent : Position => child.depth < parent.depth) :=
  (measure Position.depth).wf

private noncomputable def completedRealizedPositionBody
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (state : LazyRevealProbe.State Coordinate)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (position : Position)
    (recurse : ∀ child : Position, child.depth < position.depth → HashOutput) : HashOutput :=
  match state.values (.position position) with
  | some output => output
  | none =>
      show HashOutput from f (tweakableHashInput parameter position.domain <|
        match position with
        | .chain lay tree leafIdx chainIdx step =>
            if step.val = 0 then
              digestBytes (truncateHash ((state.values
                (.chainStart lay tree leafIdx chainIdx)).getD
                  (baseStarts lay tree leafIdx chainIdx)))
            else
              (Position.chain lay tree leafIdx chainIdx step).children.attach.flatMap fun child =>
                digestBytes (truncateHash (recurse child.1
                  (Position.depth_lt_of_mem_children child.2)))
        | .leaf lay tree leafIdx =>
            (Position.leaf lay tree leafIdx).children.attach.flatMap fun child =>
              digestBytes (truncateHash (recurse child.1
                (Position.depth_lt_of_mem_children child.2)))
        | .node lay tree level nodeIdx =>
            (Position.node lay tree level nodeIdx).children.attach.flatMap fun child =>
              digestBytes (truncateHash (recurse child.1
                (Position.depth_lt_of_mem_children child.2)))
        | .ftsLeaf index tree leafIdx =>
            (Position.ftsLeaf index tree leafIdx).children.attach.flatMap fun child =>
              digestBytes (truncateHash (recurse child.1
                (Position.depth_lt_of_mem_children child.2)))
        | .ftsNode index tree level nodeIdx =>
            (Position.ftsNode index tree level nodeIdx).children.attach.flatMap fun child =>
              digestBytes (truncateHash (recurse child.1
                (Position.depth_lt_of_mem_children child.2)))
        | .ftsRoots index =>
            (Position.ftsRoots index).children.attach.flatMap fun child =>
              digestBytes (truncateHash (recurse child.1
                (Position.depth_lt_of_mem_children child.2))))

noncomputable def completedRealizedPositionOutput
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (state : LazyRevealProbe.State Coordinate)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput) :
    Position → HashOutput :=
  positionDepth_wf.fix (completedRealizedPositionBody f parameter state baseStarts)

theorem completedRealizedPositionOutput_eq
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (state : LazyRevealProbe.State Coordinate)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (position : Position) :
    completedRealizedPositionOutput f parameter state baseStarts position =
      completedRealizedPositionBody f parameter state baseStarts position
        (fun child _ => completedRealizedPositionOutput f parameter state baseStarts child) := by
  rw [completedRealizedPositionOutput, WellFounded.fix_eq]

noncomputable def completedRealizedTable
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (state : LazyRevealProbe.State Coordinate)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput) :
    Coordinate → HashOutput
  | coordinate@(.chainStart lay tree leafIdx chainIdx) =>
      (state.values coordinate).getD (baseStarts lay tree leafIdx chainIdx)
  | .position position =>
      completedRealizedPositionOutput f parameter state baseStarts position

private theorem completedChildrenPayload_eq
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (state : LazyRevealProbe.State Coordinate)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (positions : List Position) :
    (positions.map (tableValue (completedRealizedTable f parameter state baseStarts))).flatMap
        digestBytes =
      positions.attach.flatMap fun child =>
        digestBytes (truncateHash
          (completedRealizedPositionOutput f parameter state baseStarts child.1)) := by
  let payload := fun position : Position =>
    digestBytes (truncateHash
      (completedRealizedPositionOutput f parameter state baseStarts position))
  calc
    _ = positions.flatMap payload := by
      simp [payload, tableValue, completedRealizedTable, List.flatMap_map]
    _ = positions.attach.flatMap (fun child => payload child.1) :=
      (attach_flatMap_val positions payload).symm

theorem completedRealizedTable_of_value
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (state : LazyRevealProbe.State Coordinate)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (coordinate : Coordinate) (output : HashOutput)
    (hvalue : state.values coordinate = some output) :
    completedRealizedTable f parameter state baseStarts coordinate = output := by
  cases coordinate with
  | chainStart => simp [completedRealizedTable, hvalue]
  | position position =>
      rw [completedRealizedTable, completedRealizedPositionOutput_eq]
      unfold completedRealizedPositionBody
      rw [hvalue]

theorem extendTable_completedRealizedTable
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (state : LazyRevealProbe.State Coordinate)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput) :
    extendTable state (completedRealizedTable f parameter state baseStarts) =
      completedRealizedTable f parameter state baseStarts := by
  funext coordinate
  unfold extendTable
  cases hvalue : state.values coordinate with
  | none => simp
  | some output =>
      rw [completedRealizedTable_of_value f parameter state baseStarts coordinate output hvalue]
      simp

theorem mergedCache_completedRealizedTable_agreesWith_tableAnswer
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (hconsistent : HiddenConsistent state cache) :
    (mergedCache parameter (completedRealizedTable f parameter state baseStarts)
      state.ensured cache).AgreesWithFn
        (tableAnswer parameter (completedRealizedTable f parameter state baseStarts)
          (splitFallback cache)) := by
  have hagrees := mergedCache_extendTable_agreesWith_tableAnswer parameter state
    (completedRealizedTable f parameter state baseStarts) cache hconsistent
  rw [extendTable_completedRealizedTable] at hagrees
  exact hagrees

theorem completedRealizedTable_realizes_of_missing
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (state : LazyRevealProbe.State Coordinate)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (position : Position) (hmissing : state.values (.position position) = none) :
    f (tableInput parameter (completedRealizedTable f parameter state baseStarts)
        (.position position)) =
      completedRealizedTable f parameter state baseStarts (.position position) := by
  rw [completedRealizedTable, completedRealizedPositionOutput_eq]
  unfold completedRealizedPositionBody
  rw [hmissing]
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      simp only [tableInput, tablePayload, Position.domain, completedRealizedTable]
      rw [completedChildrenPayload_eq]
  | leaf | node | ftsLeaf | ftsNode | ftsRoots =>
      simp only [tableInput, tablePayload, Position.domain]
      rw [completedChildrenPayload_eq]

theorem tableAnswer_completedRealizedTable_eq_of_missing
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (state : LazyRevealProbe.State Coordinate)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (position : Position) (hots : IsOtsPosition position)
    (hmissing : state.values (.position position) = none) :
    tableAnswer parameter (completedRealizedTable f parameter state baseStarts) f
        (tableInput parameter (completedRealizedTable f parameter state baseStarts)
          (.position position)) =
      f (tableInput parameter (completedRealizedTable f parameter state baseStarts)
        (.position position)) := by
  rw [tableAnswer_tableInput parameter _ f position hots]
  exact (completedRealizedTable_realizes_of_missing f parameter state baseStarts position
    hmissing).symm

theorem tableAnswer_completedRealizedTable_eq_of_decoded_missing
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (state : LazyRevealProbe.State Coordinate)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (input : HashInput) (position : Position) (hots : IsOtsPosition position)
    (hposition : decodePosition? parameter input = some position)
    (hmissing : state.values (.position position) = none) :
    tableAnswer parameter (completedRealizedTable f parameter state baseStarts) f input =
      f input := by
  unfold tableAnswer
  rw [hposition]
  cases position with
  | chain | leaf | node =>
      simp only [tableAnswerDecoded]
      split_ifs with hexact
      · subst input
        exact (completedRealizedTable_realizes_of_missing f parameter state baseStarts _
          hmissing).symm
      · rfl
  | ftsLeaf | ftsNode | ftsRoots => simp [IsOtsPosition] at hots

noncomputable def retainedCompletionTable
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput) :
    Coordinate → HashOutput :=
  completedRealizedTable (splitFallback cache) parameter state baseStarts

noncomputable def retainedCompletionAnswer
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput) :
    QueryImpl HashSpec Id :=
  tableAnswer parameter (retainedCompletionTable parameter state cache baseStarts)
    (splitFallback cache)

theorem tableOtsSecret_retainedCompletionTable
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    tableOtsSecret (retainedCompletionTable parameter state cache baseStarts)
        lay tree leafIdx chainIdx =
      truncateHash ((state.values (.chainStart lay tree leafIdx chainIdx)).getD
        (baseStarts lay tree leafIdx chainIdx)) := by
  rfl

theorem retainedCompletionAnswer_realizes
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput) :
    ∀ position : Position, IsOtsPosition position →
      retainedCompletionAnswer parameter state cache baseStarts
          (tableInput parameter (retainedCompletionTable parameter state cache baseStarts)
            (.position position)) =
        retainedCompletionTable parameter state cache baseStarts (.position position) := by
  exact tableAnswer_realizes_otsPositions parameter
    (retainedCompletionTable parameter state cache baseStarts) (splitFallback cache)

theorem stableCacheAgreesWithFn_retainedCompletionAnswer
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput) :
    StableCacheAgreesWithFn parameter cache
      (retainedCompletionAnswer parameter state cache baseStarts) := by
  exact stableCacheAgreesWithFn_tableAnswer parameter
    (retainedCompletionTable parameter state cache baseStarts) cache

theorem mergedCache_agreesWithFn_retainedCompletionAnswer
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (hconsistent : HiddenConsistent state cache) :
    (mergedCache parameter (retainedCompletionTable parameter state cache baseStarts)
      state.ensured cache).AgreesWithFn
        (retainedCompletionAnswer parameter state cache baseStarts) := by
  exact mergedCache_completedRealizedTable_agreesWith_tableAnswer
    (splitFallback cache) parameter state cache baseStarts hconsistent

theorem retainedCompletionAnswer_eq_fallback_of_decoded_missing
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (input : HashInput) (position : Position) (hots : IsOtsPosition position)
    (hposition : decodePosition? parameter input = some position)
    (hmissing : state.values (.position position) = none) :
    retainedCompletionAnswer parameter state cache baseStarts input = splitFallback cache input := by
  exact tableAnswer_completedRealizedTable_eq_of_decoded_missing
    (splitFallback cache) parameter state baseStarts input position hots hposition hmissing

noncomputable def realizedOtsSecret
    (chainStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput) :
    Layer → TreeIndex → LeafIndex → ChainIndex → Digest :=
  fun lay tree leafIdx chainIdx => truncateHash (chainStarts lay tree leafIdx chainIdx)

noncomputable def realizedTable
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (chainStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput) :
    Coordinate → HashOutput
  | .chainStart lay tree leafIdx chainIdx => chainStarts lay tree leafIdx chainIdx
  | .position position =>
      f (honestInput f parameter (realizedOtsSecret chainStarts) (fun _ _ _ => 0) position)

theorem tableInput_realizedTable
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (chainStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (position : Position) (hots : IsOtsPosition position) (hvalid : position.Valid) :
    f (tableInput parameter (realizedTable f parameter chainStarts) (.position position)) =
      realizedTable f parameter chainStarts (.position position) := by
  let table := realizedTable f parameter chainStarts
  let otsSecret := realizedOtsSecret chainStarts
  let ftsSecret : Index → FtsTree → FtsLeaf → Digest := fun _ _ _ => 0
  have hvalue (child : Position) :
      tableValue table child = honestValue f parameter otsSecret ftsSecret child := by
    simp [tableValue, table, realizedTable, honestValue, otsSecret, ftsSecret]
  have hpayload :
      tablePayload table position = honestPayload f parameter otsSecret ftsSecret position := by
    cases position with
    | chain lay tree leafIdx chainIdx step =>
        by_cases hstep : step.val = 0
        · simp [tablePayload, hstep, honestPayload, Concrete.honestChain_zero, table,
            realizedTable, otsSecret, realizedOtsSecret]
        · rw [tablePayload, if_neg hstep]
          rw [honestPayload_eq_slots (f := f) (parameter := parameter)
            (otsSecret := otsSecret) (ftsSecret := ftsSecret) hvalid]
          simp only [slots, hstep, if_false, childValues]
          rfl
    | leaf | node =>
        rw [honestPayload_eq_slots (f := f) (parameter := parameter)
          (otsSecret := otsSecret) (ftsSecret := ftsSecret) hvalid]
        simp only [tablePayload, slots, childValues]
        rfl
    | ftsLeaf | ftsNode | ftsRoots => simp [IsOtsPosition] at hots
  change f (tweakableHashInput parameter position.domain (tablePayload table position)) =
    f (honestInput f parameter otsSecret ftsSecret position)
  rw [hpayload]
  rfl

theorem mem_runRaw_peekCoordinate_of_value
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache)
    (fuel : Nat) (coordinate : Coordinate) (output : HashOutput)
    (hvalue : state.values coordinate = some output) :
    LazyRevealProbe.RawResult.done state fuel
        (some (truncateHash output), cache) ∈ support
      (LazyRevealProbe.runRaw state fuel ((peekCoordinate coordinate).run cache)) := by
  change LazyRevealProbe.RawResult.done state fuel
      (some (truncateHash output), cache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.peekQuery coordinate >>= fun value =>
        pure (truncateHash <$> value, cache)))
  rw [LazyRevealProbe.peekQuery, LazyRevealProbe.runRaw_peek_query_bind]
  simp [hvalue, LazyRevealProbe.runRaw]

theorem runRaw_peekCoordinate_of_value
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache)
    (fuel : Nat) (coordinate : Coordinate) (output : HashOutput)
    (hvalue : state.values coordinate = some output) :
    LazyRevealProbe.runRaw state fuel ((peekCoordinate coordinate).run cache) =
      pure (.done state fuel (some (truncateHash output), cache)) := by
  change LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.peekQuery coordinate >>= fun value =>
        pure (truncateHash <$> value, cache)) = _
  rw [LazyRevealProbe.peekQuery, LazyRevealProbe.runRaw_peek_query_bind]
  simp [hvalue, LazyRevealProbe.runRaw]

theorem mem_runRaw_peekPositionValues_of_values
    (table : Coordinate → HashOutput) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache) (fuel : Nat) : ∀ positions : List Position,
    (∀ position, position ∈ positions →
      state.values (.position position) = some (table (.position position))) →
    LazyRevealProbe.RawResult.done state fuel
        (some (positions.map (tableValue table)), cache) ∈ support
      (LazyRevealProbe.runRaw state fuel ((peekPositionValues positions).run cache))
  | [], _ => by simp [peekPositionValues, LazyRevealProbe.runRaw]
  | position :: remaining, hvalues => by
      rw [peekPositionValues, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff]
      refine ⟨.done state fuel
        (some (tableValue table position), cache), ?_, ?_⟩
      · exact mem_runRaw_peekCoordinate_of_value state cache fuel (.position position)
          (table (.position position)) (hvalues position (by simp))
      · simp only
        rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff]
        refine ⟨.done state fuel
          (some (remaining.map (tableValue table)), cache), ?_, ?_⟩
        · exact mem_runRaw_peekPositionValues_of_values table state cache fuel remaining
            (fun other hother => hvalues other (by simp [hother]))
        · simp [LazyRevealProbe.runRaw]

theorem runRaw_peekPositionValues_of_values
    (table : Coordinate → HashOutput) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache) (fuel : Nat) : ∀ positions : List Position,
    (∀ position, position ∈ positions →
      state.values (.position position) = some (table (.position position))) →
    LazyRevealProbe.runRaw state fuel ((peekPositionValues positions).run cache) =
      pure (.done state fuel (some (positions.map (tableValue table)), cache))
  | [], _ => by simp [peekPositionValues, LazyRevealProbe.runRaw]
  | position :: remaining, hvalues => by
      rw [peekPositionValues, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        runRaw_peekCoordinate_of_value state cache fuel (.position position)
          (table (.position position)) (hvalues position (by simp))]
      simp only [pure_bind]
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind,
        runRaw_peekPositionValues_of_values table state cache fuel remaining
          (fun other hother => hvalues other (by simp [hother]))]
      simp [LazyRevealProbe.runRaw, tableValue]

def TableInputAvailable (table : Coordinate → HashOutput)
    (state : LazyRevealProbe.State Coordinate) : Coordinate → Prop
  | .chainStart _ _ _ _ => False
  | .position position@(.chain lay tree leafIdx chainIdx step) =>
      if step.val = 0 then
        state.values (.chainStart lay tree leafIdx chainIdx) =
          some (table (.chainStart lay tree leafIdx chainIdx))
      else
        ∀ child, child ∈ position.children →
          state.values (.position child) = some (table (.position child))
  | .position position =>
      ∀ child, child ∈ position.children →
        state.values (.position child) = some (table (.position child))

theorem TableInputAvailable.monoValues
    {table : Coordinate → HashOutput}
    {state finalState : LazyRevealProbe.State Coordinate} {coordinate : Coordinate}
    (havailable : TableInputAvailable table state coordinate)
    (hle : LazyRevealProbe.ValuesLE state finalState) :
    TableInputAvailable table finalState coordinate := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      simp [TableInputAvailable] at havailable
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          simp only [TableInputAvailable]
          by_cases hzero : step.val = 0
          · rw [if_pos hzero]
            exact hle _ _ (by simpa [TableInputAvailable, hzero] using havailable)
          · rw [if_neg hzero]
            have havailable' : ∀ child,
                child ∈ (Position.chain lay tree leafIdx chainIdx step).children →
                  state.values (.position child) = some (table (.position child)) := by
              simpa [TableInputAvailable, hzero] using havailable
            intro child hchild
            exact hle _ _ (havailable' child hchild)
      | leaf | node | ftsLeaf | ftsNode | ftsRoots =>
          intro child hchild
          exact hle _ _ (havailable child hchild)

theorem runRaw_peekTableInput_of_available
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache)
    (fuel : Nat) (coordinate : Coordinate)
    (havailable : TableInputAvailable table state coordinate) :
    LazyRevealProbe.runRaw state fuel ((peekTableInput parameter coordinate).run cache) =
      pure (.done state fuel (some (tableInput parameter table coordinate), cache)) := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      simp [TableInputAvailable] at havailable
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          rw [peekTableInput.eq_2]
          by_cases hzero : step.val = 0
          · rw [if_pos hzero, StateT.run_bind, LazyRevealProbe.runRaw_bind,
              runRaw_peekCoordinate_of_value state cache fuel
                (.chainStart lay tree leafIdx chainIdx)
                (table (.chainStart lay tree leafIdx chainIdx))
                (by simpa [TableInputAvailable, hzero] using havailable)]
            simp [LazyRevealProbe.runRaw, tableInput, tablePayload, hzero]
          · rw [if_neg hzero, StateT.run_bind, LazyRevealProbe.runRaw_bind,
              runRaw_peekPositionValues_of_values table state cache fuel _
                (by simpa [TableInputAvailable, hzero] using havailable)]
            simp [LazyRevealProbe.runRaw, tableInput, tablePayload, hzero]
      | leaf lay tree leafIdx =>
          rw [peekTableInput.eq_3 parameter (.leaf lay tree leafIdx) (by simp),
            StateT.run_bind, LazyRevealProbe.runRaw_bind,
            runRaw_peekPositionValues_of_values table state cache fuel _ havailable]
          simp [LazyRevealProbe.runRaw, tableInput, tablePayload]
      | node lay tree level nodeIdx =>
          rw [peekTableInput.eq_3 parameter (.node lay tree level nodeIdx) (by simp),
            StateT.run_bind, LazyRevealProbe.runRaw_bind,
            runRaw_peekPositionValues_of_values table state cache fuel _ havailable]
          simp [LazyRevealProbe.runRaw, tableInput, tablePayload]
      | ftsLeaf index tree leafIdx =>
          rw [peekTableInput.eq_3 parameter (.ftsLeaf index tree leafIdx) (by simp),
            StateT.run_bind, LazyRevealProbe.runRaw_bind,
            runRaw_peekPositionValues_of_values table state cache fuel _ havailable]
          simp [LazyRevealProbe.runRaw, tableInput, tablePayload]
      | ftsNode index tree level nodeIdx =>
          rw [peekTableInput.eq_3 parameter (.ftsNode index tree level nodeIdx) (by simp),
            StateT.run_bind, LazyRevealProbe.runRaw_bind,
            runRaw_peekPositionValues_of_values table state cache fuel _ havailable]
          simp [LazyRevealProbe.runRaw, tableInput, tablePayload]
      | ftsRoots index =>
          rw [peekTableInput.eq_3 parameter (.ftsRoots index) (by simp),
            StateT.run_bind, LazyRevealProbe.runRaw_bind,
            runRaw_peekPositionValues_of_values table state cache fuel _ havailable]
          simp [LazyRevealProbe.runRaw, tableInput, tablePayload]

theorem mem_runRaw_revealCoordinateOutput_value
    (coordinate : Coordinate) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : HashOutput)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((revealCoordinateOutput coordinate).run cache))) :
    finalState.values coordinate = some output ∧
      finalCache (.hidden coordinate) = some output := by
  rw [revealCoordinateOutput_run, LazyRevealProbe.revealQuery,
    LazyRevealProbe.runRaw_reveal_query_bind] at hresult
  cases hvalue : state.values coordinate with
  | some cached =>
      rw [hvalue] at hresult
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨hvalue, by simp [Function.update]⟩
  | none =>
      rw [hvalue, mem_support_bind_iff] at hresult
      obtain ⟨sampled, _, hrest⟩ := hresult
      by_cases hhit : state.hitAt coordinate sampled
      · rw [if_pos hhit] at hrest
        simp at hrest
      · rw [if_neg hhit] at hrest
        simp [LazyRevealProbe.runRaw] at hrest
        rcases hrest with ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨by simp [LazyRevealProbe.State.materialize, Function.update],
          by simp [Function.update]⟩

theorem mem_runRaw_revealCoordinate_value
    (coordinate : Coordinate) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : Digest)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((revealCoordinate coordinate).run cache))) :
    ∃ output : HashOutput,
      value = truncateHash output ∧ finalState.values coordinate = some output := by
  rw [revealCoordinate_run, LazyRevealProbe.revealQuery,
    LazyRevealProbe.runRaw_reveal_query_bind] at hresult
  cases hvalue : state.values coordinate with
  | some output =>
      rw [hvalue] at hresult
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨output, rfl, hvalue⟩
  | none =>
      rw [hvalue, mem_support_bind_iff] at hresult
      obtain ⟨output, _, hrest⟩ := hresult
      by_cases hhit : state.hitAt coordinate output
      · rw [if_pos hhit] at hrest
        simp at hrest
      · rw [if_neg hhit] at hrest
        simp [LazyRevealProbe.runRaw] at hrest
        rcases hrest with ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨output, rfl, by
          simp [LazyRevealProbe.State.materialize, Function.update]⟩

theorem mem_runRaw_revealPublishedCoordinate_value
    (coordinate : Coordinate) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : Digest)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((revealPublishedCoordinate coordinate).run cache))) :
    ∃ output : HashOutput,
      value = truncateHash output ∧ finalState.values coordinate = some output := by
  unfold revealPublishedCoordinate at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hreveal, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done revealState revealRemaining revealResult =>
      rcases revealResult with ⟨revealed, revealCache⟩
      have hrevealed := mem_runRaw_revealCoordinate_value coordinate state revealState cache
        revealCache fuel revealRemaining revealed hreveal
      have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
        ((publishCoordinate coordinate >>= fun _ => pure revealed).run revealCache)
        revealState finalState revealRemaining remaining (value, finalCache) hrest
      simp [publishCoordinate, LazyRevealProbe.publishQuery,
        LazyRevealProbe.runRaw] at hrest
      rcases hrest with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨hrevealed.choose, hrevealed.choose_spec.1,
        hvaluesLE coordinate hrevealed.choose hrevealed.choose_spec.2⟩

theorem revealLayerValues_eq_table
    (table : Coordinate → HashOutput)
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (values : (ChainIndex → Digest) × (Fin maxLayerHeight → Digest))
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (values, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((revealLayerValues index lay encoding).run cache))) :
    values.1 = (fun chainIdx => truncateHash (table
        (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay)
          chainIdx (encoding chainIdx)))) ∧
      values.2 = (fun level =>
        if level.val < layerHeight lay then
          match level.val with
          | 0 => truncateHash (table (.position (.leaf lay (treeIndexAt index lay)
              (leafOfNat (Nat.xor (leafIndexAt index lay).val 1)))))
          | current + 1 =>
              if hlevel : current < maxLayerHeight then
                truncateHash (table (.position (.node lay (treeIndexAt index lay)
                  ⟨current, hlevel⟩ (leafOfNat
                    (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1)))))
              else 0
        else 0) := by
  unfold revealLayerValues at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨chainRaw, hchains, hafterChains⟩ := hresult
  cases chainRaw with
  | stopped hit => simp at hafterChains
  | done chainState chainRemaining chainResult =>
      rcases chainResult with ⟨chainValues, chainCache⟩
      simp only at hafterChains
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hafterChains
      obtain ⟨pathRaw, hpaths, hfinish⟩ := hafterChains
      cases pathRaw with
      | stopped hit => simp at hfinish
      | done pathState pathRemaining pathResult =>
          rcases pathResult with ⟨pathValues, pathCache⟩
          simp [LazyRevealProbe.runRaw] at hfinish
          rcases hfinish with ⟨hfinalState, hremaining, hvalues, hfinalCache⟩
          subst finalState
          subst remaining
          subst values
          subst finalCache
          have hchainValuesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
            ((sequenceFin fun level : Fin maxLayerHeight =>
              if level.val < layerHeight lay then
                match level.val with
                | 0 => revealPublishedCoordinate (.position (.leaf lay
                    (treeIndexAt index lay)
                    (leafOfNat (Nat.xor (leafIndexAt index lay).val 1))))
                | current + 1 =>
                    if hlevel : current < maxLayerHeight then
                      revealPublishedCoordinate (.position (.node lay
                        (treeIndexAt index lay) ⟨current, hlevel⟩ (leafOfNat
                          (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
                    else pure 0
              else pure 0).run chainCache)
            chainState pathState chainRemaining pathRemaining (pathValues, pathCache) hpaths
          constructor
          · funext chainIdx
            change chainValues chainIdx = _
            obtain ⟨componentState, componentFinalState, componentCache,
                componentFinalCache, componentFuel, componentRemaining, componentValue,
                hcomponent, hselected, hcomponentLE, _, _⟩ :=
              sequenceFin_component_run_of_done
                (fun chainIdx : ChainIndex => revealPublishedCoordinate
                  (chainValueCoordinate lay (treeIndexAt index lay)
                    (leafIndexAt index lay) chainIdx (encoding chainIdx)))
                (fun chainIdx => ordinaryCacheIncreasing_revealPublishedCoordinate _)
                state chainState cache chainCache fuel chainRemaining chainValues hchains chainIdx
            obtain ⟨output, hvalue, hstateValue⟩ :=
              mem_runRaw_revealPublishedCoordinate_value
                (chainValueCoordinate lay (treeIndexAt index lay)
                  (leafIndexAt index lay) chainIdx (encoding chainIdx))
                componentState componentFinalState componentCache componentFinalCache
                  componentFuel componentRemaining componentValue hcomponent
            rw [hselected, hvalue, htable _ output
              (hchainValuesLE _ _ (hcomponentLE _ _ hstateValue))]
          · funext level
            change pathValues level = _
            obtain ⟨componentState, componentFinalState, componentCache,
                componentFinalCache, componentFuel, componentRemaining, componentValue,
                hcomponent, hselected, hcomponentLE, _, _⟩ :=
              sequenceFin_component_run_of_done
                (fun level : Fin maxLayerHeight =>
                  if level.val < layerHeight lay then
                    match level.val with
                    | 0 => revealPublishedCoordinate (.position (.leaf lay
                        (treeIndexAt index lay)
                        (leafOfNat (Nat.xor (leafIndexAt index lay).val 1))))
                    | current + 1 =>
                        if hlevel : current < maxLayerHeight then
                          revealPublishedCoordinate (.position (.node lay
                            (treeIndexAt index lay) ⟨current, hlevel⟩ (leafOfNat
                              (Nat.xor ((leafIndexAt index lay).val /
                                2 ^ (current + 1)) 1))))
                        else pure 0
                  else pure 0)
                (fun level => by
                  split
                  · split
                    · exact ordinaryCacheIncreasing_revealPublishedCoordinate _
                    · split
                      · exact ordinaryCacheIncreasing_revealPublishedCoordinate _
                      · exact OrdinaryCacheIncreasing.pure 0
                  · exact OrdinaryCacheIncreasing.pure 0)
                chainState pathState chainCache pathCache chainRemaining pathRemaining
                  pathValues hpaths level
            rw [hselected]
            by_cases hinLayer : level.val < layerHeight lay
            · rw [if_pos hinLayer]
              cases hlevelValue : level.val with
              | zero =>
                  have hpositive : 0 < layerHeight lay := by omega
                  obtain ⟨output, hvalue, hstateValue⟩ :=
                    mem_runRaw_revealPublishedCoordinate_value _ componentState
                      componentFinalState componentCache componentFinalCache componentFuel
                        componentRemaining componentValue (by
                          simpa [hinLayer, hlevelValue, hpositive] using hcomponent)
                  rw [hvalue, htable _ output (hcomponentLE _ _ hstateValue)]
                  simp
              | succ current =>
                  have hcurrent : current < maxLayerHeight := by omega
                  have hcurrentLayer : current + 1 < layerHeight lay := by omega
                  let coordinate : Coordinate := .position (.node lay
                    (treeIndexAt index lay) ⟨current, hcurrent⟩ (leafOfNat
                      (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1)))
                  obtain ⟨output, hvalue, hstateValue⟩ :=
                    mem_runRaw_revealPublishedCoordinate_value coordinate componentState
                      componentFinalState componentCache componentFinalCache componentFuel
                        componentRemaining componentValue (by
                          simpa [coordinate, hlevelValue, hcurrent, hcurrentLayer] using hcomponent)
                  rw [hvalue, htable coordinate output (hcomponentLE _ _ hstateValue)]
                  simp [coordinate, hcurrent]
            · rw [if_neg hinLayer]
              simp [hinLayer, LazyRevealProbe.runRaw] at hcomponent
              exact hcomponent.2.2.1

theorem maskedOtsSignFrom_some_honest_eval
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leafIdx : LeafIndex) (secret : ChainIndex → Digest)
    (message : Digest) : ∀ attempts counter
      (state finalState : LazyRevealProbe.State Coordinate)
      (cache finalCache : SplitHashCache) (fuel remaining : Nat)
      (selectedCounter : Counter) (encoding : ChainIndex → Digit),
      StableCacheAgreesWithFn parameter finalCache f →
      LazyRevealProbe.RawResult.done finalState remaining
          (some (selectedCounter, encoding), finalCache) ∈ support
        (LazyRevealProbe.runRaw state fuel
          ((maskedOtsSignFrom parameter lay tree leafIdx message attempts counter).run cache)) →
      evalWithAnswerFn f
          (otsSignFrom parameter lay tree leafIdx secret message attempts counter) =
        some (selectedCounter, fun chainIdx =>
          honestChain f parameter lay tree leafIdx chainIdx (secret chainIdx)
            (encoding chainIdx).val)
  | 0, counter, state, finalState, cache, finalCache, fuel, remaining,
      selectedCounter, encoding, hf, hresult => by
      simp [maskedOtsSignFrom, LazyRevealProbe.runRaw] at hresult
  | attempts + 1, counter, state, finalState, cache, finalCache, fuel, remaining,
      selectedCounter, encoding, hf, hresult => by
      rw [maskedOtsSignFrom, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨raw, hencode, hrest⟩ := hresult
      cases raw with
      | stopped hit => simp at hrest
      | done encodeState encodeRemaining encodeResult =>
          rcases encodeResult with ⟨encoded, encodeCache⟩
          simp only at hrest
          cases encoded with
          | none =>
              have hordinaryLE := ordinaryCacheIncreasing_maskedOtsSignFrom parameter lay tree
                leafIdx message attempts (counter + 1) encodeState encodeCache encodeRemaining
                  finalState remaining (some (selectedCounter, encoding)) finalCache hrest
              have hfEncode : StableCacheAgreesWithFn parameter encodeCache f :=
                fun input output hstable hcached => hf input output hstable
                  (hordinaryLE hcached)
              have hencoded := (replay_of_mem_runRaw_ordinaryHashImpl_of_stable f parameter
                (encode parameter lay tree leafIdx message (BitVec.ofNat counterBits counter))
                state encodeState cache encodeCache fuel encodeRemaining none hfEncode
                  (queriesStable_encode f parameter lay tree leafIdx message
                    (BitVec.ofNat counterBits counter)) hencode).1
              rw [otsSignFrom, evalWithAnswerFn_bind, hencoded]
              exact maskedOtsSignFrom_some_honest_eval f parameter lay tree leafIdx secret message
                attempts (counter + 1) encodeState finalState encodeCache finalCache
                  encodeRemaining remaining selectedCounter encoding hf hrest
          | some selectedEncoding =>
              rw [StateT.run_bind, LazyRevealProbe.runRaw_bind,
                mem_support_bind_iff] at hrest
              obtain ⟨ensureRaw, hensure, hfinish⟩ := hrest
              cases ensureRaw with
              | stopped hit => simp at hfinish
              | done ensureState ensureRemaining ensureResult =>
                  rcases ensureResult with ⟨ensured, ensureCache⟩
                  simp [LazyRevealProbe.runRaw] at hfinish
                  rcases hfinish with ⟨rfl, rfl, hselected, rfl⟩
                  rcases hselected with ⟨hcounter, hencoding⟩
                  subst selectedCounter
                  subst encoding
                  have hordinaryLE := ordinaryCacheIncreasing_sequenceFin
                    (fun chainIdx => ensureChainPrefix lay tree leafIdx chainIdx
                      (selectedEncoding chainIdx))
                    (fun chainIdx =>
                      (splitCachePreserving_ensureChainPrefix lay tree leafIdx chainIdx
                        (selectedEncoding chainIdx)).ordinaryCacheIncreasing)
                    encodeState encodeCache encodeRemaining finalState remaining ensured finalCache
                      hensure
                  have hfEncode : StableCacheAgreesWithFn parameter encodeCache f :=
                    fun input output hstable hcached => hf input output hstable
                      (hordinaryLE hcached)
                  have hencoded := (replay_of_mem_runRaw_ordinaryHashImpl_of_stable f parameter
                    (encode parameter lay tree leafIdx message (BitVec.ofNat counterBits counter))
                    state encodeState cache encodeCache fuel encodeRemaining
                      (some selectedEncoding) hfEncode
                      (queriesStable_encode f parameter lay tree leafIdx message
                        (BitVec.ofNat counterBits counter)) hencode).1
                  rw [otsSignFrom, evalWithAnswerFn_bind, hencoded,
                    evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin,
                    evalWithAnswerFn_pure]
                  congr 2

theorem maskedOtsSign_some_honest_eval
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leafIdx : LeafIndex) (secret : ChainIndex → Digest)
    (message : Digest) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (counter : Counter) (encoding : ChainIndex → Digit)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        (some (counter, encoding), finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((maskedOtsSign parameter lay tree leafIdx message).run cache))) :
    evalWithAnswerFn f (otsSign parameter lay tree leafIdx secret message) =
      some (counter, fun chainIdx =>
        honestChain f parameter lay tree leafIdx chainIdx (secret chainIdx)
          (encoding chainIdx).val) := by
  exact maskedOtsSignFrom_some_honest_eval f parameter lay tree leafIdx secret message
    encodingAttemptLimit 0 state finalState cache finalCache fuel remaining counter encoding
      hf hresult

theorem maskedOtsLayerAfterMessage_some_honest_eval
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index) (lay : Layer)
    (secret : ChainIndex → Digest) (message actualMessage : Digest)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (counter : Counter) (encoding : ChainIndex → Digit)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (hmessage : message = actualMessage)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        (some (counter, encoding), finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((maskedOtsLayerAfterMessage parameter index lay message).run cache))) :
    evalWithAnswerFn f
        (otsSign parameter lay (treeIndexAt index lay) (leafIndexAt index lay) secret
          actualMessage) =
      some (counter, fun chainIdx =>
        honestChain f parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          chainIdx (secret chainIdx) (encoding chainIdx).val) := by
  unfold maskedOtsLayerAfterMessage at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨otsRaw, hots, hafterOts⟩ := hresult
  cases otsRaw with
  | stopped hit => simp at hafterOts
  | done otsState otsRemaining otsResult =>
      rcases otsResult with ⟨part, otsCache⟩
      cases part with
      | none => simp [LazyRevealProbe.runRaw] at hafterOts
      | some selectedPart =>
          rcases selectedPart with ⟨selectedCounter, selectedEncoding⟩
          simp only at hafterOts
          rw [StateT.run_bind, LazyRevealProbe.runRaw_bind,
            mem_support_bind_iff] at hafterOts
          obtain ⟨pathRaw, hpath, hfinish⟩ := hafterOts
          cases pathRaw with
          | stopped hit => simp at hfinish
          | done pathState pathRemaining pathResult =>
              rcases pathResult with ⟨pathUnit, pathCache⟩
              have hpathCache := splitCachePreserving_ensureTreePath lay
                (treeIndexAt index lay) (leafIndexAt index lay) otsState otsCache otsRemaining
                  pathState pathRemaining pathUnit pathCache hpath
              simp [LazyRevealProbe.runRaw] at hfinish
              rcases hfinish with ⟨rfl, rfl, hpart, rfl⟩
              rcases hpart with ⟨hcounter, hencoding⟩
              subst selectedCounter
              subst selectedEncoding
              rw [hpathCache] at hf
              subst message
              exact maskedOtsSign_some_honest_eval f parameter lay
                (treeIndexAt index lay) (leafIndexAt index lay) secret actualMessage state
                  otsState cache otsCache fuel otsRemaining counter encoding hf hots

theorem maskedSignLayer_some_honest_eval
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (counter : Counter) (encoding : ChainIndex → Digit)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        (some (counter, encoding), finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((maskedSignLayer parameter ftsSecret index lay).run cache))) :
    evalWithAnswerFn f
        (otsSign parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (tableOtsSecret table lay (treeIndexAt index lay) (leafIndexAt index lay))
          (evalWithAnswerFn f
            (layerMessage
              (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) index lay))) =
      some (counter, fun chainIdx =>
        honestChain f parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          chainIdx
          (tableOtsSecret table lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx)
          (encoding chainIdx).val) := by
  unfold maskedSignLayer at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨messageRaw, hmessage, hafterMessage⟩ := hresult
  cases messageRaw with
  | stopped hit => simp at hafterMessage
  | done messageState messageRemaining messageResult =>
      rcases messageResult with ⟨message, messageCache⟩
      simp only at hafterMessage
      change LazyRevealProbe.RawResult.done finalState remaining
          (some (counter, encoding), finalCache) ∈ support
        (LazyRevealProbe.runRaw messageState messageRemaining
          ((maskedOtsLayerAfterMessage parameter index lay message).run messageCache))
        at hafterMessage
      by_cases hbelow : lay.val + 1 < numLayers
      · let below : Layer := ⟨lay.val + 1, hbelow⟩
        have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
          ((maskedOtsLayerAfterMessage parameter index lay message).run messageCache)
            messageState finalState messageRemaining remaining
              (some (counter, encoding), finalCache) hafterMessage
        have hmessageActual := maskedLayerMessage_eq_actual_of_lt
          (f := f) (parameter := parameter) (root := root) (table := table)
          (ftsSecret := ftsSecret) (index := index) (lay := lay) (below := below)
          (hbelow := hbelow) (hbelowEq := rfl) (state := state)
          (messageState := messageState) (referenceState := finalState) (cache := cache)
          (messageCache := messageCache) (fuel := fuel) (messageRemaining := messageRemaining)
          (message := message) hvaluesLE htable hrealizes hmessage
        exact maskedOtsLayerAfterMessage_some_honest_eval f parameter index lay
          (tableOtsSecret table lay (treeIndexAt index lay) (leafIndexAt index lay)) message
          (evalWithAnswerFn f
            (layerMessage
              (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) index lay))
          messageState finalState messageCache finalCache messageRemaining remaining counter
            encoding hf hmessageActual hafterMessage
      · have hordinaryLE := ordinaryCacheIncreasing_maskedSignLayerAfterMessage parameter index lay
          message messageState messageCache messageRemaining finalState remaining
            (some (counter, encoding)) finalCache hafterMessage
        have hfMessage : StableCacheAgreesWithFn parameter messageCache f :=
          fun input output hstable hcached => hf input output hstable (hordinaryLE hcached)
        have hmessageActual := maskedLayerMessage_eq_actual_of_not_lt f parameter root table
          ftsSecret index lay hbelow state messageState cache messageCache fuel messageRemaining
            message hfMessage hmessage
        exact maskedOtsLayerAfterMessage_some_honest_eval f parameter index lay
          (tableOtsSecret table lay (treeIndexAt index lay) (leafIndexAt index lay)) message
          (evalWithAnswerFn f
            (layerMessage
              (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) index lay))
          messageState finalState messageCache finalCache messageRemaining remaining counter
            encoding hf hmessageActual hafterMessage

theorem evalWithAnswerFn_treePath_eq_table
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position)) :
    evalWithAnswerFn f
        (treePath parameter lay tree (tableOtsSecret table lay tree) leafIdx) =
      fun level =>
        if level.val < layerHeight lay then
          match level.val with
          | 0 => truncateHash (table (.position (.leaf lay tree
              (leafOfNat (Nat.xor leafIdx.val 1)))))
          | current + 1 =>
              if hcurrent : current < maxLayerHeight then
                truncateHash (table (.position (.node lay tree ⟨current, hcurrent⟩
                  (leafOfNat (Nat.xor (leafIdx.val / 2 ^ (current + 1)) 1)))))
              else 0
        else 0 := by
  funext level
  simp only [treePath, evalWithAnswerFn_sequenceFin]
  by_cases hinLayer : level.val < layerHeight lay
  · rw [if_pos hinLayer, if_pos hinLayer]
    cases hlevelValue : level.val with
    | zero =>
        have hspan := FtsProbeSimulation.sibling_node_bound maxLayerHeight leafIdx.val 0
          (by norm_num [maxLayerHeight]) leafIdx.isLt
        have hsibling : Nat.xor leafIdx.val 1 < 2 ^ maxLayerHeight := by
          simpa using hspan
        have hleafValue : (leafOfNat (Nat.xor leafIdx.val 1)).val =
            Nat.xor leafIdx.val 1 := by
          change Nat.xor leafIdx.val 1 % 2 ^ maxLayerHeight = Nat.xor leafIdx.val 1
          exact Nat.mod_eq_of_lt hsibling
        have hnode := honestNode_zero_eq_table f parameter table lay tree
          (leafOfNat (Nat.xor leafIdx.val 1)) hrealizes
        rw [hleafValue] at hnode
        simpa [honestNode, hlevelValue, tableValue] using hnode
    | succ current =>
        have hcurrent : current < maxLayerHeight := by
          have := layerHeight_le lay
          omega
        have hspan := FtsProbeSimulation.sibling_node_bound maxLayerHeight leafIdx.val
          (current + 1) (by omega) leafIdx.isLt
        have hnode := honestNode_eq_table_succ f parameter table lay tree hrealizes current
          (Nat.xor (leafIdx.val / 2 ^ (current + 1)) 1) hcurrent hspan
        simpa [honestNode, hlevelValue, hcurrent, tableValue] using hnode
  · simp [hinLayer]

theorem honestChain_eq_table_chainValueCoordinate
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (digit : Digit)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position)) :
    honestChain f parameter lay tree leafIdx chainIdx
        (tableOtsSecret table lay tree leafIdx chainIdx) digit.val =
      truncateHash (table (chainValueCoordinate lay tree leafIdx chainIdx digit)) := by
  by_cases hzero : digit.val = 0
  · simp [chainValueCoordinate, hzero, honestChain_zero, tableOtsSecret]
  · have hstep : digit.val - 1 < chainLength - 1 := by
      have := digit.isLt
      omega
    have hchain := honestChain_eq_table_succ f parameter table lay tree leafIdx chainIdx
      hrealizes (digit.val - 1) hstep
    have hvalue : digit.val - 1 + 1 = digit.val := by omega
    rw [hvalue] at hchain
    simpa [chainValueCoordinate, hzero, tableValue] using hchain

theorem maskedSignLayer_and_reveal_eval
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) (counter : Counter)
    (encoding : ChainIndex → Digit)
    (signState signFinalState : LazyRevealProbe.State Coordinate)
    (signCache signFinalCache : SplitHashCache) (signFuel signRemaining : Nat)
    (revealState revealFinalState : LazyRevealProbe.State Coordinate)
    (revealCache revealFinalCache : SplitHashCache) (revealFuel revealRemaining : Nat)
    (values : (ChainIndex → Digest) × (Fin maxLayerHeight → Digest))
    (hf : StableCacheAgreesWithFn parameter signFinalCache f)
    (htableSign : ∀ coordinate output,
      signFinalState.values coordinate = some output → output = table coordinate)
    (htableReveal : ∀ coordinate output,
      revealFinalState.values coordinate = some output → output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hsign : LazyRevealProbe.RawResult.done signFinalState signRemaining
        (some (counter, encoding), signFinalCache) ∈ support
      (LazyRevealProbe.runRaw signState signFuel
        ((maskedSignLayer parameter ftsSecret index lay).run signCache)))
    (hreveal : LazyRevealProbe.RawResult.done revealFinalState revealRemaining
        (values, revealFinalCache) ∈ support
      (LazyRevealProbe.runRaw revealState revealFuel
        ((revealLayerValues index lay encoding).run revealCache))) :
    evalWithAnswerFn f
        (signLayer
          (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) index lay) =
      some (counter, values.1, values.2) := by
  have hots := maskedSignLayer_some_honest_eval f parameter root table ftsSecret index lay
    signState signFinalState signCache signFinalCache signFuel signRemaining counter encoding hf
      htableSign hrealizes hsign
  have hotsTable : evalWithAnswerFn f
      (otsSign parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        (tableOtsSecret table lay (treeIndexAt index lay) (leafIndexAt index lay))
        (evalWithAnswerFn f
          (layerMessage
            (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) index lay))) =
    some (counter, fun chainIdx => truncateHash (table
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay)
        chainIdx (encoding chainIdx)))) := by
    rw [hots]
    congr 2
    funext chainIdx
    exact honestChain_eq_table_chainValueCoordinate f parameter table lay
      (treeIndexAt index lay) (leafIndexAt index lay) chainIdx (encoding chainIdx) hrealizes
  have hpathTable := evalWithAnswerFn_treePath_eq_table f parameter table lay
    (treeIndexAt index lay) (leafIndexAt index lay) hrealizes
  have hrevealedTable := revealLayerValues_eq_table table index lay encoding revealState
    revealFinalState revealCache revealFinalCache revealFuel revealRemaining values htableReveal
      hreveal
  rw [signLayer, evalWithAnswerFn_bind, evalWithAnswerFn_bind, hotsTable,
    evalWithAnswerFn_bind, hpathTable, evalWithAnswerFn_pure, hrevealedTable.1,
    hrevealedTable.2]

theorem mergedCache_tableInput_ne_none_of_ensured
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache)
    (position : Position) (hots : IsOtsPosition position)
    (hensured : Coordinate.position position ∈ state.ensured) :
    mergedCache parameter table state.ensured cache
        (tableInput parameter table (.position position)) ≠ none := by
  rw [mergedCache_tableInput parameter table state.ensured cache position hots]
  cases hhidden : cache (.hidden (.position position)) <;>
    simp [completedSplitHashCache, hhidden, hensured]

theorem mergedCache_eq_ordinary_of_stable
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (ensured : Finset Coordinate) (cache : SplitHashCache) (input : HashInput)
    (hstable : StableOrdinaryInput parameter input) :
    mergedCache parameter table ensured cache input = cache (.ordinary input) := by
  rcases hstable with ⟨_, hstable⟩
  unfold mergedCache
  cases hposition : decodePosition? parameter input with
  | none => rfl
  | some position =>
      have hnots := hstable position hposition
      cases position <;> simp [mergeDecodedPosition, IsOtsPosition] at hnots ⊢

theorem mergedCache_eq_ordinary_or_exact
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (ensured : Finset Coordinate) (cache : SplitHashCache) (input : HashInput) :
    mergedCache parameter table ensured cache input = cache (.ordinary input) ∨
      ∃ position : Position, IsOtsPosition position ∧
        input = tableInput parameter table (.position position) := by
  unfold mergedCache
  cases hposition : decodePosition? parameter input with
  | none => exact Or.inl rfl
  | some position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          by_cases hexact : input = tableInput parameter table
              (.position (.chain lay tree leafIdx chainIdx step))
          · refine Or.inr ⟨.chain lay tree leafIdx chainIdx step, ?_, hexact⟩
            exact True.intro
          · exact Or.inl (by simp [mergeDecodedPosition, hexact])
      | leaf lay tree leafIdx =>
          by_cases hexact : input = tableInput parameter table
              (.position (.leaf lay tree leafIdx))
          · refine Or.inr ⟨.leaf lay tree leafIdx, ?_, hexact⟩
            exact True.intro
          · exact Or.inl (by simp [mergeDecodedPosition, hexact])
      | node lay tree level nodeIdx =>
          by_cases hexact : input = tableInput parameter table
              (.position (.node lay tree level nodeIdx))
          · refine Or.inr ⟨.node lay tree level nodeIdx, ?_, hexact⟩
            exact True.intro
          · exact Or.inl (by simp [mergeDecodedPosition, hexact])
      | ftsLeaf | ftsNode | ftsRoots => exact Or.inl (by simp [mergeDecodedPosition])

theorem tableAnswer_eq_fallback_or_exact
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (fallback : QueryImpl HashSpec Id) (input : HashInput) :
    tableAnswer parameter table fallback input = fallback input ∨
      ∃ position : Position, IsOtsPosition position ∧
        input = tableInput parameter table (.position position) := by
  unfold tableAnswer
  cases hposition : decodePosition? parameter input with
  | none => exact Or.inl rfl
  | some position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          by_cases hexact : input = tableInput parameter table
              (.position (.chain lay tree leafIdx chainIdx step))
          · refine Or.inr ⟨.chain lay tree leafIdx chainIdx step, ?_, hexact⟩
            exact True.intro
          · exact Or.inl (by simp [tableAnswerDecoded, hexact])
      | leaf lay tree leafIdx =>
          by_cases hexact : input = tableInput parameter table
              (.position (.leaf lay tree leafIdx))
          · refine Or.inr ⟨.leaf lay tree leafIdx, ?_, hexact⟩
            exact True.intro
          · exact Or.inl (by simp [tableAnswerDecoded, hexact])
      | node lay tree level nodeIdx =>
          by_cases hexact : input = tableInput parameter table
              (.position (.node lay tree level nodeIdx))
          · refine Or.inr ⟨.node lay tree level nodeIdx, ?_, hexact⟩
            exact True.intro
          · exact Or.inl (by simp [tableAnswerDecoded, hexact])
      | ftsLeaf | ftsNode | ftsRoots => exact Or.inl (by simp [tableAnswerDecoded])

theorem cachedRun_mergedCache_of_stable
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache) (computation : OracleComp HashSpec alpha)
    (hstable : QueriesStable parameter f computation)
    (hrun : CachedRun (ordinaryQueryCache cache) f computation) :
    CachedRun (mergedCache parameter table state.ensured cache) f computation := by
  intro input hinput
  rw [mergedCache_eq_ordinary_of_stable parameter table state.ensured cache input
    (hstable input hinput)]
  exact hrun input hinput

def StableOrdinaryCacheLE (parameter : PublicParameter)
    (initial final : SplitHashCache) : Prop :=
  ∀ input output, StableOrdinaryInput parameter input →
    initial (.ordinary input) = some output → final (.ordinary input) = some output

theorem StableOrdinaryCacheLE.refl (parameter : PublicParameter) (cache : SplitHashCache) :
    StableOrdinaryCacheLE parameter cache cache := by
  intro input output hstable hcached
  exact hcached

theorem StableOrdinaryCacheLE.trans
    {parameter : PublicParameter} {first second third : SplitHashCache}
    (hfirst : StableOrdinaryCacheLE parameter first second)
    (hsecond : StableOrdinaryCacheLE parameter second third) :
    StableOrdinaryCacheLE parameter first third := by
  intro input output hstable hcached
  exact hsecond input output hstable (hfirst input output hstable hcached)

theorem StableOrdinaryCacheLE.of_le
    {parameter : PublicParameter} {initial final : SplitHashCache}
    (hle : ordinaryQueryCache initial ≤ ordinaryQueryCache final) :
    StableOrdinaryCacheLE parameter initial final := by
  intro input output hstable hcached
  exact hle hcached

theorem CachedRun.mono_stableOrdinary
    {f : QueryImpl HashSpec Id} {parameter : PublicParameter}
    {initial final : SplitHashCache} {computation : OracleComp HashSpec alpha}
    (hstable : QueriesStable parameter f computation)
    (hle : StableOrdinaryCacheLE parameter initial final)
    (hrun : CachedRun (ordinaryQueryCache initial) f computation) :
    CachedRun (ordinaryQueryCache final) f computation := by
  intro input hinput
  obtain ⟨output, hcached⟩ := Option.ne_none_iff_exists'.mp (hrun input hinput)
  change initial (.ordinary input) = some output at hcached
  change final (.ordinary input) ≠ none
  rw [hle input output (hstable input hinput) hcached]
  simp

theorem cachedRun_chainWalk_of_ensured
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position)) :
    ∀ steps : Nat,
      (∀ step : ChainStep, step.val < steps →
        Coordinate.position (.chain lay tree leafIdx chainIdx step) ∈ state.ensured) →
      CachedRun (mergedCache parameter table state.ensured cache) f
        (chainWalk parameter lay tree leafIdx chainIdx 0 steps
          (tableOtsSecret table lay tree leafIdx chainIdx))
  | 0, _ => CachedRun.pure _ _ _
  | steps + 1, hensured => by
      rw [chainWalk]
      apply CachedRun.bind
      · exact cachedRun_chainWalk_of_ensured f parameter table state cache lay tree leafIdx
          chainIdx hrealizes steps (fun step hstep => hensured step (by omega))
      · split_ifs with hstep
        · intro input hinput
          simp only [queriedInputs_tweakableHash, List.mem_singleton] at hinput
          subst input
          have hstep' : steps < chainLength - 1 := by omega
          let position : ChainStep := ⟨steps, hstep'⟩
          have hinput :
              tweakableHashInput parameter (.chain lay tree leafIdx chainIdx position)
                  (digestBytes (honestChain f parameter lay tree leafIdx chainIdx
                    (tableOtsSecret table lay tree leafIdx chainIdx) steps)) =
                tableInput parameter table
                  (.position (.chain lay tree leafIdx chainIdx position)) := by
            cases steps with
            | zero =>
                simp [honestChain_zero, tableInput, tablePayload, tableOtsSecret,
                  Position.domain, position]
            | succ previous =>
                have hprevious : previous < chainLength - 1 := by omega
                rw [honestChain_eq_table_succ f parameter table lay tree leafIdx chainIdx
                  hrealizes previous hprevious]
                simp [tableInput, tablePayload, Position.children, Position.domain, position]
          have hposition : (⟨0 + steps, hstep⟩ : ChainStep) = position := by
            apply Fin.ext
            simp [position]
          change mergedCache parameter table state.ensured cache
            (tweakableHashInput parameter
              (.chain lay tree leafIdx chainIdx ⟨0 + steps, hstep⟩)
              (digestBytes (honestChain f parameter lay tree leafIdx chainIdx
                (tableOtsSecret table lay tree leafIdx chainIdx) steps))) ≠ none
          rw [hposition, hinput]
          exact mergedCache_tableInput_ne_none_of_ensured parameter table state cache
            (.chain lay tree leafIdx chainIdx position) (by trivial)
              (hensured position (by simp [position]))
        · exact CachedRun.pure _ _ _

theorem mem_runRaw_ensureCoordinate_mem
    (coordinate : Coordinate) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : Unit)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel ((ensureCoordinate coordinate).run cache))) :
    coordinate ∈ finalState.ensured := by
  simp [ensureCoordinate, LazyRevealProbe.ensureQuery, LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  simp [LazyRevealProbe.State.ensure]

structure EnsuresCoordinate (coordinate : Coordinate)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha) : Prop where
  of_run : ∀ state finalState cache finalCache fuel remaining value,
    LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel (computation.run cache)) →
    coordinate ∈ finalState.ensured

theorem EnsuresCoordinate.done
    {coordinate : Coordinate}
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    (hensures : EnsuresCoordinate coordinate computation)
    {state finalState : LazyRevealProbe.State Coordinate}
    {cache finalCache : SplitHashCache} {fuel remaining : Nat} {value : alpha}
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel (computation.run cache))) :
    coordinate ∈ finalState.ensured :=
  hensures.of_run state finalState cache finalCache fuel remaining value hresult

theorem EnsuresCoordinate.bind_preserved
    {coordinate : Coordinate}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta}
    (hleft : EnsuresCoordinate coordinate left) :
    EnsuresCoordinate coordinate (left >>= next) := by
  constructor
  intro state finalState cache finalCache fuel remaining value hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (left.run cache >>= fun result => (next result.1).run result.2)) at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hraw, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done middleState middleRemaining middleResult =>
      rcases middleResult with ⟨middleValue, middleCache⟩
      have hmiddle := hleft.of_run state middleState cache middleCache fuel middleRemaining
        middleValue hraw
      exact (LazyRevealProbe.ensuredLE_of_mem_runRaw_done
        ((next middleValue).run middleCache) middleState finalState middleRemaining remaining
          (value, finalCache) hrest) hmiddle

theorem EnsuresCoordinate.bind_right
    {coordinate : Coordinate}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta}
    (hnext : ∀ value, EnsuresCoordinate coordinate (next value)) :
    EnsuresCoordinate coordinate (left >>= next) := by
  constructor
  intro state finalState cache finalCache fuel remaining value hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (left.run cache >>= fun result => (next result.1).run result.2)) at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hraw, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done middleState middleRemaining middleResult =>
      rcases middleResult with ⟨middleValue, middleCache⟩
      exact (hnext middleValue).of_run middleState finalState middleCache finalCache
        middleRemaining remaining value hrest

theorem ensuresCoordinate_ensureCoordinate (coordinate : Coordinate) :
    EnsuresCoordinate coordinate (ensureCoordinate coordinate) := by
  constructor
  intro state finalState cache finalCache fuel remaining value hresult
  exact mem_runRaw_ensureCoordinate_mem coordinate state finalState cache finalCache fuel
    remaining value hresult

theorem EnsuresCoordinate.sequenceFin_component {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (index : Fin n) (hensures : EnsuresCoordinate coordinate (computation index)) :
    EnsuresCoordinate coordinate (sequenceFin computation) := by
  induction n with
  | zero => exact index.elim0
  | succ n ih =>
      rw [sequenceFin]
      cases index using Fin.cases with
      | zero => exact hensures.bind_preserved
      | succ index =>
          apply EnsuresCoordinate.bind_right
          intro head
          exact (ih (fun current : Fin n => computation current.succ) index
            hensures).bind_preserved

def EnsuresCoordinates {n : Nat} (coordinate : Fin n → Coordinate)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha) : Prop :=
  ∀ index, EnsuresCoordinate (coordinate index) computation

theorem ensuresCoordinates_sequenceFin {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (coordinate : Fin n → Coordinate)
    (hcomponent : ∀ index, EnsuresCoordinate (coordinate index) (computation index)) :
    EnsuresCoordinates coordinate (sequenceFin computation) := by
  intro index
  exact EnsuresCoordinate.sequenceFin_component computation index (hcomponent index)

theorem mem_runRaw_ensureChainPrefix_mem
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (digit : Digit) (step : ChainStep) (hstep : step.val < digit.val)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : Unit)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((ensureChainPrefix lay tree leafIdx chainIdx digit).run cache))) :
    Coordinate.position (.chain lay tree leafIdx chainIdx step) ∈ finalState.ensured := by
  unfold ensureChainPrefix at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hsequence, hfinish⟩ := hresult
  cases raw with
  | stopped hit => simp at hfinish
  | done sequenceState sequenceRemaining sequenceResult =>
      rcases sequenceResult with ⟨values, sequenceCache⟩
      obtain ⟨componentState, componentFinalState, componentCache, componentFinalCache,
          componentFuel, componentRemaining, componentValue, hcomponent, _, _,
          hcomponentEnsured, _⟩ :=
        sequenceFin_component_run_of_done
          (fun current : ChainStep =>
            if current.val < digit.val then
              ensureCoordinate (.position (.chain lay tree leafIdx chainIdx current))
            else pure ())
          (fun current => by
            split
            · exact (splitCachePreserving_ensureCoordinate _).ordinaryCacheIncreasing
            · exact OrdinaryCacheIncreasing.pure ())
          state sequenceState cache sequenceCache fuel sequenceRemaining values hsequence step
      rw [if_pos hstep] at hcomponent
      have hensured := hcomponentEnsured (mem_runRaw_ensureCoordinate_mem _ componentState
        componentFinalState componentCache componentFinalCache componentFuel componentRemaining
          componentValue hcomponent)
      simp [LazyRevealProbe.runRaw] at hfinish
      rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
      exact hensured

theorem ensuresCoordinate_ensureChainPrefix
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (digit : Digit) (step : ChainStep) (hstep : step.val < digit.val) :
    EnsuresCoordinate (.position (.chain lay tree leafIdx chainIdx step))
      (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  constructor
  intro state finalState cache finalCache fuel remaining value hresult
  exact mem_runRaw_ensureChainPrefix_mem lay tree leafIdx chainIdx digit step hstep state
    finalState cache finalCache fuel remaining value hresult

set_option maxRecDepth 10000 in
theorem cachedRun_otsSignFrom_of_mem_runRaw_maskedOtsSignFrom
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer)
    (table : Coordinate → HashOutput) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) : ∀ attempts counter
      (state finalState : LazyRevealProbe.State Coordinate)
      (cache finalCache : SplitHashCache) (fuel remaining : Nat)
      (selectedCounter : Counter) (encoding : ChainIndex → Digit)
      (targetState : LazyRevealProbe.State Coordinate) (targetCache : SplitHashCache),
      StableCacheAgreesWithFn parameter finalCache f →
      (∀ position : Position, IsOtsPosition position →
        f (tableInput parameter table (.position position)) = table (.position position)) →
      LazyRevealProbe.RawResult.done finalState remaining
          (some (selectedCounter, encoding), finalCache) ∈ support
        (LazyRevealProbe.runRaw state fuel
          ((maskedOtsSignFrom parameter lay tree leafIdx message attempts counter).run cache)) →
      LazyRevealProbe.EnsuredLE finalState targetState →
      StableOrdinaryCacheLE parameter finalCache targetCache →
      CachedRun (mergedCache parameter table targetState.ensured targetCache) f
        (otsSignFrom parameter lay tree leafIdx (tableOtsSecret table lay tree leafIdx)
          message attempts counter)
  | 0, counter, state, finalState, cache, finalCache, fuel, remaining,
      selectedCounter, encoding, targetState, targetCache, hf, hrealizes, hresult,
      hensuredTarget, hcacheTarget => by
      simp [maskedOtsSignFrom, LazyRevealProbe.runRaw] at hresult
  | attempts + 1, counter, state, finalState, cache, finalCache, fuel, remaining,
      selectedCounter, encoding, targetState, targetCache, hf, hrealizes, hresult,
      hensuredTarget, hcacheTarget => by
      rw [maskedOtsSignFrom, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨raw, hencode, hrest⟩ := hresult
      cases raw with
      | stopped hit => simp at hrest
      | done encodeState encodeRemaining encodeResult =>
          rcases encodeResult with ⟨encoded, encodeCache⟩
          simp only at hrest
          cases encoded with
          | none =>
              have hordinaryLE := ordinaryCacheIncreasing_maskedOtsSignFrom parameter lay tree
                leafIdx message attempts (counter + 1) encodeState encodeCache encodeRemaining
                  finalState remaining (some (selectedCounter, encoding)) finalCache hrest
              have hfEncode : StableCacheAgreesWithFn parameter encodeCache f :=
                fun input output hstable hcached => hf input output hstable
                  (hordinaryLE hcached)
              have hreplay := replay_of_mem_runRaw_ordinaryHashImpl_of_stable f parameter
                (encode parameter lay tree leafIdx message (BitVec.ofNat counterBits counter))
                state encodeState cache encodeCache fuel encodeRemaining none hfEncode
                  (queriesStable_encode f parameter lay tree leafIdx message
                    (BitVec.ofNat counterBits counter)) hencode
              have hencodeRun := cachedRun_mergedCache_of_stable f parameter table targetState
                targetCache _
                  (queriesStable_encode f parameter lay tree leafIdx message
                    (BitVec.ofNat counterBits counter))
                  (CachedRun.mono_stableOrdinary
                    (queriesStable_encode f parameter lay tree leafIdx message
                      (BitVec.ofNat counterBits counter))
                    ((StableOrdinaryCacheLE.of_le hordinaryLE).trans hcacheTarget) hreplay.2)
              rw [otsSignFrom]
              apply hencodeRun.bind
              rw [hreplay.1]
              exact cachedRun_otsSignFrom_of_mem_runRaw_maskedOtsSignFrom f parameter lay table tree
                leafIdx message attempts (counter + 1) encodeState finalState encodeCache
                  finalCache encodeRemaining remaining selectedCounter encoding targetState
                    targetCache hf hrealizes hrest hensuredTarget hcacheTarget
          | some selectedEncoding =>
              rw [StateT.run_bind, LazyRevealProbe.runRaw_bind,
                mem_support_bind_iff] at hrest
              obtain ⟨ensureRaw, hensure, hfinish⟩ := hrest
              cases ensureRaw with
              | stopped hit => simp at hfinish
              | done ensureState ensureRemaining ensureResult =>
                  rcases ensureResult with ⟨ensured, ensureCache⟩
                  simp [LazyRevealProbe.runRaw] at hfinish
                  rcases hfinish with ⟨rfl, rfl, hselected, rfl⟩
                  rcases hselected with ⟨hcounter, hencoding⟩
                  subst selectedCounter
                  subst encoding
                  have hordinaryLE := ordinaryCacheIncreasing_sequenceFin
                    (fun chainIdx => ensureChainPrefix lay tree leafIdx chainIdx
                      (selectedEncoding chainIdx))
                    (fun chainIdx =>
                      (splitCachePreserving_ensureChainPrefix lay tree leafIdx chainIdx
                        (selectedEncoding chainIdx)).ordinaryCacheIncreasing)
                    encodeState encodeCache encodeRemaining finalState remaining ensured
                      finalCache hensure
                  have hfEncode : StableCacheAgreesWithFn parameter encodeCache f :=
                    fun input output hstable hcached => hf input output hstable
                      (hordinaryLE hcached)
                  have hreplay := replay_of_mem_runRaw_ordinaryHashImpl_of_stable f parameter
                    (encode parameter lay tree leafIdx message (BitVec.ofNat counterBits counter))
                    state encodeState cache encodeCache fuel encodeRemaining
                      (some selectedEncoding) hfEncode
                      (queriesStable_encode f parameter lay tree leafIdx message
                        (BitVec.ofNat counterBits counter)) hencode
                  have hencodeRun := cachedRun_mergedCache_of_stable f parameter table targetState
                    targetCache _
                      (queriesStable_encode f parameter lay tree leafIdx message
                        (BitVec.ofNat counterBits counter))
                      (CachedRun.mono_stableOrdinary
                        (queriesStable_encode f parameter lay tree leafIdx message
                          (BitVec.ofNat counterBits counter))
                        ((StableOrdinaryCacheLE.of_le hordinaryLE).trans hcacheTarget) hreplay.2)
                  have hensured : ∀ chainIdx step, step.val < (selectedEncoding chainIdx).val →
                      Coordinate.position (.chain lay tree leafIdx chainIdx step) ∈
                        targetState.ensured := by
                    intro chainIdx step hstep
                    exact hensuredTarget ((EnsuresCoordinate.sequenceFin_component
                      (fun current : ChainIndex => ensureChainPrefix lay tree leafIdx current
                        (selectedEncoding current)) chainIdx
                      (ensuresCoordinate_ensureChainPrefix lay tree leafIdx chainIdx
                        (selectedEncoding chainIdx) step hstep)).of_run encodeState finalState
                          encodeCache finalCache encodeRemaining remaining ensured hensure)
                  have hchains : ∀ chainIdx, CachedRun
                      (mergedCache parameter table targetState.ensured targetCache) f
                      (chainWalk parameter lay tree leafIdx chainIdx 0
                        (selectedEncoding chainIdx).val
                          (tableOtsSecret table lay tree leafIdx chainIdx)) := by
                    intro chainIdx
                    exact cachedRun_chainWalk_of_ensured f parameter table targetState targetCache
                      lay tree leafIdx chainIdx hrealizes (selectedEncoding chainIdx).val
                        (fun step hstep => hensured chainIdx step hstep)
                  rw [otsSignFrom]
                  apply hencodeRun.bind
                  rw [hreplay.1]
                  apply (CachedRun.sequenceFin _ hchains).bind
                  exact CachedRun.pure _ _ _

theorem cachedRun_otsSign_of_mem_runRaw_maskedOtsSign
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer)
    (table : Coordinate → HashOutput) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (selectedCounter : Counter) (encoding : ChainIndex → Digit)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        (some (selectedCounter, encoding), finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((maskedOtsSign parameter lay tree leafIdx message).run cache))) :
    CachedRun (mergedCache parameter table finalState.ensured finalCache) f
      (otsSign parameter lay tree leafIdx (tableOtsSecret table lay tree leafIdx) message) := by
  exact cachedRun_otsSignFrom_of_mem_runRaw_maskedOtsSignFrom f parameter lay table tree leafIdx
    message encodingAttemptLimit 0 state finalState cache finalCache fuel remaining selectedCounter
      encoding finalState finalCache hf hrealizes hresult
        (LazyRevealProbe.EnsuredLE.refl finalState)
          (StableOrdinaryCacheLE.refl parameter finalCache)

theorem ensuresCoordinate_ensureFullChain
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (step : ChainStep) :
    EnsuresCoordinate (.position (.chain lay tree leafIdx chainIdx step))
      (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  exact (EnsuresCoordinate.sequenceFin_component
    (fun current : ChainStep =>
      ensureCoordinate (.position (.chain lay tree leafIdx chainIdx current))) step
    (ensuresCoordinate_ensureCoordinate _)).bind_preserved

theorem ensuresCoordinates_ensureFullChains
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (step : ChainStep) :
    EnsuresCoordinates
      (fun chainIdx : ChainIndex =>
        Coordinate.position (.chain lay tree leafIdx chainIdx step))
      (sequenceFin fun chainIdx : ChainIndex =>
        ensureFullChain lay tree leafIdx chainIdx) := by
  exact ensuresCoordinates_sequenceFin
    (fun chainIdx : ChainIndex => ensureFullChain lay tree leafIdx chainIdx)
    (fun chainIdx : ChainIndex => .position (.chain lay tree leafIdx chainIdx step))
    (fun chainIdx => ensuresCoordinate_ensureFullChain lay tree leafIdx chainIdx step)

theorem ensuresCoordinate_ensureOtsLeaf_chain
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (step : ChainStep) :
    EnsuresCoordinate (.position (.chain lay tree leafIdx chainIdx step))
      (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  exact (ensuresCoordinates_ensureFullChains lay tree leafIdx step chainIdx).bind_preserved

theorem ensuresCoordinate_ensureOtsLeaf_leaf
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    EnsuresCoordinate (.position (.leaf lay tree leafIdx))
      (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  apply EnsuresCoordinate.bind_right
  intro values
  exact ensuresCoordinate_ensureCoordinate _

theorem mem_runRaw_ensureFullChain_mem
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (step : ChainStep) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : Unit)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((ensureFullChain lay tree leafIdx chainIdx).run cache))) :
    Coordinate.position (.chain lay tree leafIdx chainIdx step) ∈ finalState.ensured := by
  exact (ensuresCoordinate_ensureFullChain lay tree leafIdx chainIdx step).done hresult

attribute [local irreducible] ensureFullChain ensureOtsLeaf

set_option linter.constructorNameAsVariable false in
theorem mem_runRaw_ensureOtsLeaf_mem
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : Unit)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((ensureOtsLeaf lay tree leafIdx).run cache))) :
    (∀ chainIdx step,
      Coordinate.position (.chain lay tree leafIdx chainIdx step) ∈ finalState.ensured) ∧
      Coordinate.position (.leaf lay tree leafIdx) ∈ finalState.ensured := by
  constructor
  · intro chainIdx step
    exact (ensuresCoordinate_ensureOtsLeaf_chain lay tree leafIdx chainIdx step).of_run
      state finalState cache finalCache fuel remaining value hresult
  · exact (ensuresCoordinate_ensureOtsLeaf_leaf lay tree leafIdx).of_run
      state finalState cache finalCache fuel remaining value hresult

theorem cachedRun_oneTimePublicKey_of_ensuredOtsLeaf
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hensured : ∀ chainIdx step,
      Coordinate.position (.chain lay tree leafIdx chainIdx step) ∈ state.ensured) :
    CachedRun (mergedCache parameter table state.ensured cache) f
      (oneTimePublicKey parameter lay tree leafIdx
        (tableOtsSecret table lay tree leafIdx)) := by
  apply CachedRun.sequenceFin
  intro chainIdx
  exact cachedRun_chainWalk_of_ensured f parameter table state cache lay tree leafIdx chainIdx
    hrealizes (chainLength - 1) (fun step _ => hensured chainIdx step)

theorem cachedRun_treeNode_zero_of_ensuredOtsLeaf
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache) (lay : Layer) (tree : TreeIndex) (nodeIdx : Nat)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hchains : ∀ chainIdx step,
      Coordinate.position (.chain lay tree (leafOfNat nodeIdx) chainIdx step) ∈ state.ensured)
    (hleaf : Coordinate.position (.leaf lay tree (leafOfNat nodeIdx)) ∈ state.ensured) :
    CachedRun (mergedCache parameter table state.ensured cache) f
      (treeNode parameter lay tree (tableOtsSecret table lay tree) 0 nodeIdx) := by
  rw [treeNode_zero_eq]
  have hpublic := cachedRun_oneTimePublicKey_of_ensuredOtsLeaf f parameter table state cache lay
    tree (leafOfNat nodeIdx) hrealizes hchains
  apply hpublic.bind
  have hendpoints : evalWithAnswerFn f
      (oneTimePublicKey parameter lay tree (leafOfNat nodeIdx)
        (tableOtsSecret table lay tree (leafOfNat nodeIdx))) =
      fun chainIdx => tableValue table
        (.chain lay tree (leafOfNat nodeIdx) chainIdx Position.lastChainStep) := by
    rw [eval_oneTimePublicKey]
    simpa only [honestEndpoints_def] using
      honestEndpoints_eq_table f parameter table lay tree (leafOfNat nodeIdx) hrealizes
  intro input hinput
  simp only [leafHash, queriedInputs_tweakableHash, List.mem_singleton] at hinput
  subst input
  rw [hendpoints]
  have hinput : tweakableHashInput parameter (.leaf lay tree (leafOfNat nodeIdx))
        (leafPayload fun chainIdx => tableValue table
          (.chain lay tree (leafOfNat nodeIdx) chainIdx Position.lastChainStep)) =
      tableInput parameter table (.position (.leaf lay tree (leafOfNat nodeIdx))) := by
    simp [tableInput, tablePayload, Position.children, Position.domain, leafPayload,
      Function.comp_def]
  rw [hinput]
  exact mergedCache_tableInput_ne_none_of_ensured parameter table state cache
    (.leaf lay tree (leafOfNat nodeIdx)) (by trivial) hleaf

theorem treeNode_succ_input_eq_table
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (lay : Layer) (tree : TreeIndex)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (level nodeIdx : Nat) (hlevel : level < maxLayerHeight)
    (hspan : 2 ^ (level + 1) * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight) :
    tweakableHashInput parameter (.node lay tree (level + 1) nodeIdx)
        (nodePayload
          (evalWithAnswerFn f
            (treeNode parameter lay tree (tableOtsSecret table lay tree) level (2 * nodeIdx)))
          (evalWithAnswerFn f
            (treeNode parameter lay tree (tableOtsSecret table lay tree) level
              (2 * nodeIdx + 1)))) =
      tableInput parameter table
        (.position (.node lay tree ⟨level, hlevel⟩ (leafOfNat nodeIdx))) := by
  have hnode : nodeIdx < 2 ^ maxLayerHeight := by
    have hpow : 0 < 2 ^ (level + 1) := pow_pos (by omega) _
    nlinarith
  have hpowTwo : 2 ≤ 2 ^ (level + 1) := by
    simpa using Nat.pow_le_pow_right (n := 2) (by omega) (show 1 ≤ level + 1 by omega)
  have hleft : 2 * nodeIdx < 2 ^ maxLayerHeight := by nlinarith
  have hright : 2 * nodeIdx + 1 < 2 ^ maxLayerHeight := by nlinarith
  change tweakableHashInput parameter (.node lay tree (level + 1) nodeIdx)
      (nodePayload
        (honestNode f parameter lay tree (tableOtsSecret table lay tree) level (2 * nodeIdx))
        (honestNode f parameter lay tree (tableOtsSecret table lay tree) level
          (2 * nodeIdx + 1))) = _
  cases level with
  | zero =>
      have hleftValue := honestNode_zero_eq_table f parameter table lay tree
        (leafOfNat (2 * nodeIdx)) hrealizes
      have hrightValue := honestNode_zero_eq_table f parameter table lay tree
        (leafOfNat (2 * nodeIdx + 1)) hrealizes
      have hleftIndex : (leafOfNat (2 * nodeIdx)).val = 2 * nodeIdx := by
        simp [leafOfNat, Nat.mod_eq_of_lt hleft]
      have hrightIndex : (leafOfNat (2 * nodeIdx + 1)).val = 2 * nodeIdx + 1 := by
        simp [leafOfNat, Nat.mod_eq_of_lt hright]
      rw [hleftIndex] at hleftValue
      rw [hrightIndex] at hrightValue
      rw [hleftValue, hrightValue]
      simp only [tableInput, tablePayload, Position.domain]
      rw [Position.children, dif_pos (by
        simpa [leafOfNat, Nat.mod_eq_of_lt hnode] using hright),
        dif_neg (show ¬0 < (⟨0, hlevel⟩ : Fin maxLayerHeight).val by simp)]
      simp [nodePayload, leafOfNat, Nat.mod_eq_of_lt hnode,
        Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright]
  | succ previous =>
      have hleftSpan : 2 ^ (previous + 1) * (2 * nodeIdx + 1) ≤
          2 ^ maxLayerHeight := by
        rw [pow_succ] at hspan
        nlinarith
      have hrightSpan : 2 ^ (previous + 1) * (2 * nodeIdx + 1 + 1) ≤
          2 ^ maxLayerHeight := by
        rw [pow_succ] at hspan
        nlinarith
      rw [honestNode_eq_table_succ f parameter table lay tree hrealizes previous
          (2 * nodeIdx) (by omega) hleftSpan,
        honestNode_eq_table_succ f parameter table lay tree hrealizes previous
          (2 * nodeIdx + 1) (by omega) hrightSpan]
      simp only [tableInput, tablePayload, Position.domain]
      rw [Position.children, dif_pos (by
        simpa [leafOfNat, Nat.mod_eq_of_lt hnode] using hright),
        dif_pos (show 0 < (⟨previous + 1, hlevel⟩ : Fin maxLayerHeight).val by simp)]
      simp [nodePayload, leafOfNat, Nat.mod_eq_of_lt hnode,
        Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright]

set_option linter.unusedVariables false in
set_option linter.constructorNameAsVariable false in
theorem cachedRun_treeNode_of_mem_runRaw_ensureTreeNode
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (lay : Layer) (tree : TreeIndex)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position)) :
    ∀ level nodeIdx (hspan : 2 ^ level * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight)
        (state finalState targetState : LazyRevealProbe.State Coordinate)
        (cache finalCache targetCache : SplitHashCache) (fuel remaining : Nat) (value : Unit),
      LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
          support (LazyRevealProbe.runRaw state fuel
            ((ensureTreeNode lay tree level nodeIdx).run cache)) →
      LazyRevealProbe.EnsuredLE finalState targetState →
      CachedRun (mergedCache parameter table targetState.ensured targetCache) f
        (treeNode parameter lay tree (tableOtsSecret table lay tree) level nodeIdx)
  | 0, nodeIdx, _, state, finalState, targetState, cache, finalCache, targetCache,
      fuel, remaining, value, hresult, htarget => by
      have hensured := mem_runRaw_ensureOtsLeaf_mem lay tree (leafOfNat nodeIdx) state
        finalState cache finalCache fuel remaining value hresult
      exact cachedRun_treeNode_zero_of_ensuredOtsLeaf f parameter table targetState targetCache
        lay tree nodeIdx hrealizes (fun chainIdx step => htarget (hensured.1 chainIdx step))
          (htarget hensured.2)
  | level + 1, nodeIdx, hspan, state, finalState, targetState, cache, finalCache,
      targetCache, fuel, remaining, value, hresult, htarget => by
      have hpow : 2 ^ (level + 1) ≤ 2 ^ maxLayerHeight := calc
        2 ^ (level + 1) = 2 ^ (level + 1) * 1 := by simp
        _ ≤ 2 ^ (level + 1) * (nodeIdx + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        _ ≤ 2 ^ maxLayerHeight := hspan
      have hlevel : level < maxLayerHeight := by
        have := (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpow
        omega
      rw [ensureTreeNode, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨leftRaw, hleft, hafterLeft⟩ := hresult
      cases leftRaw with
      | stopped hit => simp at hafterLeft
      | done leftState leftRemaining leftResult =>
          rcases leftResult with ⟨leftValue, leftCache⟩
          simp only at hafterLeft
          rw [StateT.run_bind, LazyRevealProbe.runRaw_bind,
            mem_support_bind_iff] at hafterLeft
          obtain ⟨rightRaw, hright, hlast⟩ := hafterLeft
          cases rightRaw with
          | stopped hit => simp at hlast
          | done rightState rightRemaining rightResult =>
              rcases rightResult with ⟨rightValue, rightCache⟩
              rw [dif_pos hlevel] at hlast
              have hrightTarget : LazyRevealProbe.EnsuredLE rightState targetState :=
                (LazyRevealProbe.ensuredLE_of_mem_runRaw_done
                  ((ensureCoordinate (.position
                    (.node lay tree ⟨level, hlevel⟩ (leafOfNat nodeIdx)))).run rightCache)
                  rightState finalState rightRemaining remaining (value, finalCache) hlast).trans
                    htarget
              have hleftTarget : LazyRevealProbe.EnsuredLE leftState targetState :=
                (LazyRevealProbe.ensuredLE_of_mem_runRaw_done
                  ((ensureTreeNode lay tree level (2 * nodeIdx + 1)).run leftCache)
                  leftState rightState leftRemaining rightRemaining
                    (rightValue, rightCache) hright).trans hrightTarget
              have hleftSpan : 2 ^ level * (2 * nodeIdx + 1) ≤
                  2 ^ maxLayerHeight := by
                rw [pow_succ] at hspan
                nlinarith [Nat.zero_le (2 ^ level), Nat.zero_le nodeIdx]
              have hrightSpan : 2 ^ level * (2 * nodeIdx + 1 + 1) ≤
                  2 ^ maxLayerHeight := by
                rw [pow_succ] at hspan
                nlinarith [Nat.zero_le (2 ^ level), Nat.zero_le nodeIdx]
              have hleftRun := cachedRun_treeNode_of_mem_runRaw_ensureTreeNode f parameter
                table lay tree hrealizes level (2 * nodeIdx) hleftSpan state leftState
                  targetState cache leftCache targetCache fuel leftRemaining leftValue hleft
                    hleftTarget
              have hrightRun := cachedRun_treeNode_of_mem_runRaw_ensureTreeNode f parameter
                table lay tree hrealizes level (2 * nodeIdx + 1) hrightSpan leftState
                  rightState targetState leftCache rightCache targetCache leftRemaining
                    rightRemaining rightValue hright hrightTarget
              rw [treeNode_succ_eq]
              apply hleftRun.bind
              apply hrightRun.bind
              intro input hinput
              simp only [queriedInputs_tweakableHash, List.mem_singleton] at hinput
              subst input
              rw [treeNode_succ_input_eq_table f parameter table lay tree hrealizes level
                nodeIdx hlevel hspan]
              exact mergedCache_tableInput_ne_none_of_ensured parameter table targetState
                targetCache (.node lay tree ⟨level, hlevel⟩ (leafOfNat nodeIdx)) (by trivial)
                  (htarget (mem_runRaw_ensureCoordinate_mem _ rightState finalState rightCache
                    finalCache rightRemaining remaining value hlast))

set_option maxRecDepth 10000 in
theorem cachedRun_treePath_of_mem_runRaw_ensureTreePath
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : Unit)
    (targetState : LazyRevealProbe.State Coordinate) (targetCache : SplitHashCache)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((ensureTreePath lay tree leafIdx).run cache)))
    (htarget : LazyRevealProbe.EnsuredLE finalState targetState) :
    CachedRun (mergedCache parameter table targetState.ensured targetCache) f
      (treePath parameter lay tree (tableOtsSecret table lay tree) leafIdx) := by
  unfold ensureTreePath at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨sequenceRaw, hsequence, hfinish⟩ := hresult
  cases sequenceRaw with
  | stopped hit => simp at hfinish
  | done sequenceState sequenceRemaining sequenceResult =>
      rcases sequenceResult with ⟨values, sequenceCache⟩
      simp [LazyRevealProbe.runRaw] at hfinish
      rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
      unfold treePath
      apply CachedRun.sequenceFin
      intro level
      by_cases hinLayer : level.val < layerHeight lay
      · rw [if_pos hinLayer]
        obtain ⟨componentState, componentFinalState, componentCache,
            componentFinalCache, componentFuel, componentRemaining, componentValue,
            hcomponent, _, _, hcomponentEnsured, _⟩ :=
          sequenceFin_component_run_of_done
            (fun current : Fin maxLayerHeight =>
              if current.val < layerHeight lay then
                ensureTreeNode lay tree current.val
                  (Nat.xor (leafIdx.val / 2 ^ current.val) 1)
              else pure ())
            (fun current => by
              split
              · exact (splitCachePreserving_ensureTreeNode lay tree current.val
                  (Nat.xor (leafIdx.val / 2 ^ current.val) 1)).ordinaryCacheIncreasing
              · exact OrdinaryCacheIncreasing.pure ())
            state finalState cache finalCache fuel remaining values hsequence level
        rw [if_pos hinLayer] at hcomponent
        have hspan := FtsProbeSimulation.sibling_node_bound maxLayerHeight leafIdx.val
          level.val (by omega) leafIdx.isLt
        exact cachedRun_treeNode_of_mem_runRaw_ensureTreeNode f parameter table lay tree
          hrealizes level.val (Nat.xor (leafIdx.val / 2 ^ level.val) 1) hspan
            componentState componentFinalState targetState componentCache componentFinalCache
              targetCache componentFuel componentRemaining componentValue hcomponent
                (hcomponentEnsured.trans htarget)
      · rw [if_neg hinLayer]
        exact CachedRun.pure _ _ _

theorem cachedRun_treeRoot_of_mem_runRaw_maskedTreeRoot
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (lay : Layer) (tree : TreeIndex)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (state finalState targetState : LazyRevealProbe.State Coordinate)
    (cache finalCache targetCache : SplitHashCache) (fuel remaining : Nat)
    (value : Digest)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel ((maskedTreeRoot lay tree).run cache)))
    (htarget : LazyRevealProbe.EnsuredLE finalState targetState) :
    CachedRun (mergedCache parameter table targetState.ensured targetCache) f
      (treeRoot parameter lay tree (tableOtsSecret table lay tree)) := by
  have hpositive : 0 < layerHeight lay := by
    unfold layerHeight
    split <;> norm_num [maxLayerHeight]
  have hlevel : layerHeight lay - 1 < maxLayerHeight := by
    have hle := layerHeight_le lay
    omega
  have hlayer : layerHeight lay = layerHeight lay - 1 + 1 := by omega
  unfold maskedTreeRoot at hresult
  rw [hlayer, maskedTreeNode, dif_pos hlevel, StateT.run_bind,
    LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨ensureRaw, hensure, hreveal⟩ := hresult
  cases ensureRaw with
  | stopped hit => simp at hreveal
  | done ensureState ensureRemaining ensureResult =>
      rcases ensureResult with ⟨ensureValue, ensureCache⟩
      have hensuredTarget : LazyRevealProbe.EnsuredLE ensureState targetState :=
        (LazyRevealProbe.ensuredLE_of_mem_runRaw_done
          ((revealPosition (.node lay tree ⟨layerHeight lay - 1, hlevel⟩
            (leafOfNat 0))).run ensureCache) ensureState finalState ensureRemaining remaining
              (value, finalCache) hreveal).trans htarget
      have hspan : 2 ^ (layerHeight lay - 1 + 1) * (0 + 1) ≤
          2 ^ maxLayerHeight := by
        rw [← hlayer]
        simpa using Nat.pow_le_pow_right (n := 2) (by omega) (layerHeight_le lay)
      unfold treeRoot
      rw [hlayer]
      exact cachedRun_treeNode_of_mem_runRaw_ensureTreeNode f parameter table lay tree
        hrealizes (layerHeight lay - 1 + 1) 0 hspan state ensureState targetState cache
          ensureCache targetCache fuel ensureRemaining ensureValue hensure hensuredTarget

set_option maxRecDepth 10000 in
theorem cachedRun_signLayer_of_mem_runRaw_maskedSignLayer
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (counter : Counter) (encoding : ChainIndex → Digit)
    (targetState : LazyRevealProbe.State Coordinate) (targetCache : SplitHashCache)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        (some (counter, encoding), finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((maskedSignLayer parameter ftsSecret index lay).run cache)))
    (hensuredTarget : LazyRevealProbe.EnsuredLE finalState targetState)
    (hcacheTarget : StableOrdinaryCacheLE parameter finalCache targetCache) :
    CachedRun (mergedCache parameter table targetState.ensured targetCache) f
      (signLayer (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
        index lay) := by
  unfold maskedSignLayer at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨messageRaw, hmessage, hafterMessage⟩ := hresult
  cases messageRaw with
  | stopped hit => simp at hafterMessage
  | done messageState messageRemaining messageResult =>
      rcases messageResult with ⟨message, messageCache⟩
      simp only at hafterMessage
      change LazyRevealProbe.RawResult.done finalState remaining
          (some (counter, encoding), finalCache) ∈ support
        (LazyRevealProbe.runRaw messageState messageRemaining
          ((maskedOtsLayerAfterMessage parameter index lay message).run messageCache))
        at hafterMessage
      have hmessageTarget := LazyRevealProbe.ensuredLE_of_mem_runRaw_done
        ((maskedOtsLayerAfterMessage parameter index lay message).run messageCache)
          messageState finalState messageRemaining remaining
            (some (counter, encoding), finalCache) hafterMessage
      have hmessageActual : message = evalWithAnswerFn f
          (layerMessage
            (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) index lay) := by
        by_cases hbelow : lay.val + 1 < numLayers
        · let below : Layer := ⟨lay.val + 1, hbelow⟩
          have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
            ((maskedOtsLayerAfterMessage parameter index lay message).run messageCache)
              messageState finalState messageRemaining remaining
                (some (counter, encoding), finalCache) hafterMessage
          exact maskedLayerMessage_eq_actual_of_lt
            (f := f) (parameter := parameter) (root := root) (table := table)
            (ftsSecret := ftsSecret) (index := index) (lay := lay) (below := below)
            (hbelow := hbelow) (hbelowEq := rfl) (state := state)
            (messageState := messageState) (referenceState := finalState) (cache := cache)
            (messageCache := messageCache) (fuel := fuel) (messageRemaining := messageRemaining)
            (message := message) hvaluesLE htable hrealizes hmessage
        · have hordinaryLE := ordinaryCacheIncreasing_maskedSignLayerAfterMessage parameter
            index lay message messageState messageCache messageRemaining finalState remaining
              (some (counter, encoding)) finalCache hafterMessage
          have hfMessage : StableCacheAgreesWithFn parameter messageCache f :=
            fun input output hstable hcached => hf input output hstable (hordinaryLE hcached)
          exact maskedLayerMessage_eq_actual_of_not_lt f parameter root table ftsSecret index lay
            hbelow state messageState cache messageCache fuel messageRemaining message hfMessage
              hmessage
      have hmessageRun : CachedRun
          (mergedCache parameter table targetState.ensured targetCache) f
          (layerMessage
            (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) index lay) := by
        by_cases hbelow : lay.val + 1 < numLayers
        · let below : Layer := ⟨lay.val + 1, hbelow⟩
          rw [layerMessage, dif_pos hbelow]
          have hmessage' := hmessage
          rw [maskedLayerMessage, dif_pos hbelow] at hmessage'
          exact cachedRun_treeRoot_of_mem_runRaw_maskedTreeRoot f parameter table below
            (treeIndexAt index below) hrealizes state messageState targetState cache messageCache
              targetCache fuel messageRemaining message hmessage'
                (hmessageTarget.trans hensuredTarget)
        · rw [layerMessage, dif_neg hbelow]
          have hmessage' := hmessage
          rw [maskedLayerMessage, dif_neg hbelow] at hmessage'
          have hordinaryLE := ordinaryCacheIncreasing_maskedSignLayerAfterMessage parameter
            index lay message messageState messageCache messageRemaining finalState remaining
              (some (counter, encoding)) finalCache hafterMessage
          have hfMessage : StableCacheAgreesWithFn parameter messageCache f :=
            fun input output hstable hcached => hf input output hstable (hordinaryLE hcached)
          have hreplay := replay_of_mem_runRaw_ordinaryHashImpl_of_stable f parameter
            (ftsKey parameter index (ftsSecret index)) state messageState cache messageCache fuel
              messageRemaining message hfMessage
                (queriesStable_ftsKey f parameter index (ftsSecret index)) hmessage'
          exact cachedRun_mergedCache_of_stable f parameter table targetState targetCache _
            (queriesStable_ftsKey f parameter index (ftsSecret index))
              (CachedRun.mono_stableOrdinary
                (queriesStable_ftsKey f parameter index (ftsSecret index))
                ((StableOrdinaryCacheLE.of_le hordinaryLE).trans hcacheTarget) hreplay.2)
      unfold maskedOtsLayerAfterMessage at hafterMessage
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hafterMessage
      obtain ⟨otsRaw, hots, hafterOts⟩ := hafterMessage
      cases otsRaw with
      | stopped hit => simp at hafterOts
      | done otsState otsRemaining otsResult =>
          rcases otsResult with ⟨part, otsCache⟩
          cases part with
          | none => simp [LazyRevealProbe.runRaw] at hafterOts
          | some selectedPart =>
              rcases selectedPart with ⟨selectedCounter, selectedEncoding⟩
              simp only at hafterOts
              rw [StateT.run_bind, LazyRevealProbe.runRaw_bind,
                mem_support_bind_iff] at hafterOts
              obtain ⟨pathRaw, hpath, hfinish⟩ := hafterOts
              cases pathRaw with
              | stopped hit => simp at hfinish
              | done pathState pathRemaining pathResult =>
                  rcases pathResult with ⟨pathValue, pathCache⟩
                  have hpathCache := splitCachePreserving_ensureTreePath lay
                    (treeIndexAt index lay) (leafIndexAt index lay) otsState otsCache
                      otsRemaining pathState pathRemaining pathValue pathCache hpath
                  simp [LazyRevealProbe.runRaw] at hfinish
                  rcases hfinish with ⟨rfl, rfl, hpart, rfl⟩
                  rcases hpart with ⟨hcounter, hencoding⟩
                  subst selectedCounter
                  subst selectedEncoding
                  have hfOts := hf
                  rw [hpathCache] at hfOts
                  have hpathEnsured := LazyRevealProbe.ensuredLE_of_mem_runRaw_done
                    ((ensureTreePath lay (treeIndexAt index lay)
                      (leafIndexAt index lay)).run otsCache) otsState finalState otsRemaining
                        remaining (pathValue, finalCache) hpath
                  have hotsCacheTarget : StableOrdinaryCacheLE parameter otsCache
                      targetCache := by
                    have hotsToFinal : ordinaryQueryCache otsCache ≤
                        ordinaryQueryCache finalCache := by rw [hpathCache]
                    exact (StableOrdinaryCacheLE.of_le hotsToFinal).trans hcacheTarget
                  have hotsRun :=
                    cachedRun_otsSignFrom_of_mem_runRaw_maskedOtsSignFrom f parameter lay table
                      (treeIndexAt index lay) (leafIndexAt index lay) message encodingAttemptLimit
                        0 messageState otsState messageCache otsCache messageRemaining otsRemaining
                          counter encoding targetState targetCache hfOts hrealizes hots
                            (hpathEnsured.trans hensuredTarget) hotsCacheTarget
                  have hotsEval := maskedOtsSign_some_honest_eval f parameter lay
                    (treeIndexAt index lay) (leafIndexAt index lay)
                      (tableOtsSecret table lay (treeIndexAt index lay) (leafIndexAt index lay))
                        message messageState otsState messageCache otsCache messageRemaining
                          otsRemaining counter encoding hfOts hots
                  have hpathRun := cachedRun_treePath_of_mem_runRaw_ensureTreePath f parameter table
                    lay (treeIndexAt index lay) (leafIndexAt index lay) hrealizes otsState
                      finalState otsCache finalCache otsRemaining remaining pathValue targetState
                        targetCache hpath hensuredTarget
                  unfold signLayer
                  apply hmessageRun.bind
                  rw [← hmessageActual]
                  apply hotsRun.bind
                  unfold otsSign at hotsEval
                  rw [hotsEval]
                  apply hpathRun.bind
                  exact CachedRun.pure _ _ _

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
theorem successfulSignRun_of_mem_runRaw_maskedSignAfterDigest
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (message : Message) (randomness : Randomness) (index : Index)
    (leaves : DigestTree → FtsLeaf) (signature : Signature)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (targetState : LazyRevealProbe.State Coordinate) (targetCache : SplitHashCache)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hdigest : SuccessfulDigestRun f
      (mergedCache parameter table targetState.ensured targetCache)
      (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
        message randomness index leaves)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        (some signature, finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((maskedSignAfterDigest parameter ftsSecret randomness index leaves).run cache)))
    (hensuredTarget : LazyRevealProbe.EnsuredLE finalState targetState)
    (hcacheTarget : StableOrdinaryCacheLE parameter finalCache targetCache) :
    SuccessfulSignRun f (mergedCache parameter table targetState.ensured targetCache)
      (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
        message signature := by
  unfold maskedSignAfterDigest at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨pathRaw, hpath, hafterPath⟩ := hresult
  cases pathRaw with
  | stopped hit => simp at hafterPath
  | done pathState pathRemaining pathResult =>
      rcases pathResult with ⟨ftsPath, pathCache⟩
      simp only at hafterPath
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hafterPath
      obtain ⟨layersRaw, hlayers, hafterLayers⟩ := hafterPath
      cases layersRaw with
      | stopped hit => simp at hafterLayers
      | done layersState layersRemaining layersResult =>
          rcases layersResult with ⟨layers, layersCache⟩
          rw [← maskedSignLayers_eq_sequenceFin parameter ftsSecret index] at hlayers
          have hlayersLE := ordinaryCacheIncreasing_maskedSignLayers parameter ftsSecret index
            pathState pathCache pathRemaining layersState layersRemaining layers layersCache hlayers
          simp only at hafterLayers
          cases hparts : traverseOption layers with
          | none =>
              simp [hparts, LazyRevealProbe.runRaw] at hafterLayers
          | some parts =>
              rw [hparts, StateT.run_bind, LazyRevealProbe.runRaw_bind,
                mem_support_bind_iff] at hafterLayers
              obtain ⟨revealedRaw, hrevealed, hfinish⟩ := hafterLayers
              cases revealedRaw with
              | stopped hit => simp at hfinish
              | done revealedState revealedRemaining revealedResult =>
                  rcases revealedResult with ⟨revealed, revealedCache⟩
                  have hrevealedLE := ordinaryCacheIncreasing_sequenceFin
                    (fun lay => revealLayerValues index lay (parts lay).2)
                    (fun lay => ordinaryCacheIncreasing_revealLayerValues index lay (parts lay).2)
                    layersState layersCache layersRemaining revealedState revealedRemaining
                      revealed revealedCache hrevealed
                  have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
                    ((sequenceFin fun lay => revealLayerValues index lay (parts lay).2).run
                      layersCache) layersState revealedState layersRemaining revealedRemaining
                        (revealed, revealedCache) hrevealed
                  have hensuredLE := LazyRevealProbe.ensuredLE_of_mem_runRaw_done
                    ((sequenceFin fun lay => revealLayerValues index lay (parts lay).2).run
                      layersCache) layersState revealedState layersRemaining revealedRemaining
                        (revealed, revealedCache) hrevealed
                  simp [LazyRevealProbe.runRaw] at hfinish
                  rcases hfinish with ⟨rfl, rfl, hsignature, rfl⟩
                  have hfPath : StableCacheAgreesWithFn parameter pathCache f :=
                    fun input output hstable hcached => hf input output hstable
                      (hrevealedLE (hlayersLE hcached))
                  have hftsReplay := replay_of_mem_runRaw_ordinaryHashImpl_of_stable f parameter
                    (ftsOpen parameter index leaves (ftsSecret index)) state pathState cache
                      pathCache fuel pathRemaining ftsPath hfPath
                        (queriesStable_ftsOpen f parameter index leaves (ftsSecret index)) hpath
                  have hftsRun := cachedRun_mergedCache_of_stable f parameter table targetState
                    targetCache _ (queriesStable_ftsOpen f parameter index leaves (ftsSecret index))
                      (CachedRun.mono_stableOrdinary
                        (queriesStable_ftsOpen f parameter index leaves (ftsSecret index))
                        ((StableOrdinaryCacheLE.of_le (hlayersLE.trans hrevealedLE)).trans
                          hcacheTarget) hftsReplay.2)
                  rw [hsignature]
                  refine ⟨index, leaves,
                    (fun lay => ((parts lay).1, (revealed lay).1, (revealed lay).2)),
                    hdigest, rfl, hftsReplay.1.symm, rfl, rfl, rfl, hftsRun, ?_, ?_⟩
                  · intro lay
                    obtain ⟨componentState, componentFinalState, componentCache,
                        componentFinalCache, componentFuel, componentRemaining, part, hcomponent,
                        hselected, hcomponentValuesLE, hcomponentEnsuredLE,
                        hcomponentCacheLE⟩ :=
                      maskedSignLayers_component_run parameter ftsSecret index pathState
                        layersState pathCache layersCache pathRemaining layersRemaining layers
                          hlayers lay
                    have hpartsAt := traverseOption_eq_some_apply layers parts hparts lay
                    have hpart : part = some (parts lay) := hselected.symm.trans hpartsAt
                    rw [hpart, maskedSignLayerAt_eq] at hcomponent
                    obtain ⟨revealState, revealFinalState, revealCache, revealFinalCache,
                        revealFuel, revealRemaining, revealValue, hrevealComponent,
                        hrevealSelected, hrevealValuesLE, _, _⟩ :=
                      sequenceFin_component_run_of_done
                        (fun otherLay => revealLayerValues index otherLay (parts otherLay).2)
                        (fun otherLay => ordinaryCacheIncreasing_revealLayerValues index otherLay
                          (parts otherLay).2) layersState finalState layersCache finalCache
                            layersRemaining remaining revealed hrevealed lay
                    have hfComponent : StableCacheAgreesWithFn parameter componentFinalCache f :=
                      fun input output hstable hcached => hf input output hstable
                        (hrevealedLE (hcomponentCacheLE hcached))
                    have htableComponent : ∀ coordinate output,
                        componentFinalState.values coordinate = some output →
                          output = table coordinate :=
                      fun coordinate output hvalue => htable coordinate output
                        (hvaluesLE coordinate output
                          (hcomponentValuesLE coordinate output hvalue))
                    have htableReveal : ∀ coordinate output,
                        revealFinalState.values coordinate = some output →
                          output = table coordinate :=
                      fun coordinate output hvalue => htable coordinate output
                        (hrevealValuesLE coordinate output hvalue)
                    change evalWithAnswerFn f
                      (signLayer
                        (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
                          index lay) =
                        some ((parts lay).1, (revealed lay).1, (revealed lay).2)
                    rw [hrevealSelected]
                    exact maskedSignLayer_and_reveal_eval f parameter root table ftsSecret index lay
                      (parts lay).1 (parts lay).2 componentState componentFinalState componentCache
                        componentFinalCache componentFuel componentRemaining revealState
                          revealFinalState revealCache revealFinalCache revealFuel revealRemaining
                            revealValue hfComponent htableComponent htableReveal hrealizes hcomponent
                              hrevealComponent
                  · intro lay
                    obtain ⟨componentState, componentFinalState, componentCache,
                        componentFinalCache, componentFuel, componentRemaining, part, hcomponent,
                        hselected, hcomponentValuesLE, hcomponentEnsuredLE,
                        hcomponentCacheLE⟩ :=
                      maskedSignLayers_component_run parameter ftsSecret index pathState
                        layersState pathCache layersCache pathRemaining layersRemaining layers
                          hlayers lay
                    have hpartsAt := traverseOption_eq_some_apply layers parts hparts lay
                    have hpart : part = some (parts lay) := hselected.symm.trans hpartsAt
                    rw [hpart, maskedSignLayerAt_eq] at hcomponent
                    have hfComponent : StableCacheAgreesWithFn parameter componentFinalCache f :=
                      fun input output hstable hcached => hf input output hstable
                        (hrevealedLE (hcomponentCacheLE hcached))
                    have htableComponent : ∀ coordinate output,
                        componentFinalState.values coordinate = some output →
                          output = table coordinate :=
                      fun coordinate output hvalue => htable coordinate output
                        (hvaluesLE coordinate output (hcomponentValuesLE coordinate output hvalue))
                    exact cachedRun_signLayer_of_mem_runRaw_maskedSignLayer f parameter root table
                      ftsSecret index lay componentState componentFinalState componentCache
                        componentFinalCache componentFuel componentRemaining (parts lay).1
                          (parts lay).2 targetState targetCache hfComponent htableComponent hrealizes
                            hcomponent ((hcomponentEnsuredLE.trans hensuredLE).trans
                              hensuredTarget)
                              ((StableOrdinaryCacheLE.of_le
                                (hcomponentCacheLE.trans hrevealedLE)).trans hcacheTarget)

set_option maxRecDepth 10000 in
theorem successfulSignRun_of_mem_runRaw_maskedSign
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (message : Message) (signature : Signature)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (targetState : LazyRevealProbe.State Coordinate) (targetCache : SplitHashCache)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        (some signature, finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((maskedSign parameter root ftsSecret message).run cache)))
    (hensuredTarget : LazyRevealProbe.EnsuredLE finalState targetState)
    (hcacheTarget : StableOrdinaryCacheLE parameter finalCache targetCache) :
    SuccessfulSignRun f (mergedCache parameter table targetState.ensured targetCache)
      (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
        message signature := by
  let secretKey : SecretKey :=
    ⟨parameter, root, tableOtsSecret table, ftsSecret⟩
  let digestSecretKey : SecretKey :=
    ⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩
  unfold maskedSign at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨loopRaw, hloop, hrest⟩ := hresult
  cases loopRaw with
  | stopped hit => simp at hrest
  | done loopState loopRemaining loopResult =>
      rcases loopResult with ⟨selected, loopCache⟩
      simp only at hrest
      cases selected with
      | none => simp [LazyRevealProbe.runRaw] at hrest
      | some selected =>
          obtain ⟨randomness, index, leaves⟩ := selected
          have hcacheLE := ordinaryCacheIncreasing_maskedSignAfterDigest parameter ftsSecret
            randomness index leaves loopState loopCache loopRemaining finalState remaining
              (some signature) finalCache hrest
          have hdigestLoop := successfulDigestLoop_of_mem_runRaw_ordinaryRomImpl f
            digestSecretKey message digestAttemptLimit randomness index leaves state loopState
              cache loopCache fuel loopRemaining finalCache hcacheLE hf hloop
          have hdigest : SuccessfulDigestRun f (ordinaryQueryCache finalCache) secretKey message
              randomness index leaves := by
            simpa only [SuccessfulDigestRun, signAttempt, digestSecretKey, secretKey] using
              hdigestLoop
          have hdigestMerged : SuccessfulDigestRun f
              (mergedCache parameter table targetState.ensured targetCache) secretKey message
                randomness index leaves :=
            ⟨hdigest.1, hdigest.2.1,
              cachedRun_mergedCache_of_stable f parameter table targetState targetCache _
                (queriesStable_signAttempt f secretKey message randomness)
                  (CachedRun.mono_stableOrdinary
                    (queriesStable_signAttempt f secretKey message randomness) hcacheTarget
                      hdigest.2.2)⟩
          exact successfulSignRun_of_mem_runRaw_maskedSignAfterDigest f parameter root table
            ftsSecret message randomness index leaves signature loopState finalState loopCache
              finalCache loopRemaining remaining targetState targetCache hf htable hrealizes (by
                simpa only [secretKey] using hdigestMerged) hrest hensuredTarget hcacheTarget

set_option maxRecDepth 10000 in
theorem successfulSignRuns_signingTraceComputation
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) alpha)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (value : alpha) (signingLog : QueryLog SigningSpec)
    (targetState : LazyRevealProbe.State Coordinate) (targetCache : SplitHashCache)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        ((value, signingLog), finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
          (signingTraceComputation computation)).run cache)))
    (hensuredTarget : LazyRevealProbe.EnsuredLE finalState targetState)
    (hcacheTarget : StableOrdinaryCacheLE parameter finalCache targetCache) :
    ∀ (entry : (request : SignRequest) × SigningSpec.Range request)
      (signature : Signature), entry ∈ signingLog → entry.2 = some signature →
        SuccessfulSignRun f (mergedCache parameter table targetState.ensured targetCache)
          (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
            entry.1 signature := by
  induction computation using OracleComp.inductionOn generalizing signingLog state cache fuel with
  | pure result =>
      simp [signingTraceComputation, LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, hvalue, rfl⟩
      rcases hvalue with ⟨rfl, rfl⟩
      intro entry signature hentry
      simp at hentry
  | query_bind input next ih =>
      rw [signingTraceComputation_query_bind, simulateQ_bind, simulateQ_spec_query,
        StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
      obtain ⟨queryRaw, hquery, hrest⟩ := hresult
      cases queryRaw with
      | stopped hit => simp at hrest
      | done queryState queryRemaining queryResult =>
          rcases queryResult with ⟨output, queryCache⟩
          simp only at hrest
          rw [map_eq_bind_pure_comp, simulateQ_bind, StateT.run_bind,
            LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hrest
          obtain ⟨tailRaw, htail, hfinish⟩ := hrest
          cases tailRaw with
          | stopped hit => simp at hfinish
          | done tailState tailRemaining tailResult =>
              rcases tailResult with ⟨⟨tailValue, tailLog⟩, tailCache⟩
              simp [LazyRevealProbe.runRaw] at hfinish
              rcases hfinish with ⟨rfl, rfl, houtputs, rfl⟩
              rcases houtputs with ⟨rfl, rfl⟩
              have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
                ((simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
                  (signingTraceComputation (next output))).run queryCache)
                    queryState finalState queryRemaining remaining
                      ((value, tailLog), finalCache) htail
              have hensuredLE := LazyRevealProbe.ensuredLE_of_mem_runRaw_done
                ((simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
                  (signingTraceComputation (next output))).run queryCache)
                    queryState finalState queryRemaining remaining
                      ((value, tailLog), finalCache) htail
              have hstableCacheLE : StableOrdinaryCacheLE parameter queryCache finalCache := by
                intro stableInput cached hstable hcached
                exact ((ordinaryEntryPreservingImpl_maskedExpandedAdversaryImpl parameter root
                  ftsSecret stableInput hstable).simulateQ
                    (signingTraceComputation (next output))) queryState queryCache queryRemaining
                      finalState remaining (value, tailLog) finalCache cached hcached htail
              have htableQuery : ∀ coordinate cached,
                  queryState.values coordinate = some cached → cached = table coordinate :=
                fun coordinate cached hcached =>
                  htable coordinate cached (hvaluesLE coordinate cached hcached)
              have hfQuery : StableCacheAgreesWithFn parameter queryCache f :=
                StableCacheAgreesWithFn.of_run
                  (fun stableInput hstable =>
                    (ordinaryEntryPreservingImpl_maskedExpandedAdversaryImpl parameter root
                      ftsSecret stableInput hstable).simulateQ
                        (signingTraceComputation (next output)))
                  queryState finalState queryCache finalCache queryRemaining remaining
                    (value, tailLog) hf htail
              intro entry signature hentry hsignature
              simp only [List.mem_append] at hentry
              rcases hentry with hfragment | htailEntry
              · cases input with
                | inl oracleQuery => simp [signingLogFragment] at hfragment
                | inr message =>
                    have hentryEq : entry = ⟨message, output⟩ := by
                      simpa [signingLogFragment] using hfragment
                    subst entry
                    change LazyRevealProbe.RawResult.done queryState queryRemaining
                        (output, queryCache) ∈ support
                      (LazyRevealProbe.runRaw state fuel
                        ((maskedSign parameter root ftsSecret message).run cache)) at hquery
                    change output = some signature at hsignature
                    subst output
                    exact successfulSignRun_of_mem_runRaw_maskedSign f parameter root table
                      ftsSecret message signature state queryState cache queryCache fuel
                        queryRemaining targetState targetCache hfQuery htableQuery hrealizes hquery
                          (hensuredLE.trans hensuredTarget)
                            (hstableCacheLE.trans hcacheTarget)
              · exact ih output queryState queryCache queryRemaining tailLog htail entry signature
                  htailEntry hsignature

set_option maxRecDepth 10000 in
theorem successfulSignRuns_retainedGameRestComputation
    (adversary : Adversary) (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (forgery : Forgery) (signingLog : QueryLog SigningSpec) (verified : Bool)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        (((forgery, signingLog), verified), finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
          (retainedGameRestComputation adversary ⟨root, parameter⟩)).run cache))) :
    ∀ (entry : (request : SignRequest) × SigningSpec.Range request)
      (signature : Signature), entry ∈ signingLog → entry.2 = some signature →
        SuccessfulSignRun f (mergedCache parameter table finalState.ensured finalCache)
          (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
            entry.1 signature := by
  rw [simulateQ_maskedExpanded_retainedGameRestComputation, StateT.run_bind,
    LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨prefixRaw, hprefix, hrest⟩ := hresult
  cases prefixRaw with
  | stopped hit => simp at hrest
  | done prefixState prefixRemaining prefixResult =>
      rcases prefixResult with ⟨⟨prefixForgery, prefixLog⟩, prefixCache⟩
      simp only at hrest
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hrest
      obtain ⟨verifyRaw, hverify, hfinish⟩ := hrest
      cases verifyRaw with
      | stopped hit => simp at hfinish
      | done verifyState verifyRemaining verifyResult =>
          rcases verifyResult with ⟨prefixVerified, verifyCache⟩
          simp [LazyRevealProbe.runRaw] at hfinish
          rcases hfinish with ⟨rfl, rfl, houtputs, rfl⟩
          rcases houtputs with ⟨hprefixOutput, rfl⟩
          rcases hprefixOutput with ⟨rfl, rfl⟩
          have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
            ((simulateQ (probingRomImpl parameter)
              (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)).run
                prefixCache) prefixState finalState prefixRemaining remaining
                  (verified, finalCache) hverify
          have hensuredLE := LazyRevealProbe.ensuredLE_of_mem_runRaw_done
            ((simulateQ (probingRomImpl parameter)
              (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)).run
                prefixCache) prefixState finalState prefixRemaining remaining
                  (verified, finalCache) hverify
          have hstableCacheLE : StableOrdinaryCacheLE parameter prefixCache finalCache := by
            intro input output hstable hcached
            exact ((ordinaryEntryPreservingImpl_probingRomImpl parameter input hstable).simulateQ
              (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)) prefixState
                prefixCache prefixRemaining finalState remaining verified finalCache output hcached
                  hverify
          have htablePrefix : ∀ coordinate output,
              prefixState.values coordinate = some output → output = table coordinate :=
            fun coordinate output hcached =>
              htable coordinate output (hvaluesLE coordinate output hcached)
          have hfPrefix : StableCacheAgreesWithFn parameter prefixCache f :=
            StableCacheAgreesWithFn.of_run
              (fun input hstable =>
                (ordinaryEntryPreservingImpl_probingRomImpl parameter input hstable).simulateQ
                  (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature))
              prefixState finalState prefixCache finalCache prefixRemaining remaining verified hf
                hverify
          exact successfulSignRuns_signingTraceComputation f parameter root table ftsSecret
            (adversary.main ⟨root, parameter⟩) state prefixState cache prefixCache fuel
              prefixRemaining forgery signingLog finalState finalCache hfPrefix htablePrefix
                hrealizes hprefix hensuredLE hstableCacheLE

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
theorem successfulSignRuns_maskedRetainedGameAfterFtsSecrets
    (adversary : Adversary) (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel remaining : Nat) (finalState : LazyRevealProbe.State Coordinate)
    (finalCache : SplitHashCache) (root : Digest) (forgery : Forgery)
    (signingLog : QueryLog SigningSpec) (verified : Bool)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        ((root, ((forgery, signingLog), verified)), finalCache) ∈ support
      (LazyRevealProbe.runRaw (LazyRevealProbe.State.empty :
          LazyRevealProbe.State Coordinate) fuel
        ((maskedRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run
          emptySplitHashCache))) :
    ∀ (entry : (request : SignRequest) × SigningSpec.Range request)
      (signature : Signature), entry ∈ signingLog → entry.2 = some signature →
        SuccessfulSignRun f (mergedCache parameter table finalState.ensured finalCache)
          (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
            entry.1 signature := by
  unfold maskedRetainedGameAfterFtsSecrets at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨rootRaw, hroot, hafterRoot⟩ := hresult
  cases rootRaw with
  | stopped hit => simp at hafterRoot
  | done rootState rootRemaining rootResult =>
      rcases rootResult with ⟨sampledRoot, rootCache⟩
      simp only at hafterRoot
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hafterRoot
      obtain ⟨publishRaw, hpublish, hafterPublish⟩ := hafterRoot
      cases publishRaw with
      | stopped hit => simp at hafterPublish
      | done publishState publishRemaining publishResult =>
          rcases publishResult with ⟨publishedUnit, publishCache⟩
          simp only at hafterPublish
          rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hafterPublish
          obtain ⟨restRaw, hrest, hfinish⟩ := hafterPublish
          cases restRaw with
          | stopped hit => simp at hfinish
          | done restState restRemaining restResult =>
              rcases restResult with ⟨⟨prefixForgery, prefixLog⟩, restCache⟩
              simp only at hfinish
              rw [StateT.run_bind, LazyRevealProbe.runRaw_bind,
                mem_support_bind_iff] at hfinish
              obtain ⟨verifyRaw, hverify, hreturn⟩ := hfinish
              cases verifyRaw with
              | stopped hit => simp at hreturn
              | done verifyState verifyRemaining verifyResult =>
                rcases verifyResult with ⟨prefixVerified, verifyCache⟩
                simp [LazyRevealProbe.runRaw] at hreturn
                rcases hreturn with ⟨rfl, rfl, houtput, rfl⟩
                rcases houtput with ⟨hrootEq, hrestEq, rfl⟩
                rcases hrestEq with ⟨rfl, rfl⟩
                have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
                  ((simulateQ (verifierRomImpl parameter)
                    (scheme.verify ⟨sampledRoot, parameter⟩ forgery.message
                      forgery.signature)).run restCache)
                    restState finalState restRemaining remaining (verified, finalCache) hverify
                have hensuredLE := LazyRevealProbe.ensuredLE_of_mem_runRaw_done
                  ((simulateQ (verifierRomImpl parameter)
                    (scheme.verify ⟨sampledRoot, parameter⟩ forgery.message
                      forgery.signature)).run restCache)
                    restState finalState restRemaining remaining (verified, finalCache) hverify
                have hstableCacheLE : StableOrdinaryCacheLE parameter restCache finalCache := by
                  intro input output _ hcached
                  exact (ordinaryEntryPreservingImpl_verifierRomImpl parameter input).simulateQ
                    (scheme.verify ⟨sampledRoot, parameter⟩ forgery.message
                      forgery.signature) restState restCache restRemaining finalState remaining
                        verified finalCache output hcached hverify
                have htableRest : ∀ coordinate output,
                    restState.values coordinate = some output → output = table coordinate :=
                  fun coordinate output hcached =>
                    htable coordinate output (hvaluesLE coordinate output hcached)
                have hfRest : StableCacheAgreesWithFn parameter restCache f :=
                  StableCacheAgreesWithFn.of_run
                    (fun input _ =>
                      (ordinaryEntryPreservingImpl_verifierRomImpl parameter input).simulateQ
                        (scheme.verify ⟨sampledRoot, parameter⟩ forgery.message
                          forgery.signature))
                    restState finalState restCache finalCache restRemaining remaining verified hf
                      hverify
                have hruns := successfulSignRuns_signingTraceComputation f parameter sampledRoot
                  table ftsSecret (adversary.main ⟨sampledRoot, parameter⟩) publishState restState
                    publishCache restCache publishRemaining restRemaining forgery signingLog
                      finalState finalCache hfRest htableRest hrealizes hrest hensuredLE
                        hstableCacheLE
                simpa only [hrootEq] using hruns

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
theorem chainInvariant_maskedRetainedGameAfterFtsSecrets_mergedCache
    (adversary : Adversary) (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel remaining : Nat) (finalState : LazyRevealProbe.State Coordinate)
    (finalCache : SplitHashCache) (root : Digest) (forgery : Forgery)
    (signingLog : QueryLog SigningSpec) (verified : Bool)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        ((root, ((forgery, signingLog), verified)), finalCache) ∈ support
      (LazyRevealProbe.runRaw (LazyRevealProbe.State.empty :
          LazyRevealProbe.State Coordinate) fuel
        ((maskedRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run
          emptySplitHashCache))) :
    ∃ verifierState verifierFuel verifierCache,
      ChainInvariant parameter
        (CoveredChainCoordinate f
          (mergedCache parameter table finalState.ensured finalCache)
          (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) signingLog)
        verifierState verifierCache ∧
      LazyRevealProbe.RawResult.done finalState remaining (verified, finalCache) ∈ support
        (LazyRevealProbe.runRaw verifierState verifierFuel
          ((simulateQ (verifierRomImpl parameter)
            (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)).run
              verifierCache)) := by
  exact chainInvariant_maskedRetainedGameAfterFtsSecrets adversary f parameter table ftsSecret
    (mergedCache parameter table finalState.ensured finalCache) fuel remaining finalState
      finalCache root forgery signingLog verified
        (successfulSignRuns_maskedRetainedGameAfterFtsSecrets adversary f parameter table
          ftsSecret fuel remaining finalState finalCache root forgery signingLog verified hf
            htable hrealizes hresult) hf htable hrealizes hresult

theorem revealPositionValues_makes_values
    (table : Coordinate → HashOutput) (positions : List Position)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (values : List Digest)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (values, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((revealPositionValues positions).run cache))) :
    ∀ position, position ∈ positions →
      finalState.values (.position position) = some (table (.position position)) := by
  induction positions generalizing state cache fuel values with
  | nil => simp
  | cons position positions ih =>
      rw [revealPositionValues, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨headRaw, hhead, hrest⟩ := hresult
      cases headRaw with
      | stopped hit => simp at hrest
      | done headState headRemaining headResult =>
          rcases headResult with ⟨headValue, headCache⟩
          simp only at hrest
          rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hrest
          obtain ⟨tailRaw, htail, hfinish⟩ := hrest
          cases tailRaw with
          | stopped hit => simp at hfinish
          | done tailState tailRemaining tailResult =>
              rcases tailResult with ⟨tailValues, tailCache⟩
              have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
                ((revealPositionValues positions).run headCache)
                  headState tailState headRemaining tailRemaining (tailValues, tailCache) htail
              simp [LazyRevealProbe.runRaw] at hfinish
              rcases hfinish with ⟨hstate, hfuel, hvalues, hcache⟩
              subst finalState
              subst remaining
              subst values
              subst finalCache
              intro other hmem
              simp only [List.mem_cons] at hmem
              rcases hmem with heq | hmem
              · subst other
                obtain ⟨output, _, hvalue⟩ := mem_runRaw_revealCoordinate_value
                  (.position position) state headState cache headCache fuel headRemaining headValue
                    (by simpa [revealPosition] using hhead)
                rw [hvaluesLE _ _ hvalue, htable _ output (hvaluesLE _ _ hvalue)]
              · exact ih headState headCache headRemaining tailValues htail other hmem

theorem revealTableInputChildren_makes_available
    (table : Coordinate → HashOutput) (position : Position)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : Unit)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((revealTableInputChildren (.position position)).run cache))) :
    TableInputAvailable table finalState (.position position) := by
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      by_cases hzero : step.val = 0
      · simp only [revealTableInputChildren, hzero, ↓reduceIte] at hresult
        rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
        obtain ⟨raw, hreveal, hfinish⟩ := hresult
        cases raw with
        | stopped hit => simp at hfinish
        | done revealState revealRemaining revealResult =>
            rcases revealResult with ⟨revealed, revealCache⟩
            simp [LazyRevealProbe.runRaw] at hfinish
            rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
            obtain ⟨output, _, hvalue⟩ := mem_runRaw_revealCoordinate_value
              (.chainStart lay tree leafIdx chainIdx) state finalState cache finalCache fuel
                remaining revealed (by simpa [revealChainStart] using hreveal)
            simp only [TableInputAvailable, hzero, ↓reduceIte]
            rw [hvalue, htable _ output hvalue]
      · simp only [revealTableInputChildren, hzero, ↓reduceIte] at hresult
        rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
        obtain ⟨raw, hvalues, hfinish⟩ := hresult
        cases raw with
        | stopped hit => simp at hfinish
        | done valuesState valuesRemaining valuesResult =>
            rcases valuesResult with ⟨values, valuesCache⟩
            simp [LazyRevealProbe.runRaw] at hfinish
            rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
            simpa only [TableInputAvailable, hzero, ↓reduceIte] using
              revealPositionValues_makes_values table
                (Position.chain lay tree leafIdx chainIdx step).children state finalState cache
                  finalCache fuel remaining values htable hvalues
  | leaf lay tree leafIdx =>
      simp only [revealTableInputChildren] at hresult
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
      obtain ⟨raw, hvalues, hfinish⟩ := hresult
      cases raw with
      | stopped hit => simp at hfinish
      | done valuesState valuesRemaining valuesResult =>
          rcases valuesResult with ⟨values, valuesCache⟩
          simp [LazyRevealProbe.runRaw] at hfinish
          rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
          exact revealPositionValues_makes_values table _ state finalState cache finalCache fuel
            remaining values htable hvalues
  | node lay tree level nodeIdx =>
      simp only [revealTableInputChildren] at hresult
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
      obtain ⟨raw, hvalues, hfinish⟩ := hresult
      cases raw with
      | stopped hit => simp at hfinish
      | done valuesState valuesRemaining valuesResult =>
          rcases valuesResult with ⟨values, valuesCache⟩
          simp [LazyRevealProbe.runRaw] at hfinish
          rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
          exact revealPositionValues_makes_values table _ state finalState cache finalCache fuel
            remaining values htable hvalues
  | ftsLeaf index tree leafIdx =>
      simp only [revealTableInputChildren] at hresult
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
      obtain ⟨raw, hvalues, hfinish⟩ := hresult
      cases raw with
      | stopped hit => simp at hfinish
      | done valuesState valuesRemaining valuesResult =>
          rcases valuesResult with ⟨values, valuesCache⟩
          simp [LazyRevealProbe.runRaw] at hfinish
          rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
          exact revealPositionValues_makes_values table _ state finalState cache finalCache fuel
            remaining values htable hvalues
  | ftsNode index tree level nodeIdx =>
      simp only [revealTableInputChildren] at hresult
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
      obtain ⟨raw, hvalues, hfinish⟩ := hresult
      cases raw with
      | stopped hit => simp at hfinish
      | done valuesState valuesRemaining valuesResult =>
          rcases valuesResult with ⟨values, valuesCache⟩
          simp [LazyRevealProbe.runRaw] at hfinish
          rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
          exact revealPositionValues_makes_values table _ state finalState cache finalCache fuel
            remaining values htable hvalues
  | ftsRoots index =>
      simp only [revealTableInputChildren] at hresult
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
      obtain ⟨raw, hvalues, hfinish⟩ := hresult
      cases raw with
      | stopped hit => simp at hfinish
      | done valuesState valuesRemaining valuesResult =>
          rcases valuesResult with ⟨values, valuesCache⟩
          simp [LazyRevealProbe.runRaw] at hfinish
          rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
          exact revealPositionValues_makes_values table _ state finalState cache finalCache fuel
            remaining values htable hvalues

theorem resolveKnownInput_returns_table_of_available
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (coordinate : Coordinate) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : HashOutput)
    (havailable : TableInputAvailable table state coordinate)
    (htable : ∀ other cached, finalState.values other = some cached →
      cached = table other)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((resolveKnownInput parameter coordinate
          (tableInput parameter table coordinate)).run cache))) :
    output = table coordinate ∧
      finalCache (.ordinary (tableInput parameter table coordinate)) = some output := by
  have hcached := returnsCachedOrdinary_resolveKnownInput parameter coordinate
    (tableInput parameter table coordinate) state cache fuel finalState remaining output
      finalCache hresult
  unfold resolveKnownInput at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind,
    runRaw_peekTableInput_of_available parameter table state cache fuel coordinate havailable]
    at hresult
  simp only [pure_bind, ↓reduceIte] at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨revealRaw, hreveal, hrest⟩ := hresult
  cases revealRaw with
  | stopped hit => simp at hrest
  | done revealState revealRemaining revealResult =>
      rcases revealResult with ⟨revealed, revealCache⟩
      have hrevealed := mem_runRaw_revealCoordinateOutput_value coordinate state revealState
        cache revealCache fuel revealRemaining revealed hreveal
      have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
        (((publishCoordinate coordinate >>= fun _ => do
          modify fun workingCache : SplitHashCache =>
            Function.update workingCache
              (.ordinary (tableInput parameter table coordinate)) (some revealed)
          pure revealed).run revealCache))
        revealState finalState revealRemaining remaining (output, finalCache) hrest
      have hfinalValue := hvaluesLE coordinate revealed hrevealed.1
      have hrevealedTable := htable coordinate revealed hfinalValue
      have houtput : output = revealed := by
        simp [publishCoordinate, LazyRevealProbe.publishQuery,
          StateT.run_modify, LazyRevealProbe.runRaw] at hrest
        exact congrArg Prod.fst (LazyRevealProbe.RawResult.done.inj hrest).2.2
      exact ⟨houtput.trans hrevealedTable, hcached⟩

theorem resolveVerifierInput_returns_table_of_uncached
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (position : Position) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : HashOutput)
    (huncached : cache (.ordinary
      (tableInput parameter table (.position position))) = none)
    (htable : ∀ coordinate cached, finalState.values coordinate = some cached →
      cached = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((resolveVerifierInput parameter (.position position)
          (tableInput parameter table (.position position))).run cache))) :
    output = table (.position position) ∧
      finalCache (.ordinary (tableInput parameter table (.position position))) = some output := by
  unfold resolveVerifierInput at hresult
  simp [StateT.run_get, huncached] at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨revealRaw, hreveal, hresolve⟩ := hresult
  cases revealRaw with
  | stopped hit => simp at hresolve
  | done revealState revealRemaining revealResult =>
      rcases revealResult with ⟨revealed, revealCache⟩
      have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
        ((resolveKnownInput parameter (.position position)
          (tableInput parameter table (.position position))).run revealCache)
          revealState finalState revealRemaining remaining (output, finalCache) hresolve
      have htableReveal : ∀ coordinate cached,
          revealState.values coordinate = some cached → cached = table coordinate :=
        fun coordinate cached hcached =>
          htable coordinate cached (hvaluesLE coordinate cached hcached)
      have havailable := revealTableInputChildren_makes_available table position state revealState
        cache revealCache fuel revealRemaining revealed htableReveal hreveal
      exact resolveKnownInput_returns_table_of_available parameter table (.position position)
        revealState finalState revealCache finalCache revealRemaining remaining output havailable
          htable hresolve

theorem resolveVerifierInput_makes_available_of_uncached
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (position : Position) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : HashOutput)
    (huncached : cache (.ordinary
      (tableInput parameter table (.position position))) = none)
    (htable : ∀ coordinate cached, finalState.values coordinate = some cached →
      cached = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((resolveVerifierInput parameter (.position position)
          (tableInput parameter table (.position position))).run cache))) :
    TableInputAvailable table finalState (.position position) := by
  unfold resolveVerifierInput at hresult
  simp [StateT.run_get, huncached] at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨revealRaw, hreveal, hresolve⟩ := hresult
  cases revealRaw with
  | stopped hit => simp at hresolve
  | done revealState revealRemaining revealResult =>
      rcases revealResult with ⟨revealed, revealCache⟩
      have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
        ((resolveKnownInput parameter (.position position)
          (tableInput parameter table (.position position))).run revealCache)
          revealState finalState revealRemaining remaining (output, finalCache) hresolve
      have htableReveal : ∀ coordinate cached,
          revealState.values coordinate = some cached → cached = table coordinate :=
        fun coordinate cached hcached =>
          htable coordinate cached (hvaluesLE coordinate cached hcached)
      exact (revealTableInputChildren_makes_available table position state revealState cache
        revealCache fuel revealRemaining revealed htableReveal hreveal).monoValues hvaluesLE

theorem resolveVerifierInput_makes_available_of_uncached_input
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (position : Position) (input : HashInput)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : HashOutput)
    (huncached : cache (.ordinary input) = none)
    (htable : ∀ coordinate cached, finalState.values coordinate = some cached →
      cached = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((resolveVerifierInput parameter (.position position) input).run cache))) :
    TableInputAvailable table finalState (.position position) := by
  unfold resolveVerifierInput at hresult
  simp [StateT.run_get, huncached] at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨revealRaw, hreveal, hresolve⟩ := hresult
  cases revealRaw with
  | stopped hit => simp at hresolve
  | done revealState revealRemaining revealResult =>
      rcases revealResult with ⟨revealed, revealCache⟩
      have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
        ((resolveKnownInput parameter (.position position) input).run revealCache)
          revealState finalState revealRemaining remaining (output, finalCache) hresolve
      have htableReveal : ∀ coordinate cached,
          revealState.values coordinate = some cached → cached = table coordinate :=
        fun coordinate cached hcached =>
          htable coordinate cached (hvaluesLE coordinate cached hcached)
      exact (revealTableInputChildren_makes_available table position state revealState cache
        revealCache fuel revealRemaining revealed htableReveal hreveal).monoValues hvaluesLE

theorem Probe.outputCoordinate_eq_position_of_matchesInput
    (parameter : PublicParameter) (probe : Probe) (input : HashInput)
    (position : Position) (hmatches : probe.MatchesInput parameter input)
    (hposition : AtPosition parameter input position) :
    probe.outputCoordinate = .position position := by
  have hat : ∃ outputPosition,
      probe.outputCoordinate = .position outputPosition ∧
        AtPosition parameter input outputPosition := by
    rcases probe with ⟨coordinate, candidate⟩
    cases coordinate with
    | chainStart lay tree leafIdx chainIdx =>
        obtain ⟨step, hzero, hinput⟩ := hmatches
        let first : ChainStep := ⟨0, by norm_num [chainLength, winternitzBits]⟩
        have hstep : step = first := Fin.ext hzero
        subst step
        exact ⟨.chain lay tree leafIdx chainIdx first, rfl,
          ⟨digestBytes candidate, hinput⟩⟩
    | position source =>
        cases source with
        | chain lay tree leafIdx chainIdx step =>
            simp only [Probe.MatchesInput] at hmatches
            by_cases hnext : step.val + 1 < chainLength - 1
            · rw [dif_pos hnext] at hmatches
              obtain ⟨nextStep, hnextValue, hinput⟩ := hmatches
              have hstep : nextStep = ⟨step.val + 1, hnext⟩ := Fin.ext hnextValue
              subst nextStep
              exact ⟨.chain lay tree leafIdx chainIdx ⟨step.val + 1, hnext⟩,
                by simp [Probe.outputCoordinate, hnext], ⟨digestBytes candidate, hinput⟩⟩
            · rw [dif_neg hnext] at hmatches
              obtain ⟨_, payload, hinput, _⟩ := hmatches
              exact ⟨.leaf lay tree leafIdx,
                by simp [Probe.outputCoordinate, hnext], ⟨payload, hinput⟩⟩
        | leaf | node | ftsLeaf | ftsNode | ftsRoots =>
            simp [Probe.MatchesInput] at hmatches
  obtain ⟨outputPosition, houtput, hatOutput⟩ := hat
  rw [houtput]
  exact congrArg Coordinate.position (atPosition_unique parameter hatOutput hposition)

theorem Probe.outputCoordinate_eq_position_of_matchesInput'
    (probe : Probe) (parameter : PublicParameter) (input : HashInput)
    (hmatches : probe.MatchesInput parameter input) :
    ∃ position : Position, probe.outputCoordinate = .position position := by
  rcases probe with ⟨coordinate, candidate⟩
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      exact ⟨.chain lay tree leafIdx chainIdx
        ⟨0, by norm_num [chainLength, winternitzBits]⟩, rfl⟩
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          by_cases hnext : step.val + 1 < chainLength - 1
          · exact ⟨.chain lay tree leafIdx chainIdx ⟨step.val + 1, hnext⟩,
              by simp [Probe.outputCoordinate, hnext]⟩
          · exact ⟨.leaf lay tree leafIdx, by simp [Probe.outputCoordinate, hnext]⟩
      | leaf | node | ftsLeaf | ftsNode | ftsRoots =>
          simp [Probe.MatchesInput] at hmatches

theorem Probe.value_eq_table_of_output_available
    (table : Coordinate → HashOutput) (probe : Probe) (parameter : PublicParameter)
    (input : HashInput) (state : LazyRevealProbe.State Coordinate)
    (hmatches : probe.MatchesInput parameter input)
    (havailable : TableInputAvailable table state probe.outputCoordinate) :
    state.values probe.coordinate = some (table probe.coordinate) := by
  rcases probe with ⟨coordinate, candidate⟩
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      simp [Probe.outputCoordinate, TableInputAvailable] at havailable
      exact havailable
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          simp only [Probe.outputCoordinate] at havailable ⊢
          by_cases hnext : step.val + 1 < chainLength - 1
          · rw [dif_pos hnext] at havailable
            have hnonzero : (⟨step.val + 1, hnext⟩ : ChainStep).val ≠ 0 := by
              change step.val + 1 ≠ 0
              omega
            simp only [TableInputAvailable, if_neg hnonzero] at havailable
            apply havailable (.chain lay tree leafIdx chainIdx step)
            rw [Position.mem_children_iff, Position.parentOf, dif_pos hnext]
          · rw [dif_neg hnext] at havailable
            simp only [TableInputAvailable] at havailable
            apply havailable (.chain lay tree leafIdx chainIdx step)
            rw [Position.mem_children_iff, Position.parentOf, dif_neg hnext]
      | leaf | node | ftsLeaf | ftsNode | ftsRoots =>
          simp [Probe.MatchesInput] at hmatches

theorem verifierHashQuery_not_done_of_fresh_correct_probe
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (allowed : Coordinate → Prop) (probe : Probe) (input : HashInput)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : HashOutput)
    (hvalid : ChainState.ValidFor allowed state)
    (hmatches : probe.MatchesInput parameter input)
    (hcandidate : probe.candidate = truncateHash (table probe.coordinate))
    (hnotAllowed : ¬allowed probe.coordinate)
    (huncached : cache (.ordinary input) = none)
    (htable : ∀ coordinate cached, finalState.values coordinate = some cached →
      cached = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((verifierHashQuery parameter input).run cache))) : False := by
  have hchain := probe.isChainCoordinate_of_matchesInput hmatches
  have hvalue := hvalid.value_eq_none_of_not_allowed hchain hnotAllowed
  have hnotRevealed := hvalid.not_revealed_of_not_allowed hchain hnotAllowed
  cases hdecode : decodeProbe? parameter input with
  | none => exact ((decodeProbe?_eq_none_iff parameter input).1 hdecode probe hmatches).elim
  | some candidate =>
      have hcandidateMatches := (decodeProbe?_eq_some_iff parameter input candidate).1 hdecode
      have heq := Probe.matchesInput_unique parameter input hcandidateMatches hmatches
      subst candidate
      unfold verifierHashQuery at hresult
      rw [hdecode, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨probeRaw, hprobe, hresolve⟩ := hresult
      cases probeRaw with
      | stopped hit => simp at hresolve
      | done probeState probeRemaining probeResult =>
          rcases probeResult with ⟨probed, probeCache⟩
          change LazyRevealProbe.RawResult.done probeState probeRemaining
              (probed, probeCache) ∈ support
            (LazyRevealProbe.runRaw state fuel
              (LazyRevealProbe.probeQuery probe.coordinate probe.candidate >>= fun result =>
                pure (result, cache))) at hprobe
          rw [LazyRevealProbe.probeQuery,
            LazyRevealProbe.runRaw_probe_query_bind] at hprobe
          cases fuel with
          | zero => simp at hprobe
          | succ remainingFuel =>
              simp only at hprobe
              rw [if_neg hnotRevealed] at hprobe
              simp [LazyRevealProbe.runRaw] at hprobe
              rcases hprobe with ⟨rfl, rfl, rfl, rfl⟩
              obtain ⟨position, houtputPosition⟩ :=
                probe.outputCoordinate_eq_position_of_matchesInput' parameter input hmatches
              rw [houtputPosition] at hresolve
              have havailable := resolveVerifierInput_makes_available_of_uncached_input parameter
                table position input (state.addPending probe.coordinate probe.candidate) finalState
                  cache finalCache probeRemaining remaining output huncached htable hresolve
              rw [← houtputPosition] at havailable
              have hsourceValue := probe.value_eq_table_of_output_available table parameter input
                finalState hmatches havailable
              have hhit : (state.addPending probe.coordinate probe.candidate).hitAt
                  probe.coordinate (table probe.coordinate) := by
                rw [LazyRevealProbe.State.hitAt, ← hcandidate]
                exact LazyRevealProbe.State.pendingAt_addPending_self state probe.coordinate
                  probe.candidate
              have hpersist := LazyRevealProbe.pendingHit_preserved_of_mem_runRaw_done
                ((resolveVerifierInput parameter probe.outputCoordinate input).run cache)
                  probe.coordinate (table probe.coordinate)
                    (state.addPending probe.coordinate probe.candidate) finalState probeRemaining
                      remaining (output, finalCache) hvalue hhit (htable probe.coordinate) (by
                        simpa only [houtputPosition] using hresolve)
              rw [hpersist.1] at hsourceValue
              simp at hsourceValue

theorem decodeProbe?_outputCoordinate_eq_position
    (parameter : PublicParameter) (input : HashInput) (probe : Probe)
    (position : Position) (hprobe : decodeProbe? parameter input = some probe)
    (hposition : decodePosition? parameter input = some position) :
    probe.outputCoordinate = .position position := by
  exact probe.outputCoordinate_eq_position_of_matchesInput parameter input position
    ((decodeProbe?_eq_some_iff parameter input probe).1 hprobe)
    ((decodePosition?_eq_some_iff parameter input position).1 hposition)

theorem verifierHashQuery_eq_resolveVerifierInput_of_decodeProbe_none
    (parameter : PublicParameter) (input : HashInput) (position : Position)
    (hprobe : decodeProbe? parameter input = none)
    (hposition : decodePosition? parameter input = some position)
    (hots : IsOtsPosition position) :
    verifierHashQuery parameter input =
      resolveVerifierInput parameter (.position position) input := by
  unfold verifierHashQuery
  rw [hprobe, hposition]
  cases position <;> simp [IsOtsPosition] at hots ⊢

set_option maxRecDepth 10000 in
theorem verifierHashQuery_returns_table_of_uncached
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (position : Position) (hots : IsOtsPosition position)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : HashOutput)
    (huncached : cache (.ordinary
      (tableInput parameter table (.position position))) = none)
    (htable : ∀ coordinate cached, finalState.values coordinate = some cached →
      cached = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((verifierHashQuery parameter
          (tableInput parameter table (.position position))).run cache))) :
    output = table (.position position) ∧
      finalCache (.ordinary (tableInput parameter table (.position position))) = some output := by
  let input := tableInput parameter table (.position position)
  have hposition : decodePosition? parameter input = some position :=
    (decodePosition?_eq_some_iff parameter input position).2 ⟨tablePayload table position, rfl⟩
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      unfold verifierHashQuery at hresult
      rw [hprobe, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨probeRaw, hprobeRun, hrest⟩ := hresult
      cases probeRaw with
      | stopped hit => simp at hrest
      | done probeState probeRemaining probeResult =>
          rcases probeResult with ⟨probed, probeCache⟩
          have hprobeCache := splitCachePreserving_probe candidate state cache fuel probeState
            probeRemaining probed probeCache hprobeRun
          subst probeCache
          have houtputCoordinate := decodeProbe?_outputCoordinate_eq_position parameter input
            candidate position hprobe hposition
          rw [houtputCoordinate] at hrest
          exact resolveVerifierInput_returns_table_of_uncached parameter table position probeState
            finalState cache finalCache probeRemaining remaining output huncached htable hrest
  | none =>
      rw [verifierHashQuery_eq_resolveVerifierInput_of_decodeProbe_none parameter input position
        hprobe hposition hots] at hresult
      exact resolveVerifierInput_returns_table_of_uncached parameter table position state finalState
        cache finalCache fuel remaining output huncached htable hresult

theorem verifierHashQuery_returns_table
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (position : Position) (hots : IsOtsPosition position)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : HashOutput)
    (hf : (ordinaryQueryCache finalCache).AgreesWithFn f)
    (htable : ∀ coordinate cached, finalState.values coordinate = some cached →
      cached = table coordinate)
    (hrealizes : f (tableInput parameter table (.position position)) =
      table (.position position))
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((verifierHashQuery parameter
          (tableInput parameter table (.position position))).run cache))) :
    output = table (.position position) ∧
      finalCache (.ordinary (tableInput parameter table (.position position))) = some output := by
  cases hcached : cache (.ordinary
      (tableInput parameter table (.position position))) with
  | none =>
      exact verifierHashQuery_returns_table_of_uncached parameter table position hots state
        finalState cache finalCache fuel remaining output hcached htable hresult
  | some cached =>
      have hreturns := returnsCachedOrdinary_verifierHashQuery parameter
        (tableInput parameter table (.position position)) state cache fuel finalState remaining
          output finalCache hresult
      have hanswer := hf hreturns
      exact ⟨hanswer.symm.trans hrealizes, hreturns⟩

theorem probingHashQuery_eq_resolveKnownInput_of_decodeProbe_none
    (parameter : PublicParameter) (input : HashInput) (position : Position)
    (hprobe : decodeProbe? parameter input = none)
    (hposition : decodePosition? parameter input = some position)
    (hots : IsOtsPosition position) :
    probingHashQuery parameter input = resolveKnownInput parameter (.position position) input := by
  unfold probingHashQuery
  rw [hprobe, hposition]
  cases position <;> simp [IsOtsPosition] at hots ⊢

set_option maxRecDepth 10000 in
theorem probingHashQuery_returns_table_of_available
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (position : Position) (hots : IsOtsPosition position)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : HashOutput)
    (havailable : TableInputAvailable table state (.position position))
    (htable : ∀ other cached, finalState.values other = some cached →
      cached = table other)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((probingHashQuery parameter
          (tableInput parameter table (.position position))).run cache))) :
    output = table (.position position) ∧
      finalCache (.ordinary (tableInput parameter table (.position position))) = some output := by
  let input := tableInput parameter table (.position position)
  have hposition : decodePosition? parameter input = some position :=
    (decodePosition?_eq_some_iff parameter input position).2 ⟨tablePayload table position, rfl⟩
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      unfold probingHashQuery at hresult
      rw [hprobe, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨probeRaw, hprobeRun, hrest⟩ := hresult
      cases probeRaw with
      | stopped hit => simp at hrest
      | done probeState probeRemaining probeResult =>
          rcases probeResult with ⟨probed, probeCache⟩
          have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
            ((probe candidate).run cache) state probeState fuel probeRemaining
              (probed, probeCache) hprobeRun
          have havailableProbe := havailable.monoValues hvaluesLE
          have houtputCoordinate := decodeProbe?_outputCoordinate_eq_position parameter input
            candidate position hprobe hposition
          rw [houtputCoordinate] at hrest
          exact resolveKnownInput_returns_table_of_available parameter table (.position position)
            probeState finalState probeCache finalCache probeRemaining remaining output
              havailableProbe htable hrest
  | none =>
      rw [probingHashQuery_eq_resolveKnownInput_of_decodeProbe_none parameter input position
        hprobe hposition hots] at hresult
      exact resolveKnownInput_returns_table_of_available parameter table (.position position)
        state finalState cache finalCache fuel remaining output havailable htable hresult
theorem simulateQ_probingHashImpl_tweakableHash_eq_ordinaryHashImpl
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput)
    (hinRange : domain.InRange)
    (hchain : ∀ lay tree leafIdx chainIdx step,
      domain ≠ .chain lay tree leafIdx chainIdx step)
    (hleaf : ∀ lay tree leafIdx, domain ≠ .leaf lay tree leafIdx)
    (hnode : ∀ lay tree level nodeIdx, domain ≠ .node lay tree level nodeIdx) :
    simulateQ (probingHashImpl parameter) (tweakableHash parameter domain payload) =
      simulateQ ordinaryHashImpl (tweakableHash parameter domain payload) := by
  unfold tweakableHash oracleHash
  rw [simulateQ_bind, simulateQ_bind]
  simp only [HasQuery.instOfMonadLift_query, simulateQ_spec_query, simulateQ_pure]
  rw [probingHashImpl_eq_ordinaryHashImpl_of_stable parameter _
    (stableOrdinaryInput_tweakableHashInput parameter domain payload hinRange
      hchain hleaf hnode)]

theorem simulateQ_probingHashImpl_messageDigest_eq_ordinaryHashImpl
    (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) :
    simulateQ (probingHashImpl parameter)
        (messageDigest parameter root message randomness) =
      simulateQ ordinaryHashImpl
        (messageDigest parameter root message randomness) := by
  unfold messageDigest oracleHash
  rw [simulateQ_bind, simulateQ_bind]
  simp only [HasQuery.instOfMonadLift_query, simulateQ_spec_query, simulateQ_pure]
  rw [probingHashImpl_eq_ordinaryHashImpl_of_stable parameter _
    (stableOrdinaryInput_tweakableHashInput parameter .message _ (by trivial)
      (by simp) (by simp) (by simp))]

theorem simulateQ_probingHashImpl_ftsLeafHash_eq_ordinaryHashImpl
    (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (leafIdx : FtsLeaf) (secret : Digest) :
    simulateQ (probingHashImpl parameter)
        (ftsLeafHash parameter index tree leafIdx secret) =
      simulateQ ordinaryHashImpl
        (ftsLeafHash parameter index tree leafIdx secret) := by
  unfold ftsLeafHash
  exact simulateQ_probingHashImpl_tweakableHash_eq_ordinaryHashImpl parameter
    (.ftsLeaf index tree leafIdx) (digestBytes secret) (by trivial)
      (by simp) (by simp) (by simp)

theorem simulateQ_probingHashImpl_ftsFold_eq_ordinaryHashImpl
    (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (leafIdx : FtsLeaf) (path : Fin ftsTreeHeight → Digest) :
    ∀ levels value, levels ≤ ftsTreeHeight →
      simulateQ (probingHashImpl parameter)
          (ftsFold parameter index tree leafIdx path levels value) =
        simulateQ ordinaryHashImpl
          (ftsFold parameter index tree leafIdx path levels value)
  | 0, value, _ => by simp [ftsFold]
  | levels + 1, value, hlevels => by
      rw [ftsFold_succ_eq, simulateQ_bind, simulateQ_bind,
        simulateQ_probingHashImpl_ftsFold_eq_ordinaryHashImpl parameter index tree
          leafIdx path levels value (by omega)]
      apply bind_congr
      intro current
      split <;> split <;>
        exact simulateQ_probingHashImpl_tweakableHash_eq_ordinaryHashImpl parameter
          (.ftsNode index tree (levels + 1) (leafIdx.val / 2 ^ (levels + 1))) _
            (by
              show levels + 1 < 2 ^ 32 ∧ leafIdx.val / 2 ^ (levels + 1) < 2 ^ 32
              constructor
              · have hheight : ftsTreeHeight < 2 ^ 32 := by
                  norm_num [ftsTreeHeight]
                omega
              · have hleaf : leafIdx.val < 2 ^ 32 := by
                  exact lt_of_lt_of_le leafIdx.isLt (by norm_num [ftsTreeHeight])
                have hdiv := Nat.div_le_self leafIdx.val (2 ^ (levels + 1))
                omega)
            (by simp) (by simp) (by simp)

theorem simulateQ_probingHashImpl_sequenceFin_eq_ordinaryHashImpl
    (parameter : PublicParameter) {n : Nat}
    (computation : Fin n → OracleComp HashSpec alpha)
    (hcomponent : ∀ position,
      simulateQ (probingHashImpl parameter) (computation position) =
        simulateQ ordinaryHashImpl (computation position)) :
    simulateQ (probingHashImpl parameter) (sequenceFin computation) =
      simulateQ ordinaryHashImpl (sequenceFin computation) := by
  induction n with
  | zero => simp [sequenceFin]
  | succ n ih =>
      rw [sequenceFin, simulateQ_bind, simulateQ_bind, hcomponent 0]
      apply bind_congr
      intro head
      rw [simulateQ_bind, simulateQ_bind]
      have htail := ih (fun position : Fin n => computation position.succ)
        (fun position => hcomponent position.succ)
      rw [htail]
      simp only [simulateQ_pure]

theorem simulateQ_probingHashImpl_ftsRecover_eq_ordinaryHashImpl
    (parameter : PublicParameter) (index : Index)
    (leaves : DigestTree → FtsLeaf) (secrets : FtsTree → Digest)
    (paths : FtsTree → Fin ftsTreeHeight → Digest) :
    simulateQ (probingHashImpl parameter)
        (ftsRecover parameter index leaves secrets paths) =
      simulateQ ordinaryHashImpl
        (ftsRecover parameter index leaves secrets paths) := by
  unfold ftsRecover
  rw [simulateQ_bind, simulateQ_bind]
  have hroots := simulateQ_probingHashImpl_sequenceFin_eq_ordinaryHashImpl parameter
    (fun tree => do
      let leaf := leaves (ftsIndexOf tree)
      let value ← ftsLeafHash parameter index tree leaf (secrets tree)
      ftsFold parameter index tree leaf (paths tree) ftsTreeHeight value)
    (fun tree => by
      rw [simulateQ_bind, simulateQ_bind,
        simulateQ_probingHashImpl_ftsLeafHash_eq_ordinaryHashImpl]
      apply bind_congr
      intro value
      exact simulateQ_probingHashImpl_ftsFold_eq_ordinaryHashImpl parameter index tree
        (leaves (ftsIndexOf tree)) (paths tree) ftsTreeHeight value le_rfl)
  rw [hroots]
  apply bind_congr
  intro roots
  exact simulateQ_probingHashImpl_tweakableHash_eq_ordinaryHashImpl parameter
    (.ftsRoots index) (ftsRootsPayload roots) (by trivial)
      (by simp) (by simp) (by simp)

theorem relTriple_runRaw_splitUniformImpl
    (n : Nat) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache) (fuel : Nat) :
    RelTriple
      (LazyRevealProbe.runRaw state fuel ((splitUniformImpl n).run cache))
      ((liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun output =>
        pure (output, ordinaryQueryCache cache))
      (RawOrdinaryResultRelAt (alpha := Fin (n + 1)) state fuel) := by
  let uniform : ProbComp (Fin (n + 1)) := liftM (unifSpec.query n)
  have hself : RelTriple uniform uniform fun left right => left = right :=
    relTriple_refl uniform
  have hpre : RelTriple uniform uniform fun left right =>
      RawOrdinaryResultRelAt state fuel
        (.done state fuel (left, cache)) (right, ordinaryQueryCache cache) := by
    apply relTriple_post_mono hself
    intro left right heq
    subst right
    simp [RawOrdinaryResultRelAt]
  have hmapped := relTriple_map
    (R := RawOrdinaryResultRelAt (alpha := Fin (n + 1)) state fuel)
    (f := fun output => LazyRevealProbe.RawResult.done state fuel (output, cache))
    (g := fun output => (output, ordinaryQueryCache cache)) hpre
  simpa [uniform, splitUniformImpl, LazyRevealProbe.uniformQuery,
    LazyRevealProbe.runRaw_uniform_query_bind, LazyRevealProbe.runRaw,
    map_eq_bind_pure_comp] using hmapped

set_option maxRecDepth 10000 in
theorem relTriple_runRaw_simulateQ_ordinaryHashImpl
    [Inhabited alpha]
    (computation : OracleComp HashSpec alpha)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) (fuel : Nat) :
    RelTriple
      (LazyRevealProbe.runRaw state fuel
        ((simulateQ ordinaryHashImpl computation).run cache))
      ((simulateQ (randomOracle : QueryImpl HashSpec _) computation).run
        (ordinaryQueryCache cache))
      (RawOrdinaryResultRel (alpha := alpha)) := by
  have hproject :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_of_project_eq_some_exact
      projectRawOrdinary
      (default, ∅)
      (LazyRevealProbe.runRaw state fuel
        ((simulateQ ordinaryHashImpl computation).run cache))
      ((simulateQ (randomOracle : QueryImpl HashSpec _) computation).run
        (ordinaryQueryCache cache))
      (projectRawOrdinary_simulateQ_ordinaryHashImpl computation state cache fuel)
  apply relTriple_post_mono hproject
  intro rawResult ordinaryResult hrelation
  cases rawResult with
  | stopped hit => simp [projectRawOrdinary] at hrelation
  | done finalState remaining valueCache =>
      rcases valueCache with ⟨value, finalCache⟩
      change ordinaryResult = (value, ordinaryQueryCache finalCache)
      exact (Option.some.inj hrelation).symm

set_option maxRecDepth 10000 in
theorem relTriple_runRaw_simulateQ_ordinaryHashImpl_at
    [Inhabited alpha]
    (computation : OracleComp HashSpec alpha)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) (fuel : Nat) :
    RelTriple
      (LazyRevealProbe.runRaw state fuel
        ((simulateQ ordinaryHashImpl computation).run cache))
      ((simulateQ (randomOracle : QueryImpl HashSpec _) computation).run
        (ordinaryQueryCache cache))
      (RawOrdinaryResultRelAt (alpha := alpha) state fuel) := by
  have hbase := relTriple_runRaw_simulateQ_ordinaryHashImpl computation state cache fuel
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun result => match result with
        | .stopped _ => True
        | .done finalState remaining _ => finalState = state ∧ remaining = fuel)
      (by
        intro result hresult
        cases result with
        | stopped hit => trivial
        | done finalState remaining valueCache =>
            rcases valueCache with ⟨value, finalCache⟩
            have hprojection := mem_runRaw_simulateQ_ordinaryHashImpl_projects computation state
              finalState cache finalCache fuel remaining value hresult
            exact ⟨hprojection.1, hprojection.2.1⟩)
  apply relTriple_post_mono hsupported
  intro rawResult ordinaryResult hrelation
  cases rawResult with
  | stopped hit => exact hrelation.1
  | done finalState remaining valueCache =>
      rcases valueCache with ⟨value, finalCache⟩
      exact ⟨hrelation.2.1, hrelation.2.2, hrelation.1⟩

set_option maxRecDepth 10000 in
theorem relTriple_runRaw_simulateQ_ordinaryRomImpl
    [Inhabited alpha]
    (computation : OracleComp OracleWorld alpha)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) (fuel : Nat) :
    RelTriple
      (LazyRevealProbe.runRaw state fuel
        ((simulateQ ordinaryRomImpl computation).run cache))
      ((simulateQ romImpl computation).run (ordinaryQueryCache cache))
      (RawOrdinaryResultRelAt (alpha := alpha) state fuel) := by
  induction computation using OracleComp.inductionOn generalizing state cache fuel with
  | pure value =>
      simp [LazyRevealProbe.runRaw, RawOrdinaryResultRelAt]
  | query_bind query next ih =>
      rw [simulateQ_query_bind, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        simulateQ_query_bind, StateT.run_bind]
      have hquery : RelTriple
          (LazyRevealProbe.runRaw state fuel ((ordinaryRomImpl query).run cache))
          ((romImpl query).run (ordinaryQueryCache cache))
          (RawOrdinaryResultRelAt state fuel) := by
        cases query with
        | inl n =>
            change RelTriple
              (LazyRevealProbe.runRaw state fuel ((splitUniformImpl n).run cache))
              ((unifFwdImpl HashSpec n).run (ordinaryQueryCache cache))
              (RawOrdinaryResultRelAt state fuel)
            rw [show (unifFwdImpl HashSpec n).run (ordinaryQueryCache cache) =
                (fun output => (output, ordinaryQueryCache cache)) <$>
                  (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) by
              simpa using unifFwdImpl.simulateQ_run
                (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
                (ordinaryQueryCache cache)]
            simpa [map_eq_bind_pure_comp] using
              relTriple_runRaw_splitUniformImpl n state cache fuel
        | inr input =>
            simpa [ordinaryRomImpl, romImpl] using
              relTriple_runRaw_simulateQ_ordinaryHashImpl_at
                (liftM (HashSpec.query input)) state cache fuel
      apply relTriple_bind hquery
      intro rawResult ordinaryResult hrelation
      cases rawResult with
      | stopped hit => simp [RawOrdinaryResultRelAt] at hrelation
      | done finalState remaining valueCache =>
          rcases valueCache with ⟨value, finalCache⟩
          rcases hrelation with ⟨rfl, rfl, rfl⟩
          exact ih value finalState finalCache remaining

set_option maxRecDepth 10000 in
theorem evalDist_projectRawOrdinary_simulateQ_ordinaryRomImpl
    [Inhabited alpha]
    (computation : OracleComp OracleWorld alpha)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) (fuel : Nat) :
    𝒟[projectRawOrdinary <$>
        LazyRevealProbe.runRaw state fuel
          ((simulateQ ordinaryRomImpl computation).run cache)] =
      𝒟[some <$>
        (simulateQ romImpl computation).run (ordinaryQueryCache cache)] := by
  refine evalDist_map_eq_of_relTriple (relTriple_post_mono
    (relTriple_runRaw_simulateQ_ordinaryRomImpl computation state cache fuel) ?_)
  intro rawResult ordinaryResult hrelation
  cases rawResult with
  | stopped hit => simp [RawOrdinaryResultRelAt] at hrelation
  | done finalState remaining valueCache =>
      rcases valueCache with ⟨value, finalCache⟩
      rcases hrelation with ⟨_, _, rfl⟩
      rfl

set_option maxRecDepth 10000 in
theorem mem_runRaw_simulateQ_ordinaryRomImpl_projects
    [Inhabited alpha]
    (computation : OracleComp OracleWorld alpha)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : alpha)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((simulateQ ordinaryRomImpl computation).run cache))) :
    finalState = state ∧ remaining = fuel ∧
      (value, ordinaryQueryCache finalCache) ∈ support
        ((simulateQ romImpl computation).run (ordinaryQueryCache cache)) := by
  obtain ⟨ordinaryResult, hordinary, hrelation⟩ :=
    exists_right_mem_support_of_relTriple
      (relTriple_runRaw_simulateQ_ordinaryRomImpl computation state cache fuel) hresult
  exact ⟨hrelation.1, hrelation.2.1, hrelation.2.2 ▸ hordinary⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
