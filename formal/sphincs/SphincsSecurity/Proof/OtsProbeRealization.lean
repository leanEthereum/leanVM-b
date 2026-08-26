import SphincsSecurity.Proof.OtsProbeSimulation

/-!
# Realizing the concrete one-time structure

A completed opaque table determines the one-time secrets and every structural answer. If an answer
function returns the table output at each corresponding table input, the concrete chain and tree
computations recover exactly those table values.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp

set_option maxRecDepth 10000 in
theorem mergedCache_tableInput (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (ensured : Finset Coordinate)
    (cache : SplitHashCache) (position : Position) (hots : IsOtsPosition position) :
    mergedCache parameter table ensured cache
        (tableInput parameter table (.position position)) =
      completedSplitHashCache table ensured cache (.hidden (.position position)) := by
  have hdecode := (decodePosition?_eq_some_iff parameter
    (tableInput parameter table (.position position)) position).2
      ⟨tablePayload table position, rfl⟩
  change mergeDecodedPosition parameter table ensured cache
    (tableInput parameter table (.position position))
      (decodePosition? parameter (tableInput parameter table (.position position))) = _
  rw [hdecode]
  cases position <;> simp [mergeDecodedPosition, IsOtsPosition] at hots ⊢

theorem tableAnswer_tableInput (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (fallback : QueryImpl HashSpec Id)
    (position : Position) (hots : IsOtsPosition position) :
    tableAnswer parameter table fallback
        (tableInput parameter table (.position position)) =
      table (.position position) := by
  have hdecode := (decodePosition?_eq_some_iff parameter
    (tableInput parameter table (.position position)) position).2
      ⟨tablePayload table position, rfl⟩
  change tableAnswerDecoded parameter table fallback
    (tableInput parameter table (.position position))
      (decodePosition? parameter (tableInput parameter table (.position position))) = _
  rw [hdecode]
  cases position <;> simp [tableAnswerDecoded, IsOtsPosition] at hots ⊢

def splitFallback (cache : SplitHashCache) : QueryImpl HashSpec Id :=
  fun input => (cache (.ordinary input)).getD 0

noncomputable def extendTable (state : LazyRevealProbe.State Coordinate)
    (base : Coordinate → HashOutput) : Coordinate → HashOutput :=
  fun coordinate => (state.values coordinate).getD (base coordinate)

def HiddenConsistent (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache) : Prop :=
  ∀ coordinate output, cache (.hidden coordinate) = some output →
    state.values coordinate = some output

theorem hiddenConsistent_empty :
    HiddenConsistent (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      emptySplitHashCache := by
  intro coordinate output houtput
  simp [emptySplitHashCache] at houtput

theorem HiddenConsistent.updateOrdinary
    {state : LazyRevealProbe.State Coordinate} {cache : SplitHashCache}
    (hconsistent : HiddenConsistent state cache) (input : HashInput) (output : HashOutput) :
    HiddenConsistent state (Function.update cache (.ordinary input) (some output)) := by
  intro coordinate hiddenOutput hhidden
  simp [Function.update] at hhidden
  exact hconsistent coordinate hiddenOutput hhidden

theorem HiddenConsistent.ensure
    {state : LazyRevealProbe.State Coordinate} {cache : SplitHashCache}
    (hconsistent : HiddenConsistent state cache) (coordinate : Coordinate) :
    HiddenConsistent (state.ensure coordinate) cache := by
  simpa [HiddenConsistent, LazyRevealProbe.State.ensure] using hconsistent

theorem HiddenConsistent.addPending
    {state : LazyRevealProbe.State Coordinate} {cache : SplitHashCache}
    (hconsistent : HiddenConsistent state cache) (coordinate : Coordinate)
    (candidate : Digest) :
    HiddenConsistent (state.addPending coordinate candidate) cache := by
  simpa [HiddenConsistent, LazyRevealProbe.State.addPending] using hconsistent

theorem HiddenConsistent.install_of_none
    {state : LazyRevealProbe.State Coordinate} {cache : SplitHashCache}
    (hconsistent : HiddenConsistent state cache) (coordinate : Coordinate)
    (output : HashOutput) (hvalue : state.values coordinate = none) :
    HiddenConsistent (state.install coordinate output) cache := by
  intro other hiddenOutput hhidden
  by_cases heq : other = coordinate
  · subst other
    have := hconsistent coordinate hiddenOutput hhidden
    rw [hvalue] at this
    simp at this
  · simp [LazyRevealProbe.State.install, Function.update, heq]
    exact hconsistent other hiddenOutput hhidden

theorem HiddenConsistent.updateHidden_of_value
    {state : LazyRevealProbe.State Coordinate} {cache : SplitHashCache}
    (hconsistent : HiddenConsistent state cache) (coordinate : Coordinate)
    (output : HashOutput) (hvalue : state.values coordinate = some output) :
    HiddenConsistent state (Function.update cache (.hidden coordinate) (some output)) := by
  intro other hiddenOutput hhidden
  by_cases heq : other = coordinate
  · subst other
    simp [Function.update] at hhidden
    rwa [← hhidden]
  · simp [Function.update, heq] at hhidden
    exact hconsistent other hiddenOutput hhidden

theorem HiddenConsistent.updateHidden_install
    {state : LazyRevealProbe.State Coordinate} {cache : SplitHashCache}
    (hconsistent : HiddenConsistent state cache) (coordinate : Coordinate)
    (output : HashOutput) :
    HiddenConsistent (state.install coordinate output)
      (Function.update cache (.hidden coordinate) (some output)) := by
  intro other hiddenOutput hhidden
  by_cases heq : other = coordinate
  · subst other
    simp [Function.update] at hhidden
    simp [LazyRevealProbe.State.install, hhidden]
  · simp [Function.update, heq] at hhidden
    simp [LazyRevealProbe.State.install, Function.update, heq]
    exact hconsistent other hiddenOutput hhidden

theorem completedSplitHashCache_extendTable_consistent
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache)
    (base : Coordinate → HashOutput) (hconsistent : HiddenConsistent state cache) :
    ∀ coordinate output,
      completedSplitHashCache (extendTable state base) state.ensured cache
          (.hidden coordinate) = some output →
        output = extendTable state base coordinate := by
  intro coordinate output houtput
  unfold completedSplitHashCache at houtput
  change (match cache (.hidden coordinate) with
    | some cached => some cached
    | none => if coordinate ∈ state.ensured then
        some (extendTable state base coordinate) else none) = some output at houtput
  cases hcache : cache (.hidden coordinate) with
  | some cached =>
      rw [hcache] at houtput
      have heq : cached = output := Option.some.inj houtput
      subst output
      have hvalue := hconsistent coordinate cached hcache
      simp [extendTable, hvalue]
  | none =>
      rw [hcache] at houtput
      by_cases hmem : coordinate ∈ state.ensured
      · rw [if_pos hmem] at houtput
        exact Option.some.inj houtput |>.symm
      · rw [if_neg hmem] at houtput
        simp at houtput

def PreservesHidden
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha) : Prop :=
  ∀ state cache fuel finalState remaining value finalCache,
    HiddenConsistent state cache →
      LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
        support (LazyRevealProbe.runRaw state fuel (computation.run cache)) →
      HiddenConsistent finalState finalCache

theorem preservesHidden_pure (value : alpha) :
    PreservesHidden (pure value : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha) := by
  intro state cache fuel finalState remaining result finalCache hconsistent hresult
  simp [LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  exact hconsistent

theorem PreservesHidden.bind
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta}
    (hleft : PreservesHidden left) (hnext : ∀ value, PreservesHidden (next value)) :
    PreservesHidden (left >>= next) := by
  intro state cache fuel finalState remaining result finalCache hconsistent hresult
  change LazyRevealProbe.RawResult.done finalState remaining (result, finalCache) ∈
    support (LazyRevealProbe.runRaw state fuel
      (left.run cache >>= fun leftResult => (next leftResult.1).run leftResult.2)) at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hraw, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done middleState middleRemaining leftResult =>
      rcases leftResult with ⟨leftValue, middleCache⟩
      have hmiddle := hleft state cache fuel middleState middleRemaining leftValue middleCache
        hconsistent hraw
      exact hnext leftValue middleState middleCache middleRemaining finalState remaining result
        finalCache hmiddle hrest

theorem splitHashQuery_run_eq (key : SplitHashKey) (cache : SplitHashCache) :
    (splitHashQuery key).run cache =
      match cache key with
      | some output => pure (output, cache)
      | none => LazyRevealProbe.hashOutputQuery >>= fun output =>
          pure (output, Function.update cache key (some output)) := by
  cases hlookup : cache key <;> simp [splitHashQuery, hlookup]

theorem preservesHidden_splitHashQuery_ordinary (input : HashInput) :
    PreservesHidden (splitHashQuery (.ordinary input)) := by
  intro state cache fuel finalState remaining value finalCache hconsistent hresult
  rw [splitHashQuery_run_eq] at hresult
  cases hlookup : cache (.ordinary input) with
  | some output =>
      rw [hlookup] at hresult
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact hconsistent
  | none =>
      rw [hlookup] at hresult
      dsimp only at hresult
      change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
        (LazyRevealProbe.runRaw state fuel
          (LazyRevealProbe.hashOutputQuery >>= fun output =>
            pure (output, Function.update cache (.ordinary input) (some output)))) at hresult
      rw [LazyRevealProbe.hashOutputQuery,
        LazyRevealProbe.runRaw_hashOutput_query_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨output, _, hdone⟩ := hresult
      simp [LazyRevealProbe.runRaw] at hdone
      rcases hdone with ⟨rfl, rfl, rfl, rfl⟩
      exact hconsistent.updateOrdinary input value

theorem preservesHidden_ensureCoordinate (coordinate : Coordinate) :
    PreservesHidden (ensureCoordinate coordinate) := by
  intro state cache fuel finalState remaining value finalCache hconsistent hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.ensureQuery coordinate >>= fun output => pure (output, cache))) at hresult
  rw [LazyRevealProbe.ensureQuery, LazyRevealProbe.runRaw_ensure_query_bind] at hresult
  simp [LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  exact hconsistent.ensure coordinate

theorem preservesHidden_probe (candidate : Probe) :
    PreservesHidden (probe candidate) := by
  intro state cache fuel finalState remaining value finalCache hconsistent hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.probeQuery candidate.coordinate candidate.candidate >>= fun output =>
        pure (output, cache))) at hresult
  rw [LazyRevealProbe.probeQuery, LazyRevealProbe.runRaw_probe_query_bind] at hresult
  cases fuel with
  | zero => simp at hresult
  | succ remainingFuel =>
      change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
        (if candidate.coordinate ∈ state.revealed then
          LazyRevealProbe.runRaw state remainingFuel (pure ((), cache))
        else
          LazyRevealProbe.runRaw
            (state.addPending candidate.coordinate candidate.candidate) remainingFuel
              (pure ((), cache))) at hresult
      by_cases hrevealed : candidate.coordinate ∈ state.revealed
      · rw [if_pos hrevealed] at hresult
        simp [LazyRevealProbe.runRaw] at hresult
        rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
        exact hconsistent
      · rw [if_neg hrevealed] at hresult
        simp [LazyRevealProbe.runRaw] at hresult
        rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
        exact hconsistent.addPending candidate.coordinate candidate.candidate

theorem preservesHidden_peekCoordinate (coordinate : Coordinate) :
    PreservesHidden (peekCoordinate coordinate) := by
  intro state cache fuel finalState remaining value finalCache hconsistent hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.peekQuery coordinate >>= fun output =>
        pure (truncateHash <$> output, cache))) at hresult
  rw [LazyRevealProbe.peekQuery, LazyRevealProbe.runRaw_peek_query_bind] at hresult
  simp [LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  exact hconsistent

theorem revealCoordinateOutput_run (coordinate : Coordinate) (cache : SplitHashCache) :
    (revealCoordinateOutput coordinate).run cache =
      (LazyRevealProbe.revealQuery coordinate >>= fun output =>
        pure (output, Function.update cache (.hidden coordinate) (some output))) := by
  simp [revealCoordinateOutput, StateT.run_modify]

theorem preservesHidden_revealCoordinateOutput (coordinate : Coordinate) :
    PreservesHidden (revealCoordinateOutput coordinate) := by
  intro state cache fuel finalState remaining value finalCache hconsistent hresult
  rw [revealCoordinateOutput_run] at hresult
  rw [LazyRevealProbe.revealQuery, LazyRevealProbe.runRaw_reveal_query_bind] at hresult
  cases hvalue : state.values coordinate with
  | some output =>
      rw [hvalue] at hresult
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact hconsistent.updateHidden_of_value coordinate value hvalue
  | none =>
      rw [hvalue, mem_support_bind_iff] at hresult
      obtain ⟨output, _, hrest⟩ := hresult
      by_cases hhit : state.hitAt coordinate output
      · rw [if_pos hhit] at hrest
        simp at hrest
      · rw [if_neg hhit] at hrest
        simp [LazyRevealProbe.runRaw] at hrest
        rcases hrest with ⟨rfl, rfl, rfl, rfl⟩
        exact hconsistent.updateHidden_install coordinate value

theorem preservesHidden_revealCoordinate (coordinate : Coordinate) :
    PreservesHidden (revealCoordinate coordinate) := by
  unfold revealCoordinate
  exact (preservesHidden_revealCoordinateOutput coordinate).bind fun _ =>
    preservesHidden_pure _

theorem preservesHidden_splitUniformImpl (n : Nat) :
    PreservesHidden (splitUniformImpl n) := by
  intro state cache fuel finalState remaining value finalCache hconsistent hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.uniformQuery n >>= fun output => pure (output, cache))) at hresult
  rw [LazyRevealProbe.uniformQuery, LazyRevealProbe.runRaw_uniform_query_bind,
    mem_support_bind_iff] at hresult
  obtain ⟨output, _, hdone⟩ := hresult
  simp [LazyRevealProbe.runRaw] at hdone
  rcases hdone with ⟨rfl, rfl, rfl, rfl⟩
  exact hconsistent

def PreservesHiddenImpl {spec : OracleSpec ι}
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)))) : Prop :=
  ∀ query, PreservesHidden (impl query)

theorem PreservesHiddenImpl.simulateQ {spec : OracleSpec ι}
    {impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)))}
    (himpl : PreservesHiddenImpl impl) (computation : OracleComp spec alpha) :
    PreservesHidden (simulateQ impl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact preservesHidden_pure value
  | query_bind query next ih =>
      rw [simulateQ_query_bind]
      exact (himpl query).bind ih

theorem preservesHiddenImpl_ordinaryHashImpl :
    PreservesHiddenImpl ordinaryHashImpl := by
  intro input
  exact preservesHidden_splitHashQuery_ordinary input

theorem preservesHiddenImpl_splitUniformImpl :
    PreservesHiddenImpl splitUniformImpl :=
  preservesHidden_splitUniformImpl

theorem preservesHiddenImpl_ordinaryRomImpl :
    PreservesHiddenImpl ordinaryRomImpl := by
  intro query
  cases query with
  | inl query => exact preservesHiddenImpl_splitUniformImpl query
  | inr query => exact preservesHiddenImpl_ordinaryHashImpl query

theorem preservesHidden_sequenceFin {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (hcomputation : ∀ index, PreservesHidden (computation index)) :
    PreservesHidden (sequenceFin computation) := by
  induction n with
  | zero =>
      simp only [sequenceFin]
      exact preservesHidden_pure Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomputation 0).bind fun head =>
        (ih (fun index => computation index.succ)
          (fun index => hcomputation index.succ)).bind fun tail =>
            preservesHidden_pure (Fin.cases head tail : Fin (n + 1) → alpha)

theorem preservesHidden_revealPosition (position : Position) :
    PreservesHidden (revealPosition position) :=
  preservesHidden_revealCoordinate (.position position)

theorem preservesHidden_revealChainStart (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    PreservesHidden (revealChainStart lay tree leafIdx chainIdx) :=
  preservesHidden_revealCoordinate (.chainStart lay tree leafIdx chainIdx)

theorem preservesHidden_peekPositionValues (positions : List Position) :
    PreservesHidden (peekPositionValues positions) := by
  induction positions with
  | nil => exact preservesHidden_pure (some [])
  | cons position remaining ih =>
      rw [peekPositionValues]
      exact (preservesHidden_peekCoordinate (.position position)).bind fun value =>
        match value with
        | none => preservesHidden_pure none
        | some _ => ih.bind fun values =>
            match values with
            | none => preservesHidden_pure none
            | some _ => preservesHidden_pure _

theorem preservesHidden_peekTableInput (parameter : PublicParameter)
    (coordinate : Coordinate) :
    PreservesHidden (peekTableInput parameter coordinate) := by
  cases coordinate with
  | chainStart => exact preservesHidden_pure none
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          rw [peekTableInput]
          by_cases hzero : step.val = 0
          · rw [if_pos hzero]
            exact (preservesHidden_peekCoordinate
              (.chainStart lay tree leafIdx chainIdx)).bind fun value =>
                match value with
                | none => preservesHidden_pure none
                | some _ => preservesHidden_pure _
          · rw [if_neg hzero]
            exact (preservesHidden_peekPositionValues
              (Position.chain lay tree leafIdx chainIdx step).children).bind fun values =>
                match values with
                | none => preservesHidden_pure none
                | some _ => preservesHidden_pure _
      | leaf lay tree leafIdx =>
          simp only [peekTableInput]
          exact (preservesHidden_peekPositionValues _).bind fun values =>
            match values with
            | none => preservesHidden_pure none
            | some _ => preservesHidden_pure _
      | node lay tree level nodeIdx =>
          simp only [peekTableInput]
          exact (preservesHidden_peekPositionValues _).bind fun values =>
            match values with
            | none => preservesHidden_pure none
            | some _ => preservesHidden_pure _
      | ftsLeaf index tree leafIdx =>
          simp only [peekTableInput]
          exact (preservesHidden_peekPositionValues _).bind fun values =>
            match values with
            | none => preservesHidden_pure none
            | some _ => preservesHidden_pure _
      | ftsNode index tree level nodeIdx =>
          simp only [peekTableInput]
          exact (preservesHidden_peekPositionValues _).bind fun values =>
            match values with
            | none => preservesHidden_pure none
            | some _ => preservesHidden_pure _
      | ftsRoots index =>
          simp only [peekTableInput]
          exact (preservesHidden_peekPositionValues _).bind fun values =>
            match values with
            | none => preservesHidden_pure none
            | some _ => preservesHidden_pure _

theorem preservesHidden_ensureFullChain (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    PreservesHidden (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  exact (preservesHidden_sequenceFin _ fun step =>
    preservesHidden_ensureCoordinate
      (.position (.chain lay tree leafIdx chainIdx step))).bind fun _ =>
        preservesHidden_pure ()

theorem preservesHidden_ensureChainPrefix (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (digit : Digit) :
    PreservesHidden (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  unfold ensureChainPrefix
  exact (preservesHidden_sequenceFin _ fun step => by
    split
    · exact preservesHidden_ensureCoordinate
        (.position (.chain lay tree leafIdx chainIdx step))
    · exact preservesHidden_pure ()).bind fun _ => preservesHidden_pure ()

theorem preservesHidden_ensureOtsLeaf (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    PreservesHidden (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  exact (preservesHidden_sequenceFin _ fun chainIdx =>
    preservesHidden_ensureFullChain lay tree leafIdx chainIdx).bind fun _ =>
      preservesHidden_ensureCoordinate (.position (.leaf lay tree leafIdx))

theorem preservesHidden_ensureTreeNode (lay : Layer) (tree : TreeIndex)
    (level nodeIdx : Nat) :
    PreservesHidden (ensureTreeNode lay tree level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero => exact preservesHidden_ensureOtsLeaf lay tree (leafOfNat nodeIdx)
  | succ level ih =>
      rw [ensureTreeNode]
      exact (ih (2 * nodeIdx)).bind fun _ =>
        (ih (2 * nodeIdx + 1)).bind fun _ => by
          split
          · exact preservesHidden_ensureCoordinate _
          · exact preservesHidden_pure ()

theorem preservesHidden_maskedTreeNode (lay : Layer) (tree : TreeIndex)
    (level nodeIdx : Nat) :
    PreservesHidden (maskedTreeNode lay tree level nodeIdx) := by
  unfold maskedTreeNode
  exact (preservesHidden_ensureTreeNode lay tree level nodeIdx).bind fun _ =>
    match level with
    | 0 => preservesHidden_revealPosition (.leaf lay tree (leafOfNat nodeIdx))
    | current + 1 => by
        rw [show current + 1 = Nat.succ current by omega]
        change PreservesHidden
          (if hlevel : current < maxLayerHeight then
            revealPosition (.node lay tree ⟨current, hlevel⟩ (leafOfNat nodeIdx))
          else pure 0)
        by_cases hlevel : current < maxLayerHeight
        · rw [dif_pos hlevel]
          exact preservesHidden_revealPosition _
        · rw [dif_neg hlevel]
          exact preservesHidden_pure 0

theorem preservesHidden_maskedTreeRoot (lay : Layer) (tree : TreeIndex) :
    PreservesHidden (maskedTreeRoot lay tree) :=
  preservesHidden_maskedTreeNode lay tree (layerHeight lay) 0

theorem preservesHidden_maskedTreePath (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    PreservesHidden (maskedTreePath lay tree leafIdx) := by
  unfold maskedTreePath
  exact preservesHidden_sequenceFin _ fun level => by
    split
    · exact preservesHidden_maskedTreeNode _ _ _ _
    · exact preservesHidden_pure 0

theorem preservesHidden_maskedChainValue (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (digit : Digit) :
    PreservesHidden (maskedChainValue lay tree leafIdx chainIdx digit) := by
  unfold maskedChainValue
  exact (preservesHidden_ensureChainPrefix lay tree leafIdx chainIdx digit).bind fun _ => by
    split
    · exact preservesHidden_revealChainStart lay tree leafIdx chainIdx
    · exact preservesHidden_revealPosition _

theorem preservesHidden_maskedOtsSignFrom (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest)
    (attempts counter : Nat) :
    PreservesHidden
      (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter) := by
  induction attempts generalizing counter with
  | zero => exact preservesHidden_pure none
  | succ attempts ih =>
      rw [maskedOtsSignFrom]
      exact (preservesHiddenImpl_ordinaryHashImpl.simulateQ
        (encode parameter lay tree leafIdx message
          (BitVec.ofNat counterBits counter))).bind fun encoded =>
            match encoded with
            | none => ih (counter + 1)
            | some encoding =>
                (preservesHidden_sequenceFin _ fun chainIdx =>
                  preservesHidden_maskedChainValue lay tree leafIdx chainIdx
                    (encoding chainIdx)).bind fun values => preservesHidden_pure
                      (some (BitVec.ofNat counterBits counter, values))

theorem preservesHidden_maskedOtsSign (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    PreservesHidden (maskedOtsSign parameter lay tree leafIdx message) :=
  preservesHidden_maskedOtsSignFrom parameter lay tree leafIdx message
    encodingAttemptLimit 0

theorem preservesHidden_maskedLayerMessage (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay : Layer) :
    PreservesHidden (maskedLayerMessage parameter ftsSecret index lay) := by
  unfold maskedLayerMessage
  split
  · exact preservesHidden_maskedTreeRoot _ _
  · exact preservesHiddenImpl_ordinaryHashImpl.simulateQ
      (ftsKey parameter index (ftsSecret index))

theorem preservesHidden_maskedSignLayer (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay : Layer) :
    PreservesHidden (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayer
  exact (preservesHidden_maskedLayerMessage parameter ftsSecret index lay).bind fun message =>
    (preservesHidden_maskedOtsSign parameter lay (treeIndexAt index lay)
      (leafIndexAt index lay) message).bind fun result =>
        match result with
        | none => preservesHidden_pure none
        | some part =>
            (preservesHidden_maskedTreePath lay (treeIndexAt index lay)
              (leafIndexAt index lay)).bind fun path =>
                preservesHidden_pure (some (part.1, part.2, path))

theorem preservesHidden_maskedSignAfterDigest (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    PreservesHidden
      (maskedSignAfterDigest parameter ftsSecret randomness index leaves) := by
  unfold maskedSignAfterDigest
  exact (preservesHiddenImpl_ordinaryHashImpl.simulateQ
    (ftsOpen parameter index leaves (ftsSecret index))).bind fun ftsPath =>
      (preservesHidden_sequenceFin _ fun lay =>
        preservesHidden_maskedSignLayer parameter ftsSecret index lay).bind fun layers =>
          by
            cases hparts : traverseOption layers with
            | none =>
                exact preservesHidden_pure (none : Option Signature)
            | some parts =>
                exact preservesHidden_pure _

theorem preservesHidden_maskedSign (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message) :
    PreservesHidden (maskedSign parameter root ftsSecret message) := by
  unfold maskedSign
  exact (preservesHiddenImpl_ordinaryRomImpl.simulateQ
    (signDigestLoop digestAttemptLimit
      ⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩ message)).bind fun result =>
        match result with
        | none => preservesHidden_pure none
        | some selected => preservesHidden_maskedSignAfterDigest parameter ftsSecret
            selected.1 selected.2.1 selected.2.2

theorem preservesHidden_modifyOrdinary (input : HashInput) (output : HashOutput) :
    PreservesHidden
      (modify (fun cache : SplitHashCache =>
        Function.update cache (.ordinary input) (some output))) := by
  intro state cache fuel finalState remaining value finalCache hconsistent hresult
  simp [StateT.run_modify, LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  exact hconsistent.updateOrdinary input output

theorem preservesHidden_resolveKnownInput (parameter : PublicParameter)
    (coordinate : Coordinate) (input : HashInput) :
    PreservesHidden (resolveKnownInput parameter coordinate input) := by
  unfold resolveKnownInput
  exact (preservesHidden_peekTableInput parameter coordinate).bind fun known =>
    match known with
    | none => preservesHidden_splitHashQuery_ordinary input
    | some knownInput => by
        change PreservesHidden
          (if knownInput = input then do
            let output ← revealCoordinateOutput coordinate
            modify fun cache : SplitHashCache =>
              Function.update cache (.ordinary input) (some output)
            pure output
          else splitHashQuery (.ordinary input))
        by_cases heq : knownInput = input
        · rw [if_pos heq]
          exact (preservesHidden_revealCoordinateOutput coordinate).bind fun output =>
            (preservesHidden_modifyOrdinary input output).bind fun _ =>
              preservesHidden_pure output
        · rw [if_neg heq]
          exact preservesHidden_splitHashQuery_ordinary input

theorem preservesHidden_probingHashQuery (parameter : PublicParameter)
    (input : HashInput) :
    PreservesHidden (probingHashQuery parameter input) := by
  unfold probingHashQuery
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      exact (preservesHidden_probe candidate).bind fun _ =>
        preservesHidden_resolveKnownInput parameter candidate.outputCoordinate input
  | none =>
      cases hposition : decodePosition? parameter input with
      | none => exact preservesHidden_splitHashQuery_ordinary input
      | some position =>
          cases position with
          | chain lay tree leafIdx chainIdx step =>
              exact preservesHidden_resolveKnownInput parameter
                (.position (.chain lay tree leafIdx chainIdx step)) input
          | leaf lay tree leafIdx =>
              exact preservesHidden_resolveKnownInput parameter
                (.position (.leaf lay tree leafIdx)) input
          | node lay tree level nodeIdx =>
              exact preservesHidden_resolveKnownInput parameter
                (.position (.node lay tree level nodeIdx)) input
          | ftsLeaf | ftsNode | ftsRoots =>
              exact preservesHidden_splitHashQuery_ordinary input

theorem preservesHiddenImpl_probingHashImpl (parameter : PublicParameter) :
    PreservesHiddenImpl (probingHashImpl parameter) :=
  preservesHidden_probingHashQuery parameter

theorem preservesHiddenImpl_probingRomImpl (parameter : PublicParameter) :
    PreservesHiddenImpl (probingRomImpl parameter) := by
  intro query
  cases query with
  | inl query => exact preservesHiddenImpl_splitUniformImpl query
  | inr query => exact preservesHiddenImpl_probingHashImpl parameter query

theorem preservesHiddenImpl_maskedSigningImpl (parameter : PublicParameter)
    (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    PreservesHiddenImpl (maskedSigningImpl parameter root ftsSecret) :=
  preservesHidden_maskedSign parameter root ftsSecret

theorem preservesHiddenImpl_maskedExpandedAdversaryImpl (parameter : PublicParameter)
    (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    PreservesHiddenImpl (maskedExpandedAdversaryImpl parameter root ftsSecret) := by
  intro query
  cases query with
  | inl query => exact preservesHiddenImpl_probingRomImpl parameter query
  | inr query => exact preservesHiddenImpl_maskedSigningImpl parameter root ftsSecret query

theorem mergeDecodedPosition_eq_some_imp_tableAnswerDecoded
    (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (ensured : Finset Coordinate)
    (cache : SplitHashCache)
    (hhidden : ∀ coordinate output,
      completedSplitHashCache table ensured cache (.hidden coordinate) = some output →
        output = table coordinate)
    (input : HashInput) (decoded : Option Position) (output : HashOutput)
    (hcached : mergeDecodedPosition parameter table ensured cache input decoded =
      some output) :
    tableAnswerDecoded parameter table (splitFallback cache) input decoded = output := by
  cases decoded with
  | none =>
      simp only [mergeDecodedPosition] at hcached
      simp only [tableAnswerDecoded, splitFallback]
      simp [hcached]
  | some position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          by_cases hexact : input = tableInput parameter table
              (.position (.chain lay tree leafIdx chainIdx step))
          · simp only [mergeDecodedPosition, hexact, ↓reduceIte] at hcached
            simp only [tableAnswerDecoded, hexact, ↓reduceIte]
            exact (hhidden _ _ hcached).symm
          · simp only [mergeDecodedPosition, hexact, ↓reduceIte] at hcached
            simp only [tableAnswerDecoded, hexact, ↓reduceIte, splitFallback]
            simp [hcached]
      | leaf lay tree leafIdx =>
          by_cases hexact : input = tableInput parameter table
              (.position (.leaf lay tree leafIdx))
          · simp only [mergeDecodedPosition, hexact, ↓reduceIte] at hcached
            simp only [tableAnswerDecoded, hexact, ↓reduceIte]
            exact (hhidden _ _ hcached).symm
          · simp only [mergeDecodedPosition, hexact, ↓reduceIte] at hcached
            simp only [tableAnswerDecoded, hexact, ↓reduceIte, splitFallback]
            simp [hcached]
      | node lay tree level nodeIdx =>
          by_cases hexact : input = tableInput parameter table
              (.position (.node lay tree level nodeIdx))
          · simp only [mergeDecodedPosition, hexact, ↓reduceIte] at hcached
            simp only [tableAnswerDecoded, hexact, ↓reduceIte]
            exact (hhidden _ _ hcached).symm
          · simp only [mergeDecodedPosition, hexact, ↓reduceIte] at hcached
            simp only [tableAnswerDecoded, hexact, ↓reduceIte, splitFallback]
            simp [hcached]
      | ftsLeaf | ftsNode | ftsRoots =>
          simp only [mergeDecodedPosition] at hcached
          simp only [tableAnswerDecoded, splitFallback]
          simp [hcached]

theorem mergedCache_agreesWith_tableAnswer (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (ensured : Finset Coordinate)
    (cache : SplitHashCache)
    (hhidden : ∀ coordinate output,
      completedSplitHashCache table ensured cache (.hidden coordinate) = some output →
        output = table coordinate) :
    (mergedCache parameter table ensured cache).AgreesWithFn
      (tableAnswer parameter table (splitFallback cache)) := by
  intro input output hcached
  exact mergeDecodedPosition_eq_some_imp_tableAnswerDecoded parameter table ensured cache
    hhidden input (decodePosition? parameter input) output hcached

theorem fromMergedCache_tableInput (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (ensured : Finset Coordinate)
    (cache : SplitHashCache) (position : Position) (hots : IsOtsPosition position)
    (hcomplete : completedSplitHashCache table ensured cache
      (.hidden (.position position)) = some (table (.position position))) :
    fromCache (mergedCache parameter table ensured cache)
        (tableInput parameter table (.position position)) =
      table (.position position) := by
  rw [fromCache, mergedCache_tableInput parameter table ensured cache position hots,
    hcomplete]
  rfl

theorem fromMergedCache_realizesTable (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (ensured : Finset Coordinate)
    (cache : SplitHashCache)
    (hcomplete : ∀ position : Position, IsOtsPosition position →
      completedSplitHashCache table ensured cache (.hidden (.position position)) =
        some (table (.position position))) :
    ∀ position : Position, IsOtsPosition position →
      fromCache (mergedCache parameter table ensured cache)
          (tableInput parameter table (.position position)) =
        table (.position position) := by
  intro position hots
  exact fromMergedCache_tableInput parameter table ensured cache position hots
    (hcomplete position hots)

theorem honestChain_eq_table_succ
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (hf : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (step : Nat) (hstep : step < chainLength - 1) :
    honestChain f parameter lay tree leafIdx chainIdx
        (tableOtsSecret table lay tree leafIdx chainIdx) (step + 1) =
      tableValue table (.chain lay tree leafIdx chainIdx ⟨step, hstep⟩) := by
  induction step using Nat.strong_induction_on with
  | h step ih =>
      rw [honestChain_succ f parameter lay tree leafIdx chainIdx _ step hstep]
      have hinput :
          tweakableHashInput parameter (.chain lay tree leafIdx chainIdx ⟨step, hstep⟩)
              (digestBytes (honestChain f parameter lay tree leafIdx chainIdx
                (tableOtsSecret table lay tree leafIdx chainIdx) step)) =
            tableInput parameter table
              (.position (.chain lay tree leafIdx chainIdx ⟨step, hstep⟩)) := by
        cases step with
        | zero =>
            simp [honestChain_zero, tableInput, tablePayload, tableOtsSecret,
              Position.domain]
        | succ previous =>
            have hprevious : previous < chainLength - 1 := by omega
            rw [ih previous (by omega) hprevious]
            simp [tableInput, tablePayload, Position.children, Position.domain]
      rw [hinput, hf (.chain lay tree leafIdx chainIdx ⟨step, hstep⟩) (by trivial)]
      rfl

theorem honestEndpoints_eq_table
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex)
    (hf : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position)) :
    honestEndpoints f parameter lay tree (tableOtsSecret table lay tree) leafIdx =
      fun chainIdx =>
        tableValue table (.chain lay tree leafIdx chainIdx Position.lastChainStep) := by
  funext chainIdx
  unfold honestEndpoints
  have h := honestChain_eq_table_succ f parameter table lay tree leafIdx chainIdx hf
    (chainLength - 2) (by decide)
  rw [show chainLength - 2 + 1 = chainLength - 1 by
    norm_num [chainLength, winternitzBits]] at h
  have hposition : (⟨chainLength - 2, by decide⟩ : ChainStep) =
      Position.lastChainStep := Fin.ext (by rfl)
  rw [hposition] at h
  exact h

theorem honestNode_zero_eq_table
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex)
    (hf : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position)) :
    honestNode f parameter lay tree (tableOtsSecret table lay tree) 0 leafIdx.val =
      tableValue table (.leaf lay tree leafIdx) := by
  rw [honestNode_zero_eq_leafHash]
  rw [honestEndpoints_eq_table f parameter table lay tree leafIdx hf]
  have hinput :
      tweakableHashInput parameter (.leaf lay tree leafIdx)
          (leafPayload fun chainIdx =>
            tableValue table (.chain lay tree leafIdx chainIdx Position.lastChainStep)) =
        tableInput parameter table (.position (.leaf lay tree leafIdx)) := by
    simp [tableInput, tablePayload, Position.children, Position.domain, leafPayload,
      Function.comp_def]
  rw [hinput, hf (.leaf lay tree leafIdx) (by trivial)]
  rfl

theorem honestNode_eq_table_succ
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (lay : Layer) (tree : TreeIndex)
    (hf : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (level nodeIdx : Nat) (hlevel : level < maxLayerHeight)
    (hspan : 2 ^ (level + 1) * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight) :
    honestNode f parameter lay tree (tableOtsSecret table lay tree) (level + 1) nodeIdx =
      tableValue table
        (.node lay tree ⟨level, hlevel⟩ (leafOfNat nodeIdx)) := by
  induction level using Nat.strong_induction_on generalizing nodeIdx with
  | h level ih =>
      rw [honestNode_succ]
      have hnode : nodeIdx < 2 ^ maxLayerHeight := by
        have hpow : 0 < 2 ^ (level + 1) := pow_pos (by omega) _
        nlinarith
      have hpowTwo : 2 ≤ 2 ^ (level + 1) := by
        have hp : 2 ^ 1 ≤ 2 ^ (level + 1) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        simpa using hp
      have hleft : 2 * nodeIdx < 2 ^ maxLayerHeight := by
        nlinarith
      have hright : 2 * nodeIdx + 1 < 2 ^ maxLayerHeight := by
        nlinarith
      by_cases hzero : level = 0
      · subst level
        have hleftValue := honestNode_zero_eq_table f parameter table lay tree
          (leafOfNat (2 * nodeIdx)) hf
        have hrightValue := honestNode_zero_eq_table f parameter table lay tree
          (leafOfNat (2 * nodeIdx + 1)) hf
        have hleftIndex : (leafOfNat (2 * nodeIdx)).val = 2 * nodeIdx := by
          simp [leafOfNat, Nat.mod_eq_of_lt hleft]
        have hrightIndex : (leafOfNat (2 * nodeIdx + 1)).val = 2 * nodeIdx + 1 := by
          simp [leafOfNat, Nat.mod_eq_of_lt hright]
        rw [hleftIndex] at hleftValue
        rw [hrightIndex] at hrightValue
        rw [hleftValue, hrightValue]
        have hinput :
            tweakableHashInput parameter (.node lay tree 1 nodeIdx)
                (nodePayload
                  (tableValue table (.leaf lay tree (leafOfNat (2 * nodeIdx))))
                  (tableValue table (.leaf lay tree (leafOfNat (2 * nodeIdx + 1))))) =
              tableInput parameter table
                (.position (.node lay tree ⟨0, hlevel⟩ (leafOfNat nodeIdx))) := by
          simp only [tableInput, tablePayload, Position.domain]
          rw [Position.children, dif_pos (by
            simpa [leafOfNat, Nat.mod_eq_of_lt hnode] using hright),
            dif_neg (show ¬0 < (⟨0, hlevel⟩ : Fin maxLayerHeight).val by simp)]
          simp [nodePayload, leafOfNat, Nat.mod_eq_of_lt hnode,
            Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright]
        rw [hinput, hf (.node lay tree ⟨0, hlevel⟩ (leafOfNat nodeIdx)) (by trivial)]
        rfl
      · obtain ⟨previous, rfl⟩ : ∃ previous, level = previous + 1 :=
          ⟨level - 1, by omega⟩
        have hleftSpan : 2 ^ (previous + 1) * (2 * nodeIdx + 1) ≤
            2 ^ maxLayerHeight := by
          rw [pow_succ] at hspan
          nlinarith
        have hrightSpan : 2 ^ (previous + 1) * (2 * nodeIdx + 1 + 1) ≤
            2 ^ maxLayerHeight := by
          rw [pow_succ] at hspan
          nlinarith
        rw [ih previous (by omega) (2 * nodeIdx) (by omega) hleftSpan,
          ih previous (by omega) (2 * nodeIdx + 1) (by omega) hrightSpan]
        have hinput :
            tweakableHashInput parameter (.node lay tree (previous + 1 + 1) nodeIdx)
                (nodePayload
                  (tableValue table
                    (.node lay tree ⟨previous, by omega⟩ (leafOfNat (2 * nodeIdx))))
                  (tableValue table
                    (.node lay tree ⟨previous, by omega⟩
                      (leafOfNat (2 * nodeIdx + 1))))) =
              tableInput parameter table
                (.position
                  (.node lay tree ⟨previous + 1, hlevel⟩ (leafOfNat nodeIdx))) := by
          simp only [tableInput, tablePayload, Position.domain]
          rw [Position.children, dif_pos (by
            simpa [leafOfNat, Nat.mod_eq_of_lt hnode] using hright),
            dif_pos (show 0 < (⟨previous + 1, hlevel⟩ : Fin maxLayerHeight).val by
              simp)]
          simp [nodePayload, leafOfNat, Nat.mod_eq_of_lt hnode,
            Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright]
        rw [hinput,
          hf (.node lay tree ⟨previous + 1, hlevel⟩ (leafOfNat nodeIdx)) (by trivial)]
        rfl

theorem honestNode_eq_table_succ_fromMerged
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (ensured : Finset Coordinate) (cache : SplitHashCache)
    (hcomplete : ∀ position : Position, IsOtsPosition position →
      completedSplitHashCache table ensured cache (.hidden (.position position)) =
        some (table (.position position)))
    (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat)
    (hlevel : level < maxLayerHeight)
    (hspan : 2 ^ (level + 1) * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight) :
    honestNode (fromCache (mergedCache parameter table ensured cache)) parameter lay tree
        (tableOtsSecret table lay tree) (level + 1) nodeIdx =
      tableValue table
        (.node lay tree ⟨level, hlevel⟩ (leafOfNat nodeIdx)) :=
  honestNode_eq_table_succ
    (fromCache (mergedCache parameter table ensured cache)) parameter table lay tree
    (fromMergedCache_realizesTable parameter table ensured cache hcomplete)
    level nodeIdx hlevel hspan

theorem honestNode_eq_table_succ_tableAnswer
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (fallback : QueryImpl HashSpec Id) (lay : Layer) (tree : TreeIndex)
    (level nodeIdx : Nat) (hlevel : level < maxLayerHeight)
    (hspan : 2 ^ (level + 1) * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight) :
    honestNode (tableAnswer parameter table fallback) parameter lay tree
        (tableOtsSecret table lay tree) (level + 1) nodeIdx =
      tableValue table
        (.node lay tree ⟨level, hlevel⟩ (leafOfNat nodeIdx)) :=
  honestNode_eq_table_succ (tableAnswer parameter table fallback) parameter table lay tree
    (tableAnswer_tableInput parameter table fallback) level nodeIdx hlevel hspan

end SphincsSecurity.Concrete.OtsProbeSimulation
