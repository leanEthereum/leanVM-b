import SphincsSecurity.Proof.OtsProbeRetained

/-!
# Origins of published one-time chain values

Every chain value published by the masked signer belongs to one successful signing-log entry. This
module packages that semantic endpoint and proves the incompatibilities needed by the exact forged
opening events.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

def IsChainCoordinate : Coordinate → Prop
  | .chainStart _ _ _ _ => True
  | .position (.chain _ _ _ _ _) => True
  | _ => False

def ChainForwardClosed (allowed : Coordinate → Prop) : Prop :=
  ∀ candidate : Probe, allowed candidate.coordinate →
    IsChainCoordinate candidate.outputCoordinate → allowed candidate.outputCoordinate

theorem isChainCoordinate_chainValueCoordinate (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (digit : Digit) :
    IsChainCoordinate (chainValueCoordinate lay tree leafIdx chainIdx digit) := by
  unfold chainValueCoordinate
  split <;> trivial

def ChainState.ValidFor (allowed : Coordinate → Prop)
    (state : LazyRevealProbe.State Coordinate) : Prop :=
  ∀ coordinate, IsChainCoordinate coordinate →
    (state.values coordinate ≠ none → coordinate ∈ state.revealed) ∧
    (coordinate ∈ state.revealed → state.values coordinate ≠ none) ∧
    (coordinate ∈ state.revealed → allowed coordinate)

theorem ChainState.validFor_empty (allowed : Coordinate → Prop) :
    ChainState.ValidFor allowed (LazyRevealProbe.State.empty :
      LazyRevealProbe.State Coordinate) := by
  intro coordinate hchain
  simp [LazyRevealProbe.State.empty]

theorem ChainState.ValidFor.ensure {allowed : Coordinate → Prop}
    {state : LazyRevealProbe.State Coordinate} (hvalid : ChainState.ValidFor allowed state)
    (coordinate : Coordinate) : ChainState.ValidFor allowed (state.ensure coordinate) := by
  simpa [ChainState.ValidFor, LazyRevealProbe.State.ensure] using hvalid

theorem ChainState.ValidFor.addPending {allowed : Coordinate → Prop}
    {state : LazyRevealProbe.State Coordinate} (hvalid : ChainState.ValidFor allowed state)
    (coordinate : Coordinate) (candidate : Digest) :
    ChainState.ValidFor allowed (state.addPending coordinate candidate) := by
  simpa [ChainState.ValidFor, LazyRevealProbe.State.addPending] using hvalid

theorem ChainState.ValidFor.clearPending {allowed : Coordinate → Prop}
    {state : LazyRevealProbe.State Coordinate} (hvalid : ChainState.ValidFor allowed state)
    (coordinate : Coordinate) : ChainState.ValidFor allowed (state.clearPending coordinate) := by
  simpa [ChainState.ValidFor, LazyRevealProbe.State.clearPending] using hvalid

theorem ChainState.ValidFor.materialize_of_not_chain {allowed : Coordinate → Prop}
    {state : LazyRevealProbe.State Coordinate} (hvalid : ChainState.ValidFor allowed state)
    (coordinate : Coordinate) (output : HashOutput) (hnotChain : ¬IsChainCoordinate coordinate) :
    ChainState.ValidFor allowed (state.materialize coordinate output) := by
  intro other hchain
  have hne : other ≠ coordinate := by
    intro heq
    exact hnotChain (heq ▸ hchain)
  simpa [LazyRevealProbe.State.materialize, Function.update, hne] using hvalid other hchain

theorem ChainState.ValidFor.publish {allowed : Coordinate → Prop}
    {state : LazyRevealProbe.State Coordinate} (hvalid : ChainState.ValidFor allowed state)
    (coordinate : Coordinate) (hvalue : state.values coordinate ≠ none)
    (hallowed : IsChainCoordinate coordinate → allowed coordinate) :
    ChainState.ValidFor allowed (state.publish coordinate) := by
  intro other hchain
  by_cases heq : other = coordinate
  · subst other
    have hrevealed : coordinate ∈ (state.publish coordinate).revealed := by
      simp [LazyRevealProbe.State.publish]
    exact ⟨fun _ => hrevealed, fun _ => hvalue, fun _ => hallowed hchain⟩
  · have hold := hvalid other hchain
    simpa [LazyRevealProbe.State.publish, heq] using hold

theorem ChainState.ValidFor.materialize_publish {allowed : Coordinate → Prop}
    {state : LazyRevealProbe.State Coordinate} (hvalid : ChainState.ValidFor allowed state)
    (coordinate : Coordinate) (output : HashOutput)
    (hallowed : IsChainCoordinate coordinate → allowed coordinate) :
    ChainState.ValidFor allowed ((state.materialize coordinate output).publish coordinate) := by
  intro other hchain
  by_cases heq : other = coordinate
  · subst other
    simp [LazyRevealProbe.State.materialize, LazyRevealProbe.State.publish, Function.update,
      hallowed hchain]
  · have hold := hvalid other hchain
    simpa [LazyRevealProbe.State.materialize, LazyRevealProbe.State.publish, Function.update,
      heq] using hold

def PreservesChainValid (allowed : Coordinate → Prop)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha) : Prop :=
  ∀ state cache fuel finalState remaining value finalCache,
    ChainState.ValidFor allowed state →
      LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
        support (LazyRevealProbe.runRaw state fuel (computation.run cache)) →
      ChainState.ValidFor allowed finalState

theorem PreservesChainValid.bind
    {allowed : Coordinate → Prop}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta}
    (hleft : PreservesChainValid allowed left)
    (hnext : ∀ value, PreservesChainValid allowed (next value)) :
    PreservesChainValid allowed (left >>= next) := by
  intro state cache fuel finalState remaining result finalCache hvalid hresult
  change LazyRevealProbe.RawResult.done finalState remaining (result, finalCache) ∈
    support (LazyRevealProbe.runRaw state fuel
      (left.run cache >>= fun leftResult => (next leftResult.1).run leftResult.2)) at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hraw, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done middleState middleRemaining leftResult =>
      rcases leftResult with ⟨leftValue, middleCache⟩
      exact hnext leftValue middleState middleCache middleRemaining finalState remaining result
        finalCache (hleft state cache fuel middleState middleRemaining leftValue middleCache
          hvalid hraw) hrest

theorem preservesChainValid_pure (allowed : Coordinate → Prop) (value : alpha) :
    PreservesChainValid allowed
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) alpha) := by
  intro state cache fuel finalState remaining result finalCache hvalid hresult
  simp [LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  exact hvalid

theorem preservesChainValid_splitHashQuery_ordinary (allowed : Coordinate → Prop)
    (input : HashInput) : PreservesChainValid allowed (splitHashQuery (.ordinary input)) := by
  intro state cache fuel finalState remaining value finalCache hvalid hresult
  rw [splitHashQuery_run_eq] at hresult
  cases hlookup : cache (.ordinary input) with
  | some output =>
      rw [hlookup] at hresult
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact hvalid
  | none =>
      rw [hlookup] at hresult
      dsimp only at hresult
      change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
        (LazyRevealProbe.runRaw state fuel
          (LazyRevealProbe.hashOutputQuery >>= fun output =>
            pure (output, Function.update cache (.ordinary input) (some output)))) at hresult
      rw [LazyRevealProbe.hashOutputQuery,
        LazyRevealProbe.runRaw_hashOutput_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨output, _, hdone⟩ := hresult
      simp [LazyRevealProbe.runRaw] at hdone
      rcases hdone with ⟨rfl, rfl, rfl, rfl⟩
      exact hvalid

theorem preservesChainValid_ensureCoordinate (allowed : Coordinate → Prop)
    (coordinate : Coordinate) : PreservesChainValid allowed (ensureCoordinate coordinate) := by
  intro state cache fuel finalState remaining value finalCache hvalid hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.ensureQuery coordinate >>= fun output => pure (output, cache))) at hresult
  rw [LazyRevealProbe.ensureQuery, LazyRevealProbe.runRaw_ensure_query_bind] at hresult
  simp [LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  exact hvalid.ensure coordinate

theorem preservesChainValid_probe (allowed : Coordinate → Prop) (candidate : Probe) :
    PreservesChainValid allowed (probe candidate) := by
  intro state cache fuel finalState remaining value finalCache hvalid hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.probeQuery candidate.coordinate candidate.candidate >>= fun output =>
        pure (output, cache))) at hresult
  rw [LazyRevealProbe.probeQuery, LazyRevealProbe.runRaw_probe_query_bind] at hresult
  cases fuel with
  | zero => simp at hresult
  | succ remainingFuel =>
      simp only at hresult
      by_cases hrevealed : candidate.coordinate ∈ state.revealed
      · rw [if_pos hrevealed] at hresult
        simp [LazyRevealProbe.runRaw] at hresult
        rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
        exact hvalid
      · rw [if_neg hrevealed] at hresult
        simp [LazyRevealProbe.runRaw] at hresult
        rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
        exact hvalid.addPending candidate.coordinate candidate.candidate

theorem preservesChainValid_peekCoordinate (allowed : Coordinate → Prop)
    (coordinate : Coordinate) : PreservesChainValid allowed (peekCoordinate coordinate) := by
  intro state cache fuel finalState remaining value finalCache hvalid hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.peekQuery coordinate >>= fun output =>
        pure (truncateHash <$> output, cache))) at hresult
  rw [LazyRevealProbe.peekQuery, LazyRevealProbe.runRaw_peek_query_bind] at hresult
  simp [LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  exact hvalid

theorem mem_runRaw_peekCoordinate_some
    (coordinate : Coordinate) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : Digest)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (some value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel ((peekCoordinate coordinate).run cache))) :
    finalState = state ∧ remaining = fuel ∧ finalCache = cache ∧
      state.values coordinate ≠ none := by
  change LazyRevealProbe.RawResult.done finalState remaining (some value, finalCache) ∈
    support (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.peekQuery coordinate >>= fun output =>
        pure (truncateHash <$> output, cache))) at hresult
  rw [LazyRevealProbe.peekQuery, LazyRevealProbe.runRaw_peek_query_bind] at hresult
  cases hvalue : state.values coordinate with
  | none => simp [hvalue, LazyRevealProbe.runRaw] at hresult
  | some output =>
      simp [hvalue, LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨rfl, rfl, rfl, by simp⟩

theorem preservesChainValid_peekPositionValues (allowed : Coordinate → Prop)
    (positions : List Position) : PreservesChainValid allowed (peekPositionValues positions) := by
  induction positions with
  | nil => exact preservesChainValid_pure allowed (some [])
  | cons position remaining ih =>
      rw [peekPositionValues]
      exact (preservesChainValid_peekCoordinate allowed (.position position)).bind fun value =>
        match value with
        | none => preservesChainValid_pure allowed none
        | some _ => ih.bind fun values =>
            match values with
            | none => preservesChainValid_pure allowed none
            | some _ => preservesChainValid_pure allowed _

theorem preservesChainValid_peekTableInput (allowed : Coordinate → Prop)
    (parameter : PublicParameter) (coordinate : Coordinate) :
    PreservesChainValid allowed (peekTableInput parameter coordinate) := by
  cases coordinate with
  | chainStart => exact preservesChainValid_pure allowed none
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          rw [peekTableInput]
          by_cases hzero : step.val = 0
          · rw [if_pos hzero]
            exact (preservesChainValid_peekCoordinate allowed
              (.chainStart lay tree leafIdx chainIdx)).bind fun value =>
                match value with
                | none => preservesChainValid_pure allowed none
                | some _ => preservesChainValid_pure allowed _
          · rw [if_neg hzero]
            exact (preservesChainValid_peekPositionValues allowed
              (Position.chain lay tree leafIdx chainIdx step).children).bind fun values =>
                match values with
                | none => preservesChainValid_pure allowed none
                | some _ => preservesChainValid_pure allowed _
      | leaf | node | ftsLeaf | ftsNode | ftsRoots =>
          simp only [peekTableInput]
          exact (preservesChainValid_peekPositionValues allowed _).bind fun values =>
            match values with
            | none => preservesChainValid_pure allowed none
            | some _ => preservesChainValid_pure allowed _

theorem mem_runRaw_peekTableInput_chain_some_imp_source
    (parameter : PublicParameter) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (step : ChainStep) (knownInput : HashInput)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (some knownInput, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((peekTableInput parameter
          (.position (.chain lay tree leafIdx chainIdx step))).run cache))) :
    ∃ candidate : Probe,
      candidate.outputCoordinate = .position (.chain lay tree leafIdx chainIdx step) ∧
      IsChainCoordinate candidate.coordinate ∧ state.values candidate.coordinate ≠ none := by
  by_cases hzero : step.val = 0
  · rw [peekTableInput, if_pos hzero, StateT.run_bind, LazyRevealProbe.runRaw_bind,
      mem_support_bind_iff] at hresult
    obtain ⟨raw, hpeek, hrest⟩ := hresult
    cases raw with
    | stopped hit => simp at hrest
    | done peekState peekRemaining peekResult =>
        rcases peekResult with ⟨peekValue, peekCache⟩
        cases peekValue with
        | none => simp [LazyRevealProbe.runRaw] at hrest
        | some value =>
            have hvalue := mem_runRaw_peekCoordinate_some
              (.chainStart lay tree leafIdx chainIdx) state peekState cache peekCache fuel
                peekRemaining value hpeek
            refine ⟨⟨.chainStart lay tree leafIdx chainIdx, 0⟩, ?_, trivial,
              hvalue.2.2.2⟩
            have hstep : (⟨0, by norm_num [chainLength, winternitzBits]⟩ : ChainStep) = step :=
              Fin.ext hzero.symm
            simpa [Probe.outputCoordinate] using congrArg
              (fun nextStep => Coordinate.position
                (Position.chain lay tree leafIdx chainIdx nextStep)) hstep
  · have hpositive : 0 < step.val := Nat.pos_of_ne_zero hzero
    let previous : ChainStep := ⟨step.val - 1, by
      have := step.isLt
      omega⟩
    have hchildren : (Position.chain lay tree leafIdx chainIdx step).children =
        [.chain lay tree leafIdx chainIdx previous] := by
      rw [Position.children, dif_pos hpositive]
    rw [peekTableInput, if_neg hzero, hchildren] at hresult
    simp only [peekPositionValues] at hresult
    rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
    obtain ⟨raw, hvalues, hfinish⟩ := hresult
    cases raw with
    | stopped hit => simp at hfinish
    | done valuesState valuesRemaining valuesResult =>
        rcases valuesResult with ⟨values, valuesCache⟩
        cases values with
        | none => simp [LazyRevealProbe.runRaw] at hfinish
        | some values =>
            change LazyRevealProbe.RawResult.done valuesState valuesRemaining
                (some values, valuesCache) ∈ support
              (LazyRevealProbe.runRaw state fuel
                ((peekPositionValues
                  [.chain lay tree leafIdx chainIdx previous]).run cache)) at hvalues
            rw [peekPositionValues, StateT.run_bind, LazyRevealProbe.runRaw_bind,
              mem_support_bind_iff] at hvalues
            obtain ⟨peekRaw, hpeek, hvaluesRest⟩ := hvalues
            cases peekRaw with
            | stopped hit => simp at hvaluesRest
            | done peekState peekRemaining peekResult =>
                rcases peekResult with ⟨peekValue, peekCache⟩
                cases peekValue with
                | none => simp [LazyRevealProbe.runRaw] at hvaluesRest
                | some value =>
                    have hvalue := mem_runRaw_peekCoordinate_some
                      (.position (.chain lay tree leafIdx chainIdx previous)) state peekState
                        cache peekCache fuel peekRemaining value hpeek
                    refine ⟨⟨.position (.chain lay tree leafIdx chainIdx previous), 0⟩,
                      ?_, trivial, hvalue.2.2.2⟩
                    simp only [Probe.outputCoordinate]
                    rw [dif_pos (by dsimp [previous]; omega)]
                    congr 3
                    dsimp [previous]
                    omega

theorem preservesChainValid_revealPublishOrdinary
    (allowed : Coordinate → Prop) (coordinate : Coordinate) (input : HashInput)
    (hallowed : IsChainCoordinate coordinate → allowed coordinate) :
    PreservesChainValid allowed (do
      let output ← revealCoordinateOutput coordinate
      publishCoordinate coordinate
      modify fun cache : SplitHashCache =>
        Function.update cache (.ordinary input) (some output)
      pure output) := by
  intro state cache fuel finalState remaining value finalCache hvalid hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hreveal, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done revealState revealRemaining revealResult =>
      rcases revealResult with ⟨revealedOutput, revealCache⟩
      have hrevealShape :
          (state.values coordinate ≠ none ∧ revealState = state) ∨
            ∃ output, revealState = state.materialize coordinate output := by
        rw [revealCoordinateOutput_run, LazyRevealProbe.revealQuery,
          LazyRevealProbe.runRaw_reveal_query_bind] at hreveal
        cases hvalue : state.values coordinate with
        | some existing =>
            rw [hvalue] at hreveal
            simp [LazyRevealProbe.runRaw] at hreveal
            rcases hreveal with ⟨rfl, rfl, rfl, rfl⟩
            exact Or.inl ⟨by simp, rfl⟩
        | none =>
            rw [hvalue, mem_support_bind_iff] at hreveal
            obtain ⟨output, _, hsampled⟩ := hreveal
            by_cases hhit : state.hitAt coordinate output
            · rw [if_pos hhit] at hsampled
              simp at hsampled
            · rw [if_neg hhit] at hsampled
              simp [LazyRevealProbe.runRaw] at hsampled
              rcases hsampled with ⟨rfl, rfl, rfl, rfl⟩
              exact Or.inr ⟨revealedOutput, rfl⟩
      simp only at hrest
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hrest
      obtain ⟨publishRaw, hpublish, hfinish⟩ := hrest
      cases publishRaw with
      | stopped hit => simp at hfinish
      | done publishState publishRemaining publishResult =>
          rcases publishResult with ⟨publishedUnit, publishCache⟩
          change LazyRevealProbe.RawResult.done publishState publishRemaining
              (publishedUnit, publishCache) ∈ support
            (LazyRevealProbe.runRaw revealState revealRemaining
              (LazyRevealProbe.publishQuery coordinate >>= fun output =>
                pure (output, revealCache))) at hpublish
          rw [LazyRevealProbe.publishQuery,
            LazyRevealProbe.runRaw_publish_query_bind] at hpublish
          simp [LazyRevealProbe.runRaw] at hpublish
          rcases hpublish with ⟨rfl, rfl, rfl, rfl⟩
          simp [StateT.run_modify, LazyRevealProbe.runRaw] at hfinish
          rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
          rcases hrevealShape with ⟨hvalue, rfl⟩ | ⟨output, rfl⟩
          · exact hvalid.publish coordinate hvalue hallowed
          · exact hvalid.materialize_publish coordinate output hallowed

theorem preservesChainValid_resolveKnownInput
    (allowed : Coordinate → Prop) (hclosed : ChainForwardClosed allowed)
    (parameter : PublicParameter) (coordinate : Coordinate) (input : HashInput) :
    PreservesChainValid allowed (resolveKnownInput parameter coordinate input) := by
  intro state cache fuel finalState remaining value finalCache hvalid hresult
  unfold resolveKnownInput at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hpeek, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done peekState peekRemaining peekResult =>
      rcases peekResult with ⟨known, peekCache⟩
      simp only at hrest
      have hpeekValid := preservesChainValid_peekTableInput allowed parameter coordinate state cache
        fuel peekState peekRemaining known peekCache hvalid hpeek
      cases known with
      | none =>
          simp only at hrest
          exact preservesChainValid_splitHashQuery_ordinary allowed input peekState peekCache
            peekRemaining finalState remaining value finalCache hpeekValid hrest
      | some knownInput =>
          simp only at hrest
          by_cases heq : knownInput = input
          · rw [if_pos heq] at hrest
            have hallowed : IsChainCoordinate coordinate → allowed coordinate := by
              intro hchain
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  simp [peekTableInput, LazyRevealProbe.runRaw] at hpeek
              | position position =>
                  cases position with
                  | chain lay tree leafIdx chainIdx step =>
                      obtain ⟨candidate, houtput, hsourceChain, hsourceValue⟩ :=
                        mem_runRaw_peekTableInput_chain_some_imp_source parameter state peekState
                          cache peekCache fuel peekRemaining lay tree leafIdx chainIdx step
                            knownInput hpeek
                      have hsourceValid := hvalid candidate.coordinate hsourceChain
                      have hsourceAllowed := hsourceValid.2.2 (hsourceValid.1 hsourceValue)
                      exact houtput ▸ hclosed candidate hsourceAllowed (houtput.symm ▸ hchain)
                  | leaf => simp [IsChainCoordinate] at hchain
                  | node => simp [IsChainCoordinate] at hchain
                  | ftsLeaf => simp [IsChainCoordinate] at hchain
                  | ftsNode => simp [IsChainCoordinate] at hchain
                  | ftsRoots => simp [IsChainCoordinate] at hchain
            exact preservesChainValid_revealPublishOrdinary allowed coordinate input hallowed
              peekState peekCache peekRemaining finalState remaining value finalCache hpeekValid hrest
          · rw [if_neg heq] at hrest
            exact preservesChainValid_splitHashQuery_ordinary allowed input peekState peekCache
              peekRemaining finalState remaining value finalCache hpeekValid hrest

theorem preservesChainValid_probingHashQuery
    (allowed : Coordinate → Prop) (hclosed : ChainForwardClosed allowed)
    (parameter : PublicParameter) (input : HashInput) :
    PreservesChainValid allowed (probingHashQuery parameter input) := by
  unfold probingHashQuery
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      exact (preservesChainValid_probe allowed candidate).bind fun _ =>
        preservesChainValid_resolveKnownInput allowed hclosed parameter
          candidate.outputCoordinate input
  | none =>
      cases hposition : decodePosition? parameter input with
      | none => exact preservesChainValid_splitHashQuery_ordinary allowed input
      | some position =>
          cases position with
          | chain lay tree leafIdx chainIdx step =>
              exact preservesChainValid_resolveKnownInput allowed hclosed parameter
                (.position (.chain lay tree leafIdx chainIdx step)) input
          | leaf lay tree leafIdx =>
              exact preservesChainValid_resolveKnownInput allowed hclosed parameter
                (.position (.leaf lay tree leafIdx)) input
          | node lay tree level nodeIdx =>
              exact preservesChainValid_resolveKnownInput allowed hclosed parameter
                (.position (.node lay tree level nodeIdx)) input
          | ftsLeaf | ftsNode | ftsRoots =>
              exact preservesChainValid_splitHashQuery_ordinary allowed input

theorem preservesChainValid_splitUniformImpl (allowed : Coordinate → Prop) (n : Nat) :
    PreservesChainValid allowed (splitUniformImpl n) := by
  intro state cache fuel finalState remaining value finalCache hvalid hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.uniformQuery n >>= fun output => pure (output, cache))) at hresult
  rw [LazyRevealProbe.uniformQuery, LazyRevealProbe.runRaw_uniform_query_bind,
    mem_support_bind_iff] at hresult
  obtain ⟨output, _, hdone⟩ := hresult
  simp [LazyRevealProbe.runRaw] at hdone
  rcases hdone with ⟨rfl, rfl, rfl, rfl⟩
  exact hvalid

def PreservesChainValidImpl {spec : OracleSpec ι} (allowed : Coordinate → Prop)
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)))) : Prop :=
  ∀ query, PreservesChainValid allowed (impl query)

theorem PreservesChainValidImpl.simulateQ {spec : OracleSpec ι}
    {allowed : Coordinate → Prop}
    {impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)))}
    (himpl : PreservesChainValidImpl allowed impl) (computation : OracleComp spec alpha) :
    PreservesChainValid allowed (simulateQ impl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact preservesChainValid_pure allowed value
  | query_bind query next ih =>
      rw [simulateQ_query_bind]
      exact (himpl query).bind ih

theorem preservesChainValidImpl_ordinaryHashImpl (allowed : Coordinate → Prop) :
    PreservesChainValidImpl allowed ordinaryHashImpl := by
  intro input
  exact preservesChainValid_splitHashQuery_ordinary allowed input

theorem preservesChainValidImpl_splitUniformImpl (allowed : Coordinate → Prop) :
    PreservesChainValidImpl allowed splitUniformImpl :=
  preservesChainValid_splitUniformImpl allowed

theorem preservesChainValidImpl_ordinaryRomImpl (allowed : Coordinate → Prop) :
    PreservesChainValidImpl allowed ordinaryRomImpl := by
  intro query
  cases query with
  | inl query => exact preservesChainValidImpl_splitUniformImpl allowed query
  | inr query => exact preservesChainValidImpl_ordinaryHashImpl allowed query

theorem preservesChainValidImpl_probingHashImpl
    (allowed : Coordinate → Prop) (hclosed : ChainForwardClosed allowed)
    (parameter : PublicParameter) :
    PreservesChainValidImpl allowed (probingHashImpl parameter) :=
  preservesChainValid_probingHashQuery allowed hclosed parameter

theorem preservesChainValidImpl_probingRomImpl
    (allowed : Coordinate → Prop) (hclosed : ChainForwardClosed allowed)
    (parameter : PublicParameter) :
    PreservesChainValidImpl allowed (probingRomImpl parameter) := by
  intro query
  cases query with
  | inl query => exact preservesChainValidImpl_splitUniformImpl allowed query
  | inr query => exact preservesChainValidImpl_probingHashImpl allowed hclosed parameter query

theorem preservesChainValid_sequenceFin (allowed : Coordinate → Prop) {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (hcomputation : ∀ index, PreservesChainValid allowed (computation index)) :
    PreservesChainValid allowed (sequenceFin computation) := by
  induction n with
  | zero =>
      simp only [sequenceFin]
      exact preservesChainValid_pure allowed Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomputation 0).bind fun head =>
        (ih (fun index => computation index.succ)
          (fun index => hcomputation index.succ)).bind fun tail =>
            preservesChainValid_pure allowed (Fin.cases head tail : Fin (n + 1) → alpha)

theorem mem_runRaw_revealCoordinate_state
    (coordinate : Coordinate) (state finalState : LazyRevealProbe.State Coordinate)
    (fuel remaining : Nat) (cache finalCache : SplitHashCache) (value : Digest)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel ((revealCoordinate coordinate).run cache))) :
    (state.values coordinate ≠ none ∧ finalState = state) ∨
      ∃ output, finalState = state.materialize coordinate output := by
  rw [revealCoordinate_run, LazyRevealProbe.revealQuery,
    LazyRevealProbe.runRaw_reveal_query_bind] at hresult
  cases hvalue : state.values coordinate with
  | some existing =>
      rw [hvalue] at hresult
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact Or.inl ⟨by simp, rfl⟩
  | none =>
      rw [hvalue, mem_support_bind_iff] at hresult
      obtain ⟨sampled, _, hsampled⟩ := hresult
      by_cases hhit : state.hitAt coordinate sampled
      · rw [if_pos hhit] at hsampled
        simp at hsampled
      · rw [if_neg hhit] at hsampled
        simp [LazyRevealProbe.runRaw] at hsampled
        rcases hsampled with ⟨rfl, rfl, rfl, rfl⟩
        exact Or.inr ⟨sampled, rfl⟩

theorem preservesChainValid_revealCoordinate_of_not_chain
    (allowed : Coordinate → Prop) (coordinate : Coordinate)
    (hnotChain : ¬IsChainCoordinate coordinate) :
    PreservesChainValid allowed (revealCoordinate coordinate) := by
  intro state cache fuel finalState remaining value finalCache hvalid hresult
  rcases mem_runRaw_revealCoordinate_state coordinate state finalState fuel remaining cache
    finalCache value hresult with ⟨hvalue, rfl⟩ | ⟨output, rfl⟩
  · exact hvalid
  · exact hvalid.materialize_of_not_chain coordinate output hnotChain

theorem preservesChainValid_ensureFullChain (allowed : Coordinate → Prop)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    PreservesChainValid allowed (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  exact (preservesChainValid_sequenceFin allowed _ fun step =>
    preservesChainValid_ensureCoordinate allowed
      (.position (.chain lay tree leafIdx chainIdx step))).bind fun _ =>
        preservesChainValid_pure allowed ()

theorem preservesChainValid_ensureChainPrefix (allowed : Coordinate → Prop)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (digit : Digit) :
    PreservesChainValid allowed (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  unfold ensureChainPrefix
  exact (preservesChainValid_sequenceFin allowed _ fun step => by
    split
    · exact preservesChainValid_ensureCoordinate allowed
        (.position (.chain lay tree leafIdx chainIdx step))
    · exact preservesChainValid_pure allowed ()).bind fun _ =>
      preservesChainValid_pure allowed ()

theorem preservesChainValid_ensureOtsLeaf (allowed : Coordinate → Prop)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    PreservesChainValid allowed (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  exact (preservesChainValid_sequenceFin allowed _ fun chainIdx =>
    preservesChainValid_ensureFullChain allowed lay tree leafIdx chainIdx).bind fun _ =>
      preservesChainValid_ensureCoordinate allowed (.position (.leaf lay tree leafIdx))

theorem preservesChainValid_ensureTreeNode (allowed : Coordinate → Prop)
    (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx, PreservesChainValid allowed (ensureTreeNode lay tree level nodeIdx)
  | 0, nodeIdx => preservesChainValid_ensureOtsLeaf allowed lay tree (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      exact (preservesChainValid_ensureTreeNode allowed lay tree level (2 * nodeIdx)).bind
        fun _ =>
          (preservesChainValid_ensureTreeNode allowed lay tree level
            (2 * nodeIdx + 1)).bind fun _ => by
              split
              · exact preservesChainValid_ensureCoordinate allowed _
              · exact preservesChainValid_pure allowed ()

theorem preservesChainValid_maskedTreeNode (allowed : Coordinate → Prop)
    (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat) :
    PreservesChainValid allowed (maskedTreeNode lay tree level nodeIdx) := by
  cases level with
  | zero =>
      rw [maskedTreeNode]
      exact (preservesChainValid_ensureTreeNode allowed lay tree 0 nodeIdx).bind fun _ =>
        preservesChainValid_revealCoordinate_of_not_chain allowed
          (.position (.leaf lay tree (leafOfNat nodeIdx))) (by simp [IsChainCoordinate])
  | succ current =>
      rw [maskedTreeNode]
      exact (preservesChainValid_ensureTreeNode allowed lay tree (current + 1) nodeIdx).bind
        fun _ => by
          by_cases hlevel : current < maxLayerHeight
          · rw [dif_pos hlevel]
            exact preservesChainValid_revealCoordinate_of_not_chain allowed
              (.position (.node lay tree ⟨current, hlevel⟩ (leafOfNat nodeIdx)))
                (by simp [IsChainCoordinate])
          · rw [dif_neg hlevel]
            exact preservesChainValid_pure allowed 0

theorem preservesChainValid_maskedTreeRoot (allowed : Coordinate → Prop)
    (lay : Layer) (tree : TreeIndex) :
    PreservesChainValid allowed (maskedTreeRoot lay tree) :=
  preservesChainValid_maskedTreeNode allowed lay tree (layerHeight lay) 0

theorem preservesChainValid_ensureTreePath (allowed : Coordinate → Prop)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    PreservesChainValid allowed (ensureTreePath lay tree leafIdx) := by
  unfold ensureTreePath
  exact (preservesChainValid_sequenceFin allowed _ fun level => by
    split
    · exact preservesChainValid_ensureTreeNode allowed lay tree level.val
        (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
    · exact preservesChainValid_pure allowed ()).bind fun _ =>
      preservesChainValid_pure allowed ()

theorem preservesChainValid_maskedOtsSignFrom (allowed : Coordinate → Prop)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) : ∀ attempts counter,
    PreservesChainValid allowed
      (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
  | 0, counter => preservesChainValid_pure allowed none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom]
      exact ((preservesChainValidImpl_ordinaryHashImpl allowed).simulateQ
        (encode parameter lay tree leafIdx message
          (BitVec.ofNat counterBits counter))).bind fun encoded =>
            match encoded with
            | none => preservesChainValid_maskedOtsSignFrom allowed parameter lay tree leafIdx
                message attempts (counter + 1)
            | some encoding =>
                (preservesChainValid_sequenceFin allowed _ fun chainIdx =>
                  preservesChainValid_ensureChainPrefix allowed lay tree leafIdx chainIdx
                    (encoding chainIdx)).bind fun _ =>
                      preservesChainValid_pure allowed
                        (some (BitVec.ofNat counterBits counter, encoding))

theorem preservesChainValid_maskedOtsSign (allowed : Coordinate → Prop)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) :
    PreservesChainValid allowed (maskedOtsSign parameter lay tree leafIdx message) :=
  preservesChainValid_maskedOtsSignFrom allowed parameter lay tree leafIdx message
    encodingAttemptLimit 0

theorem preservesChainValid_maskedLayerMessage (allowed : Coordinate → Prop)
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) :
    PreservesChainValid allowed (maskedLayerMessage parameter ftsSecret index lay) := by
  unfold maskedLayerMessage
  split
  · exact preservesChainValid_maskedTreeRoot allowed _ _
  · exact (preservesChainValidImpl_ordinaryHashImpl allowed).simulateQ
      (ftsKey parameter index (ftsSecret index))

theorem preservesChainValid_maskedSignLayer (allowed : Coordinate → Prop)
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) :
    PreservesChainValid allowed (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayer
  exact (preservesChainValid_maskedLayerMessage allowed parameter ftsSecret index lay).bind
    fun message =>
      (preservesChainValid_maskedOtsSign allowed parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) message).bind fun result =>
          match result with
          | none => preservesChainValid_pure allowed none
          | some part =>
              (preservesChainValid_ensureTreePath allowed lay (treeIndexAt index lay)
                (leafIndexAt index lay)).bind fun _ =>
                  preservesChainValid_pure allowed (some part)

theorem preservesChainValid_revealPublishedCoordinate
    (allowed : Coordinate → Prop) (coordinate : Coordinate)
    (hallowed : IsChainCoordinate coordinate → allowed coordinate) :
    PreservesChainValid allowed (revealPublishedCoordinate coordinate) := by
  intro state cache fuel finalState remaining value finalCache hvalid hresult
  unfold revealPublishedCoordinate at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hreveal, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done revealState revealRemaining revealResult =>
    rcases revealResult with ⟨revealedValue, revealCache⟩
    have hrevealShape :
        (state.values coordinate ≠ none ∧ revealState = state) ∨
          ∃ output, revealState = state.materialize coordinate output := by
      change LazyRevealProbe.RawResult.done revealState revealRemaining
          (revealedValue, revealCache) ∈ support
        (LazyRevealProbe.runRaw state fuel ((revealCoordinate coordinate).run cache)) at hreveal
      rw [revealCoordinate_run, LazyRevealProbe.revealQuery,
        LazyRevealProbe.runRaw_reveal_query_bind] at hreveal
      cases hvalue : state.values coordinate with
      | some existing =>
          rw [hvalue] at hreveal
          simp [LazyRevealProbe.runRaw] at hreveal
          rcases hreveal with ⟨rfl, rfl, rfl, rfl⟩
          exact Or.inl ⟨by simp, rfl⟩
      | none =>
          rw [hvalue, mem_support_bind_iff] at hreveal
          obtain ⟨sampled, _, hsampled⟩ := hreveal
          by_cases hhit : state.hitAt coordinate sampled
          · rw [if_pos hhit] at hsampled
            simp at hsampled
          · rw [if_neg hhit] at hsampled
            simp [LazyRevealProbe.runRaw] at hsampled
            rcases hsampled with ⟨rfl, rfl, rfl, rfl⟩
            exact Or.inr ⟨sampled, rfl⟩
    simp only at hrest
    rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hrest
    obtain ⟨publishRaw, hpublish, hfinish⟩ := hrest
    cases publishRaw with
    | stopped hit => simp at hfinish
    | done publishState publishRemaining publishResult =>
      rcases publishResult with ⟨publishedUnit, publishCache⟩
      change LazyRevealProbe.RawResult.done publishState publishRemaining
          (publishedUnit, publishCache) ∈ support
        (LazyRevealProbe.runRaw revealState revealRemaining
          (LazyRevealProbe.publishQuery coordinate >>= fun output =>
            pure (output, revealCache))) at hpublish
      rw [LazyRevealProbe.publishQuery,
        LazyRevealProbe.runRaw_publish_query_bind] at hpublish
      simp [LazyRevealProbe.runRaw] at hpublish
      rcases hpublish with ⟨rfl, rfl, rfl, rfl⟩
      simp [LazyRevealProbe.runRaw] at hfinish
      rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
      rcases hrevealShape with ⟨hvalue, rfl⟩ | ⟨output, rfl⟩
      · exact hvalid.publish coordinate hvalue hallowed
      · exact hvalid.materialize_publish coordinate output hallowed

theorem preservesChainValid_revealLayerValues (allowed : Coordinate → Prop)
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit)
    (hallowed : ∀ chainIdx, allowed (chainValueCoordinate lay (treeIndexAt index lay)
      (leafIndexAt index lay) chainIdx (encoding chainIdx))) :
    PreservesChainValid allowed (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  exact (preservesChainValid_sequenceFin allowed _ fun chainIdx =>
    preservesChainValid_revealPublishedCoordinate allowed
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay)
        chainIdx (encoding chainIdx)) (fun _ => hallowed chainIdx)).bind fun values =>
      (preservesChainValid_sequenceFin allowed _ fun level => by
        split
        · cases hlevelValue : level.val with
          | zero =>
              exact preservesChainValid_revealPublishedCoordinate allowed _
                (by simp [IsChainCoordinate])
          | succ current =>
              rw [show current + 1 = Nat.succ current by omega]
              change PreservesChainValid allowed
                (if hlevel : current < maxLayerHeight then
                  revealPublishedCoordinate (.position (.node lay (treeIndexAt index lay)
                    ⟨current, hlevel⟩ (leafOfNat
                      (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
                else pure 0)
              by_cases hlevel : current < maxLayerHeight
              · rw [dif_pos hlevel]
                exact preservesChainValid_revealPublishedCoordinate allowed _
                  (by simp [IsChainCoordinate])
              · rw [dif_neg hlevel]
                exact preservesChainValid_pure allowed 0
        · exact preservesChainValid_pure allowed 0).bind fun path =>
          preservesChainValid_pure allowed (values, path)

def PublishedChainCoordinate (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec) (coordinate : Coordinate) : Prop :=
  ∃ (entry : (request : SignRequest) × SigningSpec.Range request) (signature : Signature)
      (index : Index) (leaves : DigestTree → FtsLeaf) (lay : Layer) (chainIdx : ChainIndex)
      (codeword : Encoding),
    entry ∈ signingLog
      ∧ entry.2 = some signature
      ∧ SuccessfulSignRun f cache secretKey entry.1 signature
      ∧ SuccessfulDigestRun f cache secretKey entry.1 signature.randomness index leaves
      ∧ evalWithAnswerFn f (encode secretKey.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) (evalWithAnswerFn f (layerMessage secretKey index lay))
        (signature.counter lay)) = some codeword
      ∧ coordinate = chainValueCoordinate lay (treeIndexAt index lay)
        (leafIndexAt index lay) chainIdx (codeword chainIdx)

def CoveredChainCoordinate (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec) (coordinate : Coordinate) : Prop :=
  ∃ (entry : (request : SignRequest) × SigningSpec.Range request) (signature : Signature)
      (index : Index) (leaves : DigestTree → FtsLeaf) (lay : Layer) (chainIdx : ChainIndex)
      (codeword : Encoding) (targetDigit : Digit),
    entry ∈ signingLog
      ∧ entry.2 = some signature
      ∧ SuccessfulSignRun f cache secretKey entry.1 signature
      ∧ SuccessfulDigestRun f cache secretKey entry.1 signature.randomness index leaves
      ∧ evalWithAnswerFn f (encode secretKey.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) (evalWithAnswerFn f (layerMessage secretKey index lay))
        (signature.counter lay)) = some codeword
      ∧ (codeword chainIdx).val ≤ targetDigit.val
      ∧ coordinate = chainValueCoordinate lay (treeIndexAt index lay)
        (leafIndexAt index lay) chainIdx targetDigit

theorem PublishedChainCoordinate.covered
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {coordinate : Coordinate}
    (hpublished : PublishedChainCoordinate f cache secretKey signingLog coordinate) :
    CoveredChainCoordinate f cache secretKey signingLog coordinate := by
  obtain ⟨entry, signature, index, leaves, lay, chainIdx, codeword, hentry, hresponse,
    hrun, hdigest, hencode, hcoordinate⟩ := hpublished
  exact ⟨entry, signature, index, leaves, lay, chainIdx, codeword, codeword chainIdx,
    hentry, hresponse, hrun, hdigest, hencode, le_rfl, hcoordinate⟩

theorem CoveredChainCoordinate.forward
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {lay : Layer} {tree : TreeIndex}
    {leafIdx : LeafIndex} {chainIdx : ChainIndex} {digit later : Digit}
    (hcovered : CoveredChainCoordinate f cache secretKey signingLog
      (chainValueCoordinate lay tree leafIdx chainIdx digit))
    (hle : digit.val ≤ later.val) :
    CoveredChainCoordinate f cache secretKey signingLog
      (chainValueCoordinate lay tree leafIdx chainIdx later) := by
  obtain ⟨entry, signature, index, leaves, publishedLay, publishedChain, codeword,
    targetDigit, hentry, hresponse, hrun, hdigest, hencode, hpublishedLe,
    hcoordinate⟩ := hcovered
  have hparts := chainValueCoordinate_injective hcoordinate
  obtain ⟨rfl, htree, hleaf, rfl, hdigit⟩ := hparts
  subst targetDigit
  exact ⟨entry, signature, index, leaves, lay, chainIdx, codeword, later, hentry, hresponse,
    hrun, hdigest, hencode, hpublishedLe.trans hle, by rw [htree, hleaf]⟩

theorem CoveredChainCoordinate.outputCoordinate
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {probe : Probe}
    (hcovered : CoveredChainCoordinate f cache secretKey signingLog probe.coordinate)
    (hchain : IsChainCoordinate probe.outputCoordinate) :
    CoveredChainCoordinate f cache secretKey signingLog probe.outputCoordinate := by
  rcases probe with ⟨coordinate, candidate⟩
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      let digit : Digit := ⟨0, by norm_num [chainLength, winternitzBits]⟩
      let later : Digit := ⟨1, by norm_num [chainLength, winternitzBits]⟩
      have hstart : chainValueCoordinate lay tree leafIdx chainIdx digit =
          .chainStart lay tree leafIdx chainIdx := by
        simp [chainValueCoordinate, digit]
      have hnext : chainValueCoordinate lay tree leafIdx chainIdx later =
          .position (.chain lay tree leafIdx chainIdx
            ⟨0, by norm_num [chainLength, winternitzBits]⟩) := by
        simp [chainValueCoordinate, later]
      change CoveredChainCoordinate f cache secretKey signingLog
        (.chainStart lay tree leafIdx chainIdx) at hcovered
      rw [← hstart] at hcovered
      have hforward := CoveredChainCoordinate.forward (digit := digit) (later := later)
        hcovered (by norm_num [digit, later])
      change CoveredChainCoordinate f cache secretKey signingLog
        (.position (.chain lay tree leafIdx chainIdx
          ⟨0, by norm_num [chainLength, winternitzBits]⟩))
      rw [← hnext]
      exact hforward
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          by_cases hnext : step.val + 1 < chainLength - 1
          · let digit : Digit := ⟨step.val + 1, by
                have := step.isLt
                omega⟩
            let later : Digit := ⟨step.val + 2, by omega⟩
            have hcurrent : chainValueCoordinate lay tree leafIdx chainIdx digit =
                .position (.chain lay tree leafIdx chainIdx step) := by
              unfold chainValueCoordinate
              rw [dif_neg (by simp [digit])]
              congr 3
            have houtput : chainValueCoordinate lay tree leafIdx chainIdx later =
                .position (.chain lay tree leafIdx chainIdx
                  ⟨step.val + 1, hnext⟩) := by
              unfold chainValueCoordinate
              rw [dif_neg (by simp [later])]
              congr 3
            change CoveredChainCoordinate f cache secretKey signingLog
              (.position (.chain lay tree leafIdx chainIdx step)) at hcovered
            rw [← hcurrent] at hcovered
            have hforward := CoveredChainCoordinate.forward (digit := digit) (later := later)
              hcovered (by norm_num [digit, later])
            change CoveredChainCoordinate f cache secretKey signingLog
              (if _hnext : step.val + 1 < chainLength - 1 then
                .position (.chain lay tree leafIdx chainIdx ⟨step.val + 1, _hnext⟩)
              else .position (.leaf lay tree leafIdx))
            rw [dif_pos hnext, ← houtput]
            exact hforward
          · simp [Probe.outputCoordinate, hnext, IsChainCoordinate] at hchain
      | leaf => simp [Probe.outputCoordinate, IsChainCoordinate] at hchain
      | node => simp [Probe.outputCoordinate, IsChainCoordinate] at hchain
      | ftsLeaf => simp [Probe.outputCoordinate, IsChainCoordinate] at hchain
      | ftsNode => simp [Probe.outputCoordinate, IsChainCoordinate] at hchain
      | ftsRoots => simp [Probe.outputCoordinate, IsChainCoordinate] at hchain

theorem coveredChainCoordinate_forwardClosed
    (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (signingLog : QueryLog SigningSpec) :
    ChainForwardClosed (CoveredChainCoordinate f cache secretKey signingLog) := by
  intro candidate hcovered hchain
  exact hcovered.outputCoordinate hchain

theorem PublishedChainCoordinate.signedLayerAt
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {coordinate : Coordinate}
    (hpublished : PublishedChainCoordinate f cache secretKey signingLog coordinate) :
    ∃ lay tree leafIdx, SignedLayerAt f cache secretKey signingLog lay tree leafIdx := by
  obtain ⟨entry, signature, index, leaves, lay, chainIdx, codeword, hentry, hresponse,
    hrun, hdigest, hencode, hcoordinate⟩ := hpublished
  obtain ⟨hmessage, hopening⟩ := hrun.honest_layer_at_of_digest hdigest lay
  have hcached := hrun.signed_encode_cached_of_digest hdigest lay
  exact ⟨lay, treeIndexAt index lay, leafIndexAt index lay, entry, signature, index, leaves,
    hentry, hresponse, hrun, hdigest, rfl, rfl, hmessage, hcached, hopening⟩

theorem ForgedFreshLayerOpening.exists_uncovered_matching_probe
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index} {signature : Signature}
    (hfresh : ForgedFreshLayerOpening f cache secretKey signingLog index signature) :
    ∃ (probe : Probe) (input : HashInput),
      probe.Hits f secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
        ∧ probe.MatchesInput secretKey.parameter input
        ∧ cache input ≠ none
        ∧ ¬CoveredChainCoordinate f cache secretKey signingLog probe.coordinate := by
  obtain ⟨valueProbe, input, hhit, hnotSigned, hmatch, hcached⟩ :=
    hfresh.toFreshLayerOpening.exists_hit_probe_cached
  refine ⟨toProbe valueProbe, input, toProbe_hits hhit,
    toProbe_matchesInput secretKey.parameter valueProbe input hmatch, hcached, ?_⟩
  intro hcovered
  obtain ⟨entry, publishedSignature, publishedIndex, leaves, publishedLay, chainIdx,
    codeword, targetDigit, hentry, hresponse, hrun, hdigest, hencode, hle,
    hcoordinate⟩ := hcovered
  obtain ⟨hmessage, hopening⟩ := hrun.honest_layer_at_of_digest hdigest publishedLay
  have hcachedEncode := hrun.signed_encode_cached_of_digest hdigest publishedLay
  have hsigned : SignedLayerAt f cache secretKey signingLog publishedLay
      (treeIndexAt publishedIndex publishedLay) (leafIndexAt publishedIndex publishedLay) :=
    ⟨entry, publishedSignature, publishedIndex, leaves, hentry, hresponse, hrun, hdigest,
      rfl, rfl, hmessage, hcachedEncode, hopening⟩
  have hparts := chainValueCoordinate_injective
    (hcoordinate.symm.trans (toProbe_coordinate valueProbe))
  exact hnotSigned (hparts.1 ▸ hparts.2.1 ▸ hparts.2.2.1 ▸ hsigned)

theorem ForgedBackwardChainOpening.exists_uncovered_matching_probe
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {forgedIndex : Index}
    {forgedSignature : Signature}
    (hbackward : ForgedBackwardChainOpening f cache secretKey signingLog forgedIndex
      forgedSignature) :
    ∃ (probe : Probe) (input : HashInput),
      probe.Hits f secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
        ∧ probe.MatchesInput secretKey.parameter input
        ∧ cache input ≠ none
        ∧ ¬CoveredChainCoordinate f cache secretKey signingLog probe.coordinate := by
  obtain ⟨lay, forgedMessage, entry, signedSignature, signedIndex, leaves, signedCodeword,
    forgedCodeword, hforgedOpening, hforgedRun, hentry, hresponse, hsignRun, hdigest,
    htree, hleaf, hmessage, hsignedOpening, hsignedCached, hsigned, hforged,
    chainIdx, hlt⟩ := hbackward
  obtain ⟨openingCodeword, hopeningEncode, hforgedValues, hpath⟩ := hforgedOpening
  have hopeningCodeword : openingCodeword = forgedCodeword :=
    Option.some.inj (hopeningEncode.symm.trans hforged)
  let valueProbe : OtsValueProbe :=
    ⟨lay, treeIndexAt forgedIndex lay, leafIndexAt forgedIndex lay, chainIdx,
      forgedCodeword chainIdx, forgedSignature.chainValue lay chainIdx⟩
  have hhit : valueProbe.Hits f secretKey.parameter secretKey.otsSecret := by
    simpa only [OtsValueProbe.Hits, OtsValueProbe.target, valueProbe,
      hopeningCodeword] using hforgedValues chainIdx
  have hdigit : (forgedCodeword chainIdx).val < chainLength - 1 := by
    have hsignedLt := (signedCodeword chainIdx).isLt
    omega
  have hopeningDigit : (openingCodeword chainIdx).val < chainLength - 1 := by
    rw [hopeningCodeword]
    exact hdigit
  let step : ChainStep := ⟨(openingCodeword chainIdx).val, hopeningDigit⟩
  let input := tweakableHashInput secretKey.parameter
    (.chain lay (treeIndexAt forgedIndex lay) (leafIndexAt forgedIndex lay) chainIdx step)
    (digestBytes (forgedSignature.chainValue lay chainIdx))
  have hquery : input ∈ queriedInputs f
      (otsLeaf secretKey.parameter lay (treeIndexAt forgedIndex lay)
        (leafIndexAt forgedIndex lay) forgedMessage (forgedSignature.counter lay)
        (forgedSignature.chainValue lay)) := by
    simpa only [input, step, Nat.add_zero, walkValue, chainWalk,
      evalWithAnswerFn_pure] using
      otsLeaf_chain_query_mem f secretKey.parameter lay (treeIndexAt forgedIndex lay)
        (leafIndexAt forgedIndex lay) forgedMessage (forgedSignature.counter lay)
        (forgedSignature.chainValue lay) openingCodeword hopeningEncode chainIdx 0
        (by omega) hopeningDigit
  have hmatch : (toProbe valueProbe).MatchesInput secretKey.parameter input := by
    apply toProbe_matchesInput secretKey.parameter valueProbe input
    exact Or.inl ⟨step, by simp [valueProbe, step, hopeningCodeword], rfl⟩
  refine ⟨toProbe valueProbe, input, toProbe_hits hhit, hmatch, hforgedRun input hquery, ?_⟩
  intro hcovered
  obtain ⟨publishedEntry, publishedSignature, publishedIndex, publishedLeaves, publishedLay,
    publishedChain, publishedCodeword, targetDigit, hpublishedEntry, hpublishedResponse,
    hpublishedRun, hpublishedDigest, hpublishedEncode, hcoveredDigit, hcoordinate⟩ := hcovered
  have hparts := chainValueCoordinate_injective
    (hcoordinate.symm.trans (toProbe_coordinate valueProbe))
  dsimp only [valueProbe] at hparts
  obtain ⟨hlay, htreePublished, hleafPublished, hchainPublished, htargetDigit⟩ := hparts
  subst publishedLay
  have htreeSame : treeIndexAt publishedIndex lay = treeIndexAt signedIndex lay :=
    htreePublished.trans htree.symm
  have hleafSame : leafIndexAt publishedIndex lay = leafIndexAt signedIndex lay :=
    hleafPublished.trans hleaf.symm
  have hpartsSame := successfulSignRun_layer_ots_eq_of_position_eq hpublishedRun hsignRun
    hpublishedDigest hdigest lay htreeSame hleafSame
  have hlayerMessage := congrArg (evalWithAnswerFn f)
    (layerMessage_eq_of_position_eq secretKey publishedIndex signedIndex lay
      htreeSame hleafSame)
  have hpublishedEncode' := hpublishedEncode
  rw [htreePublished, hleafPublished, hlayerMessage, hpartsSame.1] at hpublishedEncode'
  have hcodeword : publishedCodeword = signedCodeword :=
    Option.some.inj (hpublishedEncode'.symm.trans hsigned)
  subst publishedChain
  rw [hcodeword] at hcoveredDigit
  have hdigitValue := congrArg Fin.val htargetDigit
  omega

end SphincsSecurity.Concrete.OtsProbeSimulation
