import XmssSecurity.CausalEagerHighEventTransfer

open OracleComp OracleSpec

namespace XmssSecurity

set_option maxRecDepth 2000000
set_option linter.constructorNameAsVariable false

attribute [local irreducible]
  FilteredTreeHashProgram.computation
  filteredTreeChainHashComputation
  filteredTreePureHashComputation
  filteredTreeFreshHashComputation
  filteredTreeProbeThenFreshHashComputation

theorem eagerTraceSupport_bind
    (table : ChainValueIndex → Digest)
    (first : OracleComp
      (RevealProbeOracleSimulation.World ChainValueIndex) α)
    (next : α → OracleComp
      (RevealProbeOracleSimulation.World ChainValueIndex) β)
    (head : α ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (tail : β ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hhead : EagerTraceSupport table first head)
    (htail : EagerTraceSupport table (next head.1) tail) :
    EagerTraceSupport table (first >>= next)
      (tail.1, head.2 ++ tail.2) := by
  unfold EagerTraceSupport at hhead htail ⊢
  rw [simulateQ_bind, WriterT.run_bind', support_bind_apply_iff]
  refine ⟨head, hhead, ?_⟩
  rw [support_map_apply_iff]
  exact ⟨tail, htail, rfl⟩

abbrev VerifierHashInputTrace := List HashInput

def verifierHashInputFragment (_input : HashInput) (_output : HashOutput) :
    VerifierHashInputTrace :=
  [_input]

noncomputable def filteredHighHashTracedVerifierImpl
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) :
    QueryImpl HashSpec
      (WriterT VerifierHashInputTrace
        (StateT CausalHashState
          (OracleComp
            (RevealProbeOracleSimulation.World ChainValueIndex)))) :=
  (filteredHighHashOnlyVerifierImpl keyHigh selected).withTraceAppend
    verifierHashInputFragment

def EagerTreeInputProbe
    (parameter : PublicParameter) (selected : ChainIndex) (input : HashInput)
    (index : ChainValueIndex) (target : Digest) : Prop :=
  chainInputProbe? parameter selected input = some (index, target) ∨
    (chainInputProbe? parameter selected input = none ∧
      leafInputProbe? parameter selected input = some (index, target))

def VerifierProbeTraceCovered
    (parameter : PublicParameter) (selected : ChainIndex)
    (hashTrace : VerifierHashInputTrace) (state : CausalHashState)
    (observedTrace :
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) : Prop :=
  ∀ input ∈ hashTrace, ∀ index target,
    EagerTreeInputProbe parameter selected input index target →
    state.revealed index = none →
      RevealProbeOracleSimulation.ObservedAction.probe index target ∈
        observedTrace

set_option maxHeartbeats 2000000 in
theorem filteredTreeHashComputation_support_covers_eager_chain_probe
    (table high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex) (target : Digest)
    (hprobe : chainInputProbe? secretKey.parameter selected input =
      some (index, target))
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredTreeHashComputationAtFromHigh high secretKey selected input
          state)).run))
    (hhidden : result.1.2.revealed index = none) :
    RevealProbeOracleSimulation.ObservedAction.probe index target ∈
      result.2 := by
  have hcomputation :
      filteredTreeHashComputationAtFromHigh high secretKey selected input state =
        filteredProbingAttackerHashQueryAtFromHigh high secretKey selected input
          state (some (index, target)) := by
    rw [filteredTreeHashComputationAtFromHigh_eq_chain _ _ _ _ _ _
      (filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_chainProbe
        high secretKey selected input state (index, target) hprobe)]
    unfold filteredTreeChainHashComputation
    rfl
  rw [hcomputation] at hresult
  have hreplay :=
    simulate_eagerTrace_filteredProbingAttackerHashQueryAtFromHigh_support_replays
      table high secretKey selected input state (some (index, target)) result
        hresult
  have hinitial : state.revealed index = none :=
    hreplay.initial_none_of_final_none index hhidden
  obtain ⟨suffix, hsuffix⟩ :=
    simulate_eagerTrace_filteredProbingAttackerHashQueryAtFromHigh_hidden_support_trace
      table high secretKey selected input state index target hinitial result
        hresult
  rw [hsuffix]
  exact List.mem_cons_self

set_option maxHeartbeats 2000000 in
theorem filteredTreeHashComputation_support_covers_eager_leaf_probe
    (table high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex) (target : Digest)
    (hchain : chainInputProbe? secretKey.parameter selected input = none)
    (hleaf : leafInputProbe? secretKey.parameter selected input =
      some (index, target))
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredTreeHashComputationAtFromHigh high secretKey selected input
          state)).run))
    (hhidden : result.1.2.revealed index = none) :
    RevealProbeOracleSimulation.ObservedAction.probe index target ∈
      result.2 := by
  generalize hprogram : filteredTreeProbingAttackerHashQueryAtFromHigh high
    secretKey selected input state = program
  unfold filteredTreeHashComputationAtFromHigh at hresult
  rw [hprogram] at hresult
  have hinitial : state.revealed index = none :=
    filteredTreeHashProgram_support_initial_none_of_final_none table high
      secretKey selected input state program result hresult index hhidden
  rw [← hprogram] at hresult
  change result ∈ support
    ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (filteredTreeHashComputationAtFromHigh high secretKey selected input
        state)).run) at hresult
  rw [simulate_eagerTrace_filteredTreeLeafQuery_hidden table high secretKey
    selected input state index target hchain hleaf hinitial,
    support_map] at hresult
  obtain ⟨raw, _hraw, rfl⟩ := hresult
  change RevealProbeOracleSimulation.ObservedAction.probe index target ∈
    [RevealProbeOracleSimulation.ObservedAction.probe index target]
  exact List.mem_singleton_self
    (RevealProbeOracleSimulation.ObservedAction.probe index target)

theorem filteredTreeHashComputation_support_covers_eager_probe
    (table high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex) (target : Digest)
    (hprobe : EagerTreeInputProbe secretKey.parameter selected input index
      target)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredTreeHashComputationAtFromHigh high secretKey selected input
          state)).run))
    (hhidden : result.1.2.revealed index = none) :
    RevealProbeOracleSimulation.ObservedAction.probe index target ∈
      result.2 := by
  rcases hprobe with hchain | ⟨hchain, hleaf⟩
  ·
      have hcomputation :
          filteredTreeHashComputationAtFromHigh high secretKey selected input
              state =
            filteredProbingAttackerHashQueryAtFromHigh high secretKey selected
              input state (some (index, target)) := by
        rw [filteredTreeHashComputationAtFromHigh_eq_chain _ _ _ _ _ _
          (filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_chainProbe
            high secretKey selected input state (index, target) hchain)]
        unfold filteredTreeChainHashComputation
        rfl
      rw [hcomputation] at hresult
      have hreplay :=
        simulate_eagerTrace_filteredProbingAttackerHashQueryAtFromHigh_support_replays
          table high secretKey selected input state (some (index, target)) result
            hresult
      have hinitial : state.revealed index = none :=
        hreplay.initial_none_of_final_none index hhidden
      obtain ⟨suffix, hsuffix⟩ :=
        simulate_eagerTrace_filteredProbingAttackerHashQueryAtFromHigh_hidden_support_trace
          table high secretKey selected input state index target hinitial result
            hresult
      rw [hsuffix]
      exact List.mem_cons_self
  ·
      generalize hprogram : filteredTreeProbingAttackerHashQueryAtFromHigh high
        secretKey selected input state = program
      unfold filteredTreeHashComputationAtFromHigh at hresult
      rw [hprogram] at hresult
      have hinitial : state.revealed index = none :=
        filteredTreeHashProgram_support_initial_none_of_final_none table high
          secretKey selected input state program result hresult index hhidden
      rw [← hprogram] at hresult
      change result ∈ support
        ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          (filteredTreeHashComputationAtFromHigh high secretKey selected input
            state)).run) at hresult
      rw [simulate_eagerTrace_filteredTreeLeafQuery_hidden table high secretKey
        selected input state index target hchain hleaf hinitial,
        support_map] at hresult
      obtain ⟨raw, _hraw, rfl⟩ := hresult
      change RevealProbeOracleSimulation.ObservedAction.probe index target ∈
        [RevealProbeOracleSimulation.ObservedAction.probe index target]
      exact List.mem_singleton_self
        (RevealProbeOracleSimulation.ObservedAction.probe index target)

theorem filteredHighHashTracedVerifier_projection
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (computation : OracleComp HashSpec α) :
    Prod.fst <$>
        (simulateQ (filteredHighHashTracedVerifierImpl keyHigh selected)
          computation).run =
      simulateQ (filteredHighHashOnlyVerifierImpl keyHigh selected)
        computation := by
  exact QueryImpl.fst_map_run_withTraceAppend
    (filteredHighHashOnlyVerifierImpl keyHigh selected)
    verifierHashInputFragment computation

theorem VerifierProbeTraceCovered.nil
    (parameter : PublicParameter) (selected : ChainIndex)
    (state : CausalHashState) :
    VerifierProbeTraceCovered parameter selected [] state [] := by
  intro input hinput
  simp at hinput

theorem VerifierProbeTraceCovered.mono_state
    {parameter : PublicParameter} {selected : ChainIndex}
    {hashTrace : VerifierHashInputTrace}
    {initial final : CausalHashState}
    {observedTrace :
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex}
    (hcovered : VerifierProbeTraceCovered parameter selected hashTrace initial
      observedTrace)
    (hmonotone : RevealsMonotone initial.revealed final.revealed) :
    VerifierProbeTraceCovered parameter selected hashTrace final
      observedTrace := by
  intro input hinput index target hprobe hhidden
  exact hcovered input hinput index target hprobe
    (hmonotone index hhidden)

theorem VerifierProbeTraceCovered.append
    {parameter : PublicParameter} {selected : ChainIndex}
    {left right : VerifierHashInputTrace} {state : CausalHashState}
    {leftObserved rightObserved :
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex}
    (hleft : VerifierProbeTraceCovered parameter selected left state
      leftObserved)
    (hright : VerifierProbeTraceCovered parameter selected right state
      rightObserved) :
    VerifierProbeTraceCovered parameter selected (left ++ right) state
      (leftObserved ++ rightObserved) := by
  intro input hinput index target hprobe hhidden
  rcases List.mem_append.mp hinput with hinput | hinput
  · exact List.mem_append_left rightObserved
      (hleft input hinput index target hprobe hhidden)
  · exact List.mem_append_right leftObserved
      (hright input hinput index target hprobe hhidden)

theorem filteredHighHashTracedVerifier_step_eq_map
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (input : HashInput) (state : CausalHashState) :
    (((filteredHighHashTracedVerifierImpl keyHigh selected input).run).run
        state) =
      (fun result =>
        ((result.1, verifierHashInputFragment input result.1), result.2)) <$>
        ((filteredHighHashOnlyVerifierImpl keyHigh selected input).run state) := by
  unfold filteredHighHashTracedVerifierImpl
  rw [QueryImpl.withTraceAppend_apply, WriterT.run_bind',
    WriterT.run_monadLift', StateT.run_bind, StateT.run_map]
  simp [WriterT.run_tell, WriterT.run_pure, map_eq_bind_pure_comp]

theorem simulate_eagerTrace_filteredHighHashTracedVerifier_step_eq_map
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (((filteredHighHashTracedVerifierImpl keyHigh selected input).run).run
        state)).run =
      (fun result =>
        (((result.1.1, verifierHashInputFragment input result.1.1), result.1.2),
          result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((filteredHighHashOnlyVerifierImpl keyHigh selected input).run
            state)).run := by
  rw [filteredHighHashTracedVerifier_step_eq_map, simulateQ_map,
    WriterT.run_map']
  rfl

def FilteredHighVerifierStepSupport
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) : Prop :=
  EagerTraceSupport table
    ((filteredHighHashOnlyVerifierImpl keyHigh selected input).run state)
      result

theorem filteredHighHashOnlyVerifierImpl_run_eq
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) :
    (filteredHighHashOnlyVerifierImpl keyHigh selected input).run state =
      filteredTreeHashComputationAtFromHigh
        (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected input
          state := by
  unfold filteredHighHashOnlyVerifierImpl filteredHighVerifierRun
  rw [StateT.run_mk]

def FilteredHighVerifierStepInvariant
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) : Prop :=
  RevealsMonotone state.revealed result.1.2.revealed ∧
    VerifierProbeTraceCovered keyHigh.1.secretKey.parameter selected [input]
      result.1.2 result.2

def FilteredHighVerifierRunSupport
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (computation : OracleComp HashSpec α)
    (state : CausalHashState)
    (result : (((α × VerifierHashInputTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) : Prop :=
  EagerTraceSupport table
    (((simulateQ (filteredHighHashTracedVerifierImpl keyHigh selected)
      computation).run).run state) result

def FilteredHighVerifierRunInvariant
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (state : CausalHashState)
    (result : (((α × VerifierHashInputTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) : Prop :=
  RevealsMonotone state.revealed result.1.2.revealed ∧
    VerifierProbeTraceCovered keyHigh.1.secretKey.parameter selected
      result.1.1.2 result.1.2 result.2

theorem filteredHighVerifierRunSupport_bind
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (first : OracleComp HashSpec β)
    (next : β → OracleComp HashSpec α) (state : CausalHashState)
    (result : (((α × VerifierHashInputTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : FilteredHighVerifierRunSupport table keyHigh selected
      (first >>= next) state result) :
    ∃ head tail,
      FilteredHighVerifierRunSupport table keyHigh selected first state head ∧
      FilteredHighVerifierRunSupport table keyHigh selected
        (next head.1.1.1) head.1.2 tail ∧
      result = (((tail.1.1.1, head.1.1.2 ++ tail.1.1.2), tail.1.2),
        head.2 ++ tail.2) := by
  unfold FilteredHighVerifierRunSupport EagerTraceSupport at hresult
  simp only [simulateQ_bind, WriterT.run_bind', StateT.run_bind] at hresult
  rw [support_bind_apply_iff] at hresult
  obtain ⟨head, hhead, htail⟩ := hresult
  rw [support_map_apply_iff] at htail
  obtain ⟨tail, htail, rfl⟩ := htail
  rw [StateT.run_map, simulateQ_map, WriterT.run_map',
    support_map_apply_iff] at htail
  obtain ⟨rawTail, hrawTail, rfl⟩ := htail
  simp only [Function.comp_apply, Prod.map, Prod.map_apply, id_eq]
  refine ⟨head, rawTail, ?_, ?_, rfl⟩
  · unfold FilteredHighVerifierRunSupport EagerTraceSupport
    exact hhead
  · unfold FilteredHighVerifierRunSupport EagerTraceSupport
    exact hrawTail

theorem filteredHighVerifierRunSupport_bind_preserves_head_trace
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (first : OracleComp HashSpec β)
    (next : β → OracleComp HashSpec α) (state : CausalHashState)
    (input : HashInput)
    (hfirst : ∀ head,
      FilteredHighVerifierRunSupport table keyHigh selected first state head →
        input ∈ head.1.1.2)
    (result : (((α × VerifierHashInputTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : FilteredHighVerifierRunSupport table keyHigh selected
      (first >>= next) state result) :
    input ∈ result.1.1.2 := by
  obtain ⟨head, tail, hhead, _htail, heq⟩ :=
    filteredHighVerifierRunSupport_bind table keyHigh selected first next state
      result hresult
  rw [heq]
  exact List.mem_append_left tail.1.1.2 (hfirst head hhead)

theorem filteredHighVerifierRunSupport_pure
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (value : α) (state : CausalHashState)
    (result : (((α × VerifierHashInputTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : FilteredHighVerifierRunSupport table keyHigh selected
      (pure value) state result) :
    result = (((value, []), state), []) := by
  unfold FilteredHighVerifierRunSupport EagerTraceSupport at hresult
  simp only [simulateQ_pure, WriterT.run_pure, StateT.run_pure,
    support_pure, Set.mem_singleton_iff] at hresult
  exact hresult

theorem filteredHighVerifierRunSupport_query_trace
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (input : HashInput) (state : CausalHashState)
    (result : (((HashOutput × VerifierHashInputTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : FilteredHighVerifierRunSupport table keyHigh selected
      (HasQuery.query (spec := HashSpec) (m := OracleComp HashSpec) input)
        state result) :
    result.1.1.2 = [input] := by
  unfold FilteredHighVerifierRunSupport EagerTraceSupport at hresult
  rw [HasQuery.instOfMonadLift_query, simulateQ_query] at hresult
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map] at hresult
  rw [simulate_eagerTrace_filteredHighHashTracedVerifier_step_eq_map,
    support_map_apply_iff] at hresult
  obtain ⟨raw, _hraw, rfl⟩ := hresult
  rfl

theorem filteredHighHashTracedVerifier_tweakableHash_eq_map
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (parameter : PublicParameter)
    (domain : HashDomain) (payload : HashInput) (state : CausalHashState) :
    (((simulateQ (filteredHighHashTracedVerifierImpl keyHigh selected)
      (Concrete.tweakableHash parameter domain payload)).run).run state) =
      (fun result =>
        ((truncateHash result.1,
          [tweakableHashInput parameter domain payload]), result.2)) <$>
        ((filteredHighHashOnlyVerifierImpl keyHigh selected
          (tweakableHashInput parameter domain payload)).run state) := by
  unfold Concrete.tweakableHash Concrete.oracleHash
  rw [simulateQ_bind, WriterT.run_bind', StateT.run_bind,
    HasQuery.instOfMonadLift_query, simulateQ_query]
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
  rw [filteredHighHashTracedVerifier_step_eq_map]
  simp [verifierHashInputFragment, WriterT.run_pure, StateT.run_pure,
    map_eq_bind_pure_comp, bind_assoc]

theorem simulate_eagerTrace_filteredHighHashTracedVerifier_tweakableHash_eq_map
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (parameter : PublicParameter)
    (domain : HashDomain) (payload : HashInput) (state : CausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (((simulateQ (filteredHighHashTracedVerifierImpl keyHigh selected)
        (Concrete.tweakableHash parameter domain payload)).run).run state)).run =
      (fun result =>
        (((truncateHash result.1.1,
          [tweakableHashInput parameter domain payload]), result.1.2),
          result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((filteredHighHashOnlyVerifierImpl keyHigh selected
            (tweakableHashInput parameter domain payload)).run state)).run := by
  rw [filteredHighHashTracedVerifier_tweakableHash_eq_map, simulateQ_map,
    WriterT.run_map']
  rfl

theorem filteredHighVerifierRunSupport_tweakableHash_trace_contains
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (parameter : PublicParameter)
    (domain : HashDomain) (payload : HashInput) (state : CausalHashState)
    (result : (((Digest × VerifierHashInputTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : FilteredHighVerifierRunSupport table keyHigh selected
      (Concrete.tweakableHash parameter domain payload) state result) :
    tweakableHashInput parameter domain payload ∈
      result.1.1.2 := by
  unfold FilteredHighVerifierRunSupport EagerTraceSupport at hresult
  rw [simulate_eagerTrace_filteredHighHashTracedVerifier_tweakableHash_eq_map,
    support_map_apply_iff] at hresult
  obtain ⟨raw, _hraw, rfl⟩ := hresult
  exact List.mem_singleton_self
    (tweakableHashInput parameter domain payload)

theorem filteredHighVerifierRunSupport_chainHash_trace_contains
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (parameter : PublicParameter)
    (epoch : Epoch) (chain : ChainIndex) (step : ChainStep)
    (value : Digest) (state : CausalHashState)
    (result : (((Digest × VerifierHashInputTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : FilteredHighVerifierRunSupport table keyHigh selected
      (Concrete.chainHash parameter epoch chain step value) state result) :
    Concrete.CacheView.chainInput parameter epoch chain step value ∈
      result.1.1.2 := by
  unfold Concrete.chainHash at hresult
  unfold Concrete.CacheView.chainInput
  unfold FilteredHighVerifierRunSupport EagerTraceSupport at hresult
  rw [simulate_eagerTrace_filteredHighHashTracedVerifier_tweakableHash_eq_map,
    support_map_apply_iff] at hresult
  obtain ⟨raw, _hraw, rfl⟩ := hresult
  exact List.mem_singleton_self _

theorem filteredHighVerifierRunSupport_leafHash_trace_contains
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (parameter : PublicParameter)
    (epoch : Epoch) (endpoints : ChainIndex → Digest)
    (state : CausalHashState)
    (result : (((Digest × VerifierHashInputTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : FilteredHighVerifierRunSupport table keyHigh selected
      (Concrete.leafHash parameter epoch endpoints) state result) :
    Concrete.CacheView.leafInput parameter epoch endpoints ∈
      result.1.1.2 := by
  unfold Concrete.leafHash at hresult
  unfold Concrete.CacheView.leafInput
  unfold FilteredHighVerifierRunSupport EagerTraceSupport at hresult
  rw [simulate_eagerTrace_filteredHighHashTracedVerifier_tweakableHash_eq_map,
    support_map_apply_iff] at hresult
  obtain ⟨raw, _hraw, rfl⟩ := hresult
  exact List.mem_singleton_self _

theorem filteredHighVerifierRunSupport_chainWalk_first_trace_contains
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (parameter : PublicParameter)
    (epoch : Epoch) (chain : ChainIndex) (position steps : Nat)
    (value : Digest) (hposition : position < chainLength - 1)
    (hsteps : 0 < steps) (state : CausalHashState)
    (result : (((Digest × VerifierHashInputTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : FilteredHighVerifierRunSupport table keyHigh selected
      (Concrete.chainWalk parameter epoch chain position steps value) state
        result) :
    Concrete.CacheView.chainInput parameter epoch chain
      ⟨position, hposition⟩ value ∈ result.1.1.2 := by
  induction steps generalizing state result with
  | zero => omega
  | succ remaining ih =>
      rw [Concrete.chainWalk] at hresult
      obtain ⟨head, tail, hhead, htail, heq⟩ :=
        filteredHighVerifierRunSupport_bind table keyHigh selected _ _ state
          result hresult
      cases remaining with
      | zero =>
          have hheadEq := filteredHighVerifierRunSupport_pure table keyHigh
            selected value state head hhead
          subst head
          simp only [Nat.zero_eq, Nat.add_zero, hposition, ↓reduceDIte] at htail
          have hmem : Concrete.CacheView.chainInput parameter epoch chain
              ⟨position, hposition⟩ value ∈ tail.1.1.2 := by
            unfold Concrete.chainHash at htail
            unfold Concrete.CacheView.chainInput
            unfold FilteredHighVerifierRunSupport EagerTraceSupport at htail
            rw [simulate_eagerTrace_filteredHighHashTracedVerifier_tweakableHash_eq_map,
              support_map_apply_iff] at htail
            obtain ⟨raw, _hraw, rfl⟩ := htail
            exact List.mem_singleton_self _
          rw [heq]
          exact List.mem_append_right [] hmem
      | succ prior =>
          have hmem := ih (by omega) state head hhead
          rw [heq]
          exact List.mem_append_left tail.1.1.2 hmem

theorem filteredHighVerifierRunSupport_sequenceFin_component
    {n : Nat} (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (computation : Fin n → OracleComp HashSpec α)
    (target : Fin n) (state : CausalHashState)
    (result : ((((Fin n → α) × VerifierHashInputTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : FilteredHighVerifierRunSupport table keyHigh selected
      (Concrete.sequenceFin computation) state result) :
    ∃ before componentResult,
      FilteredHighVerifierRunSupport table keyHigh selected
        (computation target) before componentResult ∧
      componentResult.1.1.1 = result.1.1.1 target ∧
      ∀ input ∈ componentResult.1.1.2, input ∈ result.1.1.2 := by
  induction n generalizing state with
  | zero => exact Fin.elim0 target
  | succ n ih =>
      rw [Concrete.sequenceFin] at hresult
      obtain ⟨head, rest, hhead, hrest, heq⟩ :=
        filteredHighVerifierRunSupport_bind table keyHigh selected _ _ state
          result hresult
      obtain ⟨tailResult, finalResult, htailResult, hfinalResult, hrestEq⟩ :=
        filteredHighVerifierRunSupport_bind table keyHigh selected _ _
          head.1.2 rest hrest
      have hfinalEq := filteredHighVerifierRunSupport_pure table keyHigh selected
        (fun i => Fin.cases head.1.1.1 tailResult.1.1.1 i)
        tailResult.1.2 finalResult hfinalResult
      subst finalResult
      simp at hrestEq
      obtain rfl | ⟨tailTarget, rfl⟩ := target.eq_zero_or_eq_succ
      · refine ⟨state, head, hhead, ?_, ?_⟩
        · rw [heq, hrestEq]
          change head.1.1.1 =
            (fun i => Fin.cases head.1.1.1 tailResult.1.1.1 i) 0
          rfl
        intro input hinput
        rw [heq, hrestEq]
        change input ∈ head.1.1.2 ++ tailResult.1.1.2
        exact List.mem_append_left tailResult.1.1.2 hinput
      · obtain ⟨before, componentResult, hcomponent, hcomponentEq, hsubset⟩ :=
          ih (fun index => computation index.succ) tailTarget head.1.2
            tailResult htailResult
        refine ⟨before, componentResult, hcomponent, ?_, ?_⟩
        · rw [heq, hrestEq]
          change componentResult.1.1.1 = tailResult.1.1.1 tailTarget
          exact hcomponentEq
        intro input hinput
        rw [heq, hrestEq]
        change input ∈ head.1.1.2 ++ tailResult.1.1.2
        apply List.mem_append_right head.1.1.2
        exact hsubset input hinput

theorem filteredHighVerifierRunSupport_recoverEndpoints_chain_start
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (parameter : PublicParameter)
    (epoch : Epoch) (encoding : Encoding) (signature : Signature)
    (hdigit : (encoding selected).val < chainLength - 1)
    (state : CausalHashState)
    (result : ((((ChainIndex → Digest) × VerifierHashInputTrace) ×
      CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : FilteredHighVerifierRunSupport table keyHigh selected
      (Concrete.recoverEndpoints parameter epoch encoding signature) state
        result) :
    Concrete.CacheView.chainInput parameter epoch selected
      ⟨(encoding selected).val, hdigit⟩
      (signature.chainValue selected) ∈ result.1.1.2 := by
  unfold Concrete.recoverEndpoints at hresult
  obtain ⟨before, componentResult, hcomponent, _hcomponentEq, hsubset⟩ :=
    filteredHighVerifierRunSupport_sequenceFin_component table keyHigh selected
      (fun chain => Concrete.recoverChain parameter epoch chain
        (encoding chain) (signature.chainValue chain)) selected state result
          hresult
  unfold Concrete.recoverChain at hcomponent
  have hsteps : 0 < chainLength - 1 - (encoding selected).val := by omega
  have hmem :=
    filteredHighVerifierRunSupport_chainWalk_first_trace_contains table
      keyHigh selected parameter epoch selected (encoding selected).val
        (chainLength - 1 - (encoding selected).val)
        (signature.chainValue selected) hdigit hsteps before componentResult
          hcomponent
  exact hsubset _ hmem

theorem filteredHighVerifierRunSupport_recoverEndpoints_endpoint_value
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (parameter : PublicParameter)
    (epoch : Epoch) (encoding : Encoding) (signature : Signature)
    (hdigit : ¬ (encoding selected).val < chainLength - 1)
    (state : CausalHashState)
    (result : ((((ChainIndex → Digest) × VerifierHashInputTrace) ×
      CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : FilteredHighVerifierRunSupport table keyHigh selected
      (Concrete.recoverEndpoints parameter epoch encoding signature) state
        result) :
    result.1.1.1 selected = signature.chainValue selected := by
  unfold Concrete.recoverEndpoints at hresult
  obtain ⟨before, componentResult, hcomponent, hcomponentEq, _hsubset⟩ :=
    filteredHighVerifierRunSupport_sequenceFin_component table keyHigh selected
      (fun chain => Concrete.recoverChain parameter epoch chain
        (encoding chain) (signature.chainValue chain)) selected state result
          hresult
  have hzero : chainLength - 1 - (encoding selected).val = 0 := by omega
  have hcomponentPure : FilteredHighVerifierRunSupport table keyHigh selected
      (pure (signature.chainValue selected)) before componentResult := by
    simpa [Concrete.recoverChain, hzero, Concrete.chainWalk] using hcomponent
  have hresultEq := filteredHighVerifierRunSupport_pure table keyHigh selected
    (signature.chainValue selected) before componentResult hcomponentPure
  calc
    result.1.1.1 selected = componentResult.1.1.1 := hcomponentEq.symm
    _ = signature.chainValue selected := by rw [hresultEq]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem filteredHighVerifierRunSupport_leafHash_bind_trace_contains
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (parameter : PublicParameter)
    (epoch : Epoch) (endpoints : ChainIndex → Digest)
    (next : Digest → OracleComp HashSpec α) (state : CausalHashState)
    (result : (((α × VerifierHashInputTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : FilteredHighVerifierRunSupport table keyHigh selected
      (Concrete.leafHash parameter epoch endpoints >>= next) state result) :
    Concrete.CacheView.leafInput parameter epoch endpoints ∈
      result.1.1.2 := by
  let leafComputation : OracleComp HashSpec Digest :=
    Concrete.leafHash parameter epoch endpoints
  change FilteredHighVerifierRunSupport table keyHigh selected
    (leafComputation >>= next) state result at hresult
  apply filteredHighVerifierRunSupport_bind_preserves_head_trace
    (β := Digest) (α := α) (table := table) (keyHigh := keyHigh)
    (selected := selected)
    (first := leafComputation) (next := next)
    (state := state)
    (input := Concrete.CacheView.leafInput parameter epoch endpoints)
    (result := result)
  · intro head hhead
    dsimp [leafComputation] at hhead
    unfold Concrete.leafHash at hhead
    unfold Concrete.CacheView.leafInput
    unfold FilteredHighVerifierRunSupport EagerTraceSupport at hhead
    rw [simulate_eagerTrace_filteredHighHashTracedVerifier_tweakableHash_eq_map,
      support_map_apply_iff] at hhead
    obtain ⟨raw, _hraw, rfl⟩ := hhead
    exact List.mem_singleton_self _
  · assumption

def PrimaryVerifierProbeInTrace
    (parameter : PublicParameter) (selected : ChainIndex)
    (epoch : Epoch) (encoding : Encoding) (signature : Signature)
    (trace : VerifierHashInputTrace) : Prop :=
  ∃ input ∈ trace,
    EagerTreeInputProbe parameter selected input (epoch, encoding selected)
      (signature.chainValue selected)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem filteredHighVerifierRunSupport_afterEncoding_primaryProbe
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (publicKey : PublicKey)
    (epoch : Epoch) (encoding : Encoding) (signature : Signature)
    (state : CausalHashState)
    (result : (((Bool × VerifierHashInputTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : FilteredHighVerifierRunSupport table keyHigh selected
      (do
        let endpoints ← Concrete.recoverEndpoints publicKey.parameter epoch
          encoding signature
        let leaf ← Concrete.leafHash publicKey.parameter epoch endpoints
        Concrete.verifyAfterLeaf publicKey epoch signature leaf :
          OracleComp HashSpec Bool)
      state result) :
    PrimaryVerifierProbeInTrace publicKey.parameter selected epoch encoding
      signature result.1.1.2 := by
  obtain ⟨endpointsResult, rest, hendpoints, hrest, heq⟩ :=
    filteredHighVerifierRunSupport_bind table keyHigh selected _ _ state result
      hresult
  by_cases hdigit : (encoding selected).val < chainLength - 1
  · let input := Concrete.CacheView.chainInput publicKey.parameter epoch selected
      ⟨(encoding selected).val, hdigit⟩ (signature.chainValue selected)
    have hinput :=
      filteredHighVerifierRunSupport_recoverEndpoints_chain_start table
        keyHigh selected publicKey.parameter epoch encoding signature hdigit
          state endpointsResult hendpoints
    refine ⟨input, ?_, ?_⟩
    · rw [heq]
      exact List.mem_append_left rest.1.1.2 hinput
    · unfold EagerTreeInputProbe
      left
      rw [chainInputProbe?_chainInput]
      congr 3
  ·
    have hendpoint :=
      filteredHighVerifierRunSupport_recoverEndpoints_endpoint_value table
        keyHigh selected publicKey.parameter epoch encoding signature hdigit
          state endpointsResult hendpoints
    let input := Concrete.CacheView.leafInput publicKey.parameter epoch
      endpointsResult.1.1.1
    change FilteredHighVerifierRunSupport table keyHigh selected
      (Concrete.leafHash publicKey.parameter epoch endpointsResult.1.1.1 >>=
        Concrete.verifyAfterLeaf publicKey epoch signature)
      endpointsResult.1.2 rest at hrest
    have hinput : Concrete.CacheView.leafInput publicKey.parameter epoch
        endpointsResult.1.1.1 ∈ rest.1.1.2 := by
      apply filteredHighVerifierRunSupport_leafHash_bind_trace_contains
        (α := Bool) (table := table) (keyHigh := keyHigh)
        (selected := selected) (parameter := publicKey.parameter)
        (epoch := epoch) (endpoints := endpointsResult.1.1.1)
        (next := Concrete.verifyAfterLeaf publicKey epoch signature)
        (state := endpointsResult.1.2) (result := rest)
      assumption
    refine ⟨input, ?_, ?_⟩
    · rw [heq]
      exact List.mem_append_right endpointsResult.1.1.2 hinput
    · unfold EagerTreeInputProbe
      right
      constructor
      · rw [chainInputProbe?_leafInput]
      · rw [leafInputProbe?_leafInput, hendpoint]
        have hdigitEq : chainEndpointDigit = encoding selected := by
          apply Fin.ext
          simp [chainEndpointDigit]
          omega
        rw [hdigitEq]

set_option maxHeartbeats 1000000 in
theorem filteredHighVerifierRunSupport_verify_true_primaryProbe
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (publicKey : PublicKey)
    (epoch : Epoch) (message : Message) (signature : Signature)
    (state : CausalHashState)
    (result : (((Bool × VerifierHashInputTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : FilteredHighVerifierRunSupport table keyHigh selected
      (Concrete.verify publicKey epoch message signature) state result)
    (hverified : result.1.1.1 = true) :
    ∃ digest encoding,
      TargetSum.decodeDigest digest = some encoding ∧
      PrimaryVerifierProbeInTrace publicKey.parameter selected epoch encoding
        signature result.1.1.2 := by
  unfold Concrete.verify at hresult
  let digestComputation : OracleComp HashSpec Digest :=
    Concrete.encodingHash publicKey.parameter epoch message signature.randomness
  let afterDigest : Digest → OracleComp HashSpec Bool := fun digest =>
    match TargetSum.decodeDigest digest with
    | none => pure false
    | some encoding => do
        let endpoints ← Concrete.recoverEndpoints publicKey.parameter epoch
          encoding signature
        let leaf ← Concrete.leafHash publicKey.parameter epoch endpoints
        Concrete.verifyAfterLeaf publicKey epoch signature leaf
  change FilteredHighVerifierRunSupport table keyHigh selected
    (digestComputation >>= afterDigest) state result at hresult
  obtain ⟨digestResult, rest, hdigest, hrest, heq⟩ :=
    by
      apply filteredHighVerifierRunSupport_bind (β := Digest) (α := Bool)
        (table := table) (keyHigh := keyHigh) (selected := selected)
        (first := digestComputation) (next := afterDigest)
        (state := state) (result := result)
      assumption
  dsimp [afterDigest] at hrest
  cases hdecode : TargetSum.decodeDigest digestResult.1.1.1 with
  | none =>
      have hrestEq := filteredHighVerifierRunSupport_pure table keyHigh selected
        false digestResult.1.2 rest (by simpa [hdecode] using hrest)
      rw [heq, hrestEq] at hverified
      change false = true at hverified
      exact (Bool.false_ne_true hverified).elim
  | some encoding =>
      have hprimary :=
        filteredHighVerifierRunSupport_afterEncoding_primaryProbe table keyHigh
          selected publicKey epoch encoding signature digestResult.1.2 rest
            (by simpa [hdecode] using hrest)
      refine ⟨digestResult.1.1.1, encoding, hdecode, ?_⟩
      obtain ⟨input, hinput, hprobe⟩ := hprimary
      refine ⟨input, ?_, hprobe⟩
      rw [heq]
      exact List.mem_append_right digestResult.1.1.2 hinput

set_option maxHeartbeats 1000000 in
theorem filteredHighVerifier_step_support_invariant
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : FilteredHighVerifierStepSupport table keyHigh selected input
      state result) :
    FilteredHighVerifierStepInvariant keyHigh selected input state result := by
  unfold FilteredHighVerifierStepSupport EagerTraceSupport at hresult
  rw [filteredHighHashOnlyVerifierImpl_run_eq] at hresult
  constructor
  · generalize hprogram : filteredTreeProbingAttackerHashQueryAtFromHigh
      (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected input
        state = program
    unfold filteredTreeHashComputationAtFromHigh at hresult
    rw [hprogram] at hresult
    exact filteredTreeHashProgram_support_initial_none_of_final_none
      table (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
        input state program result hresult
  · intro candidate hcandidate index target hprobe hhidden
    simp only [List.mem_singleton] at hcandidate
    have hprobeInput : EagerTreeInputProbe
        keyHigh.1.secretKey.parameter selected input index target := by
      simpa [hcandidate] using hprobe
    generalize hhigh : chainValueHighTableOfEdges keyHigh.2 = high at hresult
    generalize hsecretKey : keyHigh.1.secretKey = secretKey at hresult hprobeInput
    exact filteredTreeHashComputation_support_covers_eager_probe table high
      secretKey selected input state index target hprobeInput result hresult
        hhidden

set_option maxHeartbeats 1000000 in
theorem simulate_filteredHighHashTracedVerifier_query_bind_support_invariant
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (input : HashInput)
    (next : HashOutput → OracleComp HashSpec α)
    (state : CausalHashState)
    (hheadInvariant : ∀ head,
      FilteredHighVerifierStepSupport table keyHigh selected input state head →
        FilteredHighVerifierStepInvariant keyHigh selected input state head)
    (htailInvariant : ∀ output nextState tail,
      FilteredHighVerifierRunSupport table keyHigh selected (next output)
          nextState tail →
        FilteredHighVerifierRunInvariant keyHigh selected nextState tail)
    (result : (((α × VerifierHashInputTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : FilteredHighVerifierRunSupport table keyHigh selected
      (HasQuery.query (spec := HashSpec) (m := OracleComp HashSpec) input >>=
        next) state result) :
    FilteredHighVerifierRunInvariant keyHigh selected state result := by
  obtain ⟨head, tail, hhead, htail, rfl⟩ :=
    filteredHighVerifierRunSupport_bind
      (table := table) (keyHigh := keyHigh) (selected := selected)
      (first := HasQuery.query (spec := HashSpec) (m := OracleComp HashSpec)
        input) (next := next) (state := state) (result := result) hresult
  unfold FilteredHighVerifierRunSupport EagerTraceSupport at hhead
  rw [HasQuery.instOfMonadLift_query, simulateQ_query] at hhead
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map] at hhead
  rw [simulate_eagerTrace_filteredHighHashTracedVerifier_step_eq_map,
    support_map_apply_iff] at hhead
  obtain ⟨rawHead, hrawHead, rfl⟩ := hhead
  have hhead := hheadInvariant rawHead (by
    unfold FilteredHighVerifierStepSupport EagerTraceSupport
    exact hrawHead)
  have htail := htailInvariant rawHead.1.1 rawHead.1.2 tail htail
  unfold FilteredHighVerifierStepInvariant at hhead
  unfold FilteredHighVerifierRunInvariant at htail ⊢
  exact ⟨hhead.1.trans htail.1,
    (hhead.2.mono_state htail.1).append htail.2⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 2000000 in
theorem simulate_filteredHighHashTracedVerifier_support_invariant
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (computation : OracleComp HashSpec α)
    (state : CausalHashState)
    (result : (((α × VerifierHashInputTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : FilteredHighVerifierRunSupport table keyHigh selected
      computation state result) :
    FilteredHighVerifierRunInvariant keyHigh selected state result := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      unfold FilteredHighVerifierRunSupport EagerTraceSupport at hresult
      simp only [simulateQ_pure, WriterT.run_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      unfold FilteredHighVerifierRunInvariant
      exact ⟨RevealsMonotone.refl state.revealed,
        VerifierProbeTraceCovered.nil _ _ _⟩
  | query_bind input next ih =>
      apply
        simulate_filteredHighHashTracedVerifier_query_bind_support_invariant
          table keyHigh selected input next state
      · intro head hhead
        exact filteredHighVerifier_step_support_invariant table keyHigh selected
          input state head hhead
      · intro output nextState tail htail
        exact ih output nextState tail htail
      · exact hresult

set_option maxHeartbeats 1000000 in
theorem filteredHighVerifierRunSupport_verify_true_primaryProbe_observed
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (publicKey : PublicKey)
    (hparameter : publicKey.parameter = keyHigh.1.secretKey.parameter)
    (epoch : Epoch) (message : Message) (signature : Signature)
    (state : CausalHashState)
    (result : (((Bool × VerifierHashInputTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : FilteredHighVerifierRunSupport table keyHigh selected
      (Concrete.verify publicKey epoch message signature) state result)
    (hverified : result.1.1.1 = true) :
    ∃ digest encoding,
      TargetSum.decodeDigest digest = some encoding ∧
      (result.1.2.revealed (epoch, encoding selected) = none →
        RevealProbeOracleSimulation.ObservedAction.probe
          (epoch, encoding selected) (signature.chainValue selected) ∈
            result.2) := by
  obtain ⟨digest, encoding, hdecode, input, hinput, hprobe⟩ :=
    filteredHighVerifierRunSupport_verify_true_primaryProbe
      (table := table) (keyHigh := keyHigh) (selected := selected)
      (publicKey := publicKey) (epoch := epoch) (message := message)
      (signature := signature) (state := state) (result := result)
      hresult hverified
  have hinvariant :=
    simulate_filteredHighHashTracedVerifier_support_invariant table keyHigh
      selected (Concrete.verify publicKey epoch message signature) state result
        hresult
  refine ⟨digest, encoding, hdecode, ?_⟩
  intro hhidden
  apply hinvariant.2 input hinput (epoch, encoding selected)
    (signature.chainValue selected)
  · simpa [← hparameter] using hprobe
  · exact hhidden

def eraseVerifierHashTrace
    (result : (((α × VerifierHashInputTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) :
    (α × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex :=
  ((result.1.1.1, result.1.2), result.2)

set_option maxHeartbeats 1000000 in
theorem map_filteredHighHashTracedVerifier_eager_projection
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (computation : OracleComp HashSpec α)
    (state : CausalHashState) :
    eraseVerifierHashTrace <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          (((simulateQ (filteredHighHashTracedVerifierImpl keyHigh selected)
            computation).run).run state)).run =
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ (filteredHighHashOnlyVerifierImpl keyHigh selected)
          computation).run state)).run := by
  have hprojection := filteredHighHashTracedVerifier_projection keyHigh
    selected computation
  have hrun := congrArg
    (fun candidate => candidate.run state) hprojection
  have heager := congrArg
    (fun candidate =>
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        candidate).run) hrun
  change (fun result => ((result.1.1.1, result.1.2), result.2)) <$>
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (((simulateQ (filteredHighHashTracedVerifierImpl keyHigh selected)
          computation).run).run state)).run = _
  simpa [StateT.run_map, simulateQ_map, WriterT.run_map', Functor.map_map,
    Function.comp_def] using heager

theorem filteredHighVerifierRunSupport_lift
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (computation : OracleComp HashSpec α)
    (state : CausalHashState)
    (result : (α × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ (filteredHighHashOnlyVerifierImpl keyHigh selected)
          computation).run state)).run)) :
    ∃ tracedResult,
      FilteredHighVerifierRunSupport table keyHigh selected computation state
        tracedResult ∧
      eraseVerifierHashTrace tracedResult = result := by
  rw [← map_filteredHighHashTracedVerifier_eager_projection table keyHigh
    selected computation state] at hresult
  rw [support_map] at hresult
  obtain ⟨tracedResult, htracedResult, heq⟩ := hresult
  refine ⟨tracedResult, ?_, heq⟩
  unfold FilteredHighVerifierRunSupport EagerTraceSupport
  exact htracedResult

set_option maxHeartbeats 1000000 in
theorem filteredHighVerifier_support_verify_true_primaryProbe_observed
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (publicKey : PublicKey)
    (hparameter : publicKey.parameter = keyHigh.1.secretKey.parameter)
    (epoch : Epoch) (message : Message) (signature : Signature)
    (state : CausalHashState)
    (result : (Bool × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ (filteredHighVerifierImpl keyHigh selected)
          (Concrete.singleAttemptScheme.verify publicKey epoch message signature)).run
            state)).run))
    (hverified : result.1.1 = true) :
    ∃ digest encoding,
      TargetSum.decodeDigest digest = some encoding ∧
      (result.1.2.revealed (epoch, encoding selected) = none →
        RevealProbeOracleSimulation.ObservedAction.probe
          (epoch, encoding selected) (signature.chainValue selected) ∈
            result.2) := by
  unfold Concrete.singleAttemptScheme at hresult
  rw [simulate_filteredHighVerifier_liftM_eq_hashOnly] at hresult
  obtain ⟨tracedResult, htracedResult, heq⟩ :=
    filteredHighVerifierRunSupport_lift
      (table := table) (keyHigh := keyHigh) (selected := selected)
      (computation := Concrete.verify publicKey epoch message signature)
      (state := state) (result := result) hresult
  subst result
  exact filteredHighVerifierRunSupport_verify_true_primaryProbe_observed table
    keyHigh selected publicKey hparameter epoch message signature state
      tracedResult htracedResult hverified

def FilteredHighDetailedRunSupport
    (table : ChainValueIndex → Digest)
    (adversary : Adversary Concrete.singleAttemptScheme)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (state : CausalHashState)
    (result : ((((Forgery × Bool) × AttackerActionTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) : Prop :=
  EagerTraceSupport table
    ((filteredHighDetailedGameAfterKeygen adversary keyHigh selected).run state)
      result

set_option maxHeartbeats 1000000 in
theorem filteredHighDetailedRunSupport_decompose
    (table : ChainValueIndex → Digest)
    (adversary : Adversary Concrete.singleAttemptScheme)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (state : CausalHashState)
    (result : ((((Forgery × Bool) × AttackerActionTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : FilteredHighDetailedRunSupport table adversary keyHigh selected
      state result) :
    ∃ handled verifier,
      FilteredHighRunSupport table keyHigh selected
        (adversary.main keyHigh.1.publicKey) state handled ∧
      EagerTraceSupport table
        ((simulateQ (filteredHighVerifierImpl keyHigh selected)
          (Concrete.singleAttemptScheme.verify keyHigh.1.publicKey handled.1.1.1.epoch
            handled.1.1.1.message handled.1.1.1.signature)).run
              handled.1.2) verifier ∧
      result = ((((handled.1.1.1, verifier.1.1), handled.1.1.2),
        verifier.1.2), handled.2 ++ verifier.2) := by
  unfold FilteredHighDetailedRunSupport EagerTraceSupport at hresult
  unfold filteredHighDetailedGameAfterKeygen at hresult
  rw [StateT.run_bind, simulateQ_bind, WriterT.run_bind'] at hresult
  rw [support_bind_apply_iff] at hresult
  obtain ⟨handled, hhandled, hrest⟩ := hresult
  rw [support_map_apply_iff] at hrest
  obtain ⟨tail, htail, heq⟩ := hrest
  rw [StateT.run_bind, simulateQ_bind, WriterT.run_bind'] at htail
  rw [support_bind_apply_iff] at htail
  obtain ⟨verifier, hverifier, hfinal⟩ := htail
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst tail
  subst result
  refine ⟨handled, verifier, ?_, ?_, ?_⟩
  · unfold FilteredHighRunSupport EagerTraceSupport
    exact hhandled
  · unfold EagerTraceSupport
    exact hverifier
  · simp [List.append_assoc]

theorem filteredHighVerifier_support_revealsMonotone
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (computation : OracleComp HashSpec α)
    (state : CausalHashState)
    (result : (α × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ (filteredHighHashOnlyVerifierImpl keyHigh selected)
          computation).run state)).run)) :
    RevealsMonotone state.revealed result.1.2.revealed := by
  obtain ⟨tracedResult, htracedResult, heq⟩ :=
    filteredHighVerifierRunSupport_lift table keyHigh selected computation
      state result hresult
  subst result
  exact (simulate_filteredHighHashTracedVerifier_support_invariant table
    keyHigh selected computation state tracedResult htracedResult).1

set_option maxHeartbeats 1000000 in
theorem filteredHighVerifier_support_scheme_revealsMonotone
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (publicKey : PublicKey)
    (epoch : Epoch) (message : Message) (signature : Signature)
    (state : CausalHashState)
    (result : (Bool × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ (filteredHighVerifierImpl keyHigh selected)
          (Concrete.singleAttemptScheme.verify publicKey epoch message signature)).run
            state)).run)) :
    RevealsMonotone state.revealed result.1.2.revealed := by
  unfold Concrete.singleAttemptScheme at hresult
  rw [simulate_filteredHighVerifier_liftM_eq_hashOnly] at hresult
  exact filteredHighVerifier_support_revealsMonotone table keyHigh selected
    (Concrete.verify publicKey epoch message signature) state result hresult

set_option maxHeartbeats 1000000 in
theorem filteredHighDetailedRunSupport_verified_coverage
    (table : ChainValueIndex → Digest)
    (adversary : Adversary Concrete.singleAttemptScheme)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex)
    (hparameter : keyHigh.1.publicKey.parameter =
      keyHigh.1.secretKey.parameter)
    (state : CausalHashState)
    (result : ((((Forgery × Bool) × AttackerActionTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : FilteredHighDetailedRunSupport table adversary keyHigh selected
      state result)
    (hverified : result.1.1.1.2 = true) :
    ∃ digest encoding,
      TargetSum.decodeDigest digest = some encoding ∧
      ChainProbeTraceCovered keyHigh.1.secretKey.parameter selected
        result.1.1.2 result.1.2 result.2 ∧
      (result.1.2.revealed
          (result.1.1.1.1.epoch, encoding selected) = none →
        RevealProbeOracleSimulation.ObservedAction.probe
          (result.1.1.1.1.epoch, encoding selected)
          (result.1.1.1.1.signature.chainValue selected) ∈ result.2) := by
  obtain ⟨handled, verifier, hhandled, hverifier, heq⟩ :=
    filteredHighDetailedRunSupport_decompose table adversary keyHigh selected
      state result hresult
  subst result
  have hadversary :=
    simulate_filteredHighActionTraced_support_chainProbeTraceCovered table
      keyHigh selected (adversary.main keyHigh.1.publicKey) state handled
        hhandled
  have hverifierMonotone :=
    filteredHighVerifier_support_scheme_revealsMonotone table keyHigh selected
      keyHigh.1.publicKey handled.1.1.1.epoch handled.1.1.1.message
        handled.1.1.1.signature handled.1.2 verifier hverifier
  obtain ⟨digest, encoding, hdecode, hprimary⟩ :=
    filteredHighVerifier_support_verify_true_primaryProbe_observed table
      keyHigh selected keyHigh.1.publicKey hparameter handled.1.1.1.epoch
        handled.1.1.1.message handled.1.1.1.signature handled.1.2 verifier
          hverifier hverified
  refine ⟨digest, encoding, hdecode, ?_, ?_⟩
  · exact (hadversary.2.mono_state hverifierMonotone).append_observed
  · intro hhidden
    exact List.mem_append_right handled.2 (hprimary hhidden)

set_option maxHeartbeats 1000000 in
theorem map_filteredHighMonitoredMapped_action_projection_step
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : MonitoredCausalState) (attackerTrace : AttackerActionTrace) :
    (fun result : (OracleWorld + SigningSpec).Range input ×
        MonitoredTracedState =>
      (((result.1, result.2.2), result.2.1.causal), result.2.1.trace)) <$>
        (filteredHighMonitoredMappedAdversaryImpl keyHigh selected table input
          ).run (state, attackerTrace) =
      (fun result : ((((OracleWorld + SigningSpec).Range input ×
          AttackerActionTrace) × CausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
        (((result.1.1.1, attackerTrace ++ result.1.1.2), result.1.2),
          state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          (((filteredHighActionTracedMappedAdversaryImpl keyHigh selected input
            ).run).run state.causal)).run := by
  let augment := fun result : (((OracleWorld + SigningSpec).Range input ×
      CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
    (((result.1.1,
      attackerTrace ++ attackerActionFragment input result.1.1), result.1.2),
      result.2)
  have hleft :
      (fun result : (OracleWorld + SigningSpec).Range input ×
          MonitoredTracedState =>
        (((result.1, result.2.2), result.2.1.causal), result.2.1.trace)) <$>
          (filteredHighMonitoredMappedAdversaryImpl keyHigh selected table input
            ).run (state, attackerTrace) =
        augment <$>
          ((fun result : (OracleWorld + SigningSpec).Range input ×
              MonitoredTracedState =>
            ((result.1, result.2.1.causal), result.2.1.trace)) <$>
              (filteredHighMonitoredMappedAdversaryImpl keyHigh selected table
                input).run (state, attackerTrace)) := by
    unfold filteredHighMonitoredMappedAdversaryImpl actionTracedStateImpl
    simp [augment, StateT.run_mk, Functor.map_map,
      map_eq_bind_pure_comp, bind_assoc]
  have hbase := map_simulate_filteredHighMonitoredMapped_projection keyHigh
    selected table
      (liftM (OracleSpec.query input) :
        OracleComp (OracleWorld + SigningSpec)
          ((OracleWorld + SigningSpec).Range input))
      state attackerTrace
  rw [simulateQ_spec_query] at hbase
  rw [hleft, hbase]
  rw [simulateQ_spec_query]
  simp only [Functor.map_map, Function.comp_apply, augment]
  rw [simulate_eagerTrace_filteredHighActionTraced_step_eq_map]
  simp only [Functor.map_map, Function.comp_apply]

theorem map_simulate_filteredHighMonitoredMapped_action_projection
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : MonitoredCausalState) (attackerTrace : AttackerActionTrace) :
    (fun result : α × MonitoredTracedState =>
      (((result.1, result.2.2), result.2.1.causal), result.2.1.trace)) <$>
        (simulateQ
          (filteredHighMonitoredMappedAdversaryImpl keyHigh selected table)
            computation).run (state, attackerTrace) =
      (fun result : (((α × AttackerActionTrace) × CausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
        (((result.1.1.1, attackerTrace ++ result.1.1.2), result.1.2),
          state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          (((simulateQ
            (filteredHighActionTracedMappedAdversaryImpl keyHigh selected)
              computation).run).run state.causal)).run := by
  induction computation using OracleComp.inductionOn generalizing state
      attackerTrace with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, StateT.run_bind, WriterT.run_bind', map_bind,
        simulateQ_spec_query]
      simp_rw [ih]
      let project := fun result : (OracleWorld + SigningSpec).Range input ×
          MonitoredTracedState =>
        (((result.1, result.2.2), result.2.1.causal), result.2.1.trace)
      let tail := fun head : ((((OracleWorld + SigningSpec).Range input ×
          AttackerActionTrace) × CausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
        (fun result : (((α × AttackerActionTrace) × CausalHashState) ×
            RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
          (((result.1.1.1, head.1.1.2 ++ result.1.1.2), result.1.2),
            head.2 ++ result.2)) <$>
          (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
            (((simulateQ
              (filteredHighActionTracedMappedAdversaryImpl keyHigh selected)
                (next head.1.1.1)).run).run head.1.2)).run
      change (do
        let head ←
          (filteredHighMonitoredMappedAdversaryImpl keyHigh selected table input
            ).run (state, attackerTrace)
        tail (project head)) = _
      rw [← bind_map_left project]
      rw [map_filteredHighMonitoredMapped_action_projection_step table keyHigh
        selected input state attackerTrace, bind_map_left]
      apply bind_congr
      intro head
      simp [tail, Functor.map_map, List.append_assoc]

theorem filteredHighMonitoredUniformVerifier_preserves_attackerTrace
    (table : ChainValueIndex → Digest) (n : Nat)
    (attackerTrace : AttackerActionTrace)
    (state : MonitoredTracedState) (htrace : state.2 = attackerTrace)
    (result : unifSpec.Range n × MonitoredTracedState)
    (hresult : result ∈ support
      ((filteredHighMonitoredUniformVerifierImpl table n).run state)) :
    result.2.2 = attackerTrace := by
  unfold filteredHighMonitoredUniformVerifierImpl at hresult
  simp only [StateT.run_mk] at hresult
  rw [support_map] at hresult
  obtain ⟨baseResult, _hbaseResult, rfl⟩ := hresult
  exact htrace

theorem filteredHighMonitoredHashVerifier_preserves_attackerTrace
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (hashInput : HashInput) (attackerTrace : AttackerActionTrace)
    (state : MonitoredTracedState) (htrace : state.2 = attackerTrace)
    (result : HashOutput × MonitoredTracedState)
    (hresult : result ∈ support
      ((filteredHighMonitoredHashVerifierImpl keyHigh selected table hashInput
        ).run state)) :
    result.2.2 = attackerTrace := by
  rw [filteredHighMonitoredHashVerifierImpl_run,
    filteredHighMonitoredHashVerifierRun_eq, support_map] at hresult
  obtain ⟨baseResult, _hbaseResult, rfl⟩ := hresult
  exact htrace

theorem filteredHighMonitoredVerifier_preserves_attackerTrace
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (attackerTrace : AttackerActionTrace) :
    QueryImpl.PreservesInv
      (filteredHighMonitoredVerifierImpl keyHigh selected table)
      (fun state : MonitoredTracedState => state.2 = attackerTrace) := by
  intro input state htrace result hresult
  rcases input with n | hashInput
  · exact filteredHighMonitoredUniformVerifier_preserves_attackerTrace table n
      attackerTrace state htrace result hresult
  · exact filteredHighMonitoredHashVerifier_preserves_attackerTrace keyHigh
      selected table hashInput attackerTrace state htrace result hresult

theorem filteredHighMonitoredVerifier_simulation_preserves_attackerTrace
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (state : MonitoredTracedState) (attackerTrace : AttackerActionTrace)
    (htrace : state.2 = attackerTrace)
    (result : α × MonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ (filteredHighMonitoredVerifierImpl keyHigh selected table)
        computation).run state)) :
    result.2.2 = attackerTrace := by
  exact OracleComp.simulateQ_run_preservesInv
    (filteredHighMonitoredVerifierImpl keyHigh selected table)
    (fun candidate : MonitoredTracedState => candidate.2 = attackerTrace)
    (filteredHighMonitoredVerifier_preserves_attackerTrace keyHigh selected
      table attackerTrace) computation state htrace result hresult

set_option maxHeartbeats 1000000 in
theorem filteredHighMonitoredDetailedExecution_support_action_projection
    (table : ChainValueIndex → Digest)
    (adversary : Adversary Concrete.singleAttemptScheme)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex)
    (result : (Forgery × Bool) × MonitoredTracedState)
    (hresult : result ∈ support
      (filteredHighMonitoredDetailedExecution adversary keyHigh selected
        table)) :
    FilteredHighDetailedRunSupport table adversary keyHigh selected
      (filteredCausalKeygenState selected keyHigh.1)
      ((((result.1, result.2.2), result.2.1.causal), result.2.1.trace)) := by
  unfold filteredHighMonitoredDetailedExecution at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨handled, hhandled, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨verifier, hverifier, hfinal⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  have htrace : verifier.2.2 = handled.2.2 :=
    filteredHighMonitoredVerifier_simulation_preserves_attackerTrace keyHigh
      selected table
      (Concrete.singleAttemptScheme.verify keyHigh.1.publicKey handled.1.epoch
        handled.1.message handled.1.signature)
      handled.2 handled.2.2 rfl verifier hverifier
  have hhandledMapped :
      (((handled.1, handled.2.2), handled.2.1.causal),
          handled.2.1.trace) ∈ support
        ((fun mapped : Forgery × MonitoredTracedState =>
          (((mapped.1, mapped.2.2), mapped.2.1.causal),
            mapped.2.1.trace)) <$>
          (simulateQ
            (filteredHighMonitoredMappedAdversaryImpl keyHigh selected table)
              (adversary.main keyHigh.1.publicKey)).run
                (⟨filteredCausalKeygenState selected keyHigh.1,
                  some AdaptiveRevealMonitor.State.empty, []⟩, [])) := by
    rw [support_map]
    exact ⟨handled, hhandled, rfl⟩
  rw [map_simulate_filteredHighMonitoredMapped_action_projection table
    keyHigh selected (adversary.main keyHigh.1.publicKey)
      ⟨filteredCausalKeygenState selected keyHigh.1,
        some AdaptiveRevealMonitor.State.empty, []⟩ []] at hhandledMapped
  simp only [List.nil_append] at hhandledMapped
  obtain ⟨rawHandled, hrawHandled, hhandledEq⟩ :=
    (support_map_apply_iff _ _ _).mp hhandledMapped
  have hverifierMapped :
      ((verifier.1, verifier.2.1.causal), verifier.2.1.trace) ∈ support
        ((fun mapped : Bool × MonitoredTracedState =>
          ((mapped.1, mapped.2.1.causal), mapped.2.1.trace)) <$>
          (simulateQ
            (filteredHighMonitoredVerifierImpl keyHigh selected table)
              (Concrete.singleAttemptScheme.verify keyHigh.1.publicKey handled.1.epoch
                handled.1.message handled.1.signature)).run handled.2) := by
    rw [support_map]
    exact ⟨verifier, hverifier, rfl⟩
  rw [map_simulate_filteredHighMonitoredVerifier_verify_projection keyHigh
    selected table keyHigh.1.publicKey handled.1 handled.2.1 handled.2.2]
      at hverifierMapped
  obtain ⟨rawVerifier, hrawVerifier, hverifierEq⟩ :=
    (support_map_apply_iff _ _ _).mp hverifierMapped
  have hhandledEq' : rawHandled =
      (((handled.1, handled.2.2), handled.2.1.causal),
        handled.2.1.trace) := by
    simpa only [Prod.eta] using hhandledEq
  have hforgery : rawHandled.1.1.1 = handled.1 :=
    congrArg (fun candidate => candidate.1.1.1) hhandledEq'
  have hattackerTrace : rawHandled.1.1.2 = handled.2.2 :=
    congrArg (fun candidate => candidate.1.1.2) hhandledEq'
  have hhandledState : rawHandled.1.2 = handled.2.1.causal :=
    congrArg (fun candidate => candidate.1.2) hhandledEq'
  have hhandledObserved : rawHandled.2 = handled.2.1.trace :=
    congrArg Prod.snd hhandledEq'
  have hverified : rawVerifier.1.1 = verifier.1 :=
    congrArg (fun candidate => candidate.1.1) hverifierEq
  have hverifierState : rawVerifier.1.2 = verifier.2.1.causal :=
    congrArg (fun candidate => candidate.1.2) hverifierEq
  have hverifierObserved :
      handled.2.1.trace ++ rawVerifier.2 = verifier.2.1.trace :=
    congrArg Prod.snd hverifierEq
  have hrawVerifier' : EagerTraceSupport table
      ((simulateQ (filteredHighVerifierImpl keyHigh selected)
        (Concrete.singleAttemptScheme.verify keyHigh.1.publicKey rawHandled.1.1.1.epoch
          rawHandled.1.1.1.message rawHandled.1.1.1.signature)).run
            rawHandled.1.2) rawVerifier := by
    unfold EagerTraceSupport
    simpa only [hforgery, hhandledState] using hrawVerifier
  have hcomposed : FilteredHighDetailedRunSupport table adversary keyHigh
      selected (filteredCausalKeygenState selected keyHigh.1)
      ((((rawHandled.1.1.1, rawVerifier.1.1), rawHandled.1.1.2),
        rawVerifier.1.2), rawHandled.2 ++ rawVerifier.2) := by
    unfold FilteredHighDetailedRunSupport
    unfold filteredHighDetailedGameAfterKeygen
    rw [StateT.run_bind]
    apply eagerTraceSupport_bind (head := rawHandled)
      (tail := (((((rawHandled.1.1.1, rawVerifier.1.1),
        rawHandled.1.1.2), rawVerifier.1.2), rawVerifier.2)))
    · exact hrawHandled
    · rw [StateT.run_bind]
      let verifierRun :=
        (simulateQ (filteredHighVerifierImpl keyHigh selected)
          (Concrete.singleAttemptScheme.verify keyHigh.1.publicKey
            rawHandled.1.1.1.epoch rawHandled.1.1.1.message
              rawHandled.1.1.1.signature)).run rawHandled.1.2
      let afterVerifier : Bool × CausalHashState → OracleComp
          (RevealProbeOracleSimulation.World ChainValueIndex)
          (((Forgery × Bool) × AttackerActionTrace) × CausalHashState) :=
        fun verified => pure (((rawHandled.1.1.1, verified.1),
          rawHandled.1.1.2), verified.2)
      let finalValue := (((rawHandled.1.1.1, rawVerifier.1.1),
        rawHandled.1.1.2), rawVerifier.1.2)
      have hfirst : EagerTraceSupport table verifierRun rawVerifier := by
        simpa only [verifierRun] using hrawVerifier'
      have hfinal : EagerTraceSupport table (afterVerifier rawVerifier.1)
          (finalValue, []) := by
        simp only [afterVerifier, finalValue, EagerTraceSupport,
          simulateQ_pure, WriterT.run_pure, support_pure]
        exact Set.mem_singleton _
      have htail := eagerTraceSupport_bind table verifierRun afterVerifier
        rawVerifier (finalValue, []) hfirst hfinal
      simpa only [verifierRun, afterVerifier, finalValue,
        StateT.run_pure, List.append_nil] using htail
  simpa only [hforgery, hattackerTrace, hhandledState, hhandledObserved,
    hverified, hverifierState, hverifierObserved, htrace] using hcomposed

set_option maxHeartbeats 1000000 in
theorem filteredHighMonitoredDetailedExecution_support_verified_coverage
    (table : ChainValueIndex → Digest)
    (adversary : Adversary Concrete.singleAttemptScheme)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex)
    (hparameter : keyHigh.1.publicKey.parameter =
      keyHigh.1.secretKey.parameter)
    (result : (Forgery × Bool) × MonitoredTracedState)
    (hresult : result ∈ support
      (filteredHighMonitoredDetailedExecution adversary keyHigh selected
        table))
    (hverified : result.1.2 = true) :
    ∃ digest encoding,
      TargetSum.decodeDigest digest = some encoding ∧
      ChainProbeTraceCovered keyHigh.1.secretKey.parameter selected
        result.2.2 result.2.1.causal result.2.1.trace ∧
      (result.2.1.causal.revealed
          (result.1.1.epoch, encoding selected) = none →
        RevealProbeOracleSimulation.ObservedAction.probe
          (result.1.1.epoch, encoding selected)
          (result.1.1.signature.chainValue selected) ∈
            result.2.1.trace) := by
  let projected :=
    ((((result.1, result.2.2), result.2.1.causal), result.2.1.trace))
  have hprojected : FilteredHighDetailedRunSupport table adversary keyHigh
      selected (filteredCausalKeygenState selected keyHigh.1) projected :=
    filteredHighMonitoredDetailedExecution_support_action_projection table
      adversary keyHigh selected result hresult
  simpa [projected] using
    (filteredHighDetailedRunSupport_verified_coverage table adversary keyHigh
      selected hparameter (filteredCausalKeygenState selected keyHigh.1)
        projected hprojected hverified)

end XmssSecurity
