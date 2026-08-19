import XmssSecurity.CappedChain.CausalEagerHighProjection

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option linter.constructorNameAsVariable false

def ChainProbeTraceCovered
    (parameter : PublicParameter) (selected : ChainIndex)
    (attackerTrace : AttackerActionTrace) (state : CausalHashState)
    (observedTrace : RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :
    Prop :=
  ∀ probe ∈ attackerTrace.chainInputProbes parameter selected,
    state.revealed probe.1 = none →
      RevealProbeOracleSimulation.ObservedAction.probe probe.1 probe.2 ∈
        observedTrace

@[simp]
theorem AttackerActionTrace.chainInputProbes_append
    (parameter : PublicParameter) (selected : ChainIndex)
    (left right : AttackerActionTrace) :
    (left ++ right).chainInputProbes parameter selected =
      left.chainInputProbes parameter selected ++
        right.chainInputProbes parameter selected := by
  simp [AttackerActionTrace.chainInputProbes]

def RevealsMonotone
    (initial final : ChainValueIndex → Option Digest) : Prop :=
  ∀ index, final index = none → initial index = none

theorem RevealsMonotone.refl
    (revealed : ChainValueIndex → Option Digest) :
    RevealsMonotone revealed revealed := by
  intro index hhidden
  exact hhidden

theorem RevealsMonotone.trans
    {first second third : ChainValueIndex → Option Digest}
    (hfirst : RevealsMonotone first second)
    (hsecond : RevealsMonotone second third) :
    RevealsMonotone first third := by
  intro index hhidden
  exact hfirst index (hsecond index hhidden)

theorem chainProbeTraceCovered_nil
    (parameter : PublicParameter) (selected : ChainIndex)
    (state : CausalHashState) :
    ChainProbeTraceCovered parameter selected [] state [] := by
  intro input hinput
  simp [AttackerActionTrace.chainInputProbes,
    AttackerActionTrace.hashInputs] at hinput

theorem ChainProbeTraceCovered.append_observed
    {parameter : PublicParameter} {selected : ChainIndex}
    {attackerTrace : AttackerActionTrace} {state : CausalHashState}
    {observedTrace suffix :
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex}
    (hcovered : ChainProbeTraceCovered parameter selected attackerTrace state
      observedTrace) :
    ChainProbeTraceCovered parameter selected attackerTrace state
      (observedTrace ++ suffix) := by
  intro probe hprobe hhidden
  exact List.mem_append_left suffix
    (hcovered probe hprobe hhidden)

theorem ChainProbeTraceCovered.mono_reveals
    {parameter : PublicParameter} {selected : ChainIndex}
    {attackerTrace : AttackerActionTrace} {initial final : CausalHashState}
    {observedTrace :
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex}
    {transitionTrace :
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex}
    (hcovered : ChainProbeTraceCovered parameter selected attackerTrace initial
      observedTrace)
    (hreplay : ReplaysCausalReveals initial.revealed transitionTrace
      final.revealed) :
    ChainProbeTraceCovered parameter selected attackerTrace final
      observedTrace := by
  intro probe hprobe hhidden
  apply hcovered probe hprobe
  exact hreplay.initial_none_of_final_none probe.1 hhidden

theorem ChainProbeTraceCovered.mono_state
    {parameter : PublicParameter} {selected : ChainIndex}
    {attackerTrace : AttackerActionTrace} {initial final : CausalHashState}
    {observedTrace :
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex}
    (hcovered : ChainProbeTraceCovered parameter selected attackerTrace initial
      observedTrace)
    (hmonotone : RevealsMonotone initial.revealed final.revealed) :
    ChainProbeTraceCovered parameter selected attackerTrace final
      observedTrace := by
  intro probe hprobe hhidden
  exact hcovered probe hprobe (hmonotone probe.1 hhidden)

theorem ChainProbeTraceCovered.append
    {parameter : PublicParameter} {selected : ChainIndex}
    {left right : AttackerActionTrace} {state : CausalHashState}
    {leftObserved rightObserved :
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex}
    (hleft : ChainProbeTraceCovered parameter selected left state leftObserved)
    (hright : ChainProbeTraceCovered parameter selected right state
      rightObserved) :
    ChainProbeTraceCovered parameter selected (left ++ right) state
      (leftObserved ++ rightObserved) := by
  intro probe hprobe hhidden
  rw [AttackerActionTrace.chainInputProbes_append] at hprobe
  rcases List.mem_append.mp hprobe with hprobe | hprobe
  · exact List.mem_append_left rightObserved (hleft probe hprobe hhidden)
  · exact List.mem_append_right leftObserved (hright probe hprobe hhidden)

theorem filteredTreeHashComputation_support_covers_chain_probe
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

theorem filteredProbingHashQuery_support_covers_probe
    (table high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (probe : ChainValueIndex × Digest)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredProbingAttackerHashQueryAtFromHigh high secretKey selected input
          state (some probe))).run))
    (hhidden : result.1.2.revealed probe.1 = none) :
    RevealProbeOracleSimulation.ObservedAction.probe probe.1 probe.2 ∈
      result.2 := by
  have hreplay :=
    simulate_eagerTrace_filteredProbingAttackerHashQueryAtFromHigh_support_replays
      table high secretKey selected input state (some probe) result hresult
  have hinitial : state.revealed probe.1 = none :=
    hreplay.initial_none_of_final_none probe.1 hhidden
  obtain ⟨suffix, hsuffix⟩ :=
    simulate_eagerTrace_filteredProbingAttackerHashQueryAtFromHigh_hidden_support_trace
      table high secretKey selected input state probe.1 probe.2 hinitial result
        hresult
  rw [hsuffix]
  exact List.mem_cons_self

theorem filteredTreeHashProgram_support_initial_none_of_final_none
    (table high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (program : FilteredTreeHashProgram)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (program.computation high secretKey selected input state)).run)) :
    RevealsMonotone state.revealed result.1.2.revealed := by
  intro index hfinal
  cases program with
  | chain probe =>
      exact
        (simulate_eagerTrace_filteredProbingAttackerHashQueryAtFromHigh_support_replays
          table high secretKey selected input state (some probe) result
            (by simpa [FilteredTreeHashProgram.computation,
              filteredTreeChainHashComputation] using hresult))
          |>.initial_none_of_final_none index hfinal
  | currentCached =>
      cases hcache : state.cache input with
      | none =>
          rw [FilteredTreeHashProgram.computation, hcache,
            filteredTreeFreshHashComputation,
            simulate_eagerTrace_causalHashQuery, support_map] at hresult
          obtain ⟨raw, _hraw, rfl⟩ := hresult
          exact hfinal
      | some output =>
          simp only [FilteredTreeHashProgram.computation, hcache,
            filteredTreePureHashComputation, simulateQ_pure, WriterT.run_pure,
            support_pure, Set.mem_singleton_iff] at hresult
          subst result
          exact hfinal
  | keygenCached =>
      cases hcache : state.keygenCache input with
      | none =>
          rw [FilteredTreeHashProgram.computation, hcache,
            filteredTreeFreshHashComputation,
            simulate_eagerTrace_causalHashQuery, support_map] at hresult
          obtain ⟨raw, _hraw, rfl⟩ := hresult
          exact hfinal
      | some output =>
          simp only [FilteredTreeHashProgram.computation, hcache,
            filteredTreePureHashComputation, simulateQ_pure, WriterT.run_pure,
            support_pure, Set.mem_singleton_iff] at hresult
          subst result
          exact hfinal
  | leafCached =>
      cases hcache : filteredTreeKeygenLeafOutput secretKey input state with
      | none =>
          rw [FilteredTreeHashProgram.computation, hcache,
            filteredTreeFreshHashComputation,
            simulate_eagerTrace_causalHashQuery, support_map] at hresult
          obtain ⟨raw, _hraw, rfl⟩ := hresult
          exact hfinal
      | some output =>
          simp only [FilteredTreeHashProgram.computation, hcache,
            filteredTreePureHashComputation, simulateQ_pure, WriterT.run_pure,
            support_pure, Set.mem_singleton_iff] at hresult
          subst result
          exact hfinal
  | fresh =>
      rw [FilteredTreeHashProgram.computation,
        filteredTreeFreshHashComputation,
        simulate_eagerTrace_causalHashQuery, support_map] at hresult
      obtain ⟨raw, _hraw, rfl⟩ := hresult
      exact hfinal
  | leafProbe probe =>
      rw [FilteredTreeHashProgram.computation,
        filteredTreeProbeThenFreshHashComputation,
        filteredTreeFreshHashComputation, simulateQ_bind, WriterT.run_bind',
        simulate_eagerTrace_probeQuery] at hresult
      simp only [map_eq_bind_pure_comp] at hresult
      rw [simulate_eagerTrace_causalHashQuery, map_eq_bind_pure_comp,
        mem_support_bind_iff] at hresult
      obtain ⟨raw, _hraw, hpure⟩ := hresult
      rw [mem_support_bind_iff] at hpure
      obtain ⟨middle, hmiddle, hresultEq⟩ := hpure
      simp only [support_pure, Set.mem_singleton_iff,
        Function.comp_apply] at hresultEq
      subst result
      rw [mem_support_bind_iff] at hmiddle
      obtain ⟨hashResult, _hhashResult, hmiddleEq⟩ := hmiddle
      simp only [support_pure, Set.mem_singleton_iff,
        Function.comp_apply] at hmiddleEq
      subst middle
      exact hfinal

theorem filteredTreeHashComputation_support_covers_leaf_probe
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

theorem filteredTreeHashProgram_support_covers_hash_action
    (table high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (program : FilteredTreeHashProgram)
    (hprogram : filteredTreeProbingAttackerHashQueryAtFromHigh high secretKey
      selected input state = program)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (program.computation high secretKey selected input state)).run)) :
    ChainProbeTraceCovered secretKey.parameter selected
      (attackerActionFragment (.inl (.inr input)) result.1.1)
        result.1.2 result.2 := by
  intro probe hcandidate hhidden
  cases hcurrent : chainInputProbe? secretKey.parameter selected input with
  | none =>
      simp [AttackerActionTrace.chainInputProbes,
        AttackerActionTrace.hashInputs, AttackerAction.hashInput?,
        hcurrent] at hcandidate
  | some currentProbe =>
      have heq : probe = currentProbe := by
        simpa [AttackerActionTrace.chainInputProbes,
          AttackerActionTrace.hashInputs, AttackerAction.hashInput?,
          hcurrent] using hcandidate
      rw [heq] at hhidden ⊢
      have hcomputation :
          program.computation high secretKey selected input state =
            filteredProbingAttackerHashQueryAtFromHigh high secretKey selected
              input state (some currentProbe) := by
        rw [← hprogram]
        change filteredTreeHashComputationAtFromHigh high secretKey selected
          input state = _
        rw [filteredTreeHashComputationAtFromHigh_eq_chain _ _ _ _ _ _
          (filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_chainProbe
            high secretKey selected input state currentProbe hcurrent)]
        unfold filteredTreeChainHashComputation
        rfl
      rw [hcomputation] at hresult
      exact filteredProbingHashQuery_support_covers_probe table high secretKey
        selected input state currentProbe result hresult hhidden

theorem simulate_eagerTrace_filteredHighActionTraced_step_eq_map
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (((filteredHighActionTracedMappedAdversaryImpl keyHigh selected input).run).run
        state)).run =
      (fun result =>
        (((result.1.1, attackerActionFragment input result.1.1), result.1.2),
          result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((filteredHighMappedAdversaryImpl keyHigh selected input).run
            state)).run := by
  unfold filteredHighActionTracedMappedAdversaryImpl
  rw [QueryImpl.withTraceAppend_apply, WriterT.run_bind',
    WriterT.run_monadLift', StateT.run_bind, simulateQ_bind,
    StateT.run_map, simulateQ_map]
  simp [WriterT.run_tell, WriterT.run_pure, simulateQ_pure,
    map_eq_bind_pure_comp]

theorem chainProbeTraceCovered_filteredHigh_uniform_step
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex)
    (n : Nat)
    (state : CausalHashState)
    (attackerPrefix : AttackerActionTrace)
    (observedPrefix :
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hcovered : ChainProbeTraceCovered keyHigh.1.secretKey.parameter selected
      attackerPrefix state observedPrefix)
    (result : (unifSpec n × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((causalUniformImpl n).run state)).run)) :
    ChainProbeTraceCovered keyHigh.1.secretKey.parameter selected
      (attackerPrefix ++ attackerActionFragment (.inl (.inl n)) result.1.1)
      result.1.2 (observedPrefix ++ result.2) := by
  rw [simulate_eagerTrace_causalUniformImpl, support_map] at hresult
  obtain ⟨output, _houtput, rfl⟩ := hresult
  simpa using hcovered

theorem filteredHigh_uniform_step_revealsMonotone
    (table : ChainValueIndex → Digest) (n : Nat)
    (state : CausalHashState)
    (result : (unifSpec n × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((causalUniformImpl n).run state)).run)) :
    RevealsMonotone state.revealed result.1.2.revealed := by
  rw [simulate_eagerTrace_causalUniformImpl, support_map] at hresult
  obtain ⟨output, _houtput, rfl⟩ := hresult
  exact RevealsMonotone.refl state.revealed

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 2000000 in
theorem chainProbeTraceCovered_filteredHigh_hash_step
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (hashInput : HashInput)
    (state : CausalHashState)
    (attackerPrefix : AttackerActionTrace)
    (observedPrefix :
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hcovered : ChainProbeTraceCovered keyHigh.1.secretKey.parameter selected
      attackerPrefix state observedPrefix)
    (result : (HashSpec hashInput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredTreeHashComputationAtFromHigh
          (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
            hashInput state)).run)) :
    ChainProbeTraceCovered keyHigh.1.secretKey.parameter selected
      (attackerPrefix ++ attackerActionFragment (.inl (.inr hashInput))
        result.1.1)
      result.1.2 (observedPrefix ++ result.2) := by
  intro probe hcandidate hhidden
  rw [AttackerActionTrace.chainInputProbes_append] at hcandidate
  rcases List.mem_append.mp hcandidate with hold | hnew
  · apply List.mem_append_left result.2
    apply hcovered probe hold
    generalize hprogram : filteredTreeProbingAttackerHashQueryAtFromHigh
        (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
          hashInput state = program
    unfold filteredTreeHashComputationAtFromHigh at hresult
    rw [hprogram] at hresult
    have hmonotone : RevealsMonotone state.revealed
        result.1.2.revealed := by
      apply filteredTreeHashProgram_support_initial_none_of_final_none
        (table := table) (high := chainValueHighTableOfEdges keyHigh.2)
        (secretKey := keyHigh.1.secretKey) (selected := selected)
        (input := hashInput) (state := state) (program := program)
      exact hresult
    exact hmonotone probe.1 hhidden
  · cases hcurrent : chainInputProbe? keyHigh.1.secretKey.parameter selected
        hashInput with
    | none =>
        simp [AttackerActionTrace.chainInputProbes,
          AttackerActionTrace.hashInputs, AttackerAction.hashInput?,
          hcurrent] at hnew
    | some currentProbe =>
        have heq : probe = currentProbe := by
          simpa [AttackerActionTrace.chainInputProbes,
            AttackerActionTrace.hashInputs, AttackerAction.hashInput?,
            hcurrent] using hnew
        rw [heq] at hhidden ⊢
        apply List.mem_append_right observedPrefix
        have hcomputation :
            filteredTreeHashComputationAtFromHigh
                (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey
                  selected hashInput state =
              filteredProbingAttackerHashQueryAtFromHigh
                (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey
                  selected hashInput state (some currentProbe) := by
          rw [filteredTreeHashComputationAtFromHigh_eq_chain _ _ _ _ _ _
            (filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_chainProbe
              (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey
                selected hashInput state currentProbe hcurrent)]
          unfold filteredTreeChainHashComputation
          rfl
        rw [hcomputation] at hresult
        exact filteredProbingHashQuery_support_covers_probe table
          (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
            hashInput state currentProbe result hresult hhidden

theorem filteredHighMappedAdversaryImpl_hash_run
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (hashInput : HashInput)
    (state : CausalHashState) :
    (filteredHighMappedAdversaryImpl keyHigh selected
      (.inl (.inr hashInput))).run state =
        filteredTreeHashComputationAtFromHigh
          (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
            hashInput state := by
  unfold filteredHighMappedAdversaryImpl
  rw [StateT.run_mk]
  unfold filteredHighMappedAdversaryRun
  rfl

theorem filteredHigh_hash_step_revealsMonotone
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (hashInput : HashInput)
    (state : CausalHashState)
    (result : (HashSpec hashInput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredTreeHashComputationAtFromHigh
          (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
            hashInput state)).run)) :
    RevealsMonotone state.revealed result.1.2.revealed := by
  generalize hprogram : filteredTreeProbingAttackerHashQueryAtFromHigh
      (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
        hashInput state = program
  unfold filteredTreeHashComputationAtFromHigh at hresult
  rw [hprogram] at hresult
  exact filteredTreeHashProgram_support_initial_none_of_final_none
    (table := table) (high := chainValueHighTableOfEdges keyHigh.2)
    (secretKey := keyHigh.1.secretKey) (selected := selected)
    (input := hashInput) (state := state) (program := program)
    (result := result) hresult

structure FilteredHighHashStepInvariant
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (hashInput : HashInput)
    (state : CausalHashState)
    (result : (HashSpec hashInput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) : Prop where
  monotone : RevealsMonotone state.revealed result.1.2.revealed
  covered : ChainProbeTraceCovered keyHigh.1.secretKey.parameter selected
      (attackerActionFragment (.inl (.inr hashInput)) result.1.1)
        result.1.2 result.2

set_option maxHeartbeats 2000000 in
theorem filteredHigh_hash_step_invariant
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (hashInput : HashInput)
    (state : CausalHashState)
    (result : (HashSpec hashInput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredTreeHashComputationAtFromHigh
          (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
            hashInput state)).run)) :
    FilteredHighHashStepInvariant keyHigh selected hashInput state result := by
  refine { monotone := ?_, covered := ?_ }
  · generalize hprogram : filteredTreeProbingAttackerHashQueryAtFromHigh
        (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
          hashInput state = program
    unfold filteredTreeHashComputationAtFromHigh at hresult
    rw [hprogram] at hresult
    exact filteredTreeHashProgram_support_initial_none_of_final_none
      (table := table) (high := chainValueHighTableOfEdges keyHigh.2)
      (secretKey := keyHigh.1.secretKey) (selected := selected)
      (input := hashInput) (state := state) (program := program)
      (result := result) hresult
  · intro probe hcandidate hhidden
    cases hcurrent : chainInputProbe? keyHigh.1.secretKey.parameter selected
        hashInput with
    | none =>
        simp [AttackerActionTrace.chainInputProbes,
          AttackerActionTrace.hashInputs, AttackerAction.hashInput?,
          hcurrent] at hcandidate
    | some currentProbe =>
        have heq : probe = currentProbe := by
          simpa [AttackerActionTrace.chainInputProbes,
            AttackerActionTrace.hashInputs, AttackerAction.hashInput?,
            hcurrent] using hcandidate
        rw [heq] at hhidden ⊢
        have hcomputation :
            filteredTreeHashComputationAtFromHigh
                (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey
                  selected hashInput state =
              filteredProbingAttackerHashQueryAtFromHigh
                (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey
                  selected hashInput state (some currentProbe) := by
          rw [filteredTreeHashComputationAtFromHigh_eq_chain _ _ _ _ _ _
            (filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_chainProbe
              (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey
                selected hashInput state currentProbe hcurrent)]
          unfold filteredTreeChainHashComputation
          rfl
        rw [hcomputation] at hresult
        exact filteredProbingHashQuery_support_covers_probe table
          (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
            hashInput state currentProbe result hresult hhidden

structure FilteredHighHashRangeStepInvariant
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (hashInput : HashInput)
    (state : CausalHashState)
    (result : (((OracleWorld + SigningSpec).Range
      (.inl (.inr hashInput)) × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) : Prop where
  monotone : RevealsMonotone state.revealed result.1.2.revealed
  covered : ChainProbeTraceCovered keyHigh.1.secretKey.parameter selected
    (attackerActionFragment (.inl (.inr hashInput)) result.1.1)
      result.1.2 result.2

set_option maxHeartbeats 300000 in
theorem filteredHigh_hash_range_step_invariant
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (hashInput : HashInput)
    (state : CausalHashState)
    (result : (((OracleWorld + SigningSpec).Range
      (.inl (.inr hashInput)) × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((filteredHighMappedAdversaryImpl keyHigh selected
          (.inl (.inr hashInput))).run state)).run)) :
    FilteredHighHashRangeStepInvariant keyHigh selected hashInput state
      result := by
  rw [filteredHighMappedAdversaryImpl_hash_run] at hresult
  change ((HashSpec hashInput × CausalHashState) ×
    RevealProbeOracleSimulation.ActionTrace ChainValueIndex) at result
  refine { monotone := ?_, covered := ?_ }
  · generalize hprogram : filteredTreeProbingAttackerHashQueryAtFromHigh
        (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
          hashInput state = program
    unfold filteredTreeHashComputationAtFromHigh at hresult
    rw [hprogram] at hresult
    exact filteredTreeHashProgram_support_initial_none_of_final_none
      (table := table) (high := chainValueHighTableOfEdges keyHigh.2)
      (secretKey := keyHigh.1.secretKey) (selected := selected)
      (input := hashInput) (state := state) (program := program)
      (result := result) hresult
  · intro probe hcandidate hhidden
    cases hcurrent : chainInputProbe? keyHigh.1.secretKey.parameter selected
        hashInput with
    | none =>
        simp [AttackerActionTrace.chainInputProbes,
          AttackerActionTrace.hashInputs, AttackerAction.hashInput?,
          hcurrent] at hcandidate
    | some currentProbe =>
        have heq : probe = currentProbe := by
          simpa [AttackerActionTrace.chainInputProbes,
            AttackerActionTrace.hashInputs, AttackerAction.hashInput?,
            hcurrent] using hcandidate
        rw [heq] at hhidden ⊢
        have hcomputation :
            filteredTreeHashComputationAtFromHigh
                (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey
                  selected hashInput state =
              filteredProbingAttackerHashQueryAtFromHigh
                (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey
                  selected hashInput state (some currentProbe) := by
          rw [filteredTreeHashComputationAtFromHigh_eq_chain _ _ _ _ _ _
            (filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_chainProbe
              (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey
                selected hashInput state currentProbe hcurrent)]
          unfold filteredTreeChainHashComputation
          rfl
        rw [hcomputation] at hresult
        exact filteredProbingHashQuery_support_covers_probe table
          (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
            hashInput state currentProbe result hresult hhidden

theorem filteredHigh_hash_step_revealsMonotone_of_eq
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (hashInput : HashInput)
    (state : CausalHashState)
    {computation : ProbComp (((OracleWorld + SigningSpec).Range
      (.inl (.inr hashInput)) × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex)}
    {result : (((OracleWorld + SigningSpec).Range
      (.inl (.inr hashInput)) × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex)}
    (hresult : result ∈ support computation)
    (hcomputation : computation =
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredTreeHashComputationAtFromHigh
          (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
            hashInput state)).run) :
    RevealsMonotone state.revealed result.1.2.revealed := by
  rw [hcomputation] at hresult
  change ((HashSpec hashInput × CausalHashState) ×
    RevealProbeOracleSimulation.ActionTrace ChainValueIndex) at result
  generalize hprogram : filteredTreeProbingAttackerHashQueryAtFromHigh
      (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
        hashInput state = program
  unfold filteredTreeHashComputationAtFromHigh at hresult
  rw [hprogram] at hresult
  exact filteredTreeHashProgram_support_initial_none_of_final_none
    (table := table) (high := chainValueHighTableOfEdges keyHigh.2)
    (secretKey := keyHigh.1.secretKey) (selected := selected)
    (input := hashInput) (state := state) (program := program)
    (result := result) hresult

theorem chainProbeTraceCovered_filteredHigh_hash_step_of_eq
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (hashInput : HashInput)
    (state : CausalHashState)
    {computation : ProbComp (((OracleWorld + SigningSpec).Range
      (.inl (.inr hashInput)) × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex)}
    {result : (((OracleWorld + SigningSpec).Range
      (.inl (.inr hashInput)) × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex)}
    (hresult : result ∈ support computation)
    (hcomputation : computation =
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredTreeHashComputationAtFromHigh
          (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
            hashInput state)).run) :
    ChainProbeTraceCovered keyHigh.1.secretKey.parameter selected
      (attackerActionFragment (.inl (.inr hashInput)) result.1.1)
        result.1.2 result.2 := by
  rw [hcomputation] at hresult
  change ((HashSpec hashInput × CausalHashState) ×
    RevealProbeOracleSimulation.ActionTrace ChainValueIndex) at result
  intro probe hcandidate hhidden
  cases hcurrent : chainInputProbe? keyHigh.1.secretKey.parameter selected
      hashInput with
  | none =>
      simp [AttackerActionTrace.chainInputProbes,
        AttackerActionTrace.hashInputs, AttackerAction.hashInput?,
        hcurrent] at hcandidate
  | some currentProbe =>
      have heq : probe = currentProbe := by
        simpa [AttackerActionTrace.chainInputProbes,
          AttackerActionTrace.hashInputs, AttackerAction.hashInput?,
          hcurrent] using hcandidate
      rw [heq] at hhidden ⊢
      have hcomputation :
          filteredTreeHashComputationAtFromHigh
              (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey
                selected hashInput state =
            filteredProbingAttackerHashQueryAtFromHigh
              (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey
                selected hashInput state (some currentProbe) := by
        rw [filteredTreeHashComputationAtFromHigh_eq_chain _ _ _ _ _ _
          (filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_chainProbe
            (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey
              selected hashInput state currentProbe hcurrent)]
        unfold filteredTreeChainHashComputation
        rfl
      rw [hcomputation] at hresult
      exact filteredProbingHashQuery_support_covers_probe table
        (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
          hashInput state currentProbe result hresult hhidden

set_option maxHeartbeats 2000000 in
theorem chainProbeTraceCovered_filteredHigh_signing_step
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (request : SignRequest)
    (state : CausalHashState)
    (attackerPrefix : AttackerActionTrace)
    (observedPrefix :
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hcovered : ChainProbeTraceCovered keyHigh.1.secretKey.parameter selected
      attackerPrefix state observedPrefix)
    (result : (SigningSpec request × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredCausalSigningQuery keyHigh.1 selected request state)).run)) :
    ChainProbeTraceCovered keyHigh.1.secretKey.parameter selected
      (attackerPrefix ++ attackerActionFragment (.inr request) result.1.1)
      result.1.2 (observedPrefix ++ result.2) := by
  intro probe hcandidate hhidden
  rw [AttackerActionTrace.chainInputProbes_append] at hcandidate
  have hold : probe ∈
      attackerPrefix.chainInputProbes keyHigh.1.secretKey.parameter selected := by
    rcases List.mem_append.mp hcandidate with hold | hnew
    · exact hold
    · simp [AttackerActionTrace.chainInputProbes,
        AttackerActionTrace.hashInputs, AttackerAction.hashInput?] at hnew
  apply List.mem_append_left result.2
  apply hcovered probe hold
  have hreplay :=
    simulate_eagerTrace_filteredCausalSigningQuery_support_replays table
      keyHigh.1 selected request state result hresult
  exact hreplay.initial_none_of_final_none probe.1 hhidden

theorem filteredHigh_signing_step_revealsMonotone
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (request : SignRequest)
    (state : CausalHashState)
    (result : (SigningSpec request × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredCausalSigningQuery keyHigh.1 selected request state)).run)) :
    RevealsMonotone state.revealed result.1.2.revealed := by
  intro index hhidden
  exact
    (simulate_eagerTrace_filteredCausalSigningQuery_support_replays table
      keyHigh.1 selected request state result hresult)
      |>.initial_none_of_final_none index hhidden

end XmssSecurity.CappedChain
