import XmssSecurity.CappedChain.CausalEagerHighTraceCoverage

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option linter.constructorNameAsVariable false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

def EagerTraceSupport
    (table : ChainValueIndex → Digest)
    (computation : OracleComp
      (RevealProbeOracleSimulation.World ChainValueIndex) α)
    (result : α ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) : Prop :=
  support
    ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      computation).run) result

def FilteredHighStepSupport
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : CausalHashState)
    (result : (((OracleWorld + SigningSpec).Range input × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) : Prop :=
  EagerTraceSupport table
    ((filteredHighMappedAdversaryImpl keyHigh selected input).run state) result

def FilteredHighRunSupport
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CausalHashState)
    (result : (((α × AttackerActionTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) : Prop :=
  EagerTraceSupport table
    (((simulateQ
      (filteredHighActionTracedMappedAdversaryImpl keyHigh selected)
        computation).run).run state) result

def FilteredHighStepInvariant
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : CausalHashState)
    (result : (((OracleWorld + SigningSpec).Range input × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) : Prop :=
  RevealsMonotone state.revealed result.1.2.revealed ∧
    ChainProbeTraceCovered keyHigh.1.secretKey.parameter selected
      (attackerActionFragment input result.1.1) result.1.2 result.2

def FilteredHighRunInvariant
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex)
    (state : CausalHashState)
    (result : (((α × AttackerActionTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) : Prop :=
  RevealsMonotone state.revealed result.1.2.revealed ∧
    ChainProbeTraceCovered keyHigh.1.secretKey.parameter selected
      result.1.1.2 result.1.2 result.2

theorem support_bind_apply_iff
    (mx : ProbComp α) (my : α → ProbComp β) (result : β) :
    support (mx >>= my) result ↔
      ∃ head, support mx head ∧ support (my head) result := by
  exact mem_support_bind_iff mx my result

theorem support_map_apply_iff
    (map : α → β) (computation : ProbComp α) (result : β) :
    support (map <$> computation) result ↔
      ∃ source, support computation source ∧ map source = result := by
  rw [support_map]
  rfl

theorem filteredHigh_uniform_step_support_invariant
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (n : Nat) (state : CausalHashState)
    (head : (((OracleWorld + SigningSpec).Range (.inl (.inl n)) ×
      CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hhead : support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((causalUniformImpl n).run state)).run) head) :
    RevealsMonotone state.revealed head.1.2.revealed ∧
      ChainProbeTraceCovered keyHigh.1.secretKey.parameter selected
        (attackerActionFragment (.inl (.inl n)) head.1.1)
          head.1.2 head.2 := by
  have hmonotone :=
    filteredHigh_uniform_step_revealsMonotone table n state head hhead
  have hcovered : ChainProbeTraceCovered
    keyHigh.1.secretKey.parameter selected
      (attackerActionFragment (.inl (.inl n)) head.1.1)
        head.1.2 head.2 := by
    simpa using
      (chainProbeTraceCovered_filteredHigh_uniform_step table keyHigh
        selected n state [] [] (chainProbeTraceCovered_nil _ _ _)
          head hhead)
  exact ⟨hmonotone, hcovered⟩

theorem filteredHigh_hash_step_support_invariant
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (hashInput : HashInput)
    (state : CausalHashState)
    (head : ((HashSpec hashInput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hhead : support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((filteredHighMappedAdversaryImpl keyHigh selected
          (.inl (.inr hashInput))).run state)).run) head) :
    RevealsMonotone state.revealed head.1.2.revealed ∧
      ChainProbeTraceCovered keyHigh.1.secretKey.parameter selected
        (attackerActionFragment (.inl (.inr hashInput)) head.1.1)
          head.1.2 head.2 := by
  rw [filteredHighMappedAdversaryImpl_hash_run] at hhead
  generalize hprogram : filteredTreeProbingAttackerHashQueryAtFromHigh
    (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
      hashInput state = program
  unfold filteredTreeHashComputationAtFromHigh at hhead
  rw [hprogram] at hhead
  exact ⟨filteredTreeHashProgram_support_initial_none_of_final_none
      table (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey
        selected hashInput state program head hhead,
    filteredTreeHashProgram_support_covers_hash_action table
      (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey
        selected hashInput state program hprogram head hhead⟩

theorem filteredHigh_signing_step_support_invariant
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (request : SignRequest)
    (state : CausalHashState)
    (head : (((OracleWorld + SigningSpec).Range (.inr request) ×
      CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hhead : head ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredCausalSigningQuery keyHigh.1 selected request state)).run)) :
    RevealsMonotone state.revealed head.1.2.revealed ∧
      ChainProbeTraceCovered keyHigh.1.secretKey.parameter selected
        (attackerActionFragment (.inr request) head.1.1)
          head.1.2 head.2 := by
  have hmonotone := filteredHigh_signing_step_revealsMonotone table
    keyHigh selected request state head hhead
  have hcovered : ChainProbeTraceCovered
    keyHigh.1.secretKey.parameter selected
      (attackerActionFragment (.inr request) head.1.1)
        head.1.2 head.2 := by
    simpa only [List.nil_append] using
      (chainProbeTraceCovered_filteredHigh_signing_step table keyHigh
        selected request state [] [] (chainProbeTraceCovered_nil _ _ _)
          head hhead)
  exact ⟨hmonotone, hcovered⟩

theorem filteredHighMappedAdversaryImpl_signing_run
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (request : SignRequest)
    (state : CausalHashState) :
    (filteredHighMappedAdversaryImpl keyHigh selected
      (.inr request)).run state =
        filteredCausalSigningQuery keyHigh.1 selected request state := by
  unfold filteredHighMappedAdversaryImpl
  rw [StateT.run_mk]
  unfold filteredHighMappedAdversaryRun
  rfl

theorem filteredHigh_step_support_invariant
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : CausalHashState)
    (head : (((OracleWorld + SigningSpec).Range input × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hhead : FilteredHighStepSupport table keyHigh selected input state head) :
    FilteredHighStepInvariant keyHigh selected input state head := by
  unfold FilteredHighStepSupport EagerTraceSupport at hhead
  unfold FilteredHighStepInvariant
  rcases input with (n | hashInput) | request
  · change support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((causalUniformImpl n).run state)).run) head at hhead
    exact filteredHigh_uniform_step_support_invariant table keyHigh selected n
      state head hhead
  · change ((HashSpec hashInput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) at head
    rw [filteredHighMappedAdversaryImpl_hash_run] at hhead
    generalize hprogram : filteredTreeProbingAttackerHashQueryAtFromHigh
      (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
        hashInput state = program
    unfold filteredTreeHashComputationAtFromHigh at hhead
    rw [hprogram] at hhead
    exact ⟨filteredTreeHashProgram_support_initial_none_of_final_none
        table (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey
          selected hashInput state program head hhead,
      filteredTreeHashProgram_support_covers_hash_action table
        (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey
          selected hashInput state program hprogram head hhead⟩
  · rw [filteredHighMappedAdversaryImpl_signing_run] at hhead
    exact filteredHigh_signing_step_support_invariant table keyHigh selected
      request state head hhead

theorem simulate_filteredHighActionTraced_query_bind_support_invariant
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input →
      OracleComp (OracleWorld + SigningSpec) α)
    (state : CausalHashState)
    (hheadInvariant : ∀ head,
      FilteredHighStepSupport table keyHigh selected input state head →
        FilteredHighStepInvariant keyHigh selected input state head)
    (htailInvariant : ∀ output nextState tail,
      FilteredHighRunSupport table keyHigh selected (next output) nextState tail →
        FilteredHighRunInvariant keyHigh selected nextState tail)
    (result : (((α × AttackerActionTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : FilteredHighRunSupport table keyHigh selected
      (query input >>= next) state result) :
    FilteredHighRunInvariant keyHigh selected state result := by
  unfold FilteredHighRunSupport EagerTraceSupport at hresult
  simp only [simulateQ_query_bind, WriterT.run_bind', StateT.run_bind,
    simulateQ_bind] at hresult
  rw [support_bind_apply_iff] at hresult
  obtain ⟨head, hhead, htail⟩ := hresult
  rw [support_map_apply_iff] at htail
  obtain ⟨tail, htail, rfl⟩ := htail
  rw [HasQuery.instOfMonadLift_query, simulateQ_query] at hhead
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map] at hhead
  rw [simulate_eagerTrace_filteredHighActionTraced_step_eq_map,
    support_map_apply_iff] at hhead
  obtain ⟨rawHead, hrawHead, rfl⟩ := hhead
  rw [StateT.run_map, simulateQ_map, WriterT.run_map',
    support_map_apply_iff] at htail
  obtain ⟨rawTail, hrawTail, rfl⟩ := htail
  simp only [Function.comp_apply, Prod.map, Prod.map_apply, id_eq] at hrawTail ⊢
  have hhead := hheadInvariant rawHead (by
    unfold FilteredHighStepSupport EagerTraceSupport
    exact hrawHead)
  have htail := htailInvariant rawHead.1.1 rawHead.1.2 rawTail (by
    unfold FilteredHighRunSupport EagerTraceSupport
    exact hrawTail)
  unfold FilteredHighStepInvariant at hhead
  unfold FilteredHighRunInvariant at htail ⊢
  exact ⟨hhead.1.trans htail.1,
    (hhead.2.mono_state htail.1).append htail.2⟩

set_option maxHeartbeats 300000 in
theorem simulate_filteredHighActionTraced_support_chainProbeTraceCovered
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CausalHashState)
    (result : (((α × AttackerActionTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : FilteredHighRunSupport table keyHigh selected computation state
      result) :
    FilteredHighRunInvariant keyHigh selected state result := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      unfold FilteredHighRunSupport EagerTraceSupport at hresult
      simp only [simulateQ_pure, WriterT.run_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      unfold FilteredHighRunInvariant
      exact ⟨RevealsMonotone.refl state.revealed,
        chainProbeTraceCovered_nil _ _ _⟩
  | query_bind input next ih =>
      apply simulate_filteredHighActionTraced_query_bind_support_invariant
        table keyHigh selected input next state
      · intro head hhead
        exact filteredHigh_step_support_invariant table keyHigh selected input
          state head hhead
      · intro output nextState tail htail
        exact ih output nextState tail htail
      · exact hresult

end XmssSecurity.CappedChain
