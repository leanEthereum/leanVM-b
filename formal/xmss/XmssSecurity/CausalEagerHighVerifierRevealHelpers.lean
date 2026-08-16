import XmssSecurity.CausalEagerHighRevealCoverage

open OracleComp OracleSpec

namespace XmssSecurity

set_option maxRecDepth 1000000
set_option linter.constructorNameAsVariable false

theorem simulateQ_mapStateTBase_support_stateRelation
    {ι₀ ι₁ : Type} {spec₀ : OracleSpec ι₀} {spec₁ : OracleSpec ι₁}
    {σ τ α : Type} [EmptyCollection τ] [Append τ] [LawfulAppend τ]
    (outer : QueryImpl spec₁ (WriterT τ ProbComp))
    (inner : QueryImpl spec₀ (StateT σ (OracleComp spec₁)))
    (relation : σ → σ → Prop)
    (hrefl : ∀ state, relation state state)
    (htrans : ∀ first second third,
      relation first second → relation second third → relation first third)
    (hstep : ∀ (input : spec₀.Domain) state result,
      result ∈ support
        (((outer.mapStateTBase inner input).run state).run) →
      relation state result.1.2)
    (computation : OracleComp spec₀ α) (state : σ)
    (result : (α × σ) × τ)
    (hresult : result ∈ support
      (((simulateQ (outer.mapStateTBase inner) computation).run state).run)) :
    relation state result.1.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact hrefl state
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind, WriterT.run_bind']
        at hresult
      rw [mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      rw [support_map] at htail
      obtain ⟨tail, htail, rfl⟩ := htail
      exact htrans state head.1.2 tail.1.2
        (hstep input state head hhead)
        (ih head.1.1 head.1.2 tail htail)

theorem simulateQ_mapStateTBase_support_traceRelation
    {ι₀ ι₁ : Type} {spec₀ : OracleSpec ι₀} {spec₁ : OracleSpec ι₁}
    {σ τ α : Type} [EmptyCollection τ] [Append τ] [LawfulAppend τ]
    (outer : QueryImpl spec₁ (WriterT τ ProbComp))
    (inner : QueryImpl spec₀ (StateT σ (OracleComp spec₁)))
    (relation : σ → σ → τ → Prop)
    (hnil : ∀ state, relation state state ∅)
    (happend : ∀ first middle final left right,
      relation first middle left → relation middle final right →
        relation first final (left ++ right))
    (hstep : ∀ (input : spec₀.Domain) state result,
      result ∈ support
        (((outer.mapStateTBase inner input).run state).run) →
      relation state result.1.2 result.2)
    (computation : OracleComp spec₀ α) (state : σ)
    (result : (α × σ) × τ)
    (hresult : result ∈ support
      (((simulateQ (outer.mapStateTBase inner) computation).run state).run)) :
    relation state result.1.2 result.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact hnil state
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind, WriterT.run_bind']
        at hresult
      rw [mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      rw [support_map] at htail
      obtain ⟨tail, htail, rfl⟩ := htail
      exact happend state head.1.2 tail.1.2 head.2 tail.2
        (hstep input state head hhead)
        (ih head.1.1 head.1.2 tail htail)

set_option maxHeartbeats 1000000 in
theorem simulate_filteredHighHashOnlyVerifier_support_cache_le
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
    state.cache ≤ result.1.2.cache := by
  apply simulateQ_mapStateTBase_support_stateRelation
    (outer := RevealProbeOracleSimulation.eagerTraceImpl table)
    (inner := filteredHighHashOnlyVerifierImpl keyHigh selected)
    (relation := fun first second => first.cache ≤ second.cache)
    (hrefl := fun _ => le_rfl)
    (htrans := fun _ _ _ hfirst hsecond => hfirst.trans hsecond)
    (computation := computation) (state := state) (result := result)
  · intro input stepState stepResult hstep
    unfold QueryImpl.mapStateTBase at hstep
    rw [StateT.run_mk] at hstep
    rw [filteredHighHashOnlyVerifierImpl_run_eq] at hstep
    generalize hprogram : filteredTreeProbingAttackerHashQueryAtFromHigh
      (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
        input stepState = program
    unfold filteredTreeHashComputationAtFromHigh at hstep
    rw [hprogram] at hstep
    exact filteredTreeHashProgram_support_cache_le table
      (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected input
        stepState program stepResult hstep
  · rw [← QueryImpl.simulateQ_mapStateTBase_run]
    exact hresult

set_option maxHeartbeats 1000000 in
theorem simulate_filteredHighHashOnlyVerifier_support_resultCovered
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (computation : OracleComp HashSpec α)
    (state : CausalHashState) (covered : Set ChainValueIndex)
    (hcovered : CausalRevealsCovered covered state)
    (hforward : ChainValueIndicesForwardClosed covered)
    (result : (α × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ (filteredHighHashOnlyVerifierImpl keyHigh selected)
          computation).run state)).run)) :
    CausalResultCovered covered result := by
  let relation := fun first final
      (trace : RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
    CausalRevealsCovered covered first →
      CausalRevealsCovered covered final ∧
        CausalTraceRevealsCovered covered trace
  have hinvariant := simulateQ_mapStateTBase_support_traceRelation
    (outer := RevealProbeOracleSimulation.eagerTraceImpl table)
    (inner := filteredHighHashOnlyVerifierImpl keyHigh selected)
    (relation := relation)
    (hnil := fun current hcurrent =>
      ⟨hcurrent, by simp [CausalTraceRevealsCovered]⟩)
    (happend := fun _ _ _ _ _ hleft hright hfirst =>
      let hmiddle := hleft hfirst
      let hfinal := hright hmiddle.1
      ⟨hfinal.1, hmiddle.2.append hfinal.2⟩)
    (computation := computation) (state := state) (result := result)
    (hstep := fun input stepState stepResult hstep => by
      intro hstepCovered
      unfold QueryImpl.mapStateTBase at hstep
      rw [StateT.run_mk] at hstep
      rw [filteredHighHashOnlyVerifierImpl_run_eq] at hstep
      generalize hprogram : filteredTreeProbingAttackerHashQueryAtFromHigh
        (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
          input stepState = program
      unfold filteredTreeHashComputationAtFromHigh at hstep
      rw [hprogram] at hstep
      exact filteredTreeHashProgram_support_revealsCovered table
        (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
          input stepState program covered hstepCovered hforward stepResult
            hstep)
    (by
      rw [← QueryImpl.simulateQ_mapStateTBase_run]
      exact hresult)
  exact hinvariant hcovered

end XmssSecurity
