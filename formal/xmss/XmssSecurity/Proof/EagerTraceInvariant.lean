import XmssSecurity.Proof.FirstLaneEagerBound

open OracleComp OracleSpec

namespace XmssSecurity

theorem simulateQ_eagerTrace_support_invariant
    {spec : OracleSpec ι} {State : Type}
    [Fintype Index] [DecidableEq Index]
    (table : Index → Digest)
    (impl : QueryImpl spec
      (StateT State (OracleComp (FirstLaneOracleSimulation.World Index))))
    (Invariant : State →
      FirstLaneOracleSimulation.ActionTrace Index → State → Prop)
    (empty : ∀ state, Invariant state [] state)
    (append : ∀ initial middle final headTrace tailTrace,
      Invariant initial headTrace middle →
      Invariant middle tailTrace final →
      Invariant initial (headTrace ++ tailTrace) final)
    (step : ∀ (input : spec.Domain) (state : State)
      (result : (spec.Range input × State) ×
        FirstLaneOracleSimulation.ActionTrace Index),
      result ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          ((impl input).run state)).run) →
      Invariant state result.2 result.1.2)
    (computation : OracleComp spec α) (initialState : State)
    (result : (α × State) ×
      FirstLaneOracleSimulation.ActionTrace Index)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ impl computation).run initialState)).run)) :
    Invariant initialState result.2 result.1.2 := by
  induction computation using OracleComp.inductionOn generalizing
      initialState result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact empty initialState
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_bind,
        WriterT.run_bind', mem_support_bind_iff] at hresult
      obtain ⟨⟨⟨output, middleState⟩, headTrace⟩, hhead,
        hrestMapped⟩ := hresult
      rw [support_map] at hrestMapped
      obtain ⟨suffixResult, hsuffix, heq⟩ := hrestMapped
      rw [simulateQ_spec_query] at hhead
      have hfirst := step input initialState
        ((output, middleState), headTrace) hhead
      have hrest := ih output middleState suffixResult hsuffix
      have hcomposed := append initialState middleState suffixResult.1.2
        headTrace suffixResult.2 hfirst hrest
      simpa using Eq.mp (congrArg (fun candidate =>
        Invariant initialState candidate.2 candidate.1.2) heq) hcomposed

end XmssSecurity
