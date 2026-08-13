import XmssSecurity.CausalDirectReduction

open OracleComp OracleSpec

namespace XmssSecurity

noncomputable local instance directStepSampleableChainTable :
    SampleableType (ChainValueIndex → Digest) :=
  SampleableType.ofFintype (ChainValueIndex → Digest)

noncomputable def filteredDirectLazyHashStepAt
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) : Option (ChainValueIndex × Digest) →
    ProbComp ((HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
  | none => filteredCausalLazyAttackerHashStep secretKey selected input state
  | some probe =>
      match state.revealed probe.1 with
      | some _ => filteredCausalLazyAttackerHashStep
          secretKey selected input state
      | none => do
          let result ← filteredCausalLazyAttackerHashStep
            secretKey selected input state
          pure (result.1,
            .probe probe.1 probe.2 :: result.2)

noncomputable def filteredDirectLazyHashStep
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) :
    ProbComp ((HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  filteredDirectLazyHashStepAt secretKey selected input state
    (chainInputProbe? secretKey.parameter selected input)

def prependDirectProbeContinuation
    (probe : ChainValueIndex × Digest)
    (continuation : (ChainValueIndex → Digest) →
      ((HashOutput × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α)
    (table : ChainValueIndex → Digest)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) : ProbComp α :=
  continuation table (result.1,
    RevealProbeOracleSimulation.ObservedAction.probe
      probe.1 probe.2 :: result.2)

theorem simulate_eagerTrace_probeQuery
    (table : ChainValueIndex → Digest) (index : ChainValueIndex)
    (target : Digest) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (RevealProbeOracleSimulation.probeQuery index target)).run =
        pure ((), [RevealProbeOracleSimulation.ObservedAction.probe
          index target]) := by
  simp [RevealProbeOracleSimulation.probeQuery,
    RevealProbeOracleSimulation.eagerTraceImpl,
    RevealProbeOracleSimulation.eagerImpl,
    RevealProbeOracleSimulation.traceFragment,
    QueryImpl.withTraceAppend_apply, WriterT.run_tell]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
theorem evalDist_installed_filteredProbingAttackerHashQueryAt_continuation_eq_lazy
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (probe? : Option (ChainValueIndex × Digest))
    (continuation : (ChainValueIndex → Digest) →
      ((HashOutput × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredProbingAttackerHashQueryAt
          secretKey selected input state probe?)).run
      continuation (causalInstalledTable result.1.2 base) result] =
    𝒟[do
      let result ← filteredDirectLazyHashStepAt
        secretKey selected input state probe?
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  cases probe? with
  | none =>
      simp only [filteredProbingAttackerHashQueryAt,
        filteredDirectLazyHashStepAt]
      exact
        evalDist_installed_filteredCausalAttackerHashQuery_continuation_eq_lazy
          secretKey selected input state continuation
  | some probe =>
      cases hrevealed : state.revealed probe.1 with
      | some value =>
          simp only [filteredProbingAttackerHashQueryAt,
            filteredDirectLazyHashStepAt, hrevealed]
          exact
            evalDist_installed_filteredCausalAttackerHashQuery_continuation_eq_lazy
              secretKey selected input state continuation
      | none =>
          simp only [filteredProbingAttackerHashQueryAt,
            filteredDirectLazyHashStepAt, hrevealed]
          simp only [simulateQ_bind, WriterT.run_bind',
            map_eq_bind_pure_comp, bind_assoc]
          simp_rw [simulate_eagerTrace_probeQuery]
          simp only [pure_bind, List.singleton_append, Function.comp_apply]
          exact
            evalDist_installed_filteredCausalAttackerHashQuery_continuation_eq_lazy
              (α := α) (secretKey := secretKey) (selected := selected)
              (input := input) (state := state)
              (continuation := prependDirectProbeContinuation probe continuation)

theorem simulate_eagerImpl_filteredCausalAttackerHashQuery_support_revealsAgree
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (selected : ChainIndex) (input : HashInput) (state : CausalHashState)
    (result : HashOutput × CausalHashState)
    (hagrees : CausalRevealsAgree table state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((filteredCausalAttackerHashQuery
          secretKey selected input).run state))) :
    CausalRevealsAgree table result.2 := by
  generalize hplan :
    filteredCausalAttackerHashPlan secretKey selected input state = plan
  cases plan with
  | cached output =>
      rw [filteredCausalAttackerHashQuery_run, hplan] at hresult
      simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact hagrees.causalRecordedState secretKey selected input
  | conditioned digest =>
      rw [filteredCausalAttackerHashQuery_run, hplan,
        simulateQ_bind,
        RevealProbeOracleSimulation.simulate_eagerImpl_liftProbComp,
        mem_support_bind_iff] at hresult
      obtain ⟨output, _houtput, hpure⟩ := hresult
      subst result
      exact (hagrees.causalRecordedState secretKey selected input).setCache _
  | fresh =>
      rw [filteredCausalAttackerHashQuery_run, hplan] at hresult
      exact simulate_eagerImpl_causalHashQuery_support_revealsAgree table input
        (causalRecordedState secretKey selected input state) result
          (hagrees.causalRecordedState secretKey selected input) hresult
  | reveal index =>
      rw [filteredCausalAttackerHashQuery_run, hplan] at hresult
      unfold causalRevealHashQuery at hresult
      rw [simulateQ_bind,
        RevealProbeOracleSimulation.simulate_eagerImpl_revealQuery,
        pure_bind, simulateQ_bind,
        RevealProbeOracleSimulation.simulate_eagerImpl_liftProbComp,
        mem_support_bind_iff] at hresult
      obtain ⟨output, _houtput, hpure⟩ := hresult
      subst result
      exact hagrees.causalRevealResultState secretKey selected input index
        (table index) output rfl

theorem simulate_eagerImpl_filteredCausalAttackerHashQuery_support_revealsLe
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (selected : ChainIndex) (input : HashInput) (state : CausalHashState)
    (result : HashOutput × CausalHashState)
    (hagrees : CausalRevealsAgree table state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((filteredCausalAttackerHashQuery
          secretKey selected input).run state))) :
    CausalRevealsLe state result.2 := by
  generalize hplan :
    filteredCausalAttackerHashPlan secretKey selected input state = plan
  cases plan with
  | cached output =>
      rw [filteredCausalAttackerHashQuery_run, hplan] at hresult
      simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact CausalRevealsLe.causalRecordedState secretKey selected input state
  | conditioned digest =>
      rw [filteredCausalAttackerHashQuery_run, hplan,
        simulateQ_bind,
        RevealProbeOracleSimulation.simulate_eagerImpl_liftProbComp,
        mem_support_bind_iff] at hresult
      obtain ⟨output, _houtput, hpure⟩ := hresult
      subst result
      exact (CausalRevealsLe.causalRecordedState
        secretKey selected input state).trans (CausalRevealsLe.setCache _ _)
  | fresh =>
      rw [filteredCausalAttackerHashQuery_run, hplan] at hresult
      exact (CausalRevealsLe.causalRecordedState
        secretKey selected input state).trans
          (simulate_eagerImpl_causalHashQuery_support_revealsLe
            table input (causalRecordedState secretKey selected input state)
              result hresult)
  | reveal index =>
      rw [filteredCausalAttackerHashQuery_run, hplan] at hresult
      unfold causalRevealHashQuery at hresult
      rw [simulateQ_bind,
        RevealProbeOracleSimulation.simulate_eagerImpl_revealQuery,
        pure_bind, simulateQ_bind,
        RevealProbeOracleSimulation.simulate_eagerImpl_liftProbComp,
        mem_support_bind_iff] at hresult
      obtain ⟨output, _houtput, hpure⟩ := hresult
      subst result
      apply CausalRevealsLe.causalRevealResultState
      intro previous hprevious
      exact (hagrees index previous hprevious).symm

theorem simulate_eagerTrace_filteredCausalAttackerHashQuery_support_installedTable
    (base : ChainValueIndex → Digest) (secretKey : SecretKey)
    (selected : ChainIndex) (input : HashInput) (state : CausalHashState)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl
        (causalInstalledTable state base))
        ((filteredCausalAttackerHashQuery
          secretKey selected input).run state)).run)) :
    causalInstalledTable result.1.2 base =
      causalInstalledTable state base := by
  have hprojection := simulate_eagerTrace_projection_mem_support
    (causalInstalledTable state base)
    ((filteredCausalAttackerHashQuery secretKey selected input).run state)
      result hresult
  apply causalInstalledTable_eq_of_agrees_of_revealsLe
    (causalInstalledTable state base) base state result.1.2 rfl
  · exact simulate_eagerImpl_filteredCausalAttackerHashQuery_support_revealsAgree
      (causalInstalledTable state base) secretKey selected input state result.1
        (causalRevealsAgree_causalInstalledTable state base) hprojection
  · exact simulate_eagerImpl_filteredCausalAttackerHashQuery_support_revealsLe
      (causalInstalledTable state base) secretKey selected input state result.1
        (causalRevealsAgree_causalInstalledTable state base) hprojection

theorem simulate_eagerTrace_filteredProbingAttackerHashQueryAt_support_installedTable
    (base : ChainValueIndex → Digest) (secretKey : SecretKey)
    (selected : ChainIndex) (input : HashInput) (state : CausalHashState)
    (probe? : Option (ChainValueIndex × Digest))
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl
        (causalInstalledTable state base))
        (filteredProbingAttackerHashQueryAt
          secretKey selected input state probe?)).run)) :
    causalInstalledTable result.1.2 base =
      causalInstalledTable state base := by
  cases probe? with
  | none =>
      simp only [filteredProbingAttackerHashQueryAt] at hresult
      exact simulate_eagerTrace_filteredCausalAttackerHashQuery_support_installedTable
        base secretKey selected input state result hresult
  | some probe =>
      cases hrevealed : state.revealed probe.1 with
      | some value =>
          simp only [filteredProbingAttackerHashQueryAt, hrevealed] at hresult
          exact simulate_eagerTrace_filteredCausalAttackerHashQuery_support_installedTable
            base secretKey selected input state result hresult
      | none =>
          simp only [filteredProbingAttackerHashQueryAt, hrevealed,
            simulateQ_bind, WriterT.run_bind'] at hresult
          simp_rw [simulate_eagerTrace_probeQuery] at hresult
          simp only [pure_bind, List.singleton_append,
            support_map] at hresult
          obtain ⟨rest, hrest, heq⟩ := hresult
          have hstate := congrArg (fun x => x.1) heq
          simp only [Prod.map, id_eq] at hstate
          rw [← hstate]
          exact simulate_eagerTrace_filteredCausalAttackerHashQuery_support_installedTable
            base secretKey selected input state rest hrest

set_option maxRecDepth 100000 in
theorem evalDist_installed_filteredProbingAttackerHashQueryAt_fixedContinuation_eq_lazy
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (probe? : Option (ChainValueIndex × Digest))
    (continuation : (ChainValueIndex → Digest) →
      ((HashOutput × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredProbingAttackerHashQueryAt
          secretKey selected input state probe?)).run
      continuation table result] =
    𝒟[do
      let result ← filteredDirectLazyHashStepAt
        secretKey selected input state probe?
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  calc
    _ = 𝒟[do
        let base ← $ᵗ (ChainValueIndex → Digest)
        let table := causalInstalledTable state base
        let result ← (simulateQ
          (RevealProbeOracleSimulation.eagerTraceImpl table)
          (filteredProbingAttackerHashQueryAt
            secretKey selected input state probe?)).run
        continuation (causalInstalledTable result.1.2 base) result] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro base
      simp only
      apply RevealProbeOracleSimulation.evalDist_bind_congr_of_support
      intro result hresult
      rw [simulate_eagerTrace_filteredProbingAttackerHashQueryAt_support_installedTable
        base secretKey selected input state probe? result hresult]
    _ = _ :=
      evalDist_installed_filteredProbingAttackerHashQueryAt_continuation_eq_lazy
        secretKey selected input state probe? continuation

end XmssSecurity
