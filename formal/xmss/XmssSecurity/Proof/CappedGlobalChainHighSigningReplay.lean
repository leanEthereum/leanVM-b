import XmssSecurity.Proof.CappedGlobalChainHighHashReplay

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

theorem GlobalCausalHashState.recordReveal_transition
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (value : Digest) :
    CausalRevealTransition state.revealed index value
      (state.recordReveal index value).revealed := by
  constructor
  · simp [GlobalCausalHashState.recordReveal]
  · intro candidate hne
    simp [GlobalCausalHashState.recordReveal, Function.update_of_ne hne]

theorem globalSignatureRevealResult_replays
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (chains : List ChainIndex) (signature : Signature)
    (state : GlobalCausalHashState) :
    ReplaysCausalReveals state.revealed
      (globalSignatureRevealTrace table request encoding chains)
      (globalSignatureRevealResult table request encoding chains signature
        state).2.revealed := by
  induction chains generalizing signature state with
  | nil => exact ReplaysCausalReveals.nil state.revealed
  | cons chain chains ih =>
      let index : GlobalChainValueIndex :=
        (chain, request.epoch, encoding chain)
      rw [globalSignatureRevealTrace, globalSignatureRevealResult]
      apply ReplaysCausalReveals.reveal state.revealed _ index (table index) _
        (state.recordReveal index (table index)).revealed
      · exact state.recordReveal_transition index (table index)
      · exact ih _ _

theorem simulate_eagerTrace_globalFilteredCausalSigningAttempt_support_replays
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSigningAttempt keyView request state)).run)) :
    ReplaysCausalReveals state.revealed result.2 result.1.2.revealed := by
  unfold globalFilteredCausalSigningAttempt at hresult
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp,
    mem_support_bind_iff] at hresult
  obtain ⟨randomnessTrace, hrandomnessTrace, hresult⟩ := hresult
  rw [support_map] at hrandomnessTrace
  obtain ⟨randomness, _hrandomness, rfl⟩ := hrandomnessTrace
  simp only [List.nil_append] at hresult
  rw [show (Prod.map id
    (fun trace : RevealProbeOracleSimulation.ActionTrace
      GlobalChainValueIndex => trace)) = id from rfl, id_map] at hresult
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp,
    mem_support_bind_iff] at hresult
  obtain ⟨encodedTrace, hencodedTrace, hresult⟩ := hresult
  rw [support_map] at hencodedTrace
  obtain ⟨encoded, _hencoded, rfl⟩ := hencodedTrace
  simp only [List.nil_append] at hresult
  cases hdecode : TargetSum.decodeDigest encoded.1 with
  | none =>
      simp only [hdecode, simulateQ_pure, WriterT.run_pure] at hresult
      subst result
      exact ReplaysCausalReveals.nil state.revealed
  | some encoding =>
      rw [hdecode, simulateQ_bind, WriterT.run_bind',
        simulate_eagerTrace_revealGlobalSignatureChains] at hresult
      simp only [pure_bind, simulateQ_pure, WriterT.run_pure] at hresult
      subst result
      simpa using globalSignatureRevealResult_replays table request encoding
        allChains
        (Concrete.CacheReplay.signWithEncoding keyView.cache keyView.secretKey
          request.epoch randomness encoding)
        ({ state with cache := encoded.2 } : GlobalCausalHashState)

theorem simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_support_replays
    (attempts : Nat) (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSignBoundedAttempts attempts keyView request
          state)).run)) :
    ReplaysCausalReveals state.revealed result.2 result.1.2.revealed := by
  induction attempts generalizing state result with
  | zero =>
      simp only [globalFilteredCausalSignBoundedAttempts, simulateQ_pure,
        WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ReplaysCausalReveals.nil state.revealed
  | succ attempts ih =>
      rw [simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_succ,
        mem_support_bind_iff] at hresult
      obtain ⟨attemptResult, hattempt, hresult⟩ := hresult
      have hattemptReplay :=
        simulate_eagerTrace_globalFilteredCausalSigningAttempt_support_replays
          table keyView request state attemptResult hattempt
      cases hoption : attemptResult.1.1 with
      | some signature =>
          simp only [globalFilteredCausalSignTraceContinuation, hoption,
            support_pure, Set.mem_singleton_iff] at hresult
          subst result
          exact hattemptReplay
      | none =>
          simp only [globalFilteredCausalSignTraceContinuation, hoption,
            support_map] at hresult
          obtain ⟨rest, hrest, rfl⟩ := hresult
          exact hattemptReplay.append (ih attemptResult.1.2 rest hrest)

theorem simulate_eagerTrace_globalFilteredCausalSigningQuery_support_replays
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSigningQuery keyView request state)).run)) :
    ReplaysCausalReveals state.revealed result.2 result.1.2.revealed := by
  exact
    simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_support_replays
      signingAttemptLimit table keyView request state result hresult

theorem relTriple_programmed_monitoredGlobalSigningQuery
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftCache : QueryCache HashSpec)
    (rightState : GlobalMonitoredCausalState)
    (hstate : GlobalMonitoredFilteredStateRelation left right.1 leftCache
      rightState)
    (request : SignRequest) :
    RelTriple
      ((simulateQ romImpl
        (Concrete.scheme.sign left.publicKey
          (Concrete.materializePrecomputation left.cache left.secretKey)
          request.epoch request.message)).run leftCache)
      ((monitorGlobalCausalTrace right.1.2 fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
          (globalFilteredCausalSigningQuery right.1.1 request
            causalState)).run).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredFilteredStateRelation left right.1 leftResult.2
            rightResult.2) ∨ rightResult.2.bad) := by
  rcases hstate with
    ⟨monitor, hmonitor, hmonitorAgrees, hrevealed, hcausal, hretained⟩
  apply relTriple_monitorGlobalCausalTrace_of_filtered_until_hit left right.1
    _ _ rightState monitor hmonitor hmonitorAgrees hrevealed
  · apply relTriple_post_mono
      (relTriple_programmed_globalFilteredCausalSigningQuery left right hrel
        hleftSupport hrightSupport leftCache rightState.causal hcausal request)
    intro leftResult rightResult hresult
    exact Or.inl hresult
  · intro result hresult
    constructor
    · exact RevealProbeOracleSimulation.simulate_eagerTrace_support_traceAgrees
        right.1.2 _ result hresult
    · exact
        simulate_eagerTrace_globalFilteredCausalSigningQuery_support_replays
          right.1.2 right.1.1 request rightState.causal result hresult
  · intro result hresult
    exact simulate_eagerTrace_globalFilteredCausalSigningQuery_merkleRetained
      right.1.2 right.1.1 request rightState.causal hretained result hresult

end XmssSecurity.CappedChain
