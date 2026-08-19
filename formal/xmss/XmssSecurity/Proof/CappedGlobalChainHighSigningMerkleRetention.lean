import XmssSecurity.Proof.CappedGlobalChainHighMerkleRetention
import XmssSecurity.Proof.CappedGlobalChainHighSigningSimulator

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

def GlobalCausalSigningStateExtends
    (initial final : GlobalCausalHashState) : Prop :=
  initial.cache ≤ final.cache ∧ final.keygenCache = initial.keygenCache

theorem GlobalCausalSigningStateExtends.trans
    {first second third : GlobalCausalHashState}
    (hfirst : GlobalCausalSigningStateExtends first second)
    (hsecond : GlobalCausalSigningStateExtends second third) :
    GlobalCausalSigningStateExtends first third :=
  ⟨hfirst.1.trans hsecond.1, hsecond.2.trans hfirst.2⟩

theorem simulate_eagerTrace_globalFilteredCausalSigningAttempt_stateExtends
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSigningAttempt keyView request state)).run)) :
    GlobalCausalSigningStateExtends state result.1.2 := by
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
  obtain ⟨encoded, hencoded, rfl⟩ := hencodedTrace
  simp only [List.nil_append] at hresult
  have hcacheLe : state.cache ≤ encoded.2 :=
    Concrete.CacheReplay.randomOracle_cache_le
      (Concrete.encodingHash keyView.secretKey.parameter request.epoch
        request.message randomness) state.cache encoded hencoded
  cases hdecode : TargetSum.decodeDigest encoded.1 with
  | none =>
      simp only [hdecode, simulateQ_pure, WriterT.run_pure] at hresult
      subst result
      exact ⟨hcacheLe, rfl⟩
  | some encoding =>
      rw [hdecode, simulateQ_bind, WriterT.run_bind',
        simulate_eagerTrace_revealGlobalSignatureChains] at hresult
      simp only [pure_bind, simulateQ_pure, WriterT.run_pure] at hresult
      subst result
      simp only [Prod.map, id_eq]
      constructor
      · rw [globalSignatureRevealResult_cache]
        exact hcacheLe
      · rw [globalSignatureRevealResult_keygenCache]

theorem simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_stateExtends
    (attempts : Nat) (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSignBoundedAttempts attempts keyView request
          state)).run)) :
    GlobalCausalSigningStateExtends state result.1.2 := by
  induction attempts generalizing state result with
  | zero =>
      simp only [globalFilteredCausalSignBoundedAttempts, simulateQ_pure,
        WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨le_rfl, rfl⟩
  | succ attempts ih =>
      rw [simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_succ,
        mem_support_bind_iff] at hresult
      obtain ⟨attemptResult, hattempt, hresult⟩ := hresult
      have hattemptExtends :=
        simulate_eagerTrace_globalFilteredCausalSigningAttempt_stateExtends
          table keyView request state attemptResult hattempt
      cases hoption : attemptResult.1.1 with
      | some signature =>
          simp only [globalFilteredCausalSignTraceContinuation, hoption,
            support_pure, Set.mem_singleton_iff] at hresult
          subst result
          exact hattemptExtends
      | none =>
          simp only [globalFilteredCausalSignTraceContinuation, hoption,
            support_map] at hresult
          obtain ⟨rest, hrest, rfl⟩ := hresult
          exact hattemptExtends.trans
            (ih attemptResult.1.2 rest hrest)

theorem simulate_eagerTrace_globalFilteredCausalSigningQuery_stateExtends
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSigningQuery keyView request state)).run)) :
    GlobalCausalSigningStateExtends state result.1.2 := by
  exact simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_stateExtends
    signingAttemptLimit table keyView request state result hresult

theorem simulate_eagerTrace_globalFilteredCausalSigningQuery_merkleRetained
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (hretained : GlobalMerkleKeygenCacheRetained keyView.secretKey state)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSigningQuery keyView request state)).run)) :
    GlobalMerkleKeygenCacheRetained keyView.secretKey result.1.2 := by
  have hextends :=
    simulate_eagerTrace_globalFilteredCausalSigningQuery_stateExtends
      table keyView request state result hresult
  intro input hmerkle output hkeygen
  rw [hextends.2] at hkeygen
  exact hextends.1 (hretained input hmerkle output hkeygen)

end XmssSecurity.CappedChain
