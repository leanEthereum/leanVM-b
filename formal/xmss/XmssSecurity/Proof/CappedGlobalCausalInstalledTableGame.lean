import XmssSecurity.Proof.CappedGlobalCausalInstalledResampling

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

theorem simulate_eagerTrace_globalCausalAttackerHashQuery_support_installedTable
    (base : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl
        (globalCausalInstalledTable state base))
        ((globalCausalAttackerHashQuery secretKey input).run state)).run)) :
    globalCausalInstalledTable result.1.2 base =
      globalCausalInstalledTable state base := by
  generalize hplan : globalCausalAttackerHashPlan secretKey input state = plan
  cases plan with
  | cached output =>
      rw [globalCausalAttackerHashQuery_run, hplan] at hresult
      simp only [simulateQ_pure, WriterT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact globalCausalInstalledTable_globalCausalRecordedState
        secretKey input state base
  | redirect output =>
      rw [simulate_eagerTrace_globalCausalAttackerHashQuery_redirect_eq
        (globalCausalInstalledTable state base) secretKey input state output
          hplan] at hresult
      simp only [WriterT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      rw [globalCausalInstalledTable_setCache,
        globalCausalInstalledTable_globalCausalRecordedState]
  | fresh =>
      rw [simulate_eagerTrace_globalCausalAttackerHashQuery_fresh_eq_globalCausalHashQuery
          (globalCausalInstalledTable state base) secretKey input state hplan,
        simulate_eagerTrace_globalCausalHashQuery, support_map] at hresult
      obtain ⟨raw, _hraw, rfl⟩ := hresult
      change globalCausalInstalledTable
          { (globalCausalRecordedState secretKey input state) with
            cache := raw.2 } base = globalCausalInstalledTable state base
      rw [globalCausalInstalledTable_setCache,
        globalCausalInstalledTable_globalCausalRecordedState]
  | reveal index =>
      rw [simulate_eagerTrace_globalCausalAttackerHashQuery_reveal_eq
          (globalCausalInstalledTable state base) secretKey input state index
            hplan,
        RevealProbeOracleSimulation.simulate_eagerTrace_reveal_then_liftProbComp,
        support_map] at hresult
      obtain ⟨output, _houtput, rfl⟩ := hresult
      rw [globalCausalInstalledTable_globalCausalRevealResultState]
      exact Function.update_eq_self index
        (globalCausalInstalledTable state base)

theorem simulate_eagerTrace_revealGlobalSignatureOption_support_installedTable
    (base : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (request : SignRequest)
    (signatureOption : Option Signature) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl
        (globalCausalInstalledTable state base))
        ((revealGlobalSignatureOption secretKey request signatureOption).run
          state)).run)) :
    globalCausalInstalledTable result.1.2 base =
      globalCausalInstalledTable state base := by
  cases signatureOption with
  | none =>
      rw [revealGlobalSignatureOption_run] at hresult
      simp only [simulateQ_pure, WriterT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      rfl
  | some signature =>
      cases hdecode : TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash state.cache secretKey.parameter
            request.epoch (request.message, signature.randomness)) with
      | none =>
          rw [revealGlobalSignatureOption_run] at hresult
          simp only [hdecode, simulateQ_pure, WriterT.run_pure,
            support_pure, Set.mem_singleton_iff] at hresult
          subst result
          rfl
      | some encoding =>
          rw [simulate_eagerTrace_revealGlobalSignatureOption_some_of_decode
            (globalCausalInstalledTable state base) secretKey request signature
              state encoding hdecode] at hresult
          simp only [support_pure, Set.mem_singleton_iff] at hresult
          subst result
          let table := globalCausalInstalledTable state base
          have hinvariant :=
            globalSignatureRevealResult_installedInvariant table request
              encoding allChains signature state
                (globalCausalRevealsAgree_globalCausalInstalledTable state base)
          exact globalCausalInstalledTable_eq_of_agrees_of_revealsLe
            table base state
              (globalSignatureRevealResult table request encoding allChains
                signature state).2 rfl hinvariant.1 hinvariant.2

theorem simulate_eagerTrace_globalCausalSigningQueryAfterRealRom_support_installedTable
    (base : GlobalChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl
        (globalCausalInstalledTable state base))
        (globalCausalSigningQueryAfterRealRom
          publicKey secretKey request state)).run)) :
    globalCausalInstalledTable result.1.2 base =
      globalCausalInstalledTable state base := by
  rw [simulate_eagerTrace_globalCausalSigningQueryAfterRealRom,
    mem_support_bind_iff] at hresult
  obtain ⟨signed, hsigned, hrest⟩ := hresult
  have htable : globalCausalInstalledTable
      { state with cache := signed.2 } base =
        globalCausalInstalledTable state base :=
    globalCausalInstalledTable_setCache state base signed.2
  have hfinal :=
    simulate_eagerTrace_revealGlobalSignatureOption_support_installedTable
      base secretKey request signed.1 { state with cache := signed.2 }
        result hrest
  exact hfinal.trans htable

end XmssSecurity.CappedChain
