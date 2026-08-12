import XmssSecurity.CausalStateInvariantSimulation

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

noncomputable def eagerCausalVerifierXmssRomImpl
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (chain : ChainIndex) :
    QueryImpl OracleWorld (StateT CausalHashState ProbComp) :=
  fun input state =>
    simulateQ (RevealProbeOracleSimulation.eagerImpl table)
      ((causalVerifierXmssRomImpl secretKey chain input).run state)

theorem eagerCausalVerifierXmssRomImpl_preservesRevealsAgree
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (chain : ChainIndex) :
    QueryImpl.PreservesInv
      (eagerCausalVerifierXmssRomImpl table secretKey chain)
      (CausalRevealsAgree table) := by
  intro input state hagrees result hresult
  cases input with
  | inl n =>
      exact simulate_eagerImpl_causalUniformImpl_support_revealsAgree
        table n state result hagrees hresult
  | inr input =>
      exact simulate_eagerImpl_causalAttackerHashQuery_support_revealsAgree
        table secretKey chain input state result hagrees hresult

theorem simulate_eagerImpl_simulate_causalVerifierXmssRomImpl_support_revealsAgree
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (chain : ChainIndex) (computation : OracleComp OracleWorld α)
    (state : CausalHashState) (result : α × CausalHashState)
    (hagrees : CausalRevealsAgree table state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((simulateQ (causalVerifierXmssRomImpl secretKey chain)
          computation).run state))) :
    CausalRevealsAgree table result.2 := by
  have hcollapse := simulateQ_StateT_compose
    (causalVerifierXmssRomImpl secretKey chain)
    (RevealProbeOracleSimulation.eagerImpl table)
    (eagerCausalVerifierXmssRomImpl table secretKey chain)
    (fun _ _ => rfl) computation state
  rw [hcollapse] at hresult
  exact OracleComp.simulateQ_run_preservesInv
    (eagerCausalVerifierXmssRomImpl table secretKey chain)
    (CausalRevealsAgree table)
    (eagerCausalVerifierXmssRomImpl_preservesRevealsAgree
      table secretKey chain)
    computation state hagrees result hresult

theorem simulate_eagerImpl_causalSigningQuery_support_revealsAgree
    (table : ChainValueIndex → Digest) (publicKey : PublicKey)
    (secretKey : SecretKey) (chain : ChainIndex) (request : SignRequest)
    (state : CausalHashState) (result : Option Signature × CausalHashState)
    (hagrees : CausalRevealsAgree table state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((do
          let signature ← simulateQ causalXmssRomImpl
            (Concrete.scheme.sign publicKey secretKey request.epoch
              request.message)
          revealFixedChainSignatureOption secretKey chain request signature).run
            state))) :
    CausalRevealsAgree table result.2 := by
  rw [StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at hresult
  obtain ⟨signed, hsigned, hrevealed⟩ := hresult
  have hsignedAgrees :=
    simulate_eagerImpl_simulate_causalXmssRomImpl_support_revealsAgree
      table
      (Concrete.scheme.sign publicKey secretKey request.epoch request.message)
      state signed hagrees hsigned
  exact
    simulate_eagerImpl_revealFixedChainSignatureOption_support_revealsAgree
      table secretKey chain request signed.1 signed.2 result
      hsignedAgrees hrevealed

noncomputable def eagerCausalMappedAdversaryImpl
    (table : ChainValueIndex → Digest) (publicKey : PublicKey)
    (secretKey : SecretKey) (chain : ChainIndex) :
    QueryImpl (OracleWorld + SigningSpec) (StateT CausalHashState ProbComp) :=
  fun input state =>
    simulateQ (RevealProbeOracleSimulation.eagerImpl table)
      ((causalMappedAdversaryImpl publicKey secretKey chain input).run state)

theorem eagerCausalMappedAdversaryImpl_preservesRevealsAgree
    (table : ChainValueIndex → Digest) (publicKey : PublicKey)
    (secretKey : SecretKey) (chain : ChainIndex) :
    QueryImpl.PreservesInv
      (eagerCausalMappedAdversaryImpl table publicKey secretKey chain)
      (CausalRevealsAgree table) := by
  intro input state hagrees result hresult
  rcases input with worldInput | request
  · rcases worldInput with n | hashInput
    · exact simulate_eagerImpl_causalUniformImpl_support_revealsAgree
        table n state result hagrees hresult
    · exact simulate_eagerImpl_causalAttackerHashQuery_support_revealsAgree
        table secretKey chain hashInput state result hagrees hresult
  · exact simulate_eagerImpl_causalSigningQuery_support_revealsAgree
      table publicKey secretKey chain request state result hagrees hresult

theorem simulate_eagerImpl_causalActionTracedMappedAdversaryImpl_step_support_revealsAgree
    (table : ChainValueIndex → Digest) (publicKey : PublicKey)
    (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState)
    (result : (((OracleWorld + SigningSpec).Range input ×
      AttackerActionTrace) × CausalHashState))
    (hagrees : CausalRevealsAgree table state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        (((causalActionTracedMappedAdversaryImpl publicKey secretKey chain input).run
          |>.run state)))) :
    CausalRevealsAgree table result.2 := by
  unfold causalActionTracedMappedAdversaryImpl at hresult
  rw [QueryImpl.withTraceAppend_apply, WriterT.run_bind',
    WriterT.run_monadLift', StateT.run_bind, simulateQ_bind,
    mem_support_bind_iff] at hresult
  obtain ⟨handled, hhandled, hcontinued⟩ := hresult
  rw [StateT.run_map, simulateQ_map, support_map] at hhandled
  obtain ⟨base, hbase, heq⟩ := hhandled
  subst handled
  have hhandledAgrees :=
    eagerCausalMappedAdversaryImpl_preservesRevealsAgree
      table publicKey secretKey chain input state hagrees base hbase
  simp [WriterT.run_tell] at hcontinued
  subst result
  exact hhandledAgrees

theorem simulate_eagerImpl_simulate_causalActionTracedMappedAdversaryImpl_support_revealsAgree
    (table : ChainValueIndex → Digest) (publicKey : PublicKey)
    (secretKey : SecretKey) (chain : ChainIndex)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CausalHashState)
    (result : ((α × AttackerActionTrace) × CausalHashState))
    (hagrees : CausalRevealsAgree table state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        (((simulateQ
          (causalActionTracedMappedAdversaryImpl publicKey secretKey chain)
          computation).run |>.run state)))) :
    CausalRevealsAgree table result.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp [simulateQ_pure, WriterT.run_pure] at hresult
      subst result
      exact hagrees
  | query_bind input next ih =>
      rw [simulateQ_query_bind, WriterT.run_bind', StateT.run_bind,
        simulateQ_bind, mem_support_bind_iff] at hresult
      obtain ⟨handled, hhandled, hrestMapped⟩ := hresult
      obtain ⟨⟨handledValue, handledTrace⟩, handledState⟩ := handled
      have hhandledAgrees :=
        simulate_eagerImpl_causalActionTracedMappedAdversaryImpl_step_support_revealsAgree
          table publicKey secretKey chain input state
          ((handledValue, handledTrace), handledState) hagrees hhandled
      dsimp only at hrestMapped hhandledAgrees
      rw [StateT.run_map, simulateQ_map, support_map] at hrestMapped
      obtain ⟨rest, hrest, heq⟩ := hrestMapped
      subst result
      exact ih handledValue handledState rest hhandledAgrees hrest

theorem simulate_eagerImpl_causalDetailedGameAfterKeygen_support_revealsAgree
    (table : ChainValueIndex → Digest)
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (state : CausalHashState)
    (result : (((Forgery × Bool) × AttackerActionTrace) × CausalHashState))
    (hagrees : CausalRevealsAgree table state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((causalDetailedGameAfterKeygen adversary publicKey secretKey chain).run
          state))) :
    CausalRevealsAgree table result.2 := by
  unfold causalDetailedGameAfterKeygen at hresult
  rw [StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at hresult
  obtain ⟨handled, hhandled, hverification⟩ := hresult
  have hhandledAgrees :=
    simulate_eagerImpl_simulate_causalActionTracedMappedAdversaryImpl_support_revealsAgree
      table publicKey secretKey chain (adversary.main publicKey) state handled
      hagrees hhandled
  rw [StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at hverification
  obtain ⟨verified, hvertified, hpure⟩ := hverification
  have hvertifiedAgrees :=
    simulate_eagerImpl_simulate_causalVerifierXmssRomImpl_support_revealsAgree
      table secretKey chain
      (Concrete.scheme.verify publicKey handled.1.1.epoch
        handled.1.1.message handled.1.1.signature)
      handled.2 verified hhandledAgrees hvertified
  simp only [StateT.run_pure, simulateQ_pure, support_pure,
    Set.mem_singleton_iff] at hpure
  subst result
  exact hvertifiedAgrees

theorem simulate_eagerTrace_causalDetailedGameAfterKeygen_support_revealsAgree
    (table : ChainValueIndex → Digest)
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (state : CausalHashState)
    (result : ((((Forgery × Bool) × AttackerActionTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hagrees : CausalRevealsAgree table state)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((causalDetailedGameAfterKeygen adversary publicKey secretKey chain).run
          state)).run)) :
    CausalRevealsAgree table result.1.2 := by
  apply simulate_eagerImpl_causalDetailedGameAfterKeygen_support_revealsAgree
    table adversary publicKey secretKey chain state result.1 hagrees
  exact simulate_eagerTrace_projection_mem_support table _ result hresult

theorem simulate_eagerImpl_simulate_causalMappedAdversaryImpl_support_revealsAgree
    (table : ChainValueIndex → Digest) (publicKey : PublicKey)
    (secretKey : SecretKey) (chain : ChainIndex)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CausalHashState) (result : α × CausalHashState)
    (hagrees : CausalRevealsAgree table state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((simulateQ (causalMappedAdversaryImpl publicKey secretKey chain)
          computation).run state))) :
    CausalRevealsAgree table result.2 := by
  have hcollapse := simulateQ_StateT_compose
    (causalMappedAdversaryImpl publicKey secretKey chain)
    (RevealProbeOracleSimulation.eagerImpl table)
    (eagerCausalMappedAdversaryImpl table publicKey secretKey chain)
    (fun _ _ => rfl) computation state
  rw [hcollapse] at hresult
  exact OracleComp.simulateQ_run_preservesInv
    (eagerCausalMappedAdversaryImpl table publicKey secretKey chain)
    (CausalRevealsAgree table)
    (eagerCausalMappedAdversaryImpl_preservesRevealsAgree
      table publicKey secretKey chain)
    computation state hagrees result hresult

end XmssSecurity
