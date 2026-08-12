import XmssSecurity.CausalSigningResampling
import VCVio.OracleComp.SimSemantics.SimulateQ

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

theorem simulate_eagerImpl_causalUniformImpl_support_cacheExtendsKeygen
    (table : ChainValueIndex → Digest) (n : Nat)
    (state : CausalHashState) (result : Fin (n + 1) × CausalHashState)
    (hextends : CausalCacheExtendsKeygen state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((causalUniformImpl n).run state))) :
    CausalCacheExtendsKeygen result.2 := by
  unfold causalUniformImpl at hresult
  rw [OracleComp.liftM_run_StateT, simulateQ_bind,
    mem_support_bind_iff] at hresult
  obtain ⟨value, _hvalue, hpure⟩ := hresult
  simp only [simulateQ_pure, support_pure,
    Set.mem_singleton_iff] at hpure
  subst result
  exact hextends

noncomputable def eagerCausalVerifierCacheImpl
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (chain : ChainIndex) :
    QueryImpl OracleWorld (StateT CausalHashState ProbComp) :=
  fun input state =>
    simulateQ (RevealProbeOracleSimulation.eagerImpl table)
      ((causalVerifierXmssRomImpl secretKey chain input).run state)

theorem eagerCausalVerifierCacheImpl_preservesCacheExtendsKeygen
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (chain : ChainIndex) :
    QueryImpl.PreservesInv
      (eagerCausalVerifierCacheImpl table secretKey chain)
      CausalCacheExtendsKeygen := by
  intro input state hextends result hresult
  cases input with
  | inl n =>
      exact simulate_eagerImpl_causalUniformImpl_support_cacheExtendsKeygen
        table n state result hextends hresult
  | inr input =>
      exact simulate_eagerImpl_causalAttackerHashQuery_support_cacheExtendsKeygen
        table secretKey chain input state result hextends hresult

theorem simulate_eagerImpl_simulate_causalVerifierXmssRomImpl_support_cacheExtendsKeygen
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (chain : ChainIndex) (computation : OracleComp OracleWorld α)
    (state : CausalHashState) (result : α × CausalHashState)
    (hextends : CausalCacheExtendsKeygen state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((simulateQ (causalVerifierXmssRomImpl secretKey chain)
          computation).run state))) :
    CausalCacheExtendsKeygen result.2 := by
  have hcollapse := simulateQ_StateT_compose
    (causalVerifierXmssRomImpl secretKey chain)
    (RevealProbeOracleSimulation.eagerImpl table)
    (eagerCausalVerifierCacheImpl table secretKey chain)
    (fun _ _ => rfl) computation state
  rw [hcollapse] at hresult
  exact OracleComp.simulateQ_run_preservesInv
    (eagerCausalVerifierCacheImpl table secretKey chain)
    CausalCacheExtendsKeygen
    (eagerCausalVerifierCacheImpl_preservesCacheExtendsKeygen
      table secretKey chain)
    computation state hextends result hresult

noncomputable def eagerCausalMappedAdversaryAfterRealRomCacheImpl
    (table : ChainValueIndex → Digest) (publicKey : PublicKey)
    (secretKey : SecretKey) (chain : ChainIndex) :
    QueryImpl (OracleWorld + SigningSpec) (StateT CausalHashState ProbComp) :=
  fun input state =>
    simulateQ (RevealProbeOracleSimulation.eagerImpl table)
      ((causalMappedAdversaryAfterRealRomImpl
        publicKey secretKey chain input).run state)

theorem eagerCausalMappedAdversaryAfterRealRomCacheImpl_preservesCacheExtendsKeygen
    (table : ChainValueIndex → Digest) (publicKey : PublicKey)
    (secretKey : SecretKey) (chain : ChainIndex) :
    QueryImpl.PreservesInv
      (eagerCausalMappedAdversaryAfterRealRomCacheImpl
        table publicKey secretKey chain)
      CausalCacheExtendsKeygen := by
  intro input state hextends result hresult
  rcases input with worldInput | request
  · rcases worldInput with n | hashInput
    · exact simulate_eagerImpl_causalUniformImpl_support_cacheExtendsKeygen
        table n state result hextends hresult
    · exact simulate_eagerImpl_causalAttackerHashQuery_support_cacheExtendsKeygen
        table secretKey chain hashInput state result hextends hresult
  · exact simulate_eagerImpl_causalSigningQueryAfterRealRom_support_cacheExtendsKeygen
      table publicKey secretKey chain request state result hextends hresult

theorem simulate_eagerImpl_causalActionTracedMappedAdversaryAfterRealRomImpl_step_support_cacheExtendsKeygen
    (table : ChainValueIndex → Digest) (publicKey : PublicKey)
    (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState)
    (result : (((OracleWorld + SigningSpec).Range input ×
      AttackerActionTrace) × CausalHashState))
    (hextends : CausalCacheExtendsKeygen state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        (((causalActionTracedMappedAdversaryAfterRealRomImpl
          publicKey secretKey chain input).run |>.run state)))) :
    CausalCacheExtendsKeygen result.2 := by
  unfold causalActionTracedMappedAdversaryAfterRealRomImpl at hresult
  rw [QueryImpl.withTraceAppend_apply, WriterT.run_bind',
    WriterT.run_monadLift', StateT.run_bind, simulateQ_bind,
    mem_support_bind_iff] at hresult
  obtain ⟨handled, hhandled, hcontinued⟩ := hresult
  rw [StateT.run_map, simulateQ_map, support_map] at hhandled
  obtain ⟨base, hbase, heq⟩ := hhandled
  subst handled
  have hhandledExtends :=
    eagerCausalMappedAdversaryAfterRealRomCacheImpl_preservesCacheExtendsKeygen
      table publicKey secretKey chain input state hextends base hbase
  simp [WriterT.run_tell] at hcontinued
  subst result
  exact hhandledExtends

theorem simulate_eagerImpl_simulate_causalActionTracedMappedAdversaryAfterRealRomImpl_support_cacheExtendsKeygen
    (table : ChainValueIndex → Digest) (publicKey : PublicKey)
    (secretKey : SecretKey) (chain : ChainIndex)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CausalHashState)
    (result : ((α × AttackerActionTrace) × CausalHashState))
    (hextends : CausalCacheExtendsKeygen state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        (((simulateQ
          (causalActionTracedMappedAdversaryAfterRealRomImpl
            publicKey secretKey chain) computation).run |>.run state)))) :
    CausalCacheExtendsKeygen result.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp [simulateQ_pure, WriterT.run_pure] at hresult
      subst result
      exact hextends
  | query_bind input next ih =>
      rw [simulateQ_query_bind, WriterT.run_bind', StateT.run_bind,
        simulateQ_bind, mem_support_bind_iff] at hresult
      obtain ⟨handled, hhandled, hrestMapped⟩ := hresult
      obtain ⟨⟨handledValue, handledTrace⟩, handledState⟩ := handled
      have hhandledExtends :=
        simulate_eagerImpl_causalActionTracedMappedAdversaryAfterRealRomImpl_step_support_cacheExtendsKeygen
          table publicKey secretKey chain input state
          ((handledValue, handledTrace), handledState) hextends hhandled
      dsimp only at hrestMapped hhandledExtends
      rw [StateT.run_map, simulateQ_map, support_map] at hrestMapped
      obtain ⟨rest, hrest, heq⟩ := hrestMapped
      subst result
      exact ih handledValue handledState rest hhandledExtends hrest

theorem simulate_eagerImpl_causalDetailedGameAfterKeygenAfterRealRom_support_cacheExtendsKeygen
    (table : ChainValueIndex → Digest)
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (state : CausalHashState)
    (result : (((Forgery × Bool) × AttackerActionTrace) × CausalHashState))
    (hextends : CausalCacheExtendsKeygen state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((causalDetailedGameAfterKeygenAfterRealRom
          adversary publicKey secretKey chain).run state))) :
    CausalCacheExtendsKeygen result.2 := by
  unfold causalDetailedGameAfterKeygenAfterRealRom at hresult
  rw [StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at hresult
  obtain ⟨handled, hhandled, hverification⟩ := hresult
  have hhandledExtends :=
    simulate_eagerImpl_simulate_causalActionTracedMappedAdversaryAfterRealRomImpl_support_cacheExtendsKeygen
      table publicKey secretKey chain (adversary.main publicKey) state handled
      hextends hhandled
  rw [StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at hverification
  obtain ⟨verified, hvertified, hpure⟩ := hverification
  have hvertifiedExtends :=
    simulate_eagerImpl_simulate_causalVerifierXmssRomImpl_support_cacheExtendsKeygen
      table secretKey chain
      (Concrete.scheme.verify publicKey handled.1.1.epoch
        handled.1.1.message handled.1.1.signature)
      handled.2 verified hhandledExtends hvertified
  simp only [StateT.run_pure, simulateQ_pure, support_pure,
    Set.mem_singleton_iff] at hpure
  subst result
  exact hvertifiedExtends

end XmssSecurity
