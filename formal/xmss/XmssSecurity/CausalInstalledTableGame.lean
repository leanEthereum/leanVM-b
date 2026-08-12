import XmssSecurity.CausalRevealMonotonicity

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

def CausalInstalledInvariant
    (table : ChainValueIndex → Digest) (initial current : CausalHashState) : Prop :=
  CausalRevealsAgree table current ∧ CausalRevealsLe initial current

theorem simulate_eagerImpl_causalSigningQueryAfterRealRom_support_revealsAgree
    (table : ChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (request : SignRequest) (state : CausalHashState)
    (result : Option Signature × CausalHashState)
    (hagrees : CausalRevealsAgree table state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        (causalSigningQueryAfterRealRom
          publicKey secretKey chain request state))) :
    CausalRevealsAgree table result.2 := by
  unfold causalSigningQueryAfterRealRom at hresult
  rw [simulateQ_bind,
    RevealProbeOracleSimulation.simulate_eagerImpl_liftProbComp,
    mem_support_bind_iff] at hresult
  obtain ⟨signed, _hsigned, hrest⟩ := hresult
  exact simulate_eagerImpl_revealFixedChainSignatureOption_support_revealsAgree
    table secretKey chain request signed.1 { state with cache := signed.2 }
      result (hagrees.setCache signed.2) hrest

theorem simulate_eagerImpl_causalUniformImpl_support_installedInvariant
    (table : ChainValueIndex → Digest) (initial : CausalHashState) (n : Nat)
    (state : CausalHashState) (result : Fin (n + 1) × CausalHashState)
    (hinvariant : CausalInstalledInvariant table initial state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((causalUniformImpl n).run state))) :
    CausalInstalledInvariant table initial result.2 := by
  constructor
  · exact simulate_eagerImpl_causalUniformImpl_support_revealsAgree
      table n state result hinvariant.1 hresult
  · have hsame : result.2 = state := by
      unfold causalUniformImpl at hresult
      rw [OracleComp.liftM_run_StateT, simulateQ_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨value, _hvalue, hpure⟩ := hresult
      simp only [simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hpure
      exact congrArg Prod.snd hpure
    rw [hsame]
    exact hinvariant.2

theorem simulate_eagerImpl_causalAttackerHashQuery_support_installedInvariant
    (table : ChainValueIndex → Digest) (initial : CausalHashState)
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) (result : HashOutput × CausalHashState)
    (hinvariant : CausalInstalledInvariant table initial state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((causalAttackerHashQuery secretKey chain input).run state))) :
    CausalInstalledInvariant table initial result.2 := by
  constructor
  · exact simulate_eagerImpl_causalAttackerHashQuery_support_revealsAgree
      table secretKey chain input state result hinvariant.1 hresult
  · exact hinvariant.2.trans
      (simulate_eagerImpl_causalAttackerHashQuery_support_revealsLe
        table secretKey chain input state result hinvariant.1 hresult)

theorem simulate_eagerImpl_causalSigningQueryAfterRealRom_support_installedInvariant
    (table : ChainValueIndex → Digest) (initial : CausalHashState)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (request : SignRequest) (state : CausalHashState)
    (result : Option Signature × CausalHashState)
    (hinvariant : CausalInstalledInvariant table initial state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        (causalSigningQueryAfterRealRom
          publicKey secretKey chain request state))) :
    CausalInstalledInvariant table initial result.2 := by
  constructor
  · exact simulate_eagerImpl_causalSigningQueryAfterRealRom_support_revealsAgree
      table publicKey secretKey chain request state result hinvariant.1 hresult
  · exact hinvariant.2.trans
      (simulate_eagerImpl_causalSigningQueryAfterRealRom_support_revealsLe
        table publicKey secretKey chain request state result hinvariant.1 hresult)

noncomputable def eagerCausalMappedAdversaryAfterRealRomInstalledImpl
    (table : ChainValueIndex → Digest) (publicKey : PublicKey)
    (secretKey : SecretKey) (chain : ChainIndex) :
    QueryImpl (OracleWorld + SigningSpec) (StateT CausalHashState ProbComp) :=
  fun input state =>
    simulateQ (RevealProbeOracleSimulation.eagerImpl table)
      ((causalMappedAdversaryAfterRealRomImpl
        publicKey secretKey chain input).run state)

theorem eagerCausalMappedAdversaryAfterRealRomInstalledImpl_preserves
    (table : ChainValueIndex → Digest) (initial : CausalHashState)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex) :
    QueryImpl.PreservesInv
      (eagerCausalMappedAdversaryAfterRealRomInstalledImpl
        table publicKey secretKey chain)
      (CausalInstalledInvariant table initial) := by
  intro input state hinvariant result hresult
  rcases input with worldInput | request
  · rcases worldInput with n | hashInput
    · exact simulate_eagerImpl_causalUniformImpl_support_installedInvariant
        table initial n state result hinvariant hresult
    · exact simulate_eagerImpl_causalAttackerHashQuery_support_installedInvariant
        table initial secretKey chain hashInput state result hinvariant hresult
  · exact
      simulate_eagerImpl_causalSigningQueryAfterRealRom_support_installedInvariant
        table initial publicKey secretKey chain request state result
          hinvariant hresult

theorem simulate_eagerImpl_causalActionTracedMappedAdversaryAfterRealRomImpl_step_support_installedInvariant
    (table : ChainValueIndex → Digest) (initial : CausalHashState)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState)
    (result : (((OracleWorld + SigningSpec).Range input ×
      AttackerActionTrace) × CausalHashState))
    (hinvariant : CausalInstalledInvariant table initial state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        (((causalActionTracedMappedAdversaryAfterRealRomImpl
          publicKey secretKey chain input).run |>.run state)))) :
    CausalInstalledInvariant table initial result.2 := by
  unfold causalActionTracedMappedAdversaryAfterRealRomImpl at hresult
  rw [QueryImpl.withTraceAppend_apply, WriterT.run_bind',
    WriterT.run_monadLift', StateT.run_bind, simulateQ_bind,
    mem_support_bind_iff] at hresult
  obtain ⟨handled, hhandled, hcontinued⟩ := hresult
  rw [StateT.run_map, simulateQ_map, support_map] at hhandled
  obtain ⟨base, hbase, heq⟩ := hhandled
  subst handled
  have hhandledInvariant :=
    eagerCausalMappedAdversaryAfterRealRomInstalledImpl_preserves
      table initial publicKey secretKey chain input state hinvariant base hbase
  simp [WriterT.run_tell] at hcontinued
  subst result
  exact hhandledInvariant

theorem simulate_eagerImpl_simulate_causalActionTracedMappedAdversaryAfterRealRomImpl_support_installedInvariant
    (table : ChainValueIndex → Digest) (initial : CausalHashState)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CausalHashState)
    (result : ((α × AttackerActionTrace) × CausalHashState))
    (hinvariant : CausalInstalledInvariant table initial state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        (((simulateQ
          (causalActionTracedMappedAdversaryAfterRealRomImpl
            publicKey secretKey chain) computation).run |>.run state)))) :
    CausalInstalledInvariant table initial result.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp [simulateQ_pure, WriterT.run_pure] at hresult
      subst result
      exact hinvariant
  | query_bind input next ih =>
      rw [simulateQ_query_bind, WriterT.run_bind', StateT.run_bind,
        simulateQ_bind, mem_support_bind_iff] at hresult
      obtain ⟨handled, hhandled, hrestMapped⟩ := hresult
      obtain ⟨⟨handledValue, handledTrace⟩, handledState⟩ := handled
      have hhandledInvariant :=
        simulate_eagerImpl_causalActionTracedMappedAdversaryAfterRealRomImpl_step_support_installedInvariant
          table initial publicKey secretKey chain input state
          ((handledValue, handledTrace), handledState) hinvariant hhandled
      dsimp only at hrestMapped hhandledInvariant
      rw [StateT.run_map, simulateQ_map, support_map] at hrestMapped
      obtain ⟨rest, hrest, heq⟩ := hrestMapped
      subst result
      exact ih handledValue handledState rest hhandledInvariant hrest

noncomputable def eagerCausalVerifierInstalledImpl
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (chain : ChainIndex) :
    QueryImpl OracleWorld (StateT CausalHashState ProbComp) :=
  fun input state =>
    simulateQ (RevealProbeOracleSimulation.eagerImpl table)
      ((causalVerifierXmssRomImpl secretKey chain input).run state)

theorem eagerCausalVerifierInstalledImpl_preserves
    (table : ChainValueIndex → Digest) (initial : CausalHashState)
    (secretKey : SecretKey) (chain : ChainIndex) :
    QueryImpl.PreservesInv
      (eagerCausalVerifierInstalledImpl table secretKey chain)
      (CausalInstalledInvariant table initial) := by
  intro input state hinvariant result hresult
  cases input with
  | inl n =>
      exact simulate_eagerImpl_causalUniformImpl_support_installedInvariant
        table initial n state result hinvariant hresult
  | inr input =>
      exact simulate_eagerImpl_causalAttackerHashQuery_support_installedInvariant
        table initial secretKey chain input state result hinvariant hresult

theorem simulate_eagerImpl_simulate_causalVerifierXmssRomImpl_support_installedInvariant
    (table : ChainValueIndex → Digest) (initial : CausalHashState)
    (secretKey : SecretKey) (chain : ChainIndex)
    (computation : OracleComp OracleWorld α)
    (state : CausalHashState) (result : α × CausalHashState)
    (hinvariant : CausalInstalledInvariant table initial state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((simulateQ (causalVerifierXmssRomImpl secretKey chain)
          computation).run state))) :
    CausalInstalledInvariant table initial result.2 := by
  have hcollapse := simulateQ_StateT_compose
    (causalVerifierXmssRomImpl secretKey chain)
    (RevealProbeOracleSimulation.eagerImpl table)
    (eagerCausalVerifierInstalledImpl table secretKey chain)
    (fun _ _ => rfl) computation state
  rw [hcollapse] at hresult
  exact OracleComp.simulateQ_run_preservesInv
    (eagerCausalVerifierInstalledImpl table secretKey chain)
    (CausalInstalledInvariant table initial)
    (eagerCausalVerifierInstalledImpl_preserves
      table initial secretKey chain)
    computation state hinvariant result hresult

theorem simulate_eagerImpl_causalDetailedGameAfterKeygenAfterRealRom_support_installedInvariant
    (table : ChainValueIndex → Digest) (initial : CausalHashState)
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (result : (((Forgery × Bool) × AttackerActionTrace) × CausalHashState))
    (hinvariant : CausalInstalledInvariant table initial initial)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((causalDetailedGameAfterKeygenAfterRealRom
          adversary publicKey secretKey chain).run initial))) :
    CausalInstalledInvariant table initial result.2 := by
  unfold causalDetailedGameAfterKeygenAfterRealRom at hresult
  rw [StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at hresult
  obtain ⟨handled, hhandled, hverification⟩ := hresult
  have hhandledInvariant :=
    simulate_eagerImpl_simulate_causalActionTracedMappedAdversaryAfterRealRomImpl_support_installedInvariant
      table initial publicKey secretKey chain (adversary.main publicKey)
      initial handled hinvariant hhandled
  rw [StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at hverification
  obtain ⟨verified, hvertified, hpure⟩ := hverification
  have hvertifiedInvariant :=
    simulate_eagerImpl_simulate_causalVerifierXmssRomImpl_support_installedInvariant
      table initial secretKey chain
      (Concrete.scheme.verify publicKey handled.1.1.epoch
        handled.1.1.message handled.1.1.signature)
      handled.2 verified hhandledInvariant hvertified
  simp only [StateT.run_pure, simulateQ_pure, support_pure,
    Set.mem_singleton_iff] at hpure
  subst result
  exact hvertifiedInvariant

theorem simulate_eagerImpl_causalDetailedGameAfterKeygenAfterRealRom_support_installedTable
    (base : ChainValueIndex → Digest) (initial : CausalHashState)
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (result : (((Forgery × Bool) × AttackerActionTrace) × CausalHashState))
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl
        (causalInstalledTable initial base))
        ((causalDetailedGameAfterKeygenAfterRealRom
          adversary publicKey secretKey chain).run initial))) :
    causalInstalledTable result.2 base =
      causalInstalledTable initial base := by
  let table := causalInstalledTable initial base
  have hinitial : CausalInstalledInvariant table initial initial :=
    ⟨causalRevealsAgree_causalInstalledTable initial base,
      CausalRevealsLe.refl initial⟩
  have hfinal :=
    simulate_eagerImpl_causalDetailedGameAfterKeygenAfterRealRom_support_installedInvariant
      table initial adversary publicKey secretKey chain result hinitial hresult
  exact causalInstalledTable_eq_of_agrees_of_revealsLe
    table base initial result.2 rfl hfinal.1 hfinal.2

theorem simulate_eagerTrace_causalDetailedGameAfterKeygenAfterRealRom_support_installedTable
    (base : ChainValueIndex → Digest) (initial : CausalHashState)
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (result : ((((Forgery × Bool) × AttackerActionTrace) ×
      CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl
        (causalInstalledTable initial base))
        ((causalDetailedGameAfterKeygenAfterRealRom
          adversary publicKey secretKey chain).run initial)).run)) :
    causalInstalledTable result.1.2 base =
      causalInstalledTable initial base := by
  apply
    simulate_eagerImpl_causalDetailedGameAfterKeygenAfterRealRom_support_installedTable
      base initial adversary publicKey secretKey chain result.1
  exact simulate_eagerTrace_projection_mem_support
    (causalInstalledTable initial base) _ result hresult

end XmssSecurity
