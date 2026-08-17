import XmssSecurity.CausalInstalledVerifierRun

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

noncomputable local instance causalInstalledDetailedGameSampleableChainTable :
    SampleableType (ChainValueIndex → Digest) :=
  SampleableType.ofFintype (ChainValueIndex → Digest)

def combineCausalDetailedResult
    (handled : (((Forgery × AttackerActionTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (verified : ((Bool × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) :
    ((((Forgery × Bool) × AttackerActionTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  ((((handled.1.1.1, verified.1.1), handled.1.1.2), verified.1.2),
    handled.2 ++ verified.2)

noncomputable def causalEagerVerificationContinuation
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (continuation : (ChainValueIndex → Digest) →
      ((((Forgery × Bool) × AttackerActionTrace) × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α)
    (table : ChainValueIndex → Digest)
    (handled : (((Forgery × AttackerActionTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) : ProbComp α := do
  let verified ← (simulateQ
    (RevealProbeOracleSimulation.eagerTraceImpl table)
    ((simulateQ (causalVerifierXmssRomImpl secretKey chain)
      (Concrete.singleAttemptScheme.verify publicKey handled.1.1.1.epoch
        handled.1.1.1.message handled.1.1.1.signature)).run
          handled.1.2)).run
  continuation table (combineCausalDetailedResult handled verified)

noncomputable def causalLazyDetailedGameAfterKeygen
    (adversary : Adversary Concrete.singleAttemptScheme)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (state : CausalHashState) :
    ProbComp (((((Forgery × Bool) × AttackerActionTrace) ×
      CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) := do
  let handled ← (((simulateQ
    (causalLazyActionTracedImpl publicKey secretKey chain)
      (adversary.main publicKey)).run).run state).run
  let verified ← ((simulateQ
    (causalLazyVerifierImpl publicKey secretKey chain)
    (Concrete.singleAttemptScheme.verify publicKey handled.1.1.1.epoch
      handled.1.1.1.message handled.1.1.1.signature)).run handled.1.2).run
  pure (combineCausalDetailedResult handled verified)

set_option maxRecDepth 100000 in
theorem evalDist_installed_causalDetailedGameAfterKeygenAfterRealRom_eq_lazy
    (adversary : Adversary Concrete.singleAttemptScheme)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((((Forgery × Bool) × AttackerActionTrace) × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((causalDetailedGameAfterKeygenAfterRealRom adversary
          publicKey secretKey chain).run state)).run
      continuation table result] =
    𝒟[do
      let result ← causalLazyDetailedGameAfterKeygen
        adversary publicKey secretKey chain state
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  calc
    _ = 𝒟[do
        let handled ← (((simulateQ
          (causalLazyActionTracedImpl publicKey secretKey chain)
            (adversary.main publicKey)).run).run state).run
        let base ← $ᵗ (ChainValueIndex → Digest)
        causalEagerVerificationContinuation publicKey secretKey chain
          continuation (causalInstalledTable handled.1.2 base) handled] := by
      simpa [causalDetailedGameAfterKeygenAfterRealRom,
        causalEagerVerificationContinuation, combineCausalDetailedResult,
        StateT.run_bind, simulateQ_bind, WriterT.run_bind',
        map_eq_bind_pure_comp, bind_assoc, Function.comp_apply] using
        (evalDist_installed_simulate_causalActionTracedAdversary_eq_lazy
          publicKey secretKey chain (adversary.main publicKey) state
            (causalEagerVerificationContinuation
              publicKey secretKey chain continuation))
    _ = 𝒟[do
        let handled ← (((simulateQ
          (causalLazyActionTracedImpl publicKey secretKey chain)
            (adversary.main publicKey)).run).run state).run
        let verified ← ((simulateQ
          (causalLazyVerifierImpl publicKey secretKey chain)
          (Concrete.singleAttemptScheme.verify publicKey handled.1.1.1.epoch
            handled.1.1.1.message handled.1.1.1.signature)).run
              handled.1.2).run
        let base ← $ᵗ (ChainValueIndex → Digest)
        continuation (causalInstalledTable verified.1.2 base)
          (combineCausalDetailedResult handled verified)] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro handled
      simpa [causalEagerVerificationContinuation,
        combineCausalDetailedResult, map_eq_bind_pure_comp,
        bind_assoc, Function.comp_apply] using
        (evalDist_installed_simulate_causalVerifier_eq_lazy
          publicKey secretKey chain
            (Concrete.singleAttemptScheme.verify publicKey handled.1.1.1.epoch
              handled.1.1.1.message handled.1.1.1.signature)
            handled.1.2
            (fun table verified => continuation table
              (combineCausalDetailedResult handled verified)))
    _ = _ := by
      unfold causalLazyDetailedGameAfterKeygen
      simp [combineCausalDetailedResult, bind_assoc]

end XmssSecurity
