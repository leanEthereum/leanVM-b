import XmssSecurity.CappedGlobalCausalInstalledVerifierRun

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

noncomputable local instance globalCausalInstalledDetailedGameSampleableTable :
    SampleableType (GlobalChainValueIndex → Digest) :=
  SampleableType.ofFintype (GlobalChainValueIndex → Digest)

def combineGlobalCausalDetailedResult
    (handled : (((Forgery × AttackerActionTrace) × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (verified : ((Bool × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) :
    ((((Forgery × Bool) × AttackerActionTrace) × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  ((((handled.1.1.1, verified.1.1), handled.1.1.2), verified.1.2),
    handled.2 ++ verified.2)

noncomputable def globalCausalEagerVerificationContinuation
    (publicKey : PublicKey) (secretKey : SecretKey)
    (continuation : (GlobalChainValueIndex → Digest) →
      ((((Forgery × Bool) × AttackerActionTrace) × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) →
          ProbComp α)
    (table : GlobalChainValueIndex → Digest)
    (handled : (((Forgery × AttackerActionTrace) × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) :
    ProbComp α := do
  let verified ← (simulateQ
    (RevealProbeOracleSimulation.eagerTraceImpl table)
    ((simulateQ (globalCausalVerifierXmssRomImpl secretKey)
      (Concrete.scheme.verify publicKey handled.1.1.1.epoch
        handled.1.1.1.message handled.1.1.1.signature)).run
          handled.1.2)).run
  continuation table (combineGlobalCausalDetailedResult handled verified)

noncomputable def globalCausalLazyDetailedGameAfterKeygen
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (state : GlobalCausalHashState) :
    ProbComp (((((Forgery × Bool) × AttackerActionTrace) ×
      GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) := do
  let handled ← (((simulateQ
    (globalCausalLazyActionTracedImpl publicKey secretKey)
      (adversary.main publicKey)).run).run state).run
  let verified ← ((simulateQ
    (globalCausalLazyVerifierImpl publicKey secretKey)
    (Concrete.scheme.verify publicKey handled.1.1.1.epoch
      handled.1.1.1.message handled.1.1.1.signature)).run handled.1.2).run
  pure (combineGlobalCausalDetailedResult handled verified)

set_option maxRecDepth 200000 in
theorem evalDist_installed_globalCausalDetailedGameAfterKeygenAfterRealRom_eq_lazy
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (state : GlobalCausalHashState)
    (continuation : (GlobalChainValueIndex → Digest) →
      ((((Forgery × Bool) × AttackerActionTrace) × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) →
          ProbComp α) :
    𝒟[do
      let base ← $ᵗ (GlobalChainValueIndex → Digest)
      let table := globalCausalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalDetailedGameAfterKeygenAfterRealRom adversary
          publicKey secretKey).run state)).run
      continuation table result] =
    𝒟[do
      let result ← globalCausalLazyDetailedGameAfterKeygen
        adversary publicKey secretKey state
      let base ← $ᵗ (GlobalChainValueIndex → Digest)
      continuation (globalCausalInstalledTable result.1.2 base) result] := by
  calc
    _ = 𝒟[do
        let handled ← (((simulateQ
          (globalCausalLazyActionTracedImpl publicKey secretKey)
            (adversary.main publicKey)).run).run state).run
        let base ← $ᵗ (GlobalChainValueIndex → Digest)
        globalCausalEagerVerificationContinuation publicKey secretKey
          continuation (globalCausalInstalledTable handled.1.2 base)
            handled] := by
      simpa [globalCausalDetailedGameAfterKeygenAfterRealRom,
        globalCausalEagerVerificationContinuation,
        combineGlobalCausalDetailedResult, StateT.run_bind, simulateQ_bind,
        WriterT.run_bind', map_eq_bind_pure_comp, bind_assoc,
        Function.comp_apply] using
        (evalDist_installed_simulate_globalCausalActionTracedAdversary_eq_lazy
          publicKey secretKey (adversary.main publicKey) state
            (globalCausalEagerVerificationContinuation
              publicKey secretKey continuation))
    _ = 𝒟[do
        let handled ← (((simulateQ
          (globalCausalLazyActionTracedImpl publicKey secretKey)
            (adversary.main publicKey)).run).run state).run
        let verified ← ((simulateQ
          (globalCausalLazyVerifierImpl publicKey secretKey)
          (Concrete.scheme.verify publicKey handled.1.1.1.epoch
            handled.1.1.1.message handled.1.1.1.signature)).run
              handled.1.2).run
        let base ← $ᵗ (GlobalChainValueIndex → Digest)
        continuation (globalCausalInstalledTable verified.1.2 base)
          (combineGlobalCausalDetailedResult handled verified)] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro handled
      simpa [globalCausalEagerVerificationContinuation,
        combineGlobalCausalDetailedResult, map_eq_bind_pure_comp,
        bind_assoc, Function.comp_apply] using
        (evalDist_installed_simulate_globalCausalVerifier_eq_lazy
          publicKey secretKey
            (Concrete.scheme.verify publicKey handled.1.1.1.epoch
              handled.1.1.1.message handled.1.1.1.signature)
            handled.1.2
            (fun table verified => continuation table
              (combineGlobalCausalDetailedResult handled verified)))
    _ = _ := by
      unfold globalCausalLazyDetailedGameAfterKeygen
      simp [combineGlobalCausalDetailedResult, bind_assoc]

end XmssSecurity.CappedChain
