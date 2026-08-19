import XmssSecurity.Proof.CausalDirectLazyAdversaryComposition
import XmssSecurity.Proof.CausalDirectLazyVerifier

open OracleComp OracleSpec

namespace XmssSecurity

noncomputable local instance directLazyGameSampleableChainTable :
    SampleableType (ChainValueIndex → Digest) :=
  SampleableType.ofFintype (ChainValueIndex → Digest)

@[simp]
theorem causalInstalledTable_filteredCausalKeygenState
    (selected : ChainIndex) (keyView : ProgrammedFixedChainKeygenView)
    (base : ChainValueIndex → Digest) :
    causalInstalledTable (filteredCausalKeygenState selected keyView) base =
      base := by
  funext index
  rfl

def combineFilteredDirectDetailedResult
    (handled : (((Forgery × AttackerActionTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (verified : ((Bool × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) :
    (FilteredDirectExecution ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  (((((handled.1.1.1, verified.1.1), handled.1.1.2), verified.1.2)),
    handled.2 ++ verified.2)

noncomputable def filteredDirectLazyDetailedGameAfterKeygen
    (adversary : Adversary Concrete.singleAttemptScheme)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (state : CausalHashState) :
    ProbComp (FilteredDirectExecution ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) := do
  let handled ← (((simulateQ
    (filteredDirectLazyRawActionTracedImpl keyView selected)
      (adversary.main keyView.publicKey)).run).run state).run
  let verified ← ((simulateQ
    (filteredDirectLazyVerifierImpl keyView selected)
    (Concrete.singleAttemptScheme.verify keyView.publicKey handled.1.1.1.epoch
      handled.1.1.1.message handled.1.1.1.signature)).run handled.1.2).run
  pure (combineFilteredDirectDetailedResult handled verified)

noncomputable def filteredDirectEagerVerificationContinuation
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (continuation : (ChainValueIndex → Digest) →
      (FilteredDirectExecution ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α)
    (table : ChainValueIndex → Digest)
    (handled : (((Forgery × AttackerActionTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) : ProbComp α := do
  let verified ← (simulateQ
    (RevealProbeOracleSimulation.eagerTraceImpl table)
    ((simulateQ (filteredDirectVerifierImpl keyView selected)
      (Concrete.singleAttemptScheme.verify keyView.publicKey handled.1.1.1.epoch
        handled.1.1.1.message handled.1.1.1.signature)).run
          handled.1.2)).run
  continuation table (combineFilteredDirectDetailedResult handled verified)

set_option maxHeartbeats 2000 in
set_option maxRecDepth 100000 in
theorem simulate_eagerTrace_filteredDirectDetailedGameAfterKeygen
    (table : ChainValueIndex → Digest)
    (adversary : Adversary Concrete.singleAttemptScheme)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (state : CausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((filteredDirectDetailedGameAfterKeygen adversary
        keyView selected).run state)).run = (do
      let handled ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        (((simulateQ (filteredDirectActionTracedMappedAdversaryImpl
          keyView selected) (adversary.main keyView.publicKey)).run).run
            state)).run
      let verified ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ (filteredDirectVerifierImpl keyView selected)
          (Concrete.singleAttemptScheme.verify keyView.publicKey handled.1.1.1.epoch
            handled.1.1.1.message handled.1.1.1.signature)).run
              handled.1.2)).run
      pure (combineFilteredDirectDetailedResult handled verified)) := by
  unfold filteredDirectDetailedGameAfterKeygen
  rw [StateT.run_bind, simulateQ_bind]
  rw [WriterT.run_bind']
  apply bind_congr
  intro handled
  rcases handled with ⟨⟨handled, handledState⟩, handledTrace⟩
  simp only
  rw [StateT.run_bind, simulateQ_bind, WriterT.run_bind']
  simp [combineFilteredDirectDetailedResult, simulateQ_pure,
    WriterT.run_pure, map_eq_bind_pure_comp]

set_option maxRecDepth 100000 in
theorem evalDist_installed_filteredDirectDetailedGameAfterKeygen_decompose
    (adversary : Adversary Concrete.singleAttemptScheme)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      (FilteredDirectExecution ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((filteredDirectDetailedGameAfterKeygen adversary
          keyView selected).run state)).run
      continuation table result] =
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let handled ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        (((simulateQ (filteredDirectActionTracedMappedAdversaryImpl
          keyView selected) (adversary.main keyView.publicKey)).run).run
            state)).run
      filteredDirectEagerVerificationContinuation keyView selected
        continuation table handled] := by
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro base
  change evalDist
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl
        (causalInstalledTable state base))
        ((filteredDirectDetailedGameAfterKeygen adversary
          keyView selected).run state)).run >>=
            continuation (causalInstalledTable state base)) =
    evalDist
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl
        (causalInstalledTable state base))
        (((simulateQ (filteredDirectActionTracedMappedAdversaryImpl
          keyView selected) (adversary.main keyView.publicKey)).run).run
            state)).run >>=
          filteredDirectEagerVerificationContinuation keyView selected
            continuation (causalInstalledTable state base))
  rw [simulate_eagerTrace_filteredDirectDetailedGameAfterKeygen]
  simp [filteredDirectEagerVerificationContinuation, bind_assoc]

set_option maxRecDepth 100000 in
theorem evalDist_filteredDirectEagerVerificationContinuation_eq_lazy
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (handled : (((Forgery × AttackerActionTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (continuation : (ChainValueIndex → Digest) →
      (FilteredDirectExecution ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      filteredDirectEagerVerificationContinuation keyView selected
        continuation (causalInstalledTable handled.1.2 base) handled] =
    𝒟[do
      let verified ← ((simulateQ
        (filteredDirectLazyVerifierImpl keyView selected)
        (Concrete.singleAttemptScheme.verify keyView.publicKey handled.1.1.1.epoch
          handled.1.1.1.message handled.1.1.1.signature)).run
            handled.1.2).run
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable verified.1.2 base)
        (combineFilteredDirectDetailedResult handled verified)] := by
  simpa [filteredDirectEagerVerificationContinuation,
    combineFilteredDirectDetailedResult, map_eq_bind_pure_comp,
    bind_assoc, Function.comp_apply] using
    (evalDist_installed_simulate_filteredDirectVerifier_eq_lazy
      keyView selected
        (Concrete.singleAttemptScheme.verify keyView.publicKey handled.1.1.1.epoch
          handled.1.1.1.message handled.1.1.1.signature)
        handled.1.2
        (fun table verified => continuation table
          (combineFilteredDirectDetailedResult handled verified)))

theorem evalDist_filteredDirectLazyAdversary_eagerVerifier_eq_lazyVerifier
    (adversary : Adversary Concrete.singleAttemptScheme)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      (FilteredDirectExecution ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[do
      let handled ← (((simulateQ
        (filteredDirectLazyRawActionTracedImpl keyView selected)
          (adversary.main keyView.publicKey)).run).run state).run
      let base ← $ᵗ (ChainValueIndex → Digest)
      filteredDirectEagerVerificationContinuation keyView selected
        continuation (causalInstalledTable handled.1.2 base) handled] =
    𝒟[do
      let handled ← (((simulateQ
        (filteredDirectLazyRawActionTracedImpl keyView selected)
          (adversary.main keyView.publicKey)).run).run state).run
      let verified ← ((simulateQ
        (filteredDirectLazyVerifierImpl keyView selected)
        (Concrete.singleAttemptScheme.verify keyView.publicKey handled.1.1.1.epoch
          handled.1.1.1.message handled.1.1.1.signature)).run
            handled.1.2).run
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable verified.1.2 base)
        (combineFilteredDirectDetailedResult handled verified)] := by
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro handled
  exact evalDist_filteredDirectEagerVerificationContinuation_eq_lazy
    keyView selected handled continuation

theorem filteredDirectLazyDetailedGameAfterKeygen_bind
    (adversary : Adversary Concrete.singleAttemptScheme)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      (FilteredDirectExecution ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    (do
      let result ← filteredDirectLazyDetailedGameAfterKeygen
        adversary keyView selected state
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result) =
    (do
      let handled ← (((simulateQ
        (filteredDirectLazyRawActionTracedImpl keyView selected)
          (adversary.main keyView.publicKey)).run).run state).run
      let verified ← ((simulateQ
        (filteredDirectLazyVerifierImpl keyView selected)
        (Concrete.singleAttemptScheme.verify keyView.publicKey handled.1.1.1.epoch
          handled.1.1.1.message handled.1.1.1.signature)).run
            handled.1.2).run
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable verified.1.2 base)
        (combineFilteredDirectDetailedResult handled verified)) := by
  unfold filteredDirectLazyDetailedGameAfterKeygen
  simp only [bind_assoc, pure_bind, combineFilteredDirectDetailedResult]

set_option maxHeartbeats 10000 in
set_option maxRecDepth 100000 in
theorem evalDist_installed_filteredDirectDetailedGameAfterKeygen_eq_lazy
    (adversary : Adversary Concrete.singleAttemptScheme)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      (FilteredDirectExecution ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((filteredDirectDetailedGameAfterKeygen adversary
          keyView selected).run state)).run
      continuation table result] =
    𝒟[do
      let result ← filteredDirectLazyDetailedGameAfterKeygen
        adversary keyView selected state
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  calc
    _ = 𝒟[do
        let base ← $ᵗ (ChainValueIndex → Digest)
        let table := causalInstalledTable state base
        let handled ← (simulateQ
          (RevealProbeOracleSimulation.eagerTraceImpl table)
          (((simulateQ (filteredDirectActionTracedMappedAdversaryImpl
            keyView selected) (adversary.main keyView.publicKey)).run).run
              state)).run
        filteredDirectEagerVerificationContinuation keyView selected
          continuation table handled] := by
      exact
        evalDist_installed_filteredDirectDetailedGameAfterKeygen_decompose
          adversary keyView selected state continuation
    _ = 𝒟[do
        let handled ← (((simulateQ
          (filteredDirectLazyRawActionTracedImpl keyView selected)
            (adversary.main keyView.publicKey)).run).run state).run
        let base ← $ᵗ (ChainValueIndex → Digest)
        filteredDirectEagerVerificationContinuation keyView selected
          continuation (causalInstalledTable handled.1.2 base) handled] := by
      exact evalDist_installed_simulate_filteredDirectActionTraced_eq_lazy
        keyView selected (adversary.main keyView.publicKey) state
          (filteredDirectEagerVerificationContinuation
            keyView selected continuation)
    _ = 𝒟[do
        let handled ← (((simulateQ
          (filteredDirectLazyRawActionTracedImpl keyView selected)
            (adversary.main keyView.publicKey)).run).run state).run
        let verified ← ((simulateQ
          (filteredDirectLazyVerifierImpl keyView selected)
          (Concrete.singleAttemptScheme.verify keyView.publicKey handled.1.1.1.epoch
            handled.1.1.1.message handled.1.1.1.signature)).run
              handled.1.2).run
        let base ← $ᵗ (ChainValueIndex → Digest)
        continuation (causalInstalledTable verified.1.2 base)
          (combineFilteredDirectDetailedResult handled verified)] := by
      exact
        evalDist_filteredDirectLazyAdversary_eagerVerifier_eq_lazyVerifier
          adversary keyView selected state continuation
    _ = _ := by
      exact congrArg evalDist
        (filteredDirectLazyDetailedGameAfterKeygen_bind
          adversary keyView selected state continuation).symm

noncomputable def filteredDirectLazyProgramExperiment
    (adversary : Adversary Concrete.singleAttemptScheme) (selected : ChainIndex) :
    ProbComp ((ChainValueIndex → Digest) ×
      (FilteredDirectResult ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) := do
  let keyView ← actualFixedChainKeygen selected
  let initial := filteredCausalKeygenState selected keyView
  let result ← filteredDirectLazyDetailedGameAfterKeygen
    adversary keyView selected initial
  let base ← $ᵗ (ChainValueIndex → Digest)
  let table := causalInstalledTable result.1.2 base
  pure (table, ((keyView, result.1), result.2))

set_option maxRecDepth 100000 in
theorem simulate_eagerTrace_filteredDirectProgram
    (table : ChainValueIndex → Digest)
    (adversary : Adversary Concrete.singleAttemptScheme) (selected : ChainIndex) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (filteredDirectProgram adversary selected)).run = (do
      let keyView ← actualFixedChainKeygen selected
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((filteredDirectDetailedGameAfterKeygen adversary keyView selected).run
          (filteredCausalKeygenState selected keyView))).run
      pure ((keyView, result.1), result.2)) := by
  unfold filteredDirectProgram
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, List.nil_append]
  apply bind_congr
  intro keyView
  rw [simulateQ_bind, WriterT.run_bind']
  simp [simulateQ_pure, WriterT.run_pure, map_eq_bind_pure_comp]

set_option maxRecDepth 100000 in
theorem evalDist_eagerExperiment_filteredDirectProgram_eq_lazy
    (adversary : Adversary Concrete.singleAttemptScheme) (selected : ChainIndex) :
    𝒟[RevealProbeOracleSimulation.eagerExperiment
      (filteredDirectProgram adversary selected)] =
    𝒟[filteredDirectLazyProgramExperiment adversary selected] := by
  unfold RevealProbeOracleSimulation.eagerExperiment
  calc
    _ = 𝒟[do
        let base ← $ᵗ (ChainValueIndex → Digest)
        let keyView ← actualFixedChainKeygen selected
        let result ← (simulateQ
          (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((filteredDirectDetailedGameAfterKeygen adversary keyView selected).run
            (filteredCausalKeygenState selected keyView))).run
        pure (base, ((keyView, result.1), result.2))] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro base
      rw [simulate_eagerTrace_filteredDirectProgram]
      simp only [bind_assoc, pure_bind]
    _ = 𝒟[do
        let keyView ← actualFixedChainKeygen selected
        let base ← $ᵗ (ChainValueIndex → Digest)
        let result ← (simulateQ
          (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((filteredDirectDetailedGameAfterKeygen adversary keyView selected).run
            (filteredCausalKeygenState selected keyView))).run
        pure (base, ((keyView, result.1), result.2))] := by
      rw [OracleComp.DeferredSampling.evalDist_bind_comm]
    _ = _ := by
      unfold filteredDirectLazyProgramExperiment
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro keyView
      simpa [bind_assoc] using
        (evalDist_installed_filteredDirectDetailedGameAfterKeygen_eq_lazy
          adversary keyView selected (filteredCausalKeygenState selected keyView)
            (fun table result => pure
              (table, ((keyView, result.1), result.2))))

end XmssSecurity
