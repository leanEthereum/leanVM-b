import XmssSecurity.Proof.CausalKeygenProjection

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

def causalKeyResultOfReal
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) :
    (PublicKey × SecretKey) × CausalHashState :=
  (keyResult.1, { CausalHashState.empty with cache := keyResult.2 })

noncomputable def causalStrategyAfterRealKeygen
    (adversary : Adversary Concrete.singleAttemptScheme) (chain : ChainIndex)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) :
    OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)
      (List Bool → ChainValueIndex × Digest) := do
  let causalKeyResult := causalKeyResultOfReal keyResult
  let execution ← (causalDetailedGameAfterKeygen adversary
    causalKeyResult.1.1 causalKeyResult.1.2 chain).run
      causalKeyResult.2.finishKeygen
  pure (actionTracedRevealProbeView chain
    (causalDetailedResult causalKeyResult execution)).strategy

theorem simulate_eagerTrace_causalStrategyProgram_eq_afterRealKeygen
    (table : ChainValueIndex → Digest)
    (adversary : Adversary Concrete.singleAttemptScheme) (chain : ChainIndex) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (causalStrategyProgram adversary chain)).run =
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅ >>= fun keyResult =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          (causalStrategyAfterRealKeygen adversary chain keyResult)).run) := by
  unfold causalStrategyProgram
  rw [simulateQ_bind, WriterT.run_bind',
    simulate_eagerTrace_causalKeygen_reconstruct]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, List.nil_append]
  apply bind_congr
  intro keyResult
  simp [causalStrategyAfterRealKeygen, causalKeyResultOfReal]

theorem simulate_eagerTrace_compileStrategyProbes_causalStrategyProgram_eq_afterRealKeygen
    (table : ChainValueIndex → Digest) (queries : Nat)
    (adversary : Adversary Concrete.singleAttemptScheme) (chain : ChainIndex) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (RevealProbeOracleSimulation.compileStrategyProbes queries
          (causalStrategyProgram adversary chain))).run =
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅ >>= fun keyResult =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          (RevealProbeOracleSimulation.compileStrategyProbes queries
            (causalStrategyAfterRealKeygen adversary chain keyResult))).run) := by
  unfold RevealProbeOracleSimulation.compileStrategyProbes
  rw [simulateQ_bind, WriterT.run_bind',
    simulate_eagerTrace_causalStrategyProgram_eq_afterRealKeygen]
  simp only [bind_assoc]
  apply bind_congr
  intro keyResult
  rw [simulateQ_bind, WriterT.run_bind']

end XmssSecurity
