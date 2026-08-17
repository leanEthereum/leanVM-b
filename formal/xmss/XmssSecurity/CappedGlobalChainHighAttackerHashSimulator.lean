import XmssSecurity.CappedGlobalChainHighHashCoupling

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

noncomputable def globalChainValueHighTableOfEdges
    (high : GlobalChainEdgeIndex → Digest) :
    GlobalChainValueIndex → Digest := fun index =>
  if hzero : index.2.2.val = 0 then
    0
  else
    high (index.1, index.2.1, ⟨index.2.2.val - 1, by omega⟩)

@[simp]
theorem globalChainValueHighTableOfEdges_next
    (high : GlobalChainEdgeIndex → Digest)
    (edge : GlobalChainEdgeIndex) :
    globalChainValueHighTableOfEdges high
        (edge.1, edge.2.1, chainStepNextDigit edge.2.2) =
      high edge := by
  unfold globalChainValueHighTableOfEdges
  simp only [chainStepNextDigit]
  rw [dif_neg (by omega)]
  congr 3

noncomputable def globalCausalRevealHashQueryFromHigh
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (HashOutput × GlobalCausalHashState) := do
  let value ← RevealProbeOracleSimulation.revealQuery index
  let output := Rom.hashOutputEquivDigestPair.symm (high index, value)
  pure (output, globalFilteredCausalRevealResultState secretKey input state
    index value output)

theorem simulate_eagerTrace_globalCausalRevealHashQueryFromHigh
    (table high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (globalCausalRevealHashQueryFromHigh high secretKey input state
        index)).run =
      pure ((Rom.hashOutputEquivDigestPair.symm
          (high index, table index),
        globalFilteredCausalRevealResultState secretKey input state index
          (table index) (Rom.hashOutputEquivDigestPair.symm
            (high index, table index))),
        [RevealProbeOracleSimulation.ObservedAction.reveal
          index (table index)]) := by
  unfold globalCausalRevealHashQueryFromHigh
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_revealQuery]
  simp

theorem globalChainEdgeOutputFromHigh_eq_revealOutput
    (high : GlobalChainEdgeIndex → Digest)
    (table : GlobalChainValueIndex → Digest)
    (edge : GlobalChainEdgeIndex) :
    Rom.hashOutputEquivDigestPair.symm
        (globalChainValueHighTableOfEdges high
          (edge.1, edge.2.1, chainStepNextDigit edge.2.2),
          table (edge.1, edge.2.1, chainStepNextDigit edge.2.2)) =
      globalChainEdgeOutputFromHigh high table edge := by
  unfold globalChainEdgeOutputFromHigh globalChainTableEdgeTarget
  rw [globalChainValueHighTableOfEdges_next]

end XmssSecurity.CappedChain
