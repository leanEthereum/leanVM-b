import XmssSecurity.CausalWarmedHighIndependence
import XmssSecurity.CausalDirectReduction

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

noncomputable local instance eagerHighSampleableChainTable :
    SampleableType (ChainValueIndex → Digest) :=
  SampleableType.ofFintype (ChainValueIndex → Digest)

set_option maxRecDepth 1000000 in
theorem evalDist_uniform_coupledWarmedFixedChainKeygenWithHigh_eq_baseHigh
    (chain : ChainIndex) :
    evalDist (do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let keyHigh ← coupledWarmedFixedChainKeygenWithHigh chain
      pure ((keyHigh.1, base), keyHigh.2)) =
    evalDist (coupledWarmedFixedChainKeygenWithBaseHigh chain) := by
  calc
    _ = evalDist (do
        let keyHigh ← coupledWarmedFixedChainKeygenWithHigh chain
        let base ← $ᵗ (ChainValueIndex → Digest)
        pure ((keyHigh.1, base), keyHigh.2)) :=
      OracleComp.DeferredSampling.evalDist_bind_comm
        ($ᵗ (ChainValueIndex → Digest))
        (coupledWarmedFixedChainKeygenWithHigh chain)
        (fun base keyHigh => pure ((keyHigh.1, base), keyHigh.2))
    _ = evalDist (do
        let keyHigh ← coupledWarmedFixedChainKeygenWithHigh chain
        let base ← uniformChainValueTable chain
        pure ((keyHigh.1, base), keyHigh.2)) := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro keyHigh
      unfold uniformChainValueTable
      conv_lhs => rw [evalDist_bind]
      conv_rhs => rw [evalDist_bind]
      rw [Concrete.evalDist_sampledAllEpochChainValueTableOnly_eq_uniform
        0 chain]
    _ = evalDist (coupledWarmedFixedChainKeygenWithBaseHigh chain) := by
      unfold coupledWarmedFixedChainKeygenWithHigh
        coupledWarmedFixedChainKeygenWithBaseHigh
        coupledWarmedKeygenExperimentWithHigh
        coupledWarmedKeygenWithBaseHigh
        programmedWarmedTrajectoryMaterialWithBaseHigh
      simp only [bind_assoc, pure_bind]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro parameter
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro materialHigh
      exact OracleComp.DeferredSampling.evalDist_bind_comm
        (treeValues parameter (unflattenSecret materialHigh.1.1.2)
          allTreeValueIndices materialHigh.1.2.2)
        (uniformChainValueTable chain)
        (fun tree base => pure
          ((CoupledWarmedKeygenView.toProgrammedView parameter {
              secret := unflattenSecret materialHigh.1.1.2
              table := chainValueTableOfList materialHigh.1.2.1
              values := tree.1
              cache := tree.2
            }, base), materialHigh.2))

set_option maxRecDepth 1000000 in
theorem relTriple_programmedWarmedFixedChainKeygen_uniformHigh
    (chain : ChainIndex) :
    RelTriple
      (programmedWarmedFixedChainKeygen chain)
      (do
        let base ← $ᵗ (ChainValueIndex → Digest)
        let keyHigh ← coupledWarmedFixedChainKeygenWithHigh chain
        pure ((keyHigh.1, base), keyHigh.2))
      (ProgrammedActualKeygenCacheHighRelation chain) := by
  apply relTriple_of_evalDist_eq_right
    (evalDist_uniform_coupledWarmedFixedChainKeygenWithHigh_eq_baseHigh
      chain).symm
  exact relTriple_programmedWarmedFixedChainKeygen_withBaseHigh chain

end XmssSecurity
