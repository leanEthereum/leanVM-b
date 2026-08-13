import XmssSecurity.CausalDirectLazyGame
import XmssSecurity.CausalViewCoupling

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

noncomputable local instance directFinalReductionSampleableChainTable :
    SampleableType (ChainValueIndex → Digest) :=
  SampleableType.ofFintype (ChainValueIndex → Digest)

set_option maxRecDepth 1000000 in
theorem evalDist_actualFixedChainKeygen_uniformTable_eq_withBase
    (chain : ChainIndex) :
    𝒟[do
      let keyView ← actualFixedChainKeygen chain
      let table ← $ᵗ (ChainValueIndex → Digest)
      pure (keyView, table)] =
    𝒟[do
      let keyView ← actualFixedChainKeygen chain
      let table ← uniformChainValueTable chain
      pure (keyView, table)] := by
  apply evalDist_bind_congr
  intro keyView _hkeyView
  unfold uniformChainValueTable
  simpa [map_eq_bind_pure_comp] using
    congrArg (fun distribution =>
        (fun table => (keyView, table)) <$> distribution)
      (Concrete.evalDist_sampledAllEpochChainValueTableOnly_eq_uniform
        0 chain).symm

set_option maxRecDepth 1000000 in
theorem relTriple_programmedWarmedFixedChainKeygen_fullUniform
    (chain : ChainIndex) :
    RelTriple
      (programmedWarmedFixedChainKeygen chain)
      (do
        let keyView ← actualFixedChainKeygen chain
        let table ← $ᵗ (ChainValueIndex → Digest)
        pure (keyView, table))
      (ProgrammedActualKeygenFullRelation chain) := by
  exact relTriple_of_evalDist_eq_right
    (evalDist_actualFixedChainKeygen_uniformTable_eq_withBase chain).symm
      (relTriple_programmedWarmedFixedChainKeygen_withBase_full chain)

end XmssSecurity
