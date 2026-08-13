import XmssSecurity.CausalDirectEagerRawBridge

open OracleComp OracleSpec

namespace XmssSecurity

noncomputable local instance directLazyAdversaryCompositionSampleableChainTable :
    SampleableType (ChainValueIndex → Digest) :=
  SampleableType.ofFintype (ChainValueIndex → Digest)

set_option maxRecDepth 100000 in
theorem evalDist_installed_simulate_filteredDirectActionTraced_eq_lazy
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      (((α × AttackerActionTrace) × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp β) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        (((simulateQ (filteredDirectActionTracedMappedAdversaryImpl
          keyView selected) computation).run).run state)).run
      continuation table result] =
    𝒟[do
      let result ← (((simulateQ
        (filteredDirectLazyRawActionTracedImpl keyView selected)
          computation).run).run state).run
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  calc
    _ = 𝒟[do
        let base ← $ᵗ (ChainValueIndex → Digest)
        let table := causalInstalledTable state base
        let result ← (((simulateQ
          (filteredDirectEagerRawActionTracedImpl table keyView selected)
            computation).run).run state).run
        continuation table result] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro base
      exact congrArg
        (fun comp => evalDist
          (comp >>= continuation (causalInstalledTable state base)))
        (simulate_eagerTrace_simulate_filteredDirectActionTraced_eq_raw
          (causalInstalledTable state base) keyView selected computation state)
    _ = _ :=
      evalDist_installed_simulate_filteredDirectRawActionTraced_eq_lazy
        keyView selected computation state continuation

end XmssSecurity
