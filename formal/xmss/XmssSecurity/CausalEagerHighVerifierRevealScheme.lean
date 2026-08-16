import XmssSecurity.CausalEagerHighVerifierRevealHelpers

open OracleComp OracleSpec

namespace XmssSecurity

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem filteredHighVerifier_support_scheme_cache_le
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (publicKey : PublicKey)
    (epoch : Epoch) (message : Message) (signature : Signature)
    (state : CausalHashState)
    (result : (Bool × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ (filteredHighVerifierImpl keyHigh selected)
          (Concrete.scheme.verify publicKey epoch message signature)).run
            state)).run)) :
    state.cache ≤ result.1.2.cache := by
  unfold Concrete.scheme at hresult
  rw [simulate_filteredHighVerifier_liftM_eq_hashOnly] at hresult
  generalize (Concrete.verify publicKey epoch message signature :
    OracleComp HashSpec Bool) = computation at hresult
  exact simulate_filteredHighHashOnlyVerifier_support_cache_le table keyHigh
    selected computation state result hresult

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem filteredHighVerifier_support_scheme_resultCovered
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (publicKey : PublicKey)
    (epoch : Epoch) (message : Message) (signature : Signature)
    (state : CausalHashState) (covered : Set ChainValueIndex)
    (hcovered : CausalRevealsCovered covered state)
    (hforward : ChainValueIndicesForwardClosed covered)
    (result : (Bool × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ (filteredHighVerifierImpl keyHigh selected)
          (Concrete.scheme.verify publicKey epoch message signature)).run
            state)).run)) :
    CausalResultCovered covered result := by
  unfold Concrete.scheme at hresult
  rw [simulate_filteredHighVerifier_liftM_eq_hashOnly] at hresult
  generalize (Concrete.verify publicKey epoch message signature :
    OracleComp HashSpec Bool) = computation at hresult
  exact simulate_filteredHighHashOnlyVerifier_support_resultCovered table
    keyHigh selected computation state covered hcovered hforward result hresult

end XmssSecurity
