import XmssSecurity.CausalDirectFinalReduction

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

noncomputable def chainValueHighTableOfEdges
    (high : ChainEdgeIndex → Digest) : ChainValueIndex → Digest :=
  fun index =>
    if hzero : index.2.val = 0 then
      0
    else
      high (index.1, ⟨index.2.val - 1, by omega⟩)

@[simp]
theorem chainValueHighTableOfEdges_next
    (high : ChainEdgeIndex → Digest) (edge : ChainEdgeIndex) :
    chainValueHighTableOfEdges high
        (edge.1, chainStepNextDigit edge.2) =
      high edge := by
  unfold chainValueHighTableOfEdges
  simp only [chainStepNextDigit]
  rw [dif_neg (by omega)]
  congr 2

noncomputable def causalRevealHashQueryFromHigh
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex) :
    OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)
      (HashOutput × CausalHashState) := do
  let value ← RevealProbeOracleSimulation.revealQuery index
  let output := Rom.hashOutputEquivDigestPair.symm (high index, value)
  pure (output, causalRevealResultState secretKey selected input state
    index value output)

noncomputable def filteredCausalAttackerHashQueryFromHigh
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput) :
    StateT CausalHashState
      (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))
      HashOutput := fun state =>
  let recorded := causalRecordedState secretKey selected input state
  match filteredCausalAttackerHashPlan secretKey selected input state with
  | .cached output => pure (output, recorded)
  | .reveal index =>
      causalRevealHashQueryFromHigh high secretKey selected input state index
  | .conditioned digest => do
      let output ← RevealProbeOracleSimulation.liftProbComp
        (Rom.sampleHashOutputWithDigest digest)
      pure (output,
        { recorded with cache := recorded.cache.cacheQuery input output })
  | .fresh => (causalHashQuery input).run recorded

noncomputable def filteredProbingAttackerHashQueryAtFromHigh
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) : Option (ChainValueIndex × Digest) →
    OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)
      (HashOutput × CausalHashState)
  | none => (filteredCausalAttackerHashQueryFromHigh
      high secretKey selected input).run state
  | some probe =>
      match state.revealed probe.1 with
      | some _ => (filteredCausalAttackerHashQueryFromHigh
          high secretKey selected input).run state
      | none => do
          let _ ← RevealProbeOracleSimulation.probeQuery probe.1 probe.2
          (filteredCausalAttackerHashQueryFromHigh
            high secretKey selected input).run state

end XmssSecurity
