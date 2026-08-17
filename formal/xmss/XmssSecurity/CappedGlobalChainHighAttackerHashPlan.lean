import XmssSecurity.CappedGlobalChainHighAttackerHashDisjointness

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

noncomputable def globalFilteredCausalUncachedAttackerHashPlan
    (_input : HashInput) (state : GlobalCausalHashState) :
    Option (GlobalChainValueIndex × Digest) → GlobalCausalHashPlan
  | some (index, target) =>
      match state.revealed index with
      | some value =>
          if value = target then
            if hnext : index.2.2.val + 1 < chainLength then
              .reveal (index.1, index.2.1,
                ⟨index.2.2.val + 1, hnext⟩)
            else .fresh
          else .fresh
      | none => .fresh
  | none => .fresh

noncomputable def globalFilteredCausalAttackerHashPlan
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) : GlobalCausalHashPlan :=
  match state.cache input with
  | some output => .cached output
  | none => globalFilteredCausalUncachedAttackerHashPlan input state
      (globalChainInputProbe? secretKey.parameter input)

theorem globalFilteredCausalUncachedAttackerHashPlan_eq_reveal
    (_input : HashInput) (state : GlobalCausalHashState)
    (index : GlobalChainValueIndex) (target : Digest)
    (hvalue : state.revealed index = some target)
    (hnext : index.2.2.val + 1 < chainLength) :
    globalFilteredCausalUncachedAttackerHashPlan _input state
        (some (index, target)) =
      .reveal (index.1, index.2.1, ⟨index.2.2.val + 1, hnext⟩) := by
  simp [globalFilteredCausalUncachedAttackerHashPlan, hvalue, hnext]

@[simp]
theorem globalChainInputProbe?_globalChainTableEdgeInput
    (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest)
    (edge : GlobalChainEdgeIndex) :
    globalChainInputProbe? parameter
        (globalChainTableEdgeInput parameter table edge) =
      some ((edge.1, edge.2.1, chainStepDigit edge.2.2),
        table (edge.1, edge.2.1, chainStepDigit edge.2.2)) := by
  exact globalChainInputProbe?_chainInput parameter edge.2.1 edge.1 edge.2.2
    (table (edge.1, edge.2.1, chainStepDigit edge.2.2))

theorem globalFilteredCausalAttackerHashPlan_eq_reveal_globalEdge
    (secretKey : SecretKey)
    (table : GlobalChainValueIndex → Digest)
    (edge : GlobalChainEdgeIndex) (state : GlobalCausalHashState)
    (hcache : state.cache
      (globalChainTableEdgeInput secretKey.parameter table edge) = none)
    (hrevealed : state.revealed
      (edge.1, edge.2.1, chainStepDigit edge.2.2) =
        some (table (edge.1, edge.2.1, chainStepDigit edge.2.2))) :
    globalFilteredCausalAttackerHashPlan secretKey
        (globalChainTableEdgeInput secretKey.parameter table edge) state =
      .reveal (edge.1, edge.2.1, chainStepNextDigit edge.2.2) := by
  rw [globalFilteredCausalAttackerHashPlan, hcache]
  rw [globalChainInputProbe?_globalChainTableEdgeInput]
  have hnext :
      (⟨(chainStepDigit edge.2.2).val + 1,
        (chainStepNextDigit edge.2.2).isLt⟩ : Digit) =
        chainStepNextDigit edge.2.2 := by
    apply Fin.ext
    rfl
  rw [← hnext]
  exact globalFilteredCausalUncachedAttackerHashPlan_eq_reveal
    (globalChainTableEdgeInput secretKey.parameter table edge) state
    (edge.1, edge.2.1, chainStepDigit edge.2.2)
    (table (edge.1, edge.2.1, chainStepDigit edge.2.2)) hrevealed
    (chainStepNextDigit edge.2.2).isLt

noncomputable def globalCausalAttackerHashQueryFromHigh
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput) :
    StateT GlobalCausalHashState
      (OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex))
      HashOutput := fun state =>
  let recorded := globalCausalRecordedState secretKey input state
  match globalFilteredCausalAttackerHashPlan secretKey input state with
  | .cached output => pure (output, recorded)
  | .redirect output =>
      pure (output, { recorded with
        cache := recorded.cache.cacheQuery input output })
  | .fresh => (globalCausalHashQuery input).run recorded
  | .reveal index =>
      globalCausalRevealHashQueryFromHigh high secretKey input state index

theorem globalCausalAttackerHashQueryFromHigh_run
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    (globalCausalAttackerHashQueryFromHigh high secretKey input).run state =
      (let recorded := globalCausalRecordedState secretKey input state
       match globalFilteredCausalAttackerHashPlan secretKey input state with
       | .cached output => pure (output, recorded)
       | .redirect output =>
           pure (output, { recorded with
             cache := recorded.cache.cacheQuery input output })
       | .fresh => (globalCausalHashQuery input).run recorded
       | .reveal index =>
           globalCausalRevealHashQueryFromHigh high secretKey input state
             index) := rfl

end XmssSecurity.CappedChain
