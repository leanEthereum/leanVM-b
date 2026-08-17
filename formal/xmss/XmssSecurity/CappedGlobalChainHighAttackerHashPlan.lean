import XmssSecurity.CappedGlobalChainHighLeafPlan

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

noncomputable def globalFilteredCausalUncachedAttackerHashPlan
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    Option (GlobalChainValueIndex × Digest) → GlobalFilteredCausalHashPlan
  | some (index, target) =>
      match state.revealed index with
      | some value =>
          if value = target then
            if hnext : index.2.2.val + 1 < chainLength then
              .reveal (index.1, index.2.1,
                ⟨index.2.2.val + 1, hnext⟩)
            else .fresh
          else .fresh
      | none =>
          if _hnext : index.2.2.val + 1 < chainLength then
            .probeThenFresh index target
          else .fresh
  | none => globalFilteredCausalLeafHashPlan secretKey input state

noncomputable def globalFilteredCausalAttackerHashPlan
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) : GlobalFilteredCausalHashPlan :=
  match state.cache input with
  | some output => .cached output
  | none => globalFilteredCausalUncachedAttackerHashPlan secretKey input state
      (globalChainInputProbe? secretKey.parameter input)

theorem globalFilteredCausalUncachedAttackerHashPlan_eq_reveal
    (secretKey : SecretKey) (_input : HashInput)
    (state : GlobalCausalHashState)
    (index : GlobalChainValueIndex) (target : Digest)
    (hvalue : state.revealed index = some target)
    (hnext : index.2.2.val + 1 < chainLength) :
    globalFilteredCausalUncachedAttackerHashPlan secretKey _input state
        (some (index, target)) =
      .reveal (index.1, index.2.1, ⟨index.2.2.val + 1, hnext⟩) := by
  simp [globalFilteredCausalUncachedAttackerHashPlan, hvalue, hnext]

theorem globalFilteredCausalUncachedAttackerHashPlan_eq_probeThenFresh
    (secretKey : SecretKey) (_input : HashInput)
    (state : GlobalCausalHashState)
    (index : GlobalChainValueIndex) (target : Digest)
    (hhidden : state.revealed index = none)
    (hnext : index.2.2.val + 1 < chainLength) :
    globalFilteredCausalUncachedAttackerHashPlan secretKey _input state
        (some (index, target)) =
      .probeThenFresh index target := by
  simp [globalFilteredCausalUncachedAttackerHashPlan, hhidden, hnext]

theorem globalFilteredCausalAttackerHashPlan_eq_probeThenFresh
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (target : Digest)
    (hcache : state.cache input = none)
    (hprobe : globalChainInputProbe? secretKey.parameter input =
      some (index, target))
    (hhidden : state.revealed index = none)
    (hnext : index.2.2.val + 1 < chainLength) :
    globalFilteredCausalAttackerHashPlan secretKey input state =
      .probeThenFresh index target := by
  rw [globalFilteredCausalAttackerHashPlan, hcache, hprobe]
  exact globalFilteredCausalUncachedAttackerHashPlan_eq_probeThenFresh
    secretKey input state index target hhidden hnext

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
    secretKey
    (globalChainTableEdgeInput secretKey.parameter table edge) state
    (edge.1, edge.2.1, chainStepDigit edge.2.2)
    (table (edge.1, edge.2.1, chainStepDigit edge.2.2)) hrevealed
    (chainStepNextDigit edge.2.2).isLt

theorem globalFilteredCausalAttackerHashPlan_eq_probeThenFresh_globalEdge
    (secretKey : SecretKey)
    (table : GlobalChainValueIndex → Digest)
    (edge : GlobalChainEdgeIndex) (state : GlobalCausalHashState)
    (hcache : state.cache
      (globalChainTableEdgeInput secretKey.parameter table edge) = none)
    (hhidden : state.revealed
      (edge.1, edge.2.1, chainStepDigit edge.2.2) = none) :
    globalFilteredCausalAttackerHashPlan secretKey
        (globalChainTableEdgeInput secretKey.parameter table edge) state =
      .probeThenFresh
        (edge.1, edge.2.1, chainStepDigit edge.2.2)
        (table (edge.1, edge.2.1, chainStepDigit edge.2.2)) := by
  rw [globalFilteredCausalAttackerHashPlan, hcache]
  rw [globalChainInputProbe?_globalChainTableEdgeInput]
  exact globalFilteredCausalUncachedAttackerHashPlan_eq_probeThenFresh
    secretKey
    (globalChainTableEdgeInput secretKey.parameter table edge) state
    (edge.1, edge.2.1, chainStepDigit edge.2.2)
    (table (edge.1, edge.2.1, chainStepDigit edge.2.2)) hhidden
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
  | .probeThenFresh index target => do
      let _ ← RevealProbeOracleSimulation.probeQuery index target
      (globalCausalHashQuery input).run recorded
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
       | .probeThenFresh index target => do
           let _ ← RevealProbeOracleSimulation.probeQuery index target
           (globalCausalHashQuery input).run recorded
       | .fresh => (globalCausalHashQuery input).run recorded
       | .reveal index =>
           globalCausalRevealHashQueryFromHigh high secretKey input state
             index) := rfl

end XmssSecurity.CappedChain
