import XmssSecurity.CausalFilteredProbe

open OracleComp OracleSpec

namespace XmssSecurity

noncomputable def selectedChainSuffixEdges
    (epoch : Epoch) (start : Digit) : List ChainEdgeIndex :=
  allChainEdges.filter fun edge =>
    edge.1 = epoch ∧ start.val ≤ edge.2.val

noncomputable def filteredCausalMaterializeEdges
    (parameter : PublicParameter) (selected : ChainIndex) :
    List ChainEdgeIndex →
      StateT CausalHashState
        (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)) Unit
  | [] => pure ()
  | edge :: edges => fun state => do
      let currentIndex := (edge.1, chainStepDigit edge.2)
      let nextIndex := (edge.1, chainStepNextDigit edge.2)
      let current ← RevealProbeOracleSimulation.revealQuery currentIndex
      let next ← RevealProbeOracleSimulation.revealQuery nextIndex
      let output ← RevealProbeOracleSimulation.liftProbComp
        (Rom.sampleHashOutputWithDigest next)
      let input := Concrete.CacheView.chainInput parameter edge.1 selected
        edge.2 current
      let recorded := (state.recordReveal currentIndex current).recordReveal
        nextIndex next
      filteredCausalMaterializeEdges parameter selected edges
        { recorded with cache := recorded.cache.cacheQuery input output }

noncomputable def filteredCausalMaterializeSuffix
    (parameter : PublicParameter) (selected : ChainIndex)
    (epoch : Epoch) (start : Digit) :
    StateT CausalHashState
      (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)) Digest :=
  fun state => do
    let index := (epoch, start)
    let value ← RevealProbeOracleSimulation.revealQuery index
    let recorded := state.recordReveal index value
    let result ← (filteredCausalMaterializeEdges parameter selected
      (selectedChainSuffixEdges epoch start)).run recorded
    pure (value, result.2)

theorem filteredCausalMaterializeEdges_run_isProbeQueryBoundP
    (parameter : PublicParameter) (selected : ChainIndex)
    (edges : List ChainEdgeIndex) (state : CausalHashState) :
    (filteredCausalMaterializeEdges parameter selected edges).run state
      |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  induction edges generalizing state with
  | nil => exact OracleComp.isQueryBoundP_pure (p :=
      RevealProbeOracleSimulation.IsProbeQuery) ((), state) 0
  | cons edge edges ih =>
      simp only [filteredCausalMaterializeEdges, StateT.run]
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (RevealProbeOracleSimulation.revealQuery_isProbeQueryBoundP
          (edge.1, chainStepDigit edge.2) 0)
      intro current _hcurrent
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (RevealProbeOracleSimulation.revealQuery_isProbeQueryBoundP
          (edge.1, chainStepNextDigit edge.2) 0)
      intro next _hnext
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (RevealProbeOracleSimulation.liftProbComp_isProbeQueryBoundP
          (Rom.sampleHashOutputWithDigest next) 0)
      intro output _houtput
      exact ih { ((state.recordReveal
        (edge.1, chainStepDigit edge.2) current).recordReveal
          (edge.1, chainStepNextDigit edge.2) next) with
        cache := ((state.recordReveal
          (edge.1, chainStepDigit edge.2) current).recordReveal
            (edge.1, chainStepNextDigit edge.2) next).cache.cacheQuery
              (Concrete.CacheView.chainInput parameter edge.1 selected
                edge.2 current) output }

theorem filteredCausalMaterializeSuffix_run_isProbeQueryBoundP
    (parameter : PublicParameter) (selected : ChainIndex)
    (epoch : Epoch) (start : Digit) (state : CausalHashState) :
    (filteredCausalMaterializeSuffix parameter selected epoch start).run state
      |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  unfold filteredCausalMaterializeSuffix
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (RevealProbeOracleSimulation.revealQuery_isProbeQueryBoundP
      (epoch, start) 0)
  intro value _hvalue
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (filteredCausalMaterializeEdges_run_isProbeQueryBoundP parameter selected
      (selectedChainSuffixEdges epoch start)
        (state.recordReveal (epoch, start) value))
  intro result _hresult
  exact OracleComp.isQueryBoundP_pure
    (p := RevealProbeOracleSimulation.IsProbeQuery) (value, result.2) 0

noncomputable def filteredDirectSigningQuery
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (state : CausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)
      (Option Signature × CausalHashState) := do
  let randomness ← RevealProbeOracleSimulation.liftProbComp
    Concrete.signingRandomness
  let encoded ← RevealProbeOracleSimulation.liftProbComp
    ((simulateQ randomOracle
      (Concrete.encodingHash keyView.secretKey.parameter request.epoch
        request.message randomness)).run state.cache)
  let encodedState := { state with cache := encoded.2 }
  match TargetSum.decodeDigest encoded.1 with
  | none => pure (none, encodedState)
  | some encoding => do
      let materialized ← (filteredCausalMaterializeSuffix
        keyView.secretKey.parameter selected request.epoch
          (encoding selected)).run encodedState
      let signature := replaceSignatureChainValue
        (Concrete.CacheReplay.signWithEncoding keyView.cache keyView.secretKey
          request.epoch randomness encoding) selected materialized.1
      pure (some signature, materialized.2)

theorem filteredDirectSigningQuery_isProbeQueryBoundP
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (state : CausalHashState) :
    (filteredDirectSigningQuery keyView selected request state)
      |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  unfold filteredDirectSigningQuery
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (RevealProbeOracleSimulation.liftProbComp_isProbeQueryBoundP
      Concrete.signingRandomness 0)
  intro randomness _hrandomness
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (RevealProbeOracleSimulation.liftProbComp_isProbeQueryBoundP
      ((simulateQ randomOracle
        (Concrete.encodingHash keyView.secretKey.parameter request.epoch
          request.message randomness)).run state.cache) 0)
  intro encoded _hencoded
  cases hdecode : TargetSum.decodeDigest encoded.1 with
  | none =>
      exact OracleComp.isQueryBoundP_pure
        (p := RevealProbeOracleSimulation.IsProbeQuery)
          (none, { state with cache := encoded.2 }) 0
  | some encoding =>
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (filteredCausalMaterializeSuffix_run_isProbeQueryBoundP
          keyView.secretKey.parameter selected request.epoch
            (encoding selected) { state with cache := encoded.2 })
      intro materialized _hmaterialized
      exact OracleComp.isQueryBoundP_pure
        (p := RevealProbeOracleSimulation.IsProbeQuery)
          (some (replaceSignatureChainValue
            (Concrete.CacheReplay.signWithEncoding keyView.cache
              keyView.secretKey request.epoch randomness encoding)
            selected materialized.1), materialized.2) 0

end XmssSecurity
