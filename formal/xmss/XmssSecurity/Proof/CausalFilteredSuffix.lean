import XmssSecurity.Proof.CausalFilteredProbe

open OracleComp OracleSpec

namespace XmssSecurity

noncomputable def selectedChainSuffixEdges
    (epoch : Epoch) (start : Digit) : List ChainEdgeIndex :=
  allChainEdges.filter fun edge =>
    edge.1 = epoch ∧ start.val ≤ edge.2.val

def UnrevealedChainInputsAbsent
    (table : ChainValueIndex → Digest)
    (parameter : PublicParameter) (selected : ChainIndex)
    (state : CausalHashState) : Prop :=
  ∀ edge,
    state.revealed (edge.1, chainStepDigit edge.2) = none →
      state.cache (chainTableEdgeInput parameter selected table edge) = none

theorem chainTableEdgeInput_not_outside
    (table : ChainValueIndex → Digest)
    (parameter : PublicParameter) (selected : ChainIndex)
    (edge : ChainEdgeIndex) :
    ¬ OutsideChainHashInput parameter selected
      (chainTableEdgeInput parameter selected table edge) := by
  rintro ⟨epoch, candidate, step, hne, hcandidate⟩
  have hselected : AtHashAddress parameter
      (.chain edge.1 selected edge.2)
      (chainTableEdgeInput parameter selected table edge) := by
    simp [chainTableEdgeInput, Concrete.CacheView.chainInput]
  have heq := atHashAddress_unique parameter
    (.chain epoch candidate step) (.chain edge.1 selected edge.2)
      (chainTableEdgeInput parameter selected table edge)
        hcandidate hselected
  simp only [HashDomain.chain.injEq] at heq
  exact hne heq.2.1

theorem filteredCausalKeygenState_unrevealedChainInputsAbsent
    (table : ChainValueIndex → Digest)
    (selected : ChainIndex) (view : ProgrammedFixedChainKeygenView) :
    UnrevealedChainInputsAbsent table view.secretKey.parameter selected
      (filteredCausalKeygenState selected view) := by
  intro edge _hhidden
  rw [filteredCausalKeygenState_cache]
  exact outsideChainOnly_of_not_outside _ _ _ _
    (chainTableEdgeInput_not_outside table view.secretKey.parameter
      selected edge)

def filteredMaterializedEdgeState
    (parameter : PublicParameter) (selected : ChainIndex)
    (edge : ChainEdgeIndex) (state : CausalHashState)
    (current next : Digest) (output : HashOutput) : CausalHashState :=
  let currentIndex := (edge.1, chainStepDigit edge.2)
  let nextIndex := (edge.1, chainStepNextDigit edge.2)
  let input := Concrete.CacheView.chainInput parameter edge.1 selected
    edge.2 current
  let recorded := (state.recordReveal currentIndex current).recordReveal
    nextIndex next
  { recorded with cache := recorded.cache.cacheQuery input output }

theorem CausalRevealsAgree.filteredMaterializedEdgeState
    (table : ChainValueIndex → Digest)
    (parameter : PublicParameter) (selected : ChainIndex)
    (edge : ChainEdgeIndex) (state : CausalHashState)
    (hagrees : CausalRevealsAgree table state)
    (output : HashOutput) :
    CausalRevealsAgree table
      (filteredMaterializedEdgeState parameter selected edge state
        (table (edge.1, chainStepDigit edge.2))
        (table (edge.1, chainStepNextDigit edge.2)) output) := by
  unfold XmssSecurity.filteredMaterializedEdgeState
  exact ((hagrees.recordReveal
    (edge.1, chainStepDigit edge.2)
      (table (edge.1, chainStepDigit edge.2)) rfl).recordReveal
    (edge.1, chainStepNextDigit edge.2)
      (table (edge.1, chainStepNextDigit edge.2)) rfl).setCache _

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
      filteredCausalMaterializeEdges parameter selected edges
        (filteredMaterializedEdgeState parameter selected edge state
          current next output)

noncomputable def filteredLazyMaterializeEdges
    (table : ChainValueIndex → Digest)
    (parameter : PublicParameter) (selected : ChainIndex) :
    List ChainEdgeIndex → CausalHashState →
      ProbComp ((Unit × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
  | [], state => pure (((), state), [])
  | edge :: edges, state => do
      let currentIndex := (edge.1, chainStepDigit edge.2)
      let nextIndex := (edge.1, chainStepNextDigit edge.2)
      let output ← Rom.sampleHashOutputWithDigest (table nextIndex)
      let nextState := filteredMaterializedEdgeState parameter selected edge
        state (table currentIndex) (table nextIndex) output
      let rest ← filteredLazyMaterializeEdges table parameter selected
        edges nextState
      pure (rest.1,
        [.reveal currentIndex (table currentIndex),
          .reveal nextIndex (table nextIndex)] ++ rest.2)

set_option maxRecDepth 100000 in
theorem simulate_eagerTrace_filteredCausalMaterializeEdges
    (table : ChainValueIndex → Digest)
    (parameter : PublicParameter) (selected : ChainIndex)
    (edges : List ChainEdgeIndex) (state : CausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((filteredCausalMaterializeEdges parameter selected edges).run state)).run =
        filteredLazyMaterializeEdges table parameter selected edges state := by
  induction edges generalizing state with
  | nil => simp [filteredCausalMaterializeEdges,
      filteredLazyMaterializeEdges]
  | cons edge edges ih =>
      change (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table) (do
          let current ← RevealProbeOracleSimulation.revealQuery
            (edge.1, chainStepDigit edge.2)
          let next ← RevealProbeOracleSimulation.revealQuery
            (edge.1, chainStepNextDigit edge.2)
          let output ← RevealProbeOracleSimulation.liftProbComp
            (Rom.sampleHashOutputWithDigest next)
          (filteredCausalMaterializeEdges parameter selected edges).run
            (filteredMaterializedEdgeState parameter selected edge state
              current next output))).run = _
      simp [filteredLazyMaterializeEdges, simulateQ_bind,
        RevealProbeOracleSimulation.simulate_eagerTrace_revealQuery,
        RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp,
        ih, map_eq_bind_pure_comp, bind_assoc]

theorem filteredLazyMaterializeEdges_support_revealsAgree
    (table : ChainValueIndex → Digest)
    (parameter : PublicParameter) (selected : ChainIndex)
    (edges : List ChainEdgeIndex) (state : CausalHashState)
    (hagrees : CausalRevealsAgree table state)
    (result : (Unit × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      (filteredLazyMaterializeEdges table parameter selected edges state)) :
    CausalRevealsAgree table result.1.2 := by
  induction edges generalizing state result with
  | nil =>
      simp only [filteredLazyMaterializeEdges, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact hagrees
  | cons edge edges ih =>
      rw [filteredLazyMaterializeEdges, mem_support_bind_iff] at hresult
      obtain ⟨output, _houtput, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      exact ih
        (filteredMaterializedEdgeState parameter selected edge state
          (table (edge.1, chainStepDigit edge.2))
          (table (edge.1, chainStepNextDigit edge.2)) output)
        (CausalRevealsAgree.filteredMaterializedEdgeState table parameter
          selected edge state hagrees output)
        rest
        hrest

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

noncomputable def filteredLazyMaterializeSuffix
    (table : ChainValueIndex → Digest)
    (parameter : PublicParameter) (selected : ChainIndex)
    (epoch : Epoch) (start : Digit) (state : CausalHashState) :
    ProbComp ((Digest × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) := do
  let index := (epoch, start)
  let value := table index
  let result ← filteredLazyMaterializeEdges table parameter selected
    (selectedChainSuffixEdges epoch start) (state.recordReveal index value)
  pure ((value, result.1.2), .reveal index value :: result.2)

set_option maxRecDepth 100000 in
theorem simulate_eagerTrace_filteredCausalMaterializeSuffix
    (table : ChainValueIndex → Digest)
    (parameter : PublicParameter) (selected : ChainIndex)
    (epoch : Epoch) (start : Digit) (state : CausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((filteredCausalMaterializeSuffix parameter selected epoch start).run
        state)).run =
      filteredLazyMaterializeSuffix table parameter selected epoch start state := by
  change (simulateQ
    (RevealProbeOracleSimulation.eagerTraceImpl table) (do
      let value ← RevealProbeOracleSimulation.revealQuery (epoch, start)
      let result ← (filteredCausalMaterializeEdges parameter selected
        (selectedChainSuffixEdges epoch start)).run
          (state.recordReveal (epoch, start) value)
      pure (value, result.2))).run = _
  simp [filteredLazyMaterializeSuffix, simulateQ_bind,
    RevealProbeOracleSimulation.simulate_eagerTrace_revealQuery,
    simulate_eagerTrace_filteredCausalMaterializeEdges,
    map_eq_bind_pure_comp, bind_assoc]

theorem filteredLazyMaterializeSuffix_support_revealsAgree
    (table : ChainValueIndex → Digest)
    (parameter : PublicParameter) (selected : ChainIndex)
    (epoch : Epoch) (start : Digit) (state : CausalHashState)
    (hagrees : CausalRevealsAgree table state)
    (result : (Digest × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      (filteredLazyMaterializeSuffix table parameter selected epoch start state)) :
    CausalRevealsAgree table result.1.2 := by
  unfold filteredLazyMaterializeSuffix at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨rest, hrest, hpure⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  apply filteredLazyMaterializeEdges_support_revealsAgree table parameter
    selected (selectedChainSuffixEdges epoch start)
      (state.recordReveal (epoch, start) (table (epoch, start)))
  · exact hagrees.recordReveal (epoch, start) (table (epoch, start)) rfl
  · exact hrest

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

noncomputable def filteredLazyDirectSigningQuery
    (table : ChainValueIndex → Digest)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (state : CausalHashState) :
    ProbComp ((Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) := do
  let randomness ← Concrete.signingRandomness
  let encoded ← (simulateQ randomOracle
    (Concrete.encodingHash keyView.secretKey.parameter request.epoch
      request.message randomness)).run state.cache
  let encodedState := { state with cache := encoded.2 }
  match TargetSum.decodeDigest encoded.1 with
  | none => pure ((none, encodedState), [])
  | some encoding => do
      let materialized ← filteredLazyMaterializeSuffix table
        keyView.secretKey.parameter selected request.epoch
          (encoding selected) encodedState
      let signature := replaceSignatureChainValue
        (Concrete.CacheReplay.signWithEncoding keyView.cache keyView.secretKey
          request.epoch randomness encoding) selected materialized.1.1
      pure ((some signature, materialized.1.2), materialized.2)

set_option maxRecDepth 100000 in
theorem simulate_eagerTrace_filteredDirectSigningQuery
    (table : ChainValueIndex → Digest)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (state : CausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (filteredDirectSigningQuery keyView selected request state)).run =
        filteredLazyDirectSigningQuery table keyView selected request state := by
  unfold filteredDirectSigningQuery filteredLazyDirectSigningQuery
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, List.nil_append]
  apply bind_congr
  intro randomness
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, List.nil_append]
  apply bind_congr
  intro encoded
  cases hdecode : TargetSum.decodeDigest encoded.1 with
  | none => simp
  | some encoding =>
      simp only
      rw [simulateQ_bind, WriterT.run_bind',
        simulate_eagerTrace_filteredCausalMaterializeSuffix]
      simp [map_eq_bind_pure_comp, bind_assoc]

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
