import XmssSecurity.Proof.PostKeygenLoss

open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

namespace XmssSecurity.FirstLaneOracleSimulation

variable {Index : Type}

def encodingQueryCount : ActionTrace Index → Nat
  | [] => 0
  | .encoding (.query _ _) :: rest => (encodingQueryCount rest).succ
  | _ :: rest => encodingQueryCount rest

theorem encodingQueryCount_le_hazardCount (trace : ActionTrace Index) :
    encodingQueryCount trace ≤ hazardCount trace := by
  induction trace with
  | nil => rfl
  | cons action trace ih =>
      cases action with
      | encoding action =>
          cases action <;> simp [encodingQueryCount, hazardCount, ih]
      | chain action =>
          cases action <;> simp [encodingQueryCount, hazardCount, ih] <;> omega

theorem encodingQueryCount_eq_zero_of_encodingActions_eq_nil
    {trace : ActionTrace Index} (htrace : trace.encodingActions = []) :
    encodingQueryCount trace = 0 := by
  induction trace with
  | nil => rfl
  | cons action trace ih =>
      cases action with
      | encoding action =>
          cases action <;>
            simp [ActionTrace.encodingActions] at htrace
      | chain action =>
          change FirstLaneOracleSimulation.ActionTrace.encodingActions trace = [] at htrace
          exact ih htrace

theorem hazardCount_eq_counts (trace : ActionTrace Index) :
    hazardCount trace = encodingQueryCount trace +
      RevealProbeOracleSimulation.observedProbeCount trace.chainActions := by
  induction trace with
  | nil => rfl
  | cons action trace ih =>
      cases action with
      | encoding action =>
          cases action <;> simp [hazardCount, encodingQueryCount,
            ActionTrace.chainActions, ih] <;> omega
      | chain action =>
          cases action <;> simp [hazardCount, encodingQueryCount,
            ActionTrace.chainActions,
            RevealProbeOracleSimulation.observedProbeCount, ih] <;> omega

end XmssSecurity.FirstLaneOracleSimulation

namespace XmssSecurity.CappedChain

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000000

theorem length_filter_finRange_eq_card_filter {n : Nat}
    (predicate : Fin n → Bool) :
    ((List.ofFn fun index : Fin n => index).filter predicate).length =
      (Finset.univ.filter fun index : Fin n => predicate index).card := by
  induction n with
  | zero => simp
  | succ n ih =>
      have htail : List.ofFn (fun index : Fin n => index.succ) =
          List.map Fin.succ (List.ofFn fun index : Fin n => index) := by
        rw [List.map_ofFn]
        rfl
      rw [List.ofFn_succ, List.filter_cons, Finset.card_filter,
        Fin.sum_univ_succ]
      split
      · simp only [List.length_cons]
        rw [htail, List.filter_map, List.length_map]
        rw [ih (predicate ∘ Fin.succ)]
        rw [Finset.card_filter]
        simp only [Function.comp_apply]
        change (∑ index : Fin n,
            if predicate index.succ = true then 1 else 0) + 1 =
          1 + ∑ index : Fin n,
            if predicate index.succ = true then 1 else 0
        omega
      · rw [htail, List.filter_map, List.length_map]
        rw [ih (predicate ∘ Fin.succ)]
        rw [Finset.card_filter]
        simp only [Function.comp_apply, Nat.zero_add]
        change (∑ index : Fin n,
            if predicate index.succ = true then 1 else 0) =
          ∑ index : Fin n,
            if predicate index.succ = true then 1 else 0
        rfl

theorem length_filter_ofFn_eq_card_filter {n : Nat}
    (values : Fin n → α) (predicate : α → Bool) :
    ((List.ofFn values).filter predicate).length =
      (Finset.univ.filter fun index : Fin n => predicate (values index)).card := by
  have hvalues : List.ofFn values =
      List.map values (List.ofFn fun index : Fin n => index) := by
    rw [List.map_ofFn]
    rfl
  rw [hvalues, List.filter_map, List.length_map]
  exact length_filter_finRange_eq_card_filter (predicate ∘ values)

theorem isQueryBoundP_map
    {spec : OracleSpec index} {predicate : spec.Domain → Prop}
    [DecidablePred predicate] {computation : OracleComp spec α}
    (hbound : computation.IsQueryBoundP predicate bound) (f : α → β) :
    (f <$> computation).IsQueryBoundP predicate bound := by
  rw [map_eq_bind_pure_comp]
  exact OracleComp.isQueryBoundP_bind (n := bound) (m := 0) hbound
    (fun value _ => OracleComp.isQueryBoundP_pure
      (spec := spec) (p := predicate) (f value) 0)

def IsVerifierHazardHashQuery (input : HashInput) : Prop :=
  ¬∃ parameter level node left right,
    input = Concrete.CacheView.merkleInput parameter level node left right

noncomputable instance :
    DecidablePred IsVerifierHazardHashQuery :=
  Classical.decPred _

noncomputable local instance : DecidableEq
    (FirstLaneOracleSimulation.ObservedAction GlobalChainValueIndex) :=
  Classical.decEq _

@[simp]
theorem IsVerifierHazardHashQuery_merkleInput
    (parameter : PublicParameter) (level : MerkleLevel) (node : MerkleNode)
    (left right : Digest) :
    ¬IsVerifierHazardHashQuery
      (Concrete.CacheView.merkleInput parameter level node left right) := by
  intro hnonmerkle
  exact hnonmerkle ⟨parameter, level, node, left, right, rfl⟩

theorem Concrete.authenticationNodeHash_hazardQueryBound_zero
    (parameter : PublicParameter) (epoch : Epoch) (signature : Signature)
    (level : Nat) (current : Digest) (hlevel : level < treeHeight) :
    (Concrete.authenticationNodeHash (m := OracleComp HashSpec) parameter epoch
      level current (Concrete.signaturePath signature level)).IsQueryBoundP
        IsVerifierHazardHashQuery 0 := by
  unfold Concrete.authenticationNodeHash
  simp only [hlevel, ↓reduceDIte]
  split
  · change ((liftM (HashSpec.query (Concrete.CacheView.merkleInput parameter
        ⟨level, hlevel⟩ (Concrete.CacheView.nodeIndex epoch level)
        (Concrete.signaturePath signature level) current)) :
          OracleComp HashSpec HashOutput) >>= fun output =>
      pure (truncateHash output)).IsQueryBoundP IsVerifierHazardHashQuery 0
    rw [OracleComp.isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (fun hhazard => hhazard ⟨parameter, ⟨level, hlevel⟩,
      Concrete.CacheView.nodeIndex epoch level,
      Concrete.signaturePath signature level, current, rfl⟩),
      fun output => OracleComp.isQueryBoundP_pure
        (spec := HashSpec) (p := IsVerifierHazardHashQuery)
        (truncateHash output) 0⟩
  · change ((liftM (HashSpec.query (Concrete.CacheView.merkleInput parameter
        ⟨level, hlevel⟩ (Concrete.CacheView.nodeIndex epoch level)
        current (Concrete.signaturePath signature level))) :
          OracleComp HashSpec HashOutput) >>= fun output =>
      pure (truncateHash output)).IsQueryBoundP IsVerifierHazardHashQuery 0
    rw [OracleComp.isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (fun hhazard => hhazard ⟨parameter, ⟨level, hlevel⟩,
      Concrete.CacheView.nodeIndex epoch level, current,
      Concrete.signaturePath signature level, rfl⟩),
      fun output => OracleComp.isQueryBoundP_pure
        (spec := HashSpec) (p := IsVerifierHazardHashQuery)
        (truncateHash output) 0⟩

theorem Concrete.authenticationRoot_hazardQueryBound_zero
    (parameter : PublicParameter) (epoch : Epoch) (signature : Signature)
    (levels : Nat) (leaf : Digest) (hlevels : levels ≤ treeHeight) :
    (Concrete.authenticationRoot (m := OracleComp HashSpec) parameter epoch
      signature levels leaf).IsQueryBoundP
        IsVerifierHazardHashQuery 0 := by
  induction levels generalizing leaf with
  | zero => trivial
  | succ levels ih =>
      rw [Concrete.authenticationRoot]
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (ih leaf (by omega))
      intro current _
      exact Concrete.authenticationNodeHash_hazardQueryBound_zero parameter
        epoch signature levels current (by omega)

attribute [local irreducible] Concrete.authenticationRoot

theorem Concrete.verifyAfterLeaf_hazardQueryBound_zero
    (publicKey : PublicKey) (epoch : Epoch) (signature : Signature)
    (leaf : Digest) :
    (Concrete.verifyAfterLeaf (m := OracleComp HashSpec) publicKey epoch
      signature leaf).IsQueryBoundP IsVerifierHazardHashQuery 0 := by
  unfold Concrete.verifyAfterLeaf
  have hroot :
      (Concrete.authenticationRoot (m := OracleComp HashSpec)
        publicKey.parameter epoch signature treeHeight leaf).IsQueryBoundP
          IsVerifierHazardHashQuery 0 :=
    Concrete.authenticationRoot_hazardQueryBound_zero publicKey.parameter
      epoch signature treeHeight leaf (Nat.le_refl _)
  exact OracleComp.isQueryBoundP_bind (n := 0) (m := 0) hroot
    (fun root _ => OracleComp.isQueryBoundP_pure
      (spec := HashSpec) (p := IsVerifierHazardHashQuery)
      (decide (root = publicKey.root)) 0)

theorem Concrete.verify_hazardQueryBound
    (publicKey : PublicKey) (epoch : Epoch) (message : Message)
    (signature : Signature) :
    (Concrete.verify (m := OracleComp HashSpec) publicKey epoch message signature)
      |>.IsQueryBoundP IsVerifierHazardHashQuery
        (verificationChainHashes + 2) := by
  unfold Concrete.verify
  apply OracleComp.isQueryBoundP_bind (n := 1)
    (m := verificationChainHashes + 1)
  · exact (ExactQueryCount.tweakableHash publicKey.parameter (.encoding epoch)
      (Concrete.encodingPayload message signature.randomness)).isTotalQueryBound_self.isQueryBoundP
  intro digest _
  cases hdecode : TargetSum.decodeDigest digest with
  | none => simp [hdecode]
  | some encoding =>
      have hvalid : TargetSum.Valid encoding :=
        (TargetSum.decodeDigest_eq_some_iff.mp hdecode).2
      apply OracleComp.isQueryBoundP_bind (n := verificationChainHashes)
        (m := 1)
      · have hrecover := ExactQueryCount.recoverEndpoints publicKey.parameter
          epoch encoding signature
        rw [TargetSum.verificationWork_eq encoding hvalid] at hrecover
        exact hrecover.isTotalQueryBound_self.isQueryBoundP
      intro endpoints _
      apply OracleComp.isQueryBoundP_bind (n := 1) (m := 0)
      · exact (ExactQueryCount.tweakableHash publicKey.parameter (.leaf epoch)
          (Concrete.leafPayload endpoints)).isTotalQueryBound_self.isQueryBoundP
      intro leaf _
      exact Concrete.verifyAfterLeaf_hazardQueryBound_zero publicKey epoch
        signature leaf

def IsVerifierHazardOracleQuery : OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr input => IsVerifierHazardHashQuery input

noncomputable instance :
    DecidablePred IsVerifierHazardOracleQuery :=
  Classical.decPred _

theorem Concrete.scheme_verify_hazardQueryBound
    (publicKey : PublicKey) (epoch : Epoch) (message : Message)
    (signature : Signature) :
    (Concrete.scheme.verify publicKey epoch message signature).IsQueryBoundP
      IsVerifierHazardOracleQuery
      (verificationChainHashes + 2) := by
  unfold Concrete.scheme
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (p := IsVerifierHazardHashQuery)
    (q := IsVerifierHazardOracleQuery)
    (fun input => by rfl)
    (Concrete.verify_hazardQueryBound publicKey epoch message signature)

theorem Concrete.verify_totalHashQueryBound
    (publicKey : PublicKey) (epoch : Epoch) (message : Message)
    (signature : Signature) :
    (Concrete.verify (m := OracleComp HashSpec) publicKey epoch message signature)
      |>.IsTotalQueryBound (verificationChainHashes + 2 + treeHeight) := by
  unfold Concrete.verify
  have hencoding : ExactQueryCount
      (Concrete.encodingHash publicKey.parameter epoch message
        signature.randomness : OracleComp HashSpec Digest) 1 := by
    unfold Concrete.encodingHash
    exact (ExactQueryCount.tweakableHash publicKey.parameter (.encoding epoch)
      (Concrete.encodingPayload message signature.randomness))
  refine OracleComp.isTotalQueryBound_bind (n₁ := 1)
    (n₂ := verificationChainHashes + 1 + treeHeight)
      hencoding.isTotalQueryBound_self ?_
  intro digest
  cases hdecode : TargetSum.decodeDigest digest with
  | none => simp [hdecode, OracleComp.IsTotalQueryBound]
  | some encoding =>
      have hvalid : TargetSum.Valid encoding :=
        (TargetSum.decodeDigest_eq_some_iff.mp hdecode).2
      have hrecover := ExactQueryCount.recoverEndpoints publicKey.parameter
        epoch encoding signature
      rw [TargetSum.verificationWork_eq encoding hvalid] at hrecover
      refine OracleComp.isTotalQueryBound_bind (n₁ := verificationChainHashes)
        (n₂ := 1 + treeHeight) hrecover.isTotalQueryBound_self ?_
      intro endpoints
      exact ((ExactQueryCount.tweakableHash publicKey.parameter (.leaf epoch)
        (Concrete.leafPayload endpoints)).bind _ treeHeight fun leaf =>
          ExactQueryCount.verifyAfterLeaf publicKey epoch signature leaf
        ).isTotalQueryBound_self

def IsHashOracleQuery : OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr _ => True

noncomputable instance : DecidablePred IsHashOracleQuery := Classical.decPred _

theorem Concrete.scheme_verify_totalHashQueryBound
    (publicKey : PublicKey) (epoch : Epoch) (message : Message)
    (signature : Signature) :
    (Concrete.scheme.verify publicKey epoch message signature).IsQueryBoundP
      IsHashOracleQuery
      (verificationChainHashes + 2 + treeHeight) := by
  unfold Concrete.scheme
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (p := fun _ : HashInput => True)
    (q := IsHashOracleQuery)
    (fun input => by rfl)
    (by simpa [OracleComp.IsTotalQueryBound, OracleComp.IsQueryBoundP] using
      Concrete.verify_totalHashQueryBound publicKey epoch message signature)

theorem domain_eq_of_tweakableHashInput_eq_any
    {leftParameter rightParameter : PublicParameter}
    {leftDomain rightDomain : HashDomain}
    {leftMessage rightMessage : HashInput}
    (heq : tweakableHashInput leftParameter leftDomain leftMessage =
      tweakableHashInput rightParameter rightDomain rightMessage) :
    leftDomain = rightDomain := by
  apply tweakBytes_injective
  have hpref := congrArg (List.take 16) heq
  simpa [tweakableHashInput, tweakBytes] using hpref

@[simp]
theorem encodingInputEpoch?_merkleInput
    (hashParameter parameter : PublicParameter)
    (level : MerkleLevel) (node : MerkleNode)
    (left right : Digest) :
    encodingInputEpoch? hashParameter
      (Concrete.CacheView.merkleInput parameter level node left right) = none := by
  unfold encodingInputEpoch?
  split
  · rename_i hexists
    obtain ⟨epoch, payload, heq⟩ := hexists
    have hdomain := domain_eq_of_tweakableHashInput_eq_any heq
    cases hdomain
  · rfl

@[simp]
theorem globalChainInputProbe?_merkleInput
    (hashParameter parameter : PublicParameter)
    (level : MerkleLevel) (node : MerkleNode)
    (left right : Digest) :
    globalChainInputProbe? hashParameter
      (Concrete.CacheView.merkleInput parameter level node left right) = none := by
  unfold globalChainInputProbe?
  split
  · rename_i hexists
    obtain ⟨data, heq⟩ := hexists
    have hdomain := domain_eq_of_tweakableHashInput_eq_any heq
    cases hdomain
  · rfl

@[simp]
theorem globalLeafInputData?_merkleInput
    (hashParameter parameter : PublicParameter)
    (level : MerkleLevel) (node : MerkleNode)
    (left right : Digest) :
    globalLeafInputData? hashParameter
      (Concrete.CacheView.merkleInput parameter level node left right) = none := by
  unfold globalLeafInputData?
  split
  · rename_i hexists
    obtain ⟨data, heq⟩ := hexists
    have hdomain := domain_eq_of_tweakableHashInput_eq_any heq.symm
    cases hdomain
  · rfl

theorem globalFirstLaneAttackerHashQueryFromHigh_merkle_hazardBound_zero
    (high : GlobalChainValueIndex → Digest) (secretKey : SecretKey)
    (parameter : PublicParameter)
    (level : MerkleLevel) (node : MerkleNode) (left right : Digest)
    (state : GlobalCausalHashState) :
    (globalFirstLaneAttackerHashQueryFromHighRun high secretKey
      (Concrete.CacheView.merkleInput parameter level node left right)
      state).IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery 0 := by
  rw [globalFirstLaneAttackerHashQueryFromHighRun_eq_none high secretKey _ state
    (encodingInputEpoch?_merkleInput secretKey.parameter parameter level node left right)]
  apply globalFirstLaneLiftRevealProbe_hazardBound _ 0
  apply globalCausalAttackerHashQueryFromHigh_irrelevant_isProbeQueryBoundP
  simp [GlobalChainProbeRelevantInput]

theorem globalFirstLaneExactTracedVerifierImpl_hazardBound_of_base
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : OracleWorld.Domain) (state : GlobalFirstLaneExactTracedState)
    (fuel : Nat)
    (hbase : ((globalFirstLaneVerifierImpl keyView edgeHigh input).run
      state.causalState).IsQueryBoundP
        FirstLaneOracleSimulation.IsHazardQuery fuel) :
    ((globalFirstLaneExactTracedVerifierImpl keyView edgeHigh input).run state)
      |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery fuel := by
  rw [globalFirstLaneExactTracedVerifierImpl_run_eq_map,
    map_eq_bind_pure_comp]
  apply OracleComp.isQueryBoundP_bind (n := fuel) (m := 0) hbase
  intro result _
  exact OracleComp.isQueryBoundP_pure
    (p := FirstLaneOracleSimulation.IsHazardQuery) _ 0

theorem globalFirstLaneExactTracedVerifierImpl_uniform_hazardBound_sharp
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (n : Nat) (state : GlobalFirstLaneExactTracedState) :
    ((globalFirstLaneExactTracedVerifierImpl keyView edgeHigh (.inl n)).run state)
      |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery
        0 := by
  exact globalFirstLaneExactTracedVerifierImpl_hazardBound keyView edgeHigh
    (.inl n) state

theorem globalFirstLaneVerifier_eq_hashComputation
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp HashSpec α) :
    simulateQ (globalFirstLaneVerifierImpl keyView edgeHigh)
        (OracleComp.liftComp computation OracleWorld) =
      simulateQ (fun input => StateT.mk
        (globalFirstLaneVerifierHashExecution keyView edgeHigh input))
        computation := by
  trans simulateQ (globalFirstLaneHashImpl keyView edgeHigh) computation
  · apply QueryImpl.simulateQ_liftComp_right_eq_of_apply
    intro input
    exact globalFirstLaneVerifierImpl_hash keyView edgeHigh input
  · congr 1
    funext input
    unfold globalFirstLaneVerifierHashExecution
    rfl

theorem globalFirstLaneVerificationHash_step_hazardCount_one
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : HashInput) (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneVerifierHashExecution keyView edgeHigh input
          state)).run)) :
    FirstLaneOracleSimulation.hazardCount result.2 ≤ 1 := by
  apply FirstLaneOracleSimulation.simulate_eagerTrace_support_hazardCount_le
    table _ 1 _ result hresult
  unfold globalFirstLaneVerifierHashExecution
  exact globalFirstLaneAttackerHashQueryFromHigh_hazardBound
    (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey input
      state

theorem globalFirstLaneAttackerHashQueryFromHigh_merkle_hazardCount_zero
    (table high : GlobalChainValueIndex → Digest) (secretKey : SecretKey)
    (parameter : PublicParameter) (level : MerkleLevel) (node : MerkleNode)
    (left right : Digest) (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneAttackerHashQueryFromHighRun high secretKey
          (Concrete.CacheView.merkleInput parameter level node left right)
            state)).run)) :
    FirstLaneOracleSimulation.hazardCount result.2 ≤ 0 := by
  apply FirstLaneOracleSimulation.simulate_eagerTrace_support_hazardCount_le
    table _ 0 _ result hresult
  exact globalFirstLaneAttackerHashQueryFromHigh_merkle_hazardBound_zero high
    secretKey parameter level node left right state

theorem globalFirstLaneVerificationHash_merkle_hazardCount_zero
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (parameter : PublicParameter) (level : MerkleLevel) (node : MerkleNode)
    (left right : Digest) (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneVerifierHashExecution keyView edgeHigh
          (Concrete.CacheView.merkleInput parameter level node left right)
            state)).run)) :
    FirstLaneOracleSimulation.hazardCount result.2 ≤ 0 := by
  unfold globalFirstLaneVerifierHashExecution at hresult
  change result ∈ support
    ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (globalFirstLaneAttackerHashQueryFromHighRun
        (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey
          (Concrete.CacheView.merkleInput parameter level node left right)
            state)).run) at hresult
  exact globalFirstLaneAttackerHashQueryFromHigh_merkle_hazardCount_zero table
    (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey parameter level
      node left right state result hresult

theorem globalFirstLaneVerificationHash_step_hazardCount_sharp
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : HashInput) (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneVerifierHashExecution keyView edgeHigh input
          state)).run)) :
    FirstLaneOracleSimulation.hazardCount result.2 ≤
      if IsVerifierHazardHashQuery input then 1 else 0 := by
  by_cases hhazard : IsVerifierHazardHashQuery input
  · simpa [hhazard] using globalFirstLaneVerificationHash_step_hazardCount_one
      table keyView edgeHigh input state result hresult
  · obtain ⟨parameter, level, node, left, right, rfl⟩ := not_not.mp hhazard
    simpa only [IsVerifierHazardHashQuery_merkleInput, if_false] using
      globalFirstLaneVerificationHash_merkle_hazardCount_zero table keyView
        edgeHigh parameter level node left right state result hresult

theorem simulateQ_eagerTrace_hazardCount_le_of_queryBound
    {spec : OracleSpec index} {predicate : spec.Domain → Prop}
    [DecidablePred predicate]
    (table : GlobalChainValueIndex → Digest)
    (impl : QueryImpl spec
      (StateT State (OracleComp GlobalFirstLaneWorld)))
    (hstep : ∀ (input : spec.Domain) (state : State)
      (result : (spec.Range input × State) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex),
      result ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          ((impl input).run state)).run) →
      FirstLaneOracleSimulation.hazardCount result.2 ≤
        if predicate input then 1 else 0)
    (computation : OracleComp spec α)
    (hbound : computation.IsQueryBoundP predicate bound)
    (state : State)
    (result : (α × State) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ impl computation).run state)).run)) :
    FirstLaneOracleSimulation.hazardCount result.2 ≤ bound := by
  induction computation using OracleComp.inductionOn generalizing
      bound state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      simp [FirstLaneOracleSimulation.hazardCount]
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [simulateQ_bind, StateT.run_bind, simulateQ_bind,
        WriterT.run_bind', mem_support_bind_iff] at hresult
      obtain ⟨⟨⟨output, middleState⟩, firstTrace⟩, hfirst,
        hrestMapped⟩ := hresult
      rw [support_map] at hrestMapped
      obtain ⟨restResult, hrest, heq⟩ := hrestMapped
      rw [simulateQ_spec_query] at hfirst
      have hfirstBound := hstep input state
        ((output, middleState), firstTrace) hfirst
      have hrestBound := ih output (hbound.2 output) middleState restResult hrest
      have htrace : firstTrace ++ restResult.2 = result.2 := by
        simpa using congrArg Prod.snd heq
      rw [← htrace, FirstLaneOracleSimulation.hazardCount_append]
      have hpositive := hbound.1
      by_cases hp : predicate input <;>
        simp [hp] at hpositive hfirstBound hrestBound ⊢ <;> omega

theorem globalFirstLaneExactTracedVerifier_verify_hazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (epoch : Epoch) (message : Message) (signature : Signature)
    (state : GlobalFirstLaneExactTracedState) :
    ((simulateQ (globalFirstLaneExactTracedVerifierImpl keyView edgeHigh)
      (Concrete.scheme.verify keyView.publicKey epoch message signature)).run state)
        |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery
          (verificationChainHashes + 2 + treeHeight) := by
  apply OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step
    (Concrete.scheme_verify_totalHashQueryBound keyView.publicKey epoch message
      signature)
    (fun input state => by
      cases input with
      | inl n =>
          simpa [IsHashOracleQuery] using
            globalFirstLaneExactTracedVerifierImpl_hazardBound keyView edgeHigh
              (.inl n) state
      | inr input =>
          simpa [IsHashOracleQuery] using
            globalFirstLaneExactTracedVerifierImpl_hazardBound keyView edgeHigh
              (.inr input) state)
    state

theorem globalFirstLaneExactTracedMappedAdversary_step_encodingQueryCount
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : GlobalFirstLaneExactTracedState)
    (result : ((OracleWorld + SigningSpec).Range input ×
      GlobalFirstLaneExactTracedState) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh input
          ).run initialState)).run)) :
    initialState.attackerTrace.hashInputs.length +
        FirstLaneOracleSimulation.encodingQueryCount result.2 ≤
      result.1.2.attackerTrace.hashInputs.length := by
  have hcount : FirstLaneOracleSimulation.encodingQueryCount result.2 ≤
      directHashActionCost input := by
    apply (FirstLaneOracleSimulation.encodingQueryCount_le_hazardCount
      result.2).trans
    apply FirstLaneOracleSimulation.simulate_eagerTrace_support_hazardCount_le
      table
      ((globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh input
        ).run initialState)
      (directHashActionCost input)
      (globalFirstLaneExactTracedMappedAdversaryImpl_hazardBound keyView
        edgeHigh input initialState) result hresult
  have htrace : result.1.2.attackerTrace =
      initialState.attackerTrace ++ attackerActionFragment input result.1.1 := by
    rcases input with (worldInput | request)
    · rcases worldInput with uniformInput | hashInput
      · unfold globalFirstLaneExactTracedMappedAdversaryImpl
          globalFirstLaneExactTracedOracleImpl at hresult
        obtain ⟨baseResult, _hbase, heq⟩ :=
          globalFirstLaneExactTracedLift_eager_support_decompose table keyView
            (.inl (.inl uniformInput))
            (StateT.mk fun causalState =>
              globalFirstLaneOracleExecution keyView edgeHigh
                (.inl uniformInput) causalState)
            initialState result hresult
        rw [heq]
        unfold globalExactTracedNextState
        rfl
      · unfold globalFirstLaneExactTracedMappedAdversaryImpl
          globalFirstLaneExactTracedOracleImpl at hresult
        obtain ⟨baseResult, _hbase, heq⟩ :=
          globalFirstLaneExactTracedLift_eager_support_decompose table keyView
            (.inl (.inr hashInput))
            (StateT.mk fun causalState =>
              globalFirstLaneOracleExecution keyView edgeHigh
                (.inr hashInput) causalState)
            initialState result hresult
        rw [heq]
        unfold globalExactTracedNextState
        rfl
    · unfold globalFirstLaneExactTracedMappedAdversaryImpl
        globalFirstLaneExactTracedSigningImpl at hresult
      obtain ⟨baseResult, _hbase, heq⟩ :=
        globalFirstLaneExactTracedLift_eager_support_decompose table keyView
          (.inr request) (globalFirstLaneSigningImpl keyView request)
          initialState result hresult
      rw [heq]
      unfold globalExactTracedNextState
      rfl
  rw [htrace, AttackerActionTrace.hashInputs_append,
    List.length_append, attackerActionFragment_hashInputs_length]
  omega

theorem globalFirstLaneExactTracedMappedAdversary_step_hazardCount
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : GlobalFirstLaneExactTracedState)
    (result : ((OracleWorld + SigningSpec).Range input ×
      GlobalFirstLaneExactTracedState) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh input
          ).run initialState)).run)) :
    initialState.attackerTrace.hashInputs.length +
        FirstLaneOracleSimulation.hazardCount result.2 ≤
      result.1.2.attackerTrace.hashInputs.length := by
  have hcount : FirstLaneOracleSimulation.hazardCount result.2 ≤
      directHashActionCost input := by
    apply FirstLaneOracleSimulation.simulate_eagerTrace_support_hazardCount_le
      table
      ((globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh input
        ).run initialState)
      (directHashActionCost input)
      (globalFirstLaneExactTracedMappedAdversaryImpl_hazardBound keyView
        edgeHigh input initialState) result hresult
  have htrace : result.1.2.attackerTrace =
      initialState.attackerTrace ++ attackerActionFragment input result.1.1 := by
    rcases input with (worldInput | request)
    · rcases worldInput with uniformInput | hashInput
      · unfold globalFirstLaneExactTracedMappedAdversaryImpl
          globalFirstLaneExactTracedOracleImpl at hresult
        obtain ⟨baseResult, _hbase, heq⟩ :=
          globalFirstLaneExactTracedLift_eager_support_decompose table keyView
            (.inl (.inl uniformInput))
            (StateT.mk fun causalState =>
              globalFirstLaneOracleExecution keyView edgeHigh
                (.inl uniformInput) causalState)
            initialState result hresult
        rw [heq]
        unfold globalExactTracedNextState
        rfl
      · unfold globalFirstLaneExactTracedMappedAdversaryImpl
          globalFirstLaneExactTracedOracleImpl at hresult
        obtain ⟨baseResult, _hbase, heq⟩ :=
          globalFirstLaneExactTracedLift_eager_support_decompose table keyView
            (.inl (.inr hashInput))
            (StateT.mk fun causalState =>
              globalFirstLaneOracleExecution keyView edgeHigh
                (.inr hashInput) causalState)
            initialState result hresult
        rw [heq]
        unfold globalExactTracedNextState
        rfl
    · unfold globalFirstLaneExactTracedMappedAdversaryImpl
        globalFirstLaneExactTracedSigningImpl at hresult
      obtain ⟨baseResult, _hbase, heq⟩ :=
        globalFirstLaneExactTracedLift_eager_support_decompose table keyView
          (.inr request) (globalFirstLaneSigningImpl keyView request)
          initialState result hresult
      rw [heq]
      unfold globalExactTracedNextState
      rfl
  rw [htrace, AttackerActionTrace.hashInputs_append,
    List.length_append, attackerActionFragment_hashInputs_length]
  omega

theorem globalFirstLaneExactTracedMappedAdversary_hazardCount
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : GlobalFirstLaneExactTracedState)
    (result : (α × GlobalFirstLaneExactTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ
          (globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh)
            computation).run initialState)).run)) :
    initialState.attackerTrace.hashInputs.length +
        FirstLaneOracleSimulation.hazardCount result.2 ≤
      result.1.2.attackerTrace.hashInputs.length := by
  induction computation using OracleComp.inductionOn generalizing
      initialState result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      simp [FirstLaneOracleSimulation.hazardCount]
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_bind,
        WriterT.run_bind', mem_support_bind_iff] at hresult
      obtain ⟨⟨⟨output, middleState⟩, firstTrace⟩, hfirst,
        hrestMapped⟩ := hresult
      rw [support_map] at hrestMapped
      obtain ⟨restResult, hrest, heq⟩ := hrestMapped
      rw [simulateQ_spec_query] at hfirst
      have hhead := globalFirstLaneExactTracedMappedAdversary_step_hazardCount
        table keyView edgeHigh input initialState
          ((output, middleState), firstTrace) hfirst
      have htail := ih output middleState restResult hrest
      change initialState.attackerTrace.hashInputs.length +
        FirstLaneOracleSimulation.hazardCount firstTrace ≤
          middleState.attackerTrace.hashInputs.length at hhead
      change middleState.attackerTrace.hashInputs.length +
        FirstLaneOracleSimulation.hazardCount restResult.2 ≤
          restResult.1.2.attackerTrace.hashInputs.length at htail
      have hstate : restResult.1.2.attackerTrace =
          result.1.2.attackerTrace := by
        simpa using congrArg (fun candidate => candidate.1.2.attackerTrace) heq
      have htrace : firstTrace ++ restResult.2 = result.2 := by
        simpa using congrArg Prod.snd heq
      rw [← hstate, ← htrace, FirstLaneOracleSimulation.hazardCount_append]
      omega

theorem globalFirstLaneExactTracedVerifier_verify_hazardCount
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (epoch : Epoch) (message : Message) (signature : Signature)
    (initialState : GlobalFirstLaneExactTracedState)
    (result : (Bool × GlobalFirstLaneExactTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (globalFirstLaneExactTracedVerifierImpl keyView edgeHigh)
          (Concrete.scheme.verify keyView.publicKey epoch message signature)).run
            initialState)).run)) :
    FirstLaneOracleSimulation.hazardCount result.2 ≤
      verificationChainHashes + 2 + treeHeight := by
  exact FirstLaneOracleSimulation.simulate_eagerTrace_support_hazardCount_le
    table _ _
      (globalFirstLaneExactTracedVerifier_verify_hazardBound keyView edgeHigh
        epoch message signature initialState) result hresult

@[simp]
theorem encodingInputEpoch?_chainInput
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) :
    encodingInputEpoch? parameter
      (Concrete.CacheView.chainInput parameter epoch chain step value) = none := by
  unfold encodingInputEpoch?
  split
  · rename_i hexists
    obtain ⟨candidateEpoch, payload, heq⟩ := hexists
    have hdomain := domain_eq_of_tweakableHashInput_eq parameter heq
    cases hdomain
  · rfl

theorem chainAction_mem_chainActions
    {trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex}
    {action : RevealProbeOracleSimulation.ObservedAction GlobalChainValueIndex}
    (hmem : (.chain action :
      FirstLaneOracleSimulation.ObservedAction GlobalChainValueIndex) ∈ trace) :
    action ∈ trace.chainActions := by
  exact List.mem_filterMap.mpr ⟨_, hmem, rfl⟩

theorem chainAction_mem_of_mem_chainActions
    {trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex}
    {action : RevealProbeOracleSimulation.ObservedAction GlobalChainValueIndex}
    (hmem : action ∈ trace.chainActions) :
    (.chain action :
      FirstLaneOracleSimulation.ObservedAction GlobalChainValueIndex) ∈ trace := by
  obtain ⟨candidate, hcandidate, hfiltered⟩ := List.mem_filterMap.mp hmem
  cases candidate with
  | encoding action => simp at hfiltered
  | chain observed =>
      simp only at hfiltered
      cases hfiltered
      exact hcandidate

theorem hazard_add_missing_le_one_of_no_chain_actions
    (trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (action : RevealProbeOracleSimulation.ObservedAction GlobalChainValueIndex)
    (hencoding : trace.encodingActions = [])
    (hchain : trace.chainActions = []) :
    FirstLaneOracleSimulation.hazardCount trace +
        (if (.chain action :
          FirstLaneOracleSimulation.ObservedAction GlobalChainValueIndex) ∈
            trace then 0 else 1) ≤ 1 := by
  have hnot : (.chain action :
      FirstLaneOracleSimulation.ObservedAction GlobalChainValueIndex) ∉ trace := by
    intro hmem
    have := chainAction_mem_chainActions hmem
    simp [hchain] at this
  rw [FirstLaneOracleSimulation.hazardCount_eq_counts,
    FirstLaneOracleSimulation.encodingQueryCount_eq_zero_of_encodingActions_eq_nil
      hencoding,
    hchain]
  simp [hnot, RevealProbeOracleSimulation.observedProbeCount]

theorem hazard_add_missing_le_one_of_single_reveal
    (trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (probeIndex index : GlobalChainValueIndex) (target value : Digest)
    (hencoding : trace.encodingActions = [])
    (hchain : trace.chainActions = [.reveal index value]) :
    FirstLaneOracleSimulation.hazardCount trace +
        (if (.chain (.probe probeIndex target) :
          FirstLaneOracleSimulation.ObservedAction GlobalChainValueIndex) ∈
            trace then 0 else 1) ≤ 1 := by
  have hnot : (.chain (.probe probeIndex target) :
      FirstLaneOracleSimulation.ObservedAction GlobalChainValueIndex) ∉ trace := by
    intro hmem
    have := chainAction_mem_chainActions hmem
    rw [hchain] at this
    simp at this
  rw [FirstLaneOracleSimulation.hazardCount_eq_counts,
    FirstLaneOracleSimulation.encodingQueryCount_eq_zero_of_encodingActions_eq_nil
      hencoding,
    hchain]
  simp [hnot, RevealProbeOracleSimulation.observedProbeCount]

theorem hazard_add_missing_le_one_of_single_probe
    (trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (index : GlobalChainValueIndex) (value : Digest)
    (hencoding : trace.encodingActions = [])
    (hchain : trace.chainActions = [.probe index value]) :
    FirstLaneOracleSimulation.hazardCount trace +
        (if (.chain (.probe index value) :
          FirstLaneOracleSimulation.ObservedAction GlobalChainValueIndex) ∈
            trace then 0 else 1) ≤ 1 := by
  have hmem : (.chain (.probe index value) :
      FirstLaneOracleSimulation.ObservedAction GlobalChainValueIndex) ∈ trace := by
    apply chainAction_mem_of_mem_chainActions
    simp [hchain]
  rw [FirstLaneOracleSimulation.hazardCount_eq_counts,
    FirstLaneOracleSimulation.encodingQueryCount_eq_zero_of_encodingActions_eq_nil
      hencoding,
    hchain]
  simp [hmem, RevealProbeOracleSimulation.observedProbeCount]

theorem globalFirstLane_chainQuery_hazard_add_missing_le_one
    (table high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (epoch : Epoch) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneAttackerHashQueryFromHighRun high secretKey
          (Concrete.CacheView.chainInput secretKey.parameter epoch chain step value)
            state)).run)) :
    FirstLaneOracleSimulation.hazardCount result.2 +
        (if (.chain (.probe (chain, epoch, chainStepDigit step) value) :
          FirstLaneOracleSimulation.ObservedAction GlobalChainValueIndex) ∈
            result.2 then 0 else 1) ≤ 1 := by
  classical
  rw [globalFirstLaneAttackerHashQueryFromHighRun_eq_none high secretKey _ state
    (encodingInputEpoch?_chainInput secretKey.parameter epoch chain step value)]
    at hresult
  have hencoding := globalFirstLaneLiftRevealProbe_encodingActions_eq_nil table
    ((globalCausalAttackerHashQueryFromHigh high secretKey
      (Concrete.CacheView.chainInput secretKey.parameter epoch chain step value)
        ).run state) result hresult
  have hencodingCount : FirstLaneOracleSimulation.encodingQueryCount result.2 = 0 :=
    FirstLaneOracleSimulation.encodingQueryCount_eq_zero_of_encodingActions_eq_nil
      hencoding
  have hprojected := globalFirstLaneLiftRevealProbe_mem_eagerTrace_support table
    ((globalCausalAttackerHashQueryFromHigh high secretKey
      (Concrete.CacheView.chainInput secretKey.parameter epoch chain step value)
        ).run state) result hresult
  have horiginal := hprojected
  rw [globalCausalAttackerHashQueryFromHigh_run] at hprojected
  generalize hplan : globalFilteredCausalAttackerHashPlan secretKey
    (Concrete.CacheView.chainInput secretKey.parameter epoch chain step value)
      state = plan at hprojected
  cases plan with
  | cached output =>
      simp only [support_pure, Set.mem_singleton_iff] at hprojected
      have hchain : result.2.chainActions = [] := congrArg Prod.snd hprojected
      exact hazard_add_missing_le_one_of_no_chain_actions result.2 _ hencoding
        hchain
  | redirect output =>
      simp only [support_pure, Set.mem_singleton_iff] at hprojected
      have hchain : result.2.chainActions = [] := congrArg Prod.snd hprojected
      exact hazard_add_missing_le_one_of_no_chain_actions result.2 _ hencoding
        hchain
  | fresh =>
      rw [simulate_eagerTrace_globalCausalHashQuery, support_map] at hprojected
      obtain ⟨output, _houtput, heq⟩ := hprojected
      have hchain : result.2.chainActions = [] := (congrArg Prod.snd heq).symm
      exact hazard_add_missing_le_one_of_no_chain_actions result.2 _ hencoding
        hchain
  | reveal index =>
      rw [simulate_eagerTrace_globalCausalRevealHashQueryFromHigh] at hprojected
      simp only [support_pure, Set.mem_singleton_iff] at hprojected
      have heq := hprojected
      have hchain : result.2.chainActions = [.reveal index (table index)] :=
        by simpa using congrArg Prod.snd heq
      exact hazard_add_missing_le_one_of_single_reveal result.2
        (chain, epoch, chainStepDigit step) index value (table index) hencoding
          hchain
  | probeThenFresh index target =>
      rw [simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_probeThenFresh
        table high secretKey _ state index target hplan, support_map] at horiginal
      obtain ⟨baseResult, _hbase, heq⟩ := horiginal
      have hprobe := congrArg Prod.snd heq
      have hparsed : index = (chain, epoch, chainStepDigit step) ∧
          target = value := by
        unfold globalFilteredCausalAttackerHashPlan at hplan
        split at hplan
        · cases hplan
        · rw [globalChainInputProbe?_chainInput] at hplan
          unfold globalFilteredCausalUncachedAttackerHashPlan at hplan
          split at hplan
          · split at hplan
            · split at hplan <;> cases hplan
            · cases hplan
          · split at hplan
            · injection hplan with hindex htarget
              exact ⟨hindex.symm, htarget.symm⟩
            · cases hplan
      have hchain : result.2.chainActions =
          [.probe (chain, epoch, chainStepDigit step) value] := by
        simpa [hparsed.1, hparsed.2] using hprobe.symm
      exact hazard_add_missing_le_one_of_single_probe result.2
        (chain, epoch, chainStepDigit step) value hencoding hchain

def ChainPrimaryStepCovered (epoch : Epoch) (chain : ChainIndex)
    (step : ChainStep) (value : Digest)
    (trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) : Prop :=
  FirstLaneOracleSimulation.hazardCount trace +
      (if (.chain (.probe (chain, epoch, chainStepDigit step) value) :
        FirstLaneOracleSimulation.ObservedAction GlobalChainValueIndex) ∈ trace
        then 0 else 1) ≤ 1

theorem globalFirstLaneVerificationHashImpl_chain_primary_covered
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (epoch : Epoch) (chain : ChainIndex) (step : ChainStep) (value : Digest)
    (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneVerifierHashExecution keyView edgeHigh
          (Concrete.CacheView.chainInput keyView.secretKey.parameter epoch
            chain step value) state)).run)) :
  ChainPrimaryStepCovered epoch chain step value result.2 := by
  classical
  unfold globalFirstLaneVerifierHashExecution at hresult
  change result ∈ support
    ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (globalFirstLaneAttackerHashQueryFromHighRun
        (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey
          (Concrete.CacheView.chainInput keyView.secretKey.parameter epoch chain
            step value) state)).run) at hresult
  unfold ChainPrimaryStepCovered
  exact globalFirstLane_chainQuery_hazard_add_missing_le_one table
    (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey epoch chain
      step value state result hresult

theorem globalFirstLaneVerificationHashImpl_hazardCount_le_one
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (input : HashInput)
    (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneVerifierHashExecution keyView edgeHigh input state)
          ).run)) :
    FirstLaneOracleSimulation.hazardCount result.2 ≤ 1 := by
  exact globalFirstLaneVerificationHash_step_hazardCount_one table keyView
    edgeHigh input state result hresult

theorem concreteChainHash_eq_query (parameter : PublicParameter)
    (epoch : Epoch) (chain : ChainIndex) (step : ChainStep) (value : Digest) :
    (Concrete.chainHash parameter epoch chain step value :
        OracleComp HashSpec Digest) = (do
      let output ← HasQuery.query (spec := HashSpec)
        (Concrete.CacheView.chainInput parameter epoch chain step value)
      pure (truncateHash output)) := by
  unfold Concrete.CacheView.chainInput Concrete.chainHash Concrete.tweakableHash
    Concrete.oracleHash
  rfl

theorem globalFirstLaneChainHash_support_decompose
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (epoch : Epoch) (chain : ChainIndex) (step : ChainStep) (value : Digest)
    (state : GlobalCausalHashState)
    (result : (Digest × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun input => StateT.mk
          (globalFirstLaneVerifierHashExecution keyView edgeHigh input))
          (Concrete.chainHash keyView.secretKey.parameter epoch chain step value :
            OracleComp HashSpec Digest)).run state)).run)) :
    ∃ queryHead : (HashOutput × GlobalCausalHashState) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex,
      queryHead ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (globalFirstLaneVerifierHashExecution keyView edgeHigh
            (Concrete.CacheView.chainInput keyView.secretKey.parameter epoch
              chain step value) state)).run) ∧
      result = ((truncateHash queryHead.1.1, queryHead.1.2), queryHead.2) := by
  rw [concreteChainHash_eq_query] at hresult
  exact simulateQ_eagerTrace_query_pure_support_decompose table
    (globalFirstLaneVerifierHashExecution keyView edgeHigh)
    (Concrete.CacheView.chainInput keyView.secretKey.parameter epoch chain step
      value) truncateHash state result hresult

theorem globalFirstLaneChainHash_hazard_add_missing_le_one
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (epoch : Epoch) (chain : ChainIndex) (step : ChainStep) (value : Digest)
    (state : GlobalCausalHashState)
    (result : (Digest × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun input => StateT.mk
          (globalFirstLaneVerifierHashExecution keyView edgeHigh input))
          (Concrete.chainHash keyView.secretKey.parameter epoch chain step value :
            OracleComp HashSpec Digest)).run state)).run)) :
    FirstLaneOracleSimulation.hazardCount result.2 +
        (if (.chain (.probe (chain, epoch, chainStepDigit step) value) :
          FirstLaneOracleSimulation.ObservedAction GlobalChainValueIndex) ∈
            result.2 then 0 else 1) ≤ 1 := by
  classical
  obtain ⟨queryHead, hquery, rfl⟩ :=
    globalFirstLaneChainHash_support_decompose table keyView edgeHigh epoch
      chain step value state result hresult
  simpa [ChainPrimaryStepCovered] using
    globalFirstLaneVerificationHashImpl_chain_primary_covered table keyView
      edgeHigh epoch chain step value state queryHead hquery

theorem globalFirstLaneChainHash_hazardCount_le_one
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (epoch : Epoch) (chain : ChainIndex) (step : ChainStep) (value : Digest)
    (state : GlobalCausalHashState)
    (result : (Digest × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun input => StateT.mk
          (globalFirstLaneVerifierHashExecution keyView edgeHigh input))
          (Concrete.chainHash keyView.secretKey.parameter epoch chain step value :
            OracleComp HashSpec Digest)).run state)).run)) :
    FirstLaneOracleSimulation.hazardCount result.2 ≤ 1 := by
  have hbound := globalFirstLaneChainHash_hazard_add_missing_le_one table
    keyView edgeHigh epoch chain step value state result hresult
  exact (Nat.le_add_right _ _).trans hbound

theorem globalFirstLaneExactTraced_chainWalk_hazard_add_missing_le
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (epoch : Epoch) (chain : ChainIndex) (position steps : Nat)
    (value : Digest) (hposition : position + (steps + 1) ≤ chainLength - 1)
    (hparameter : keyView.publicKey.parameter = keyView.secretKey.parameter)
    (state : GlobalCausalHashState)
    (result : (Digest × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun input => StateT.mk
          (globalFirstLaneVerifierHashExecution keyView edgeHigh input))
          (Concrete.chainWalk (m := OracleComp HashSpec) keyView.publicKey.parameter
            epoch chain position (steps + 1) value)).run state)).run)) :
    FirstLaneOracleSimulation.hazardCount result.2 +
        (if (.chain (.probe
          (chain, epoch, ⟨position, by omega⟩) value) :
            FirstLaneOracleSimulation.ObservedAction GlobalChainValueIndex) ∈
              result.2 then 0 else 1) ≤ steps + 1 := by
  rw [hparameter] at hresult
  induction steps generalizing state result with
  | zero =>
      rw [Concrete.chainWalk] at hresult
      have hstep : position < chainLength - 1 := by omega
      simp only [Concrete.chainWalk, Nat.add_zero, simulateQ_pure, StateT.run_pure,
        simulateQ_bind, StateT.run_bind, WriterT.run_bind', pure_bind,
        List.nil_append] at hresult
      rw [dif_pos hstep] at hresult
      have hsingle :=
        globalFirstLaneChainHash_hazard_add_missing_le_one table keyView
          edgeHigh epoch chain ⟨position, hstep⟩ value state result
            (by simpa using hresult)
      have hindex : chainStepDigit ⟨position, hstep⟩ =
          ⟨position, by omega⟩ := Fin.ext rfl
      rw [hindex] at hsingle
      exact hsingle
  | succ steps ih =>
      rw [Concrete.chainWalk] at hresult
      have hstep : position + (steps + 1) < chainLength - 1 := by omega
      simp only [hstep, ↓reduceDIte, simulateQ_bind, StateT.run_bind,
        WriterT.run_bind', mem_support_bind_iff] at hresult
      obtain ⟨⟨⟨previous, middleState⟩, prefixTrace⟩, hprefix,
        htailMapped⟩ := hresult
      rw [support_map] at htailMapped
      obtain ⟨tailResult, htail, heq⟩ := htailMapped
      have hprefixBound := ih (by omega) state
        ((previous, middleState), prefixTrace) hprefix
      have hprefixBound' : FirstLaneOracleSimulation.hazardCount prefixTrace +
          (if (.chain (.probe (chain, epoch, ⟨position, by omega⟩) value) :
            FirstLaneOracleSimulation.ObservedAction GlobalChainValueIndex) ∈
              prefixTrace then 0 else 1) ≤ steps + 1 := by
        simpa using hprefixBound
      have htailBound :=
        globalFirstLaneChainHash_hazardCount_le_one table keyView edgeHigh epoch
          chain ⟨position + (steps + 1), hstep⟩ previous middleState
            tailResult (by simpa using htail)
      have htrace : prefixTrace ++ tailResult.2 = result.2 := by
        simpa using congrArg Prod.snd heq
      rw [← htrace, FirstLaneOracleSimulation.hazardCount_append]
      by_cases hprefixMem :
          (.chain (.probe (chain, epoch, ⟨position, by omega⟩) value) :
            FirstLaneOracleSimulation.ObservedAction GlobalChainValueIndex) ∈
              prefixTrace
      · simp [hprefixMem] at hprefixBound' ⊢
        omega
      · by_cases htailMem :
          (.chain (.probe (chain, epoch, ⟨position, by omega⟩) value) :
            FirstLaneOracleSimulation.ObservedAction GlobalChainValueIndex) ∈
              tailResult.2
        · simp [hprefixMem, htailMem] at hprefixBound' ⊢
          omega
        · simp [hprefixMem, htailMem] at hprefixBound' ⊢
          omega

noncomputable def missingPrimaryCount {n : Nat}
    (primary : Fin n → Option (FirstLaneOracleSimulation.ObservedAction
      GlobalChainValueIndex))
    (trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) : Nat :=
  ∑ index, match primary index with
    | none => 0
    | some action => if action ∈ trace then 0 else 1

theorem missingPrimaryCount_append_le_add {n : Nat}
    (primary : Fin n → Option (FirstLaneOracleSimulation.ObservedAction
      GlobalChainValueIndex))
    (left right : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) :
    missingPrimaryCount primary (left ++ right) ≤
      missingPrimaryCount primary left + missingPrimaryCount primary right := by
  unfold missingPrimaryCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro index _
  cases hprimary : primary index with
  | none => simp [hprimary]
  | some action =>
      by_cases hleft : action ∈ left
      · simp [hprimary, hleft]
      · by_cases hright : action ∈ right <;>
          simp [hprimary, hleft, hright] <;> omega

theorem missingPrimaryCount_append_le_left {n : Nat}
    (primary : Fin n → Option (FirstLaneOracleSimulation.ObservedAction
      GlobalChainValueIndex))
    (left right : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) :
    missingPrimaryCount primary (left ++ right) ≤
      missingPrimaryCount primary left := by
  unfold missingPrimaryCount
  apply Finset.sum_le_sum
  intro index _
  cases hprimary : primary index with
  | none => simp [hprimary]
  | some action =>
      by_cases hleft : action ∈ left <;>
        simp [hprimary, hleft] <;> split <;> omega

theorem missingPrimaryCount_append_le_right {n : Nat}
    (primary : Fin n → Option (FirstLaneOracleSimulation.ObservedAction
      GlobalChainValueIndex))
    (left right : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) :
    missingPrimaryCount primary (left ++ right) ≤
      missingPrimaryCount primary right := by
  unfold missingPrimaryCount
  apply Finset.sum_le_sum
  intro index _
  cases hprimary : primary index with
  | none => simp [hprimary]
  | some action =>
      by_cases hright : action ∈ right <;>
        simp [hprimary, hright] <;> split <;> omega

theorem simulate_sequenceFin_hazard_add_missing_le
    {n : Nat}
    (table : GlobalChainValueIndex → Digest)
    (impl : QueryImpl HashSpec
      (StateT GlobalCausalHashState
        (OracleComp GlobalFirstLaneWorld)))
    (computation : Fin n → OracleComp HashSpec Digest)
    (cost : Fin n → Nat)
    (primary : Fin n → Option (FirstLaneOracleSimulation.ObservedAction
      GlobalChainValueIndex))
    (hsingle : ∀ index state result,
      result ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          ((simulateQ impl (computation index)).run state)).run) →
      FirstLaneOracleSimulation.hazardCount result.2 +
          (match primary index with
            | none => 0
            | some action => if action ∈ result.2 then 0 else 1) ≤ cost index)
    (state : GlobalCausalHashState)
    (result : ((Fin n → Digest) × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ impl (Concrete.sequenceFin computation)).run state)).run)) :
    FirstLaneOracleSimulation.hazardCount result.2 +
        missingPrimaryCount primary result.2 ≤ ∑ index, cost index := by
  induction n generalizing state with
  | zero =>
      simp [Concrete.sequenceFin] at hresult
      subst result
      simp [missingPrimaryCount, FirstLaneOracleSimulation.hazardCount]
  | succ n ih =>
      rw [Concrete.sequenceFin, simulateQ_bind, StateT.run_bind,
        simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hresult
      obtain ⟨⟨⟨head, middleState⟩, headTrace⟩, hhead,
        htailMapped⟩ := hresult
      rw [support_map] at htailMapped
      obtain ⟨tailResult, htail, heq⟩ := htailMapped
      have hheadBound := hsingle 0 state
        ((head, middleState), headTrace) hhead
      let tailComputation := fun index : Fin n => computation index.succ
      let tailCost := fun index : Fin n => cost index.succ
      let tailPrimary := fun index : Fin n => primary index.succ
      change tailResult ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          ((simulateQ impl
            ((fun tail => Fin.cases head tail) <$>
              Concrete.sequenceFin tailComputation)).run middleState)).run)
        at htail
      rw [simulateQ_map, StateT.run_map, simulateQ_map, WriterT.run_map',
        support_map] at htail
      obtain ⟨tailBase, htailBase, rfl⟩ := htail
      have htailBound := ih tailComputation tailCost tailPrimary
        (fun index => hsingle index.succ) middleState tailBase htailBase
      change FirstLaneOracleSimulation.hazardCount tailBase.2 +
          (∑ index : Fin n,
            match primary index.succ with
            | none => 0
            | some action => if action ∈ tailBase.2 then 0 else 1) ≤
        ∑ index : Fin n, cost index.succ at htailBound
      change FirstLaneOracleSimulation.hazardCount headTrace +
          (match primary 0 with
            | none => 0
            | some action => if action ∈ headTrace then 0 else 1) ≤
        cost 0 at hheadBound
      have htrace : headTrace ++ tailBase.2 = result.2 := by
        simpa using congrArg Prod.snd heq
      rw [← htrace, FirstLaneOracleSimulation.hazardCount_append,
        Fin.sum_univ_succ]
      unfold missingPrimaryCount
      rw [Fin.sum_univ_succ]
      have hzero :
          (match primary 0 with
            | none => 0
            | some action =>
                if action ∈ headTrace ++ tailBase.2 then 0 else 1) ≤
          (match primary 0 with
            | none => 0
            | some action => if action ∈ headTrace then 0 else 1) := by
        cases hprimary : primary 0 with
        | none => simp [hprimary]
        | some action =>
            by_cases hmem : action ∈ headTrace <;>
              simp [hprimary, hmem] <;> split <;> omega
      have hsucc :
          (∑ index : Fin n,
              match primary index.succ with
              | none => 0
              | some action =>
                  if action ∈ headTrace ++ tailBase.2 then 0 else 1) ≤
            ∑ index : Fin n,
              match primary index.succ with
              | none => 0
              | some action => if action ∈ tailBase.2 then 0 else 1 := by
        apply Finset.sum_le_sum
        intro index _
        cases hprimary : primary index.succ with
        | none => simp [hprimary]
        | some action =>
            by_cases hmem : action ∈ tailBase.2 <;>
              simp [hprimary, hmem] <;> split <;> omega
      omega

def recoverChainPrimaryProbe?
    (epoch : Epoch) (encoding : Encoding) (signature : Signature)
    (chain : ChainIndex) : Option
      (FirstLaneOracleSimulation.ObservedAction GlobalChainValueIndex) :=
  if hposition : (encoding chain).val < chainLength - 1 then
    some (.chain (.probe
      (chain, epoch, ⟨(encoding chain).val, by omega⟩)
      (signature.chainValue chain)))
  else
    none

theorem globalFirstLaneExactTraced_recoverChain_hazard_add_missing_le
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (epoch : Epoch) (encoding : Encoding) (signature : Signature)
    (chain : ChainIndex)
    (hparameter : keyView.publicKey.parameter = keyView.secretKey.parameter)
    (state : GlobalCausalHashState)
    (result : (Digest × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun input => StateT.mk
          (globalFirstLaneVerifierHashExecution keyView edgeHigh input))
          (Concrete.recoverChain (m := OracleComp HashSpec)
            keyView.publicKey.parameter epoch chain (encoding chain)
            (signature.chainValue chain))).run state)).run)) :
    FirstLaneOracleSimulation.hazardCount result.2 +
        (match recoverChainPrimaryProbe? epoch encoding signature chain with
          | none => 0
          | some action => if action ∈ result.2 then 0 else 1) ≤
      chainLength - 1 - (encoding chain).val := by
  by_cases hposition : (encoding chain).val < chainLength - 1
  · have hpositive : chainLength - 1 - (encoding chain).val ≠ 0 := by
      omega
    obtain ⟨steps, hsteps⟩ := Nat.exists_eq_succ_of_ne_zero hpositive
    have hbound : (encoding chain).val + (steps + 1) ≤ chainLength - 1 := by
      omega
    simp only [Concrete.recoverChain, hsteps] at hresult
    have hwalk := globalFirstLaneExactTraced_chainWalk_hazard_add_missing_le
      table keyView edgeHigh epoch chain (encoding chain).val steps
        (signature.chainValue chain) hbound hparameter state result
    simpa [Concrete.recoverChain, hsteps, recoverChainPrimaryProbe?, hposition]
      using hwalk hresult
  · have hzero : chainLength - 1 - (encoding chain).val = 0 := by
      omega
    simp [Concrete.recoverChain, hzero, Concrete.chainWalk,
      recoverChainPrimaryProbe?, hposition] at hresult
    subst result
    simp [recoverChainPrimaryProbe?, hposition, hzero,
      FirstLaneOracleSimulation.hazardCount]

theorem globalFirstLaneExactTraced_recoverEndpoints_hazard_add_missing_le
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (epoch : Epoch) (encoding : Encoding) (signature : Signature)
    (hparameter : keyView.publicKey.parameter = keyView.secretKey.parameter)
    (state : GlobalCausalHashState)
    (result : ((ChainIndex → Digest) × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun input => StateT.mk
          (globalFirstLaneVerifierHashExecution keyView edgeHigh input))
          (Concrete.recoverEndpoints (m := OracleComp HashSpec)
            keyView.publicKey.parameter epoch encoding signature)).run state)).run)) :
    FirstLaneOracleSimulation.hazardCount result.2 +
        missingPrimaryCount
          (recoverChainPrimaryProbe? epoch encoding signature) result.2 ≤
      TargetSum.verificationWork encoding := by
  apply simulate_sequenceFin_hazard_add_missing_le table
    (fun input => StateT.mk
      (globalFirstLaneVerifierHashExecution keyView edgeHigh input))
    (fun chain => Concrete.recoverChain keyView.publicKey.parameter epoch chain
      (encoding chain) (signature.chainValue chain))
    (fun chain => chainLength - 1 - (encoding chain).val)
    (recoverChainPrimaryProbe? epoch encoding signature)
    (globalFirstLaneExactTraced_recoverChain_hazard_add_missing_le
      table keyView edgeHigh epoch encoding signature · hparameter)
    state result
  simpa [Concrete.recoverEndpoints, TargetSum.verificationWork] using hresult

theorem globalFirstLaneExactTracedHash_simulateQ_cache_le
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp HashSpec α)
    (state : GlobalCausalHashState)
    (result : (α × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun input => StateT.mk
          (globalFirstLaneVerifierHashExecution keyView edgeHigh input))
          computation).run state)).run)) :
    state.cache ≤ result.1.2.cache := by
  exact globalFirstLaneVerifierHashExecution_simulateQ_cache_le table keyView
    edgeHigh computation state result hresult

theorem globalFirstLaneExactTraced_encodingHash_cache_eq
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (epoch : Epoch) (message : Message) (randomness : Randomness)
    (hparameter : keyView.publicKey.parameter = keyView.secretKey.parameter)
    (state : GlobalCausalHashState)
    (result : (Digest × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun input => StateT.mk
          (globalFirstLaneVerifierHashExecution keyView edgeHigh input))
          (Concrete.encodingHash keyView.publicKey.parameter epoch message
            randomness : OracleComp HashSpec Digest)).run state)).run)) :
    ∃ output,
      result.1.2.cache
          (Concrete.CacheView.encodingInput keyView.secretKey.parameter epoch
            (message, randomness)) = some output ∧
      truncateHash output = result.1.1 := by
  obtain ⟨queryHead, hquery, heq⟩ :=
    globalFirstLaneEncodingHash_support_decompose table keyView edgeHigh epoch
      message randomness state result hresult
  let input := Concrete.CacheView.encodingInput keyView.secretKey.parameter
    epoch (message, randomness)
  have hinput : tweakableHashInput keyView.publicKey.parameter (.encoding epoch)
      (Concrete.encodingPayload message randomness) = input := by
    rw [hparameter]
    rfl
  have hepoch : encodingInputEpoch? keyView.secretKey.parameter input =
      some epoch := by
    simpa [input] using encodingInputEpoch?_encodingInput
      keyView.secretKey.parameter epoch (message, randomness)
  have hquery' : queryHead ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneAttackerHashQueryAtEpoch keyView.secretKey input
          state epoch)).run) := by
    unfold globalFirstLaneVerifierHashExecution at hquery
    rw [hinput] at hquery
    rw [globalFirstLaneAttackerHashQueryFromHighRun_eq_some _ _ _ _ epoch
      hepoch] at hquery
    exact hquery
  have hcached := globalFirstLaneAttackerHashQueryAtEpoch_cache_eq_some table
    keyView.secretKey input state epoch queryHead hquery'
  refine ⟨queryHead.1.1, ?_, ?_⟩
  · have hresultCache : result.1.2.cache = queryHead.1.2.cache := by
      simpa using congrArg (fun candidate => candidate.1.2.cache) heq
    rw [hresultCache]
    exact hcached
  · have hresultOutput : result.1.1 = truncateHash queryHead.1.1 := by
      simpa using congrArg (fun candidate => candidate.1.1) heq
    rw [hresultOutput]

theorem Concrete.verificationAfterEndpoints_hazardQueryBound
    (publicKey : PublicKey) (epoch : Epoch) (signature : Signature)
    (endpoints : ChainIndex → Digest) :
    (do
      let leaf ← Concrete.leafHash publicKey.parameter epoch endpoints
      Concrete.verifyAfterLeaf publicKey epoch signature leaf :
        OracleComp HashSpec Bool).IsQueryBoundP
      IsVerifierHazardHashQuery 1 := by
  apply OracleComp.isQueryBoundP_bind (n := 1) (m := 0)
  · exact (ExactQueryCount.tweakableHash publicKey.parameter (.leaf epoch)
      (Concrete.leafPayload endpoints)).isTotalQueryBound_self.isQueryBoundP
  intro leaf _
  unfold Concrete.verifyAfterLeaf
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (Concrete.authenticationRoot_hazardQueryBound_zero publicKey.parameter
      epoch signature treeHeight leaf (Nat.le_refl _))
  intro root _
  exact OracleComp.isQueryBoundP_pure
    (spec := HashSpec) (p := IsVerifierHazardHashQuery) _ 0

theorem concreteNodeHash_eq_query (parameter : PublicParameter)
    (level : MerkleLevel) (node : MerkleNode) (left right : Digest) :
    (Concrete.nodeHash parameter level node left right :
        OracleComp HashSpec Digest) = (do
      let output ← HasQuery.query (spec := HashSpec)
        (Concrete.CacheView.merkleInput parameter level node left right)
      pure (truncateHash output)) := by
  unfold Concrete.nodeHash Concrete.tweakableHash Concrete.oracleHash
  rfl

theorem concreteLeafHash_eq_query (parameter : PublicParameter)
    (epoch : Epoch) (endpoints : ChainIndex → Digest) :
    (Concrete.leafHash parameter epoch endpoints :
        OracleComp HashSpec Digest) = (do
      let output ← HasQuery.query (spec := HashSpec)
        (Concrete.CacheView.leafInput parameter epoch endpoints)
      pure (truncateHash output)) := by
  unfold Concrete.leafHash Concrete.tweakableHash Concrete.oracleHash
    Concrete.CacheView.leafInput
  rfl

theorem globalFirstLaneLeafHash_hazardCount_one
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (parameter : PublicParameter) (epoch : Epoch)
    (endpoints : ChainIndex → Digest) (state : GlobalCausalHashState)
    (result : (Digest × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun input => StateT.mk
          (globalFirstLaneVerifierHashExecution keyView edgeHigh input))
          (Concrete.leafHash parameter epoch endpoints :
            OracleComp HashSpec Digest)).run state)).run)) :
    FirstLaneOracleSimulation.hazardCount result.2 ≤ 1 := by
  rw [concreteLeafHash_eq_query] at hresult
  obtain ⟨queryHead, hquery, rfl⟩ :=
    simulateQ_eagerTrace_query_pure_support_decompose table
      (globalFirstLaneVerifierHashExecution keyView edgeHigh)
      (Concrete.CacheView.leafInput parameter epoch endpoints)
      truncateHash state result hresult
  exact globalFirstLaneVerificationHash_step_hazardCount_one table keyView
    edgeHigh (Concrete.CacheView.leafInput parameter epoch endpoints) state
      queryHead hquery

theorem globalFirstLaneNodeHash_hazardCount_zero
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (parameter : PublicParameter) (level : MerkleLevel) (node : MerkleNode)
    (left right : Digest) (state : GlobalCausalHashState)
    (result : (Digest × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun input => StateT.mk
          (globalFirstLaneVerifierHashExecution keyView edgeHigh input))
          (Concrete.nodeHash parameter level node left right :
            OracleComp HashSpec Digest)).run state)).run)) :
    FirstLaneOracleSimulation.hazardCount result.2 ≤ 0 := by
  rw [concreteNodeHash_eq_query] at hresult
  obtain ⟨queryHead, hquery, rfl⟩ :=
    simulateQ_eagerTrace_query_pure_support_decompose table
      (globalFirstLaneVerifierHashExecution keyView edgeHigh)
      (Concrete.CacheView.merkleInput parameter level node left right)
      truncateHash state result hresult
  exact globalFirstLaneVerificationHash_merkle_hazardCount_zero table keyView
    edgeHigh parameter level node left right state queryHead hquery

theorem globalFirstLaneExactTraced_authenticationNodeHash_hazardCount_zero
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (epoch : Epoch) (signature : Signature) (level : Nat) (current : Digest)
    (hlevel : level < treeHeight)
    (state : GlobalCausalHashState)
    (result : (Digest × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun input => StateT.mk
          (globalFirstLaneVerifierHashExecution keyView edgeHigh input))
          (Concrete.authenticationNodeHash keyView.publicKey.parameter epoch
            level current (Concrete.signaturePath signature level) :
              OracleComp HashSpec Digest)).run state)).run)) :
    FirstLaneOracleSimulation.hazardCount result.2 ≤ 0 := by
  unfold Concrete.authenticationNodeHash at hresult
  simp only [hlevel, ↓reduceDIte] at hresult
  split at hresult
  · rename_i hbit
    exact globalFirstLaneNodeHash_hazardCount_zero table keyView edgeHigh
      keyView.publicKey.parameter ⟨level, hlevel⟩
      (Concrete.CacheView.nodeIndex epoch level)
      (Concrete.signaturePath signature level) current state result hresult
  · rename_i hbit
    exact globalFirstLaneNodeHash_hazardCount_zero table keyView edgeHigh
      keyView.publicKey.parameter ⟨level, hlevel⟩
      (Concrete.CacheView.nodeIndex epoch level) current
      (Concrete.signaturePath signature level) state result hresult

def postKeygenAuthenticationRoot
    (parameter : PublicParameter) (epoch : Epoch) (signature : Signature)
    (levels : Nat) (leaf : Digest) : OracleComp HashSpec Digest :=
  Concrete.authenticationRoot parameter epoch signature levels leaf

theorem globalFirstLaneExactTraced_authenticationRoot_hazardCount_zero
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (epoch : Epoch) (signature : Signature) (levels : Nat) (leaf : Digest)
    (hlevels : levels ≤ treeHeight)
    (state : GlobalCausalHashState)
    (result : (Digest × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun input => StateT.mk
          (globalFirstLaneVerifierHashExecution keyView edgeHigh input))
          (postKeygenAuthenticationRoot keyView.publicKey.parameter epoch
            signature levels leaf)).run state)).run)) :
    FirstLaneOracleSimulation.hazardCount result.2 ≤ 0 := by
  induction levels generalizing leaf state result with
  | zero =>
      simp only [postKeygenAuthenticationRoot, Concrete.authenticationRoot,
        simulateQ_pure, StateT.run_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      rfl
  | succ levels ih =>
      rw [postKeygenAuthenticationRoot, Concrete.authenticationRoot,
        simulateQ_bind, StateT.run_bind,
        simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hresult
      obtain ⟨⟨⟨current, middleState⟩, headTrace⟩, hhead,
        htailMapped⟩ := hresult
      rw [support_map] at htailMapped
      obtain ⟨tailResult, htail, heq⟩ := htailMapped
      have hhead' : ((current, middleState), headTrace) ∈ support
          ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
            ((simulateQ (fun input => StateT.mk
              (globalFirstLaneVerifierHashExecution keyView edgeHigh input))
              (postKeygenAuthenticationRoot keyView.publicKey.parameter epoch
                signature levels leaf)).run state)).run) := by
        simpa [postKeygenAuthenticationRoot] using hhead
      have hheadBound := ih leaf (by omega) state
        ((current, middleState), headTrace) hhead'
      have htailBound :=
        globalFirstLaneExactTraced_authenticationNodeHash_hazardCount_zero table
          keyView edgeHigh epoch signature levels current (by omega) middleState
            tailResult htail
      have hheadBound' : FirstLaneOracleSimulation.hazardCount headTrace ≤ 0 := by
        simpa using hheadBound
      have htailBound' : FirstLaneOracleSimulation.hazardCount tailResult.2 ≤ 0 := by
        simpa using htailBound
      have htrace : headTrace ++ tailResult.2 = result.2 := by
        simpa using congrArg Prod.snd heq
      rw [← htrace, FirstLaneOracleSimulation.hazardCount_append]
      omega

theorem globalFirstLaneExactTraced_verifyAfterLeaf_hazardCount_zero
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (epoch : Epoch) (signature : Signature) (leaf : Digest)
    (state : GlobalCausalHashState)
    (result : (Bool × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun input => StateT.mk
          (globalFirstLaneVerifierHashExecution keyView edgeHigh input))
          (Concrete.verifyAfterLeaf keyView.publicKey epoch signature leaf :
            OracleComp HashSpec Bool)).run state)).run)) :
    FirstLaneOracleSimulation.hazardCount result.2 ≤ 0 := by
  unfold Concrete.verifyAfterLeaf at hresult
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, WriterT.run_bind',
    mem_support_bind_iff] at hresult
  obtain ⟨⟨⟨root, middleState⟩, headTrace⟩, hhead, htailMapped⟩ := hresult
  rw [support_map] at htailMapped
  obtain ⟨tailResult, htail, heq⟩ := htailMapped
  have hhead' : ((root, middleState), headTrace) ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun input => StateT.mk
          (globalFirstLaneVerifierHashExecution keyView edgeHigh input))
          (postKeygenAuthenticationRoot keyView.publicKey.parameter epoch
            signature treeHeight leaf)).run state)).run) := by
    simpa [postKeygenAuthenticationRoot] using hhead
  have hheadBound :=
    globalFirstLaneExactTraced_authenticationRoot_hazardCount_zero table keyView
      edgeHigh epoch signature treeHeight leaf (Nat.le_refl _) state
        ((root, middleState), headTrace) hhead'
  simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure', support_pure,
    Set.mem_singleton_iff] at htail
  subst tailResult
  have htrace : headTrace = result.2 := by
    simpa using congrArg Prod.snd heq
  rw [← htrace]
  exact hheadBound

theorem globalFirstLaneExactTraced_verificationAfterEndpoints_hazardCount
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (epoch : Epoch) (signature : Signature)
    (endpoints : ChainIndex → Digest)
    (state : GlobalCausalHashState)
    (result : (Bool × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun input => StateT.mk
          (globalFirstLaneVerifierHashExecution keyView edgeHigh input))
          (do
            let leaf ← Concrete.leafHash keyView.publicKey.parameter epoch
              endpoints
            Concrete.verifyAfterLeaf keyView.publicKey epoch signature leaf :
              OracleComp HashSpec Bool)).run state)).run)) :
    FirstLaneOracleSimulation.hazardCount result.2 ≤ 1 := by
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, WriterT.run_bind',
    mem_support_bind_iff] at hresult
  obtain ⟨⟨⟨leaf, middleState⟩, headTrace⟩, hhead, htailMapped⟩ := hresult
  rw [support_map] at htailMapped
  obtain ⟨tailResult, htail, heq⟩ := htailMapped
  have hheadBound := globalFirstLaneLeafHash_hazardCount_one table keyView
    edgeHigh keyView.publicKey.parameter epoch endpoints state
      ((leaf, middleState), headTrace) hhead
  have hheadBound' : FirstLaneOracleSimulation.hazardCount headTrace ≤ 1 := by
    simpa using hheadBound
  have htailBound :=
    globalFirstLaneExactTraced_verifyAfterLeaf_hazardCount_zero table keyView
      edgeHigh epoch signature leaf middleState tailResult htail
  have htrace : headTrace ++ tailResult.2 = result.2 := by
    simpa using congrArg Prod.snd heq
  rw [← htrace, FirstLaneOracleSimulation.hazardCount_append]
  omega

theorem globalFirstLaneExactTraced_afterEncoding_hazard_add_missing_le
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (epoch : Epoch) (encoding : Encoding) (signature : Signature)
    (hparameter : keyView.publicKey.parameter = keyView.secretKey.parameter)
    (state : GlobalCausalHashState)
    (result : (Bool × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun input => StateT.mk
          (globalFirstLaneVerifierHashExecution keyView edgeHigh input))
          (do
            let endpoints ← Concrete.recoverEndpoints
              keyView.publicKey.parameter epoch encoding signature
            let leaf ← Concrete.leafHash keyView.publicKey.parameter epoch
              endpoints
            Concrete.verifyAfterLeaf keyView.publicKey epoch signature leaf :
              OracleComp HashSpec Bool)).run state)).run)) :
    FirstLaneOracleSimulation.hazardCount result.2 +
        missingPrimaryCount
          (recoverChainPrimaryProbe? epoch encoding signature) result.2 ≤
      TargetSum.verificationWork encoding + 1 := by
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, WriterT.run_bind',
    mem_support_bind_iff] at hresult
  obtain ⟨⟨⟨endpoints, middleState⟩, prefixTrace⟩, hprefix,
    htailMapped⟩ := hresult
  rw [support_map] at htailMapped
  obtain ⟨tailResult, htail, heq⟩ := htailMapped
  have hprefixBound :=
    globalFirstLaneExactTraced_recoverEndpoints_hazard_add_missing_le table
      keyView edgeHigh epoch encoding signature hparameter state
        ((endpoints, middleState), prefixTrace) hprefix
  have hprefixBound' : FirstLaneOracleSimulation.hazardCount prefixTrace +
      missingPrimaryCount
        (recoverChainPrimaryProbe? epoch encoding signature) prefixTrace ≤
      TargetSum.verificationWork encoding := by
    change FirstLaneOracleSimulation.hazardCount prefixTrace +
        missingPrimaryCount
          (recoverChainPrimaryProbe? epoch encoding signature) prefixTrace ≤
      TargetSum.verificationWork encoding at hprefixBound
    exact hprefixBound
  have htailBound :=
    globalFirstLaneExactTraced_verificationAfterEndpoints_hazardCount table
      keyView edgeHigh epoch signature endpoints middleState tailResult htail
  have htrace : prefixTrace ++ tailResult.2 = result.2 := by
    simpa using congrArg Prod.snd heq
  rw [← htrace, FirstLaneOracleSimulation.hazardCount_append]
  have hmissing := missingPrimaryCount_append_le_left
    (recoverChainPrimaryProbe? epoch encoding signature) prefixTrace tailResult.2
  omega

theorem globalFirstLaneExactTraced_verify_hash_of_decode
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (epoch : Epoch) (message : Message) (signature : Signature)
    (hparameter : keyView.publicKey.parameter = keyView.secretKey.parameter)
    (state middleState : GlobalCausalHashState)
    (digest : Digest)
    (headTrace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (tailResult result : (Bool × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (encoding : Encoding)
    (hhead : ((digest, middleState), headTrace) ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun input => StateT.mk
          (globalFirstLaneVerifierHashExecution keyView edgeHigh input))
          (Concrete.encodingHash keyView.publicKey.parameter epoch message
            signature.randomness : OracleComp HashSpec Digest)).run state)).run))
    (htail : tailResult ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun input => StateT.mk
          (globalFirstLaneVerifierHashExecution keyView edgeHigh input))
          (do
            let endpoints ← Concrete.recoverEndpoints
              keyView.publicKey.parameter epoch encoding signature
            let leaf ← Concrete.leafHash keyView.publicKey.parameter epoch
              endpoints
            Concrete.verifyAfterLeaf keyView.publicKey epoch signature leaf :
              OracleComp HashSpec Bool)).run middleState)).run))
    (heq : ((tailResult.1.1, tailResult.1.2),
      headTrace ++ tailResult.2) = result)
    (hdecode : TargetSum.decodeDigest digest = some encoding)
    (hheadBound : FirstLaneOracleSimulation.hazardCount headTrace ≤ 1) :
    ∃ selected,
      TargetSum.Valid selected ∧
      TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash result.1.2.cache
            keyView.secretKey.parameter epoch (message, signature.randomness)) =
        some selected ∧
      FirstLaneOracleSimulation.hazardCount result.2 +
          missingPrimaryCount
            (recoverChainPrimaryProbe? epoch selected signature) result.2 ≤
        verificationChainHashes + 2 := by
  have hvalid : TargetSum.Valid encoding :=
    (TargetSum.decodeDigest_eq_some_iff.mp hdecode).2
  obtain ⟨output, hcachedHead, htruncate⟩ :=
    globalFirstLaneExactTraced_encodingHash_cache_eq table keyView edgeHigh
      epoch message signature.randomness hparameter state
        ((digest, middleState), headTrace) hhead
  have htailBound :=
    globalFirstLaneExactTraced_afterEncoding_hazard_add_missing_le table
      keyView edgeHigh epoch encoding signature hparameter middleState tailResult
        htail
  have htailCacheLe :=
    globalFirstLaneExactTracedHash_simulateQ_cache_le table keyView edgeHigh
      (do
        let endpoints ← Concrete.recoverEndpoints
          keyView.publicKey.parameter epoch encoding signature
        let leaf ← Concrete.leafHash keyView.publicKey.parameter epoch
          endpoints
        Concrete.verifyAfterLeaf keyView.publicKey epoch signature leaf :
          OracleComp HashSpec Bool)
      middleState tailResult htail
  have hcachedFinal : tailResult.1.2.cache
      (Concrete.CacheView.encodingInput keyView.secretKey.parameter epoch
        (message, signature.randomness)) = some output :=
    htailCacheLe hcachedHead
  have hdecodeFinal : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash tailResult.1.2.cache
        keyView.secretKey.parameter epoch (message, signature.randomness)) =
      some encoding := by
    rw [Concrete.CacheView.encodingHash,
      Concrete.CacheView.digestAt_eq_of_cache_eq_some hcachedFinal,
      htruncate, hdecode]
  have htrace : headTrace ++ tailResult.2 = result.2 := by
    simpa using congrArg Prod.snd heq
  have hdecodeResult : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash result.1.2.cache
        keyView.secretKey.parameter epoch (message, signature.randomness)) =
      some encoding := by
    calc
      _ = TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash tailResult.1.2.cache
            keyView.secretKey.parameter epoch
              (message, signature.randomness)) := by
            simpa using (congrArg (fun candidate => TargetSum.decodeDigest
              (Concrete.CacheView.encodingHash candidate.1.2.cache
                keyView.secretKey.parameter epoch
                  (message, signature.randomness))) heq).symm
      _ = some encoding := hdecodeFinal
  refine ⟨encoding, hvalid, hdecodeResult, ?_⟩
  rw [← htrace, FirstLaneOracleSimulation.hazardCount_append]
  have hmissing := missingPrimaryCount_append_le_right
    (recoverChainPrimaryProbe? epoch encoding signature) headTrace tailResult.2
  rw [TargetSum.verificationWork_eq encoding hvalid] at htailBound
  omega

theorem globalFirstLaneExactTraced_verify_hash_support_of_verified
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (epoch : Epoch) (message : Message) (signature : Signature)
    (state : GlobalCausalHashState)
    (result : (Bool × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun input => StateT.mk
          (globalFirstLaneVerifierHashExecution keyView edgeHigh input))
          (Concrete.verify keyView.publicKey epoch message signature :
            OracleComp HashSpec Bool)).run state)).run))
    (hverified : result.1.1 = true) :
    ∃ digest middleState headTrace tailResult encoding,
      ((digest, middleState), headTrace) ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          ((simulateQ (fun input => StateT.mk
            (globalFirstLaneVerifierHashExecution keyView edgeHigh input))
            (Concrete.encodingHash keyView.publicKey.parameter epoch message
              signature.randomness : OracleComp HashSpec Digest)).run state)).run) ∧
      tailResult ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          ((simulateQ (fun input => StateT.mk
            (globalFirstLaneVerifierHashExecution keyView edgeHigh input))
            (do
              let endpoints ← Concrete.recoverEndpoints
                keyView.publicKey.parameter epoch encoding signature
              let leaf ← Concrete.leafHash keyView.publicKey.parameter epoch
                endpoints
              Concrete.verifyAfterLeaf keyView.publicKey epoch signature leaf :
                OracleComp HashSpec Bool)).run middleState)).run) ∧
      ((tailResult.1.1, tailResult.1.2), headTrace ++ tailResult.2) = result ∧
      TargetSum.decodeDigest digest = some encoding := by
  unfold Concrete.verify at hresult
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, WriterT.run_bind',
    mem_support_bind_iff] at hresult
  obtain ⟨⟨⟨digest, middleState⟩, headTrace⟩, hhead,
    htailMapped⟩ := hresult
  rw [support_map] at htailMapped
  obtain ⟨tailResult, htail, heq⟩ := htailMapped
  cases hdecode : TargetSum.decodeDigest digest with
  | none =>
      simp only [hdecode, simulateQ_pure, StateT.run_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff] at htail
      subst tailResult
      have hfalse : result.1.1 = false := by
        simpa using congrArg (fun candidate => candidate.1.1) heq.symm
      rw [hverified] at hfalse
      contradiction
  | some encoding =>
      have htailSome := htail
      simp only [hdecode] at htailSome
      exact ⟨digest, middleState, headTrace, tailResult, encoding, hhead,
        htailSome, heq, hdecode⟩

theorem globalFirstLaneExactTraced_verify_hash_hazard_add_missing_exists
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (epoch : Epoch) (message : Message) (signature : Signature)
    (hparameter : keyView.publicKey.parameter = keyView.secretKey.parameter)
    (state : GlobalCausalHashState)
    (result : (Bool × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun input => StateT.mk
          (globalFirstLaneVerifierHashExecution keyView edgeHigh input))
          (Concrete.verify keyView.publicKey epoch message signature :
            OracleComp HashSpec Bool)).run state)).run))
    (hverified : result.1.1 = true) :
    ∃ encoding,
      TargetSum.Valid encoding ∧
      TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash result.1.2.cache
            keyView.secretKey.parameter epoch (message, signature.randomness)) =
        some encoding ∧
      FirstLaneOracleSimulation.hazardCount result.2 +
          missingPrimaryCount
            (recoverChainPrimaryProbe? epoch encoding signature) result.2 ≤
        verificationChainHashes + 2 := by
  obtain ⟨digest, middleState, headTrace, tailResult, encoding, hhead,
    htail, heq, hdecode⟩ :=
    globalFirstLaneExactTraced_verify_hash_support_of_verified table keyView
      edgeHigh epoch message signature state result hresult hverified
  obtain ⟨queryHead, hquery, hheadEq⟩ :=
    globalFirstLaneEncodingHash_support_decompose table keyView edgeHigh epoch
      message signature.randomness state ((digest, middleState), headTrace) hhead
  have hqueryBound := globalFirstLaneVerificationHash_step_hazardCount_one
    table keyView edgeHigh
      (tweakableHashInput keyView.publicKey.parameter (.encoding epoch)
        (Concrete.encodingPayload message signature.randomness)) state
      queryHead hquery
  have hheadBound : FirstLaneOracleSimulation.hazardCount headTrace ≤ 1 := by
    have hheadTrace : headTrace = queryHead.2 := by
      simpa using congrArg Prod.snd hheadEq
    rw [hheadTrace]
    exact hqueryBound
  exact globalFirstLaneExactTraced_verify_hash_of_decode table keyView
    edgeHigh epoch message signature hparameter state middleState digest
      headTrace tailResult result encoding hhead htail heq hdecode hheadBound

theorem globalFirstLaneExactTracedVerifier_hazard_add_missing_exists
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (epoch : Epoch) (message : Message) (signature : Signature)
    (hparameter : keyView.publicKey.parameter = keyView.secretKey.parameter)
    (state : GlobalFirstLaneExactTracedState)
    (result : (Bool × GlobalFirstLaneExactTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (globalFirstLaneExactTracedVerifierImpl keyView edgeHigh)
          (Concrete.scheme.verify keyView.publicKey epoch message signature)).run
            state)).run))
    (hverified : result.1.1 = true) :
    ∃ encoding,
      TargetSum.Valid encoding ∧
      TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash result.1.2.causalState.cache
            keyView.secretKey.parameter epoch (message, signature.randomness)) =
        some encoding ∧
      FirstLaneOracleSimulation.hazardCount result.2 +
          missingPrimaryCount
            (recoverChainPrimaryProbe? epoch encoding signature) result.2 ≤
        verificationChainHashes + 2 := by
  obtain ⟨baseResult, hbase, heq⟩ :=
    globalFirstLaneExactTracedVerifier_eager_support_decompose table keyView
      edgeHigh
        (Concrete.scheme.verify keyView.publicKey epoch message signature)
        state result hresult
  let forgery : Forgery := { epoch, message, signature }
  have hbase' : baseResult ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun input => StateT.mk
          (globalFirstLaneVerifierHashExecution keyView edgeHigh input))
          (Concrete.verify keyView.publicKey epoch message signature :
            OracleComp HashSpec Bool)).run state.causalState)).run) := by
    rw [← globalFirstLaneVerifier_eq_hashExecution keyView edgeHigh forgery]
    simpa [forgery] using hbase
  have hverifiedBase : baseResult.1.1 = true := by
    have := congrArg (fun candidate => candidate.1.1) heq
    simpa [hverified] using this.symm
  obtain ⟨encoding, hvalid, hdecode, hbound⟩ :=
    globalFirstLaneExactTraced_verify_hash_hazard_add_missing_exists table
      keyView edgeHigh epoch message signature hparameter state.causalState
        baseResult hbase' hverifiedBase
  refine ⟨encoding, hvalid, ?_, ?_⟩
  · have hcache : result.1.2.causalState.cache = baseResult.1.2.cache := by
      simpa using congrArg (fun candidate => candidate.1.2.causalState.cache) heq
    rw [hcache]
    exact hdecode
  · have htrace : result.2 = baseResult.2 := by
      simpa using congrArg Prod.snd heq
    rw [htrace]
    exact hbound

theorem globalFirstLaneExactTracedDetailedExecution_hazard_add_missing_exists
    (table : GlobalChainValueIndex → Digest)
    (adversary : Adversary Concrete.scheme)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (hparameter : keyView.publicKey.parameter = keyView.secretKey.parameter)
    (initialState : GlobalFirstLaneExactTracedState)
    (result : ((Forgery × Bool) × GlobalFirstLaneExactTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalFirstLaneExactTracedDetailedExecution adversary keyView edgeHigh
          ).run initialState)).run))
    (hverified : result.1.1.2 = true) :
    ∃ encoding,
      TargetSum.Valid encoding ∧
      TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash result.1.2.causalState.cache
            keyView.secretKey.parameter result.1.1.1.epoch
              (result.1.1.1.message, result.1.1.1.signature.randomness)) =
        some encoding ∧
      initialState.attackerTrace.hashInputs.length +
          FirstLaneOracleSimulation.hazardCount result.2 +
          missingPrimaryCount
            (recoverChainPrimaryProbe? result.1.1.1.epoch encoding
              result.1.1.1.signature) result.2 ≤
        result.1.2.attackerTrace.hashInputs.length +
          (verificationChainHashes + 2) := by
  unfold globalFirstLaneExactTracedDetailedExecution at hresult
  rw [StateT.run_mk, simulateQ_bind, WriterT.run_bind',
    mem_support_bind_iff] at hresult
  obtain ⟨handled, hadversary, hrestMapped⟩ := hresult
  rw [support_map] at hrestMapped
  obtain ⟨verificationResult, hverificationBlock, hresultEq⟩ := hrestMapped
  rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff]
    at hverificationBlock
  obtain ⟨verified, hverify, hfinalMapped⟩ := hverificationBlock
  simp only [simulateQ_pure, WriterT.run_pure', map_pure, support_pure,
    Set.mem_singleton_iff, Prod.map_apply, id_eq] at hfinalMapped
  cases hfinalMapped
  cases hresultEq
  have hadversaryCount :=
    globalFirstLaneExactTracedMappedAdversary_hazardCount table keyView
      edgeHigh (adversary.main keyView.publicKey) initialState handled
        hadversary
  obtain ⟨encoding, hvalid, hdecode, hverifierCount⟩ :=
    globalFirstLaneExactTracedVerifier_hazard_add_missing_exists table keyView
      edgeHigh handled.1.1.epoch handled.1.1.message handled.1.1.signature hparameter
        handled.1.2 verified hverify hverified
  have hstate : verified.1.2.attackerTrace =
      handled.1.2.attackerTrace := by
    obtain ⟨baseResult, _hbase, heq⟩ :=
      globalFirstLaneExactTracedVerifier_eager_support_decompose table keyView
        edgeHigh
        (Concrete.scheme.verify keyView.publicKey handled.1.1.epoch
          handled.1.1.message handled.1.1.signature)
        handled.1.2 verified hverify
    simpa using congrArg (fun candidate => candidate.1.2.attackerTrace) heq
  refine ⟨encoding, hvalid, hdecode, ?_⟩
  simp only [Prod.map_apply, id_eq]
  rw [show (∅ : FirstLaneOracleSimulation.ActionTrace
    GlobalChainValueIndex) = [] by rfl, List.append_nil,
    FirstLaneOracleSimulation.hazardCount_append]
  have hmissing := missingPrimaryCount_append_le_right
    (recoverChainPrimaryProbe? handled.1.1.epoch encoding
      handled.1.1.signature) handled.2 verified.2
  rw [hstate]
  omega

theorem globalFirstLaneExactTracedProgram_support_info
    (table : GlobalChainValueIndex → Digest)
    (adversary : Adversary Concrete.scheme)
    (result : GlobalFirstLaneExactTracedResult ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneExactTracedProgram adversary)).run)) :
    ∃ keyResult detail,
      keyResult ∈ support globalHighDirectKeygen ∧
      detail ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          ((globalFirstLaneExactTracedDetailedExecution adversary keyResult.1
            keyResult.2).run
              (GlobalExactTracedState.mk
                (globalFilteredCausalKeygenState keyResult.1) [] []))).run) ∧
      result = ((keyResult, detail.1), detail.2) := by
  unfold globalFirstLaneExactTracedProgram at hresult
  rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hresult
  obtain ⟨keyHead, hkeyHead, hrestMapped⟩ := hresult
  rw [FirstLaneOracleSimulation.simulate_eagerTrace_liftProbComp,
    support_map] at hkeyHead
  obtain ⟨keyResult, hkeyResult, hkeyHeadEq⟩ := hkeyHead
  subst keyHead
  simp only [List.nil_append] at hrestMapped
  rw [support_map] at hrestMapped
  obtain ⟨execution, hexecution, heq⟩ := hrestMapped
  rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hexecution
  obtain ⟨detail, hdetail, hfinal⟩ := hexecution
  simp only [simulateQ_pure, WriterT.run_pure', map_pure, support_pure,
    Set.mem_singleton_iff, Prod.map_apply, id_eq] at hfinal
  subst execution
  subst result
  refine ⟨keyResult, detail, hkeyResult, hdetail, ?_⟩
  simp

theorem globalFirstLaneExactTracedProgram_hazard_add_missing_exists
    (table : GlobalChainValueIndex → Digest)
    (adversary : Adversary Concrete.scheme)
    (result : GlobalFirstLaneExactTracedResult ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneExactTracedProgram adversary)).run))
    (hverified : result.1.2.1.2 = true) :
    ∃ encoding,
      TargetSum.Valid encoding ∧
      TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash result.1.2.2.causalState.cache
            result.1.1.1.secretKey.parameter result.1.2.1.1.epoch
              (result.1.2.1.1.message,
                result.1.2.1.1.signature.randomness)) = some encoding ∧
      FirstLaneOracleSimulation.hazardCount result.2 +
          missingPrimaryCount
            (recoverChainPrimaryProbe? result.1.2.1.1.epoch encoding
              result.1.2.1.1.signature) result.2 ≤
        result.1.2.2.attackerTrace.hashInputs.length +
          (verificationChainHashes + 2) := by
  obtain ⟨keyResult, detail, hkeyResult, hdetail, rfl⟩ :=
    globalFirstLaneExactTracedProgram_support_info table adversary result hresult
  have hcount :=
    globalFirstLaneExactTracedDetailedExecution_hazard_add_missing_exists table
      adversary keyResult.1 keyResult.2
        (globalHighDirectKeygen_support_parameter_eq keyResult hkeyResult)
        (GlobalExactTracedState.mk
          (globalFilteredCausalKeygenState keyResult.1) [] []) detail hdetail
  obtain ⟨encoding, hvalid, hdecode, hbound⟩ := hcount hverified
  refine ⟨encoding, hvalid, hdecode, ?_⟩
  simpa [AttackerActionTrace.hashInputs] using hbound

theorem globalFirstLaneExactTracedDetailedExecution_hazardCount
    (table : GlobalChainValueIndex → Digest)
    (adversary : Adversary Concrete.scheme)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (initialState : GlobalFirstLaneExactTracedState)
    (result : ((Forgery × Bool) × GlobalFirstLaneExactTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalFirstLaneExactTracedDetailedExecution adversary keyView edgeHigh
          ).run initialState)).run)) :
    initialState.attackerTrace.hashInputs.length +
        FirstLaneOracleSimulation.hazardCount result.2 ≤
      result.1.2.attackerTrace.hashInputs.length +
        (verificationChainHashes + 2 + treeHeight) := by
  unfold globalFirstLaneExactTracedDetailedExecution at hresult
  rw [StateT.run_mk, simulateQ_bind, WriterT.run_bind',
    mem_support_bind_iff] at hresult
  obtain ⟨handled, hadversary, hrestMapped⟩ := hresult
  rw [support_map] at hrestMapped
  obtain ⟨verificationResult, hverificationBlock, hresultEq⟩ := hrestMapped
  rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff]
    at hverificationBlock
  obtain ⟨verified, hverify, hfinalMapped⟩ := hverificationBlock
  simp only [simulateQ_pure, WriterT.run_pure', map_pure, support_pure,
    Set.mem_singleton_iff, Prod.map_apply, id_eq] at hfinalMapped
  cases hfinalMapped
  cases hresultEq
  have hadversaryCount :=
    globalFirstLaneExactTracedMappedAdversary_hazardCount table keyView
      edgeHigh (adversary.main keyView.publicKey) initialState handled
        hadversary
  have hverifierCount :=
    globalFirstLaneExactTracedVerifier_verify_hazardCount table keyView
      edgeHigh handled.1.1.epoch handled.1.1.message
        handled.1.1.signature handled.1.2 verified hverify
  have hstate : verified.1.2.attackerTrace =
      handled.1.2.attackerTrace := by
    obtain ⟨baseResult, _hbase, heq⟩ :=
      globalFirstLaneExactTracedVerifier_eager_support_decompose table keyView
        edgeHigh
        (Concrete.scheme.verify keyView.publicKey handled.1.1.epoch
          handled.1.1.message handled.1.1.signature)
        handled.1.2 verified hverify
    simpa using congrArg (fun candidate => candidate.1.2.attackerTrace) heq
  simp only [Prod.map_apply, id_eq]
  rw [show (∅ : FirstLaneOracleSimulation.ActionTrace
    GlobalChainValueIndex) = [] by rfl, List.append_nil,
    FirstLaneOracleSimulation.hazardCount_append]
  rw [hstate]
  omega

theorem globalFirstLaneExactTracedProgram_hazardCount
    (table : GlobalChainValueIndex → Digest)
    (adversary : Adversary Concrete.scheme)
    (result : GlobalFirstLaneExactTracedResult ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneExactTracedProgram adversary)).run)) :
    FirstLaneOracleSimulation.hazardCount result.2 ≤
      result.1.2.2.attackerTrace.hashInputs.length +
        (verificationChainHashes + 2 + treeHeight) := by
  unfold globalFirstLaneExactTracedProgram at hresult
  rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hresult
  obtain ⟨keyHead, hkeyHead, hrestMapped⟩ := hresult
  rw [FirstLaneOracleSimulation.simulate_eagerTrace_liftProbComp,
    support_map] at hkeyHead
  obtain ⟨keyResult, _hkeyResult, hkeyHeadEq⟩ := hkeyHead
  subst keyHead
  simp only [List.nil_append] at hrestMapped
  rw [support_map] at hrestMapped
  obtain ⟨execution, hexecution, heq⟩ := hrestMapped
  rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hexecution
  obtain ⟨detail, hdetail, hfinal⟩ := hexecution
  simp only [simulateQ_pure, WriterT.run_pure', map_pure, support_pure,
    Set.mem_singleton_iff, Prod.map_apply, id_eq] at hfinal
  subst execution
  have hcount := globalFirstLaneExactTracedDetailedExecution_hazardCount table
    adversary keyResult.1 keyResult.2
      (GlobalExactTracedState.mk
        (globalFilteredCausalKeygenState keyResult.1) [] []) detail hdetail
  subst result
  simpa [AttackerActionTrace.hashInputs] using hcount

noncomputable def exactForgeryEncoding
    (result : GlobalHighDirectExactTracedResult) : Encoding :=
  actionTracedForgeryEncoding
    (globalHighDirectErasedResult
      (globalHighDirectExactTracedBaseProjection result))

theorem exactForgeryEncoding_eq_of_decode
    (result : GlobalHighDirectExactTracedResult) (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash result.2.2.causalState.cache
        result.1.1.secretKey.parameter result.2.1.1.epoch
          (result.2.1.1.message, result.2.1.1.signature.randomness)) =
        some encoding) :
    exactForgeryEncoding result = encoding := by
  change (TargetSum.decodeDigest
    (Concrete.CacheView.encodingHash result.2.2.causalState.cache
      result.1.1.secretKey.parameter result.2.1.1.epoch
        (result.2.1.1.message,
          result.2.1.1.signature.randomness))).getD _ = encoding
  simp only [hdecode, Option.getD_some]

theorem globalFirstLaneExactTracedProgram_hazard_add_missing_exact
    (table : GlobalChainValueIndex → Digest)
    (adversary : Adversary Concrete.scheme)
    (result : GlobalFirstLaneExactTracedResult ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneExactTracedProgram adversary)).run))
    (hverified : result.1.2.1.2 = true) :
    TargetSum.Valid (exactForgeryEncoding result.1) ∧
    FirstLaneOracleSimulation.hazardCount result.2 +
        missingPrimaryCount
          (recoverChainPrimaryProbe? result.1.2.1.1.epoch
            (exactForgeryEncoding result.1) result.1.2.1.1.signature) result.2 ≤
      result.1.2.2.attackerTrace.hashInputs.length +
        (verificationChainHashes + 2) := by
  obtain ⟨encoding, hvalid, hdecode, hcount⟩ :=
    globalFirstLaneExactTracedProgram_hazard_add_missing_exists table adversary
      result hresult hverified
  have hencoding : exactForgeryEncoding result.1 = encoding :=
    exactForgeryEncoding_eq_of_decode result.1 encoding hdecode
  simpa [hencoding] using And.intro hvalid hcount

noncomputable def exactForgeryMissingPrimaryChains
    (baseTrace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (result : GlobalHighDirectExactTracedResult) : Finset ChainIndex :=
  Finset.univ.filter fun chain =>
    (.chain (.probe
      (chain, result.2.1.1.epoch, exactForgeryEncoding result chain)
      (result.2.1.1.signature.chainValue chain)) :
        FirstLaneOracleSimulation.ObservedAction GlobalChainValueIndex) ∉
      baseTrace

noncomputable def exactForgeryMissingPrimaryTrace
    (baseTrace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (result : GlobalHighDirectExactTracedResult) :
    FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex :=
  (exactForgeryMissingPrimaryChains baseTrace result).toList.map fun chain =>
    .chain (.probe
      (chain, result.2.1.1.epoch, exactForgeryEncoding result chain)
      (result.2.1.1.signature.chainValue chain))

theorem exactForgeryMissingPrimaryTrace_all_probes
    (baseTrace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (result : GlobalHighDirectExactTracedResult)
    (action : FirstLaneOracleSimulation.ObservedAction GlobalChainValueIndex)
    (haction : action ∈ exactForgeryMissingPrimaryTrace baseTrace result) :
    ∃ index target, action = .chain (.probe index target) := by
  unfold exactForgeryMissingPrimaryTrace at haction
  rw [List.mem_map] at haction
  obtain ⟨chain, _hchain, rfl⟩ := haction
  exact ⟨_, _, rfl⟩

@[simp]
theorem hazardCount_exactForgeryMissingPrimaryTrace
    (baseTrace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (result : GlobalHighDirectExactTracedResult) :
    FirstLaneOracleSimulation.hazardCount
      (exactForgeryMissingPrimaryTrace baseTrace result) =
        (exactForgeryMissingPrimaryChains baseTrace result).card := by
  have hcount : ∀ trace : FirstLaneOracleSimulation.ActionTrace
      GlobalChainValueIndex,
      (∀ action ∈ trace, ∃ index target, action = .chain (.probe index target)) →
      FirstLaneOracleSimulation.hazardCount trace = trace.length := by
    intro trace hprobes
    induction trace with
    | nil => rfl
    | cons action rest ih =>
        obtain ⟨index, target, rfl⟩ := hprobes action (by simp)
        simp only [FirstLaneOracleSimulation.hazardCount, List.length_cons,
          Nat.succ.injEq]
        apply ih
        intro candidate hcandidate
        exact hprobes candidate (by simp [hcandidate])
  rw [hcount]
  · simp [exactForgeryMissingPrimaryTrace]
  · exact exactForgeryMissingPrimaryTrace_all_probes baseTrace result

theorem exactForgeryMissingPrimaryChains_card_le
    (baseTrace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (result : GlobalHighDirectExactTracedResult) :
    (exactForgeryMissingPrimaryChains baseTrace result).card ≤
      missingPrimaryCount
        (recoverChainPrimaryProbe? result.2.1.1.epoch
          (exactForgeryEncoding result) result.2.1.1.signature) baseTrace +
      (TargetSum.terminalChains (exactForgeryEncoding result)).card := by
  classical
  let nonterminalMissing : Finset ChainIndex := Finset.univ.filter fun chain =>
    (exactForgeryEncoding result chain).val < chainLength - 1 ∧
    (.chain (.probe
      (chain, result.2.1.1.epoch, exactForgeryEncoding result chain)
      (result.2.1.1.signature.chainValue chain)) :
        FirstLaneOracleSimulation.ObservedAction GlobalChainValueIndex) ∉
      baseTrace
  have hsubset : exactForgeryMissingPrimaryChains baseTrace result ⊆
      nonterminalMissing ∪ TargetSum.terminalChains (exactForgeryEncoding result) := by
    intro chain hchain
    have hmissing := (Finset.mem_filter.mp hchain).2
    by_cases hterminal :
        (exactForgeryEncoding result chain).val = chainLength - 1
    · apply Finset.mem_union_right
      simp [TargetSum.terminalChains, hterminal]
    · apply Finset.mem_union_left
      simp [nonterminalMissing, hmissing]
      omega
  have hnonterminal : nonterminalMissing.card =
      missingPrimaryCount
        (recoverChainPrimaryProbe? result.2.1.1.epoch
          (exactForgeryEncoding result) result.2.1.1.signature) baseTrace := by
    unfold nonterminalMissing missingPrimaryCount
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro chain _
    by_cases hposition :
        (exactForgeryEncoding result chain).val < chainLength - 1
    · by_cases hmem :
          (.chain (.probe
            (chain, result.2.1.1.epoch, exactForgeryEncoding result chain)
            (result.2.1.1.signature.chainValue chain)) :
              FirstLaneOracleSimulation.ObservedAction
                GlobalChainValueIndex) ∈ baseTrace <;>
        simp [recoverChainPrimaryProbe?, hposition, hmem]
    · simp [recoverChainPrimaryProbe?, hposition]
  have hcard := Finset.card_le_card hsubset
  have hunion := Finset.card_union_le nonterminalMissing
    (TargetSum.terminalChains (exactForgeryEncoding result))
  rw [hnonterminal] at hunion
  omega

noncomputable def exactForgeryMissingPrimaryProbeTrace
    (baseTrace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (result : GlobalHighDirectExactTracedResult) :
    RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex :=
  (globalHighDirectExactForgeryPrimaryProbeTrace result).filter fun action =>
    FirstLaneOracleSimulation.ObservedAction.chain action ∉ baseTrace

theorem exactForgeryMissingPrimaryProbeTrace_all_probes
    (baseTrace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (result : GlobalHighDirectExactTracedResult)
    (action : RevealProbeOracleSimulation.ObservedAction GlobalChainValueIndex)
    (haction : action ∈ exactForgeryMissingPrimaryProbeTrace baseTrace result) :
    ∃ index target, action = .probe index target := by
  unfold exactForgeryMissingPrimaryProbeTrace at haction
  have hfull := (List.mem_filter.mp haction).1
  exact globalHighDirectForgeryPrimaryProbeTrace_all_probes
    (globalHighDirectExactTracedBaseProjection result) action hfull

theorem exactForgeryMissingPrimaryProbeTrace_agrees
    (table : GlobalChainValueIndex → Digest)
    (baseTrace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (result : GlobalHighDirectExactTracedResult) :
    RevealProbeOracleSimulation.TraceAgrees table
      (exactForgeryMissingPrimaryProbeTrace baseTrace result) := by
  apply traceAgrees_of_all_probes
  intro action haction
  exact exactForgeryMissingPrimaryProbeTrace_all_probes baseTrace result action
    haction

@[simp]
theorem observedProbeCount_exactForgeryMissingPrimaryProbeTrace
    (baseTrace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (result : GlobalHighDirectExactTracedResult) :
    RevealProbeOracleSimulation.observedProbeCount
      (exactForgeryMissingPrimaryProbeTrace baseTrace result) =
        (exactForgeryMissingPrimaryChains baseTrace result).card := by
  have hcount : ∀ trace : RevealProbeOracleSimulation.ActionTrace
      GlobalChainValueIndex,
      (∀ action ∈ trace, ∃ index target, action = .probe index target) →
      RevealProbeOracleSimulation.observedProbeCount trace = trace.length := by
    intro trace hprobes
    induction trace with
    | nil => rfl
    | cons action rest ih =>
        obtain ⟨index, target, rfl⟩ := hprobes action (by simp)
        simp only [RevealProbeOracleSimulation.observedProbeCount,
          List.length_cons, Nat.succ.injEq]
        apply ih
        intro candidate hcandidate
        exact hprobes candidate (by simp [hcandidate])
  rw [hcount]
  · unfold exactForgeryMissingPrimaryProbeTrace
      globalHighDirectExactForgeryPrimaryProbeTrace
      globalHighDirectForgeryPrimaryProbeTrace globalForgeryPrimaryProbeTrace
      globalHighDirectExactTracedBaseProjection globalHighDirectErasedResult
      exactForgeryMissingPrimaryChains exactForgeryEncoding actionTraceOutcome
    unfold globalHighDirectExactTracedBaseProjection globalHighDirectErasedResult
      actionTraceOutcome
    dsimp only
    let values : ChainIndex →
        RevealProbeOracleSimulation.ObservedAction GlobalChainValueIndex :=
      fun chain => .probe
        (chain, result.2.1.1.epoch,
          actionTracedForgeryEncoding
            ((((result.1.1.publicKey, result.1.1.secretKey),
                result.1.1.cache),
              { publicKey := result.1.1.publicKey
                secretKey := result.1.1.secretKey
                forgery := result.2.1.1
                signingLog := AttackerActionTrace.toSigningLog []
                verified := result.2.1.2 },
              result.2.2.causalState.cache), []) chain)
        (result.2.1.1.signature.chainValue chain)
    let predicate := fun action :
        RevealProbeOracleSimulation.ObservedAction GlobalChainValueIndex =>
      decide ((.chain action :
        FirstLaneOracleSimulation.ObservedAction GlobalChainValueIndex) ∉
          baseTrace)
    simpa [values, predicate, decide_eq_true_eq] using
      (length_filter_ofFn_eq_card_filter values predicate)
  · exact exactForgeryMissingPrimaryProbeTrace_all_probes baseTrace result

noncomputable def globalFirstLaneTraceLoggingImpl :
    QueryImpl GlobalFirstLaneWorld
      (StateT (FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
        (OracleComp GlobalFirstLaneWorld)) :=
  fun input => StateT.mk fun trace => do
    let output ← liftM (GlobalFirstLaneWorld.query input)
    pure (output, trace ++ FirstLaneOracleSimulation.traceFragment input output)

theorem simulate_eagerTrace_traceLogging_query
    (table : GlobalChainValueIndex → Digest)
    (input : GlobalFirstLaneWorld.Domain)
    (trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) :
    (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((globalFirstLaneTraceLoggingImpl input).run trace)).run =
    (fun result => ((result.1, trace ++ result.2), result.2)) <$>
      (FirstLaneOracleSimulation.eagerTraceImpl table input).run := by
  cases input <;> simp [globalFirstLaneTraceLoggingImpl,
    FirstLaneOracleSimulation.eagerTraceImpl,
    FirstLaneOracleSimulation.eagerImpl,
    FirstLaneOracleSimulation.traceFragment,
    QueryImpl.withTraceAppend_apply]

theorem simulate_eagerTrace_traceLogging_aux
    (table : GlobalChainValueIndex → Digest)
    (initial : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (computation : OracleComp GlobalFirstLaneWorld α) :
    (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((simulateQ globalFirstLaneTraceLoggingImpl computation).run initial)).run =
    (fun result => ((result.1, initial ++ result.2), result.2)) <$>
      (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        computation).run := by
  induction computation using OracleComp.inductionOn generalizing initial with
  | pure value => simp [globalFirstLaneTraceLoggingImpl]
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind]
      simp only [simulateQ_liftM_query, simulateQ_bind, WriterT.run_bind',
        map_bind]
      have hloggingQuery :
          globalFirstLaneTraceLoggingImpl.mapQuery
              (liftM (OracleSpec.query input)) =
            globalFirstLaneTraceLoggingImpl input := rfl
      have heagerQuery :
          (FirstLaneOracleSimulation.eagerTraceImpl table).mapQuery
              (liftM (OracleSpec.query input)) =
            FirstLaneOracleSimulation.eagerTraceImpl table input := by
        cases input <;> rfl
      rw [hloggingQuery, heagerQuery]
      rw [simulate_eagerTrace_traceLogging_query]
      simp only [map_eq_bind_pure_comp]
      rw [bind_assoc]
      apply bind_congr
      intro output
      simp only [Function.comp_apply, pure_bind]
      rw [ih output.1]
      simp [map_eq_bind_pure_comp, bind_assoc, List.append_assoc]

theorem simulate_eagerTrace_traceLogging
    (table : GlobalChainValueIndex → Digest)
    (computation : OracleComp GlobalFirstLaneWorld α) :
    (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((simulateQ globalFirstLaneTraceLoggingImpl computation).run [])).run =
    (fun result => ((result.1, result.2), result.2)) <$>
      (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        computation).run := by
  simpa using simulate_eagerTrace_traceLogging_aux table [] computation

noncomputable def globalFirstLaneExactTracedMissingPublicProgram
    (adversary : Adversary Concrete.scheme) :
    OracleComp GlobalFirstLaneWorld GlobalFirstLaneExactTracedResult := do
  let logged ← (simulateQ globalFirstLaneTraceLoggingImpl
    (globalFirstLaneExactTracedProgram adversary)).run []
  let _ ← globalFirstLaneLiftRevealProbe
    (RevealProbeOracleSimulation.emitObservedTrace
      (exactForgeryMissingPrimaryProbeTrace logged.2 logged.1))
  pure logged.1

noncomputable def appendMissingExactPublicTrace
    (result : GlobalFirstLaneExactPublicEagerResult) :
    GlobalFirstLaneExactPublicEagerResult :=
  (result.1, (result.2.1, result.2.2 ++
    liftGlobalChainTrace
      (exactForgeryMissingPrimaryProbeTrace result.2.2 result.2.1)))

theorem simulate_eagerTrace_bind_lift_emitObservedTrace_project
    (table : GlobalChainValueIndex → Digest)
    (computation : OracleComp GlobalFirstLaneWorld α)
    (suffix : α →
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (project : α → β)
    (hagrees : ∀ result, RevealProbeOracleSimulation.TraceAgrees table
      (suffix result)) :
    (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table) (do
      let result ← computation
      let _ ← globalFirstLaneLiftRevealProbe
        (RevealProbeOracleSimulation.emitObservedTrace (suffix result))
      pure (project result))).run =
    (fun result =>
      (project result.1,
        result.2 ++ liftGlobalChainTrace (suffix result.1))) <$>
      (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        computation).run := by
  rw [simulateQ_bind, WriterT.run_bind']
  apply bind_congr
  intro result
  rcases result with ⟨result, trace⟩
  simp only [Function.comp_apply]
  rw [simulateQ_bind, WriterT.run_bind']
  rw [simulate_eagerTrace_lift_emitObservedTrace table (suffix result)
    (hagrees result)]
  simp only [simulateQ_pure, WriterT.run_pure', map_pure, pure_bind,
    Prod.map_apply, id_eq]
  change (pure (project result,
      trace ++ (liftGlobalChainTrace (suffix result) ++ [])) : ProbComp _) =
    pure (project result, trace ++ liftGlobalChainTrace (suffix result))
  rw [List.append_nil]

theorem eagerExperiment_globalFirstLaneExactTracedMissingPublicProgram_eq_append
    (adversary : Adversary Concrete.scheme) :
    FirstLaneOracleSimulation.eagerExperiment
      (globalFirstLaneExactTracedMissingPublicProgram adversary) =
    appendMissingExactPublicTrace <$>
      FirstLaneOracleSimulation.eagerExperiment
        (globalFirstLaneExactTracedProgram adversary) := by
  unfold globalFirstLaneExactTracedMissingPublicProgram
    FirstLaneOracleSimulation.eagerExperiment
  simp only [map_bind]
  apply bind_congr
  intro table
  rw [simulate_eagerTrace_bind_lift_emitObservedTrace_project table
    ((simulateQ globalFirstLaneTraceLoggingImpl
      (globalFirstLaneExactTracedProgram adversary)).run [])
    (fun logged => exactForgeryMissingPrimaryProbeTrace logged.2 logged.1)
    Prod.fst
    (fun logged => exactForgeryMissingPrimaryProbeTrace_agrees table logged.2
      logged.1)]
  rw [simulate_eagerTrace_traceLogging]
  simp [appendMissingExactPublicTrace, map_eq_bind_pure_comp, bind_assoc]

variable {Index : Type} [Fintype Index] [DecidableEq Index]

def replayChainObserved
    (table : Index → Digest) : AdaptiveRevealMonitor.State Index →
      RevealProbeOracleSimulation.ActionTrace Index →
      Option (AdaptiveRevealMonitor.State Index)
  | state, [] => some state
  | state, .probe index target :: rest =>
      match state.revealed index with
      | some _ => replayChainObserved table state rest
      | none => replayChainObserved table (state.addPending index target) rest
  | state, .reveal index _ :: rest =>
      match state.revealed index with
      | some _ => replayChainObserved table state rest
      | none =>
          if table index ∈ state.pending index then none
          else replayChainObserved table (state.install index (table index)) rest

theorem runObserved_eq_replayChainObserved
    (table : Index → Digest) (state : AdaptiveRevealMonitor.State Index)
    (trace : RevealProbeOracleSimulation.ActionTrace Index) :
    RevealProbeOracleSimulation.runObserved table state trace =
      match replayChainObserved table state trace with
      | none => true
      | some finalState => RevealProbeOracleSimulation.tableHits finalState table := by
  induction trace generalizing state with
  | nil => rfl
  | cons action rest ih =>
      cases action with
      | probe index target =>
          cases hrevealed : state.revealed index <;>
            simp [RevealProbeOracleSimulation.runObserved,
              replayChainObserved, hrevealed, ih]
      | reveal index value =>
          cases hrevealed : state.revealed index with
          | some revealed =>
              simp [RevealProbeOracleSimulation.runObserved,
                replayChainObserved, hrevealed, ih]
          | none =>
              by_cases hhit : table index ∈ state.pending index
              · simp [RevealProbeOracleSimulation.runObserved,
                  replayChainObserved, hrevealed, hhit]
              · simp [RevealProbeOracleSimulation.runObserved,
                  replayChainObserved, hrevealed, hhit, ih]

theorem replayChainObserved_append
    (table : Index → Digest) (state : AdaptiveRevealMonitor.State Index)
    (left right : RevealProbeOracleSimulation.ActionTrace Index) :
    replayChainObserved table state (left ++ right) =
      (replayChainObserved table state left).bind fun middle =>
        replayChainObserved table middle right := by
  induction left generalizing state with
  | nil => rfl
  | cons action left ih =>
      cases action with
      | probe index target =>
          cases hrevealed : state.revealed index <;>
            simp [replayChainObserved, hrevealed, ih]
      | reveal index value =>
          cases hrevealed : state.revealed index with
          | some revealed => simp [replayChainObserved, hrevealed, ih]
          | none =>
              by_cases hhit : table index ∈ state.pending index <;>
                simp [replayChainObserved, hrevealed, hhit, ih]

theorem replayChainObserved_revealed_persists
    (table : Index → Digest) (state finalState : AdaptiveRevealMonitor.State Index)
    (trace : RevealProbeOracleSimulation.ActionTrace Index)
    (index : Index) (hrevealed : state.revealed index ≠ none)
    (hreplay : replayChainObserved table state trace = some finalState) :
    finalState.revealed index ≠ none := by
  induction trace generalizing state with
  | nil =>
      simp [replayChainObserved] at hreplay
      subst finalState
      exact hrevealed
  | cons action rest ih =>
      cases action with
      | probe candidate target =>
          cases hcandidate : state.revealed candidate with
          | some value =>
              apply ih state hrevealed
              simpa [replayChainObserved, hcandidate] using hreplay
          | none =>
              apply ih (state.addPending candidate target)
              · simpa [AdaptiveRevealMonitor.State.addPending] using hrevealed
              · simpa [replayChainObserved, hcandidate] using hreplay
      | reveal candidate value =>
          cases hcandidate : state.revealed candidate with
          | some revealed =>
              apply ih state hrevealed
              simpa [replayChainObserved, hcandidate] using hreplay
          | none =>
              by_cases hhit : table candidate ∈ state.pending candidate
              · simp [replayChainObserved, hcandidate, hhit] at hreplay
              · apply ih (state.install candidate (table candidate))
                · by_cases heq : candidate = index
                  · subst candidate
                    exact False.elim (hrevealed hcandidate)
                  · simpa [AdaptiveRevealMonitor.State.install,
                      Function.update_of_ne (Ne.symm heq)] using hrevealed
                · simpa [replayChainObserved, hcandidate, hhit] using hreplay

theorem replayChainObserved_pending_persists
    (table : Index → Digest) (state finalState : AdaptiveRevealMonitor.State Index)
    (trace : RevealProbeOracleSimulation.ActionTrace Index)
    (index : Index) (target : Digest)
    (hpending : target ∈ state.pending index)
    (hreplay : replayChainObserved table state trace = some finalState) :
    finalState.revealed index ≠ none ∨ target ∈ finalState.pending index := by
  induction trace generalizing state with
  | nil =>
      simp [replayChainObserved] at hreplay
      subst finalState
      exact Or.inr hpending
  | cons action rest ih =>
      cases action with
      | probe candidate candidateTarget =>
          cases hrevealed : state.revealed candidate with
          | some value =>
              apply ih state hpending
              simpa [replayChainObserved, hrevealed] using hreplay
          | none =>
              apply ih (state.addPending candidate candidateTarget)
              · by_cases heq : candidate = index
                · subst candidate
                  simpa [AdaptiveRevealMonitor.State.addPending] using
                    Finset.mem_insert_of_mem hpending
                · simpa [AdaptiveRevealMonitor.State.addPending,
                    Function.update_of_ne (Ne.symm heq)] using hpending
              · simpa [replayChainObserved, hrevealed] using hreplay
      | reveal candidate value =>
          cases hrevealed : state.revealed candidate with
          | some revealed =>
              apply ih state hpending
              simpa [replayChainObserved, hrevealed] using hreplay
          | none =>
              by_cases hhit : table candidate ∈ state.pending candidate
              · simp [replayChainObserved, hrevealed, hhit] at hreplay
              · by_cases heq : candidate = index
                · subst candidate
                  left
                  apply replayChainObserved_revealed_persists table
                    (state.install index (table index)) finalState rest index
                  · simp [AdaptiveRevealMonitor.State.install]
                  · simpa [replayChainObserved, hrevealed, hhit] using hreplay
                · apply ih (state.install candidate (table candidate))
                  · simpa [AdaptiveRevealMonitor.State.install,
                      Function.update_of_ne (Ne.symm heq)] using hpending
                  · simpa [replayChainObserved, hrevealed, hhit] using hreplay

theorem replayChainObserved_mem_probe
    (table : Index → Digest) (state finalState : AdaptiveRevealMonitor.State Index)
    (trace : RevealProbeOracleSimulation.ActionTrace Index)
    (index : Index) (target : Digest)
    (hmem : .probe index target ∈ trace)
    (hreplay : replayChainObserved table state trace = some finalState) :
    finalState.revealed index ≠ none ∨ target ∈ finalState.pending index := by
  induction trace generalizing state with
  | nil => simp at hmem
  | cons action rest ih =>
      cases action with
      | probe candidate candidateTarget =>
          rw [List.mem_cons] at hmem
          cases hrevealed : state.revealed candidate with
          | some value =>
              rcases hmem with heq | htail
              · cases heq
                left
                apply replayChainObserved_revealed_persists table state finalState
                  rest index
                · simp [hrevealed]
                · simpa [replayChainObserved, hrevealed] using hreplay
              · apply ih state htail
                simpa [replayChainObserved, hrevealed] using hreplay
          | none =>
              rcases hmem with heq | htail
              · cases heq
                apply replayChainObserved_pending_persists table
                  (state.addPending index target) finalState rest index target
                · simp [AdaptiveRevealMonitor.State.addPending]
                · simpa [replayChainObserved, hrevealed] using hreplay
              · apply ih (state.addPending candidate candidateTarget) htail
                simpa [replayChainObserved, hrevealed] using hreplay
      | reveal candidate value =>
          have htail : .probe index target ∈ rest := by simpa using hmem
          cases hrevealed : state.revealed candidate with
          | some revealed =>
              apply ih state htail
              simpa [replayChainObserved, hrevealed] using hreplay
          | none =>
              by_cases hhit : table candidate ∈ state.pending candidate
              · simp [replayChainObserved, hrevealed, hhit] at hreplay
              · apply ih (state.install candidate (table candidate)) htail
                simpa [replayChainObserved, hrevealed, hhit] using hreplay

theorem addPending_eq_self_of_mem
    (state : AdaptiveRevealMonitor.State Index) (index : Index) (target : Digest)
    (hmem : target ∈ state.pending index) :
    state.addPending index target = state := by
  unfold AdaptiveRevealMonitor.State.addPending
  have hinsert : insert target (state.pending index) = state.pending index :=
    Finset.insert_eq_self.mpr hmem
  rw [hinsert]
  cases state
  congr
  exact Function.update_eq_self index _

theorem replayChainObserved_insert_seen_probe
    (table : Index → Digest) (state : AdaptiveRevealMonitor.State Index)
    (before after : RevealProbeOracleSimulation.ActionTrace Index)
    (index : Index) (target : Digest)
    (hmem : .probe index target ∈ before) :
    replayChainObserved table state
        (before ++ .probe index target :: after) =
      replayChainObserved table state (before ++ after) := by
  rw [replayChainObserved_append, replayChainObserved_append]
  cases hreplay : replayChainObserved table state before with
  | none => simp
  | some finalState =>
      have hseen := replayChainObserved_mem_probe table state finalState before
        index target hmem hreplay
      simp only [Option.bind_some]
      rcases hseen with hrevealed | hpending
      · cases hvalue : finalState.revealed index with
        | none => exact False.elim (hrevealed hvalue)
        | some value => simp [replayChainObserved, hvalue]
      · have hhidden : finalState.revealed index = none ∨
            finalState.revealed index ≠ none := eq_or_ne _ _
        rcases hhidden with hhidden | hrevealed
        · simp only [replayChainObserved, hhidden]
          rw [show finalState.addPending index target = finalState from
              addPending_eq_self_of_mem finalState index target hpending]
        · cases hvalue : finalState.revealed index with
          | none => exact False.elim (hrevealed hvalue)
          | some value => simp [replayChainObserved, hvalue]

theorem replayChainObserved_filter_seen_probes
    (table : Index → Digest) (state : AdaptiveRevealMonitor.State Index)
    (original current suffix : RevealProbeOracleSimulation.ActionTrace Index)
    (hcurrent : ∀ action ∈ original, action ∈ current)
    (hprobes : ∀ action ∈ suffix, ∃ index target, action = .probe index target) :
    replayChainObserved table state
        (current ++ suffix.filter fun action => action ∉ original) =
      replayChainObserved table state (current ++ suffix) := by
  induction suffix generalizing current with
  | nil => simp
  | cons action rest ih =>
      obtain ⟨index, target, rfl⟩ := hprobes action (by simp)
      have hrest : ∀ candidate ∈ rest,
          ∃ index target, candidate = .probe index target := by
        intro candidate hcandidate
        exact hprobes candidate (by simp [hcandidate])
      by_cases hseen : RevealProbeOracleSimulation.ObservedAction.probe
          index target ∈ original
      · simp only [List.filter_cons]
        rw [if_neg (by simp [hseen])]
        rw [ih current hcurrent hrest]
        exact (replayChainObserved_insert_seen_probe table state current rest
          index target (hcurrent _ hseen)).symm
      · simp only [List.filter_cons]
        rw [if_pos (by simp [hseen])]
        have htail := ih (current ++ [.probe index target])
          (fun candidate hcandidate =>
            List.mem_append_left _ (hcurrent candidate hcandidate)) hrest
        simpa [List.append_assoc] using htail

theorem runObserved_filter_seen_probes
    (table : Index → Digest) (state : AdaptiveRevealMonitor.State Index)
    (before after : RevealProbeOracleSimulation.ActionTrace Index)
    (hprobes : ∀ action ∈ after, ∃ index target, action = .probe index target) :
    RevealProbeOracleSimulation.runObserved table state
        (before ++ after.filter fun action => action ∉ before) =
      RevealProbeOracleSimulation.runObserved table state (before ++ after) := by
  rw [runObserved_eq_replayChainObserved,
    runObserved_eq_replayChainObserved,
    replayChainObserved_filter_seen_probes table state before before after
      (fun _ hmem => hmem) hprobes]

theorem exactForgeryMissingPrimaryProbeTrace_eq_chainFilter
    (baseTrace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (result : GlobalHighDirectExactTracedResult) :
    exactForgeryMissingPrimaryProbeTrace baseTrace result =
      (globalHighDirectExactForgeryPrimaryProbeTrace result).filter fun action =>
        action ∉ baseTrace.chainActions := by
  unfold exactForgeryMissingPrimaryProbeTrace
  apply List.filter_congr
  intro action _haction
  by_cases hmem : (.chain action :
      FirstLaneOracleSimulation.ObservedAction GlobalChainValueIndex) ∈ baseTrace
  · have hchain := chainAction_mem_chainActions hmem
    simp [hmem, hchain]
  · have hchain : action ∉ baseTrace.chainActions := fun haction =>
      hmem (chainAction_mem_of_mem_chainActions haction)
    simp [hmem, hchain]

theorem combinedHit_appendMissingExactPublicTrace_iff_full
    (result : GlobalFirstLaneExactPublicEagerResult) :
    FirstLaneOracleSimulation.CombinedHit
        (appendMissingExactPublicTrace result).1
        (appendMissingExactPublicTrace result).2.2 ↔
      FirstLaneOracleSimulation.CombinedHit
        (appendGlobalFirstLaneExactPublicTrace result).1
        (appendGlobalFirstLaneExactPublicTrace result).2.2 := by
  have hprobes : ∀ action ∈
      globalHighDirectExactForgeryPrimaryProbeTrace result.2.1,
      ∃ index target, action = .probe index target := by
    intro action haction
    unfold globalHighDirectExactForgeryPrimaryProbeTrace
      globalHighDirectForgeryPrimaryProbeTrace globalForgeryPrimaryProbeTrace
      at haction
    rw [List.mem_ofFn] at haction
    obtain ⟨chain, rfl⟩ := haction
    exact ⟨_, _, rfl⟩
  have hchain := runObserved_filter_seen_probes result.1
    AdaptiveRevealMonitor.State.empty result.2.2.chainActions
      (globalHighDirectExactForgeryPrimaryProbeTrace result.2.1) hprobes
  rw [← exactForgeryMissingPrimaryProbeTrace_eq_chainFilter
    result.2.2 result.2.1] at hchain
  unfold FirstLaneOracleSimulation.CombinedHit
    appendMissingExactPublicTrace appendGlobalFirstLaneExactPublicTrace
  simp only [FirstLaneOracleSimulation.ActionTrace.encodingActions_append,
    FirstLaneOracleSimulation.ActionTrace.chainActions_append,
    liftGlobalChainTrace_encodingActions, liftGlobalChainTrace_chainActions,
    List.append_nil]
  rw [hchain]

noncomputable def globalFirstLaneExactCoupledMissingPublicProjection
    (result : GlobalFirstLaneExactCoupledProgramResult) :
    GlobalFirstLaneExactPublicEagerResult :=
  appendMissingExactPublicTrace (globalFirstLaneExactCoupledProjection result)

theorem hazardCount_globalFirstLaneExactCoupledMissingPublicProjection
    (result : GlobalFirstLaneExactCoupledProgramResult) :
    FirstLaneOracleSimulation.hazardCount
        (globalFirstLaneExactCoupledMissingPublicProjection result).2.2 =
      FirstLaneOracleSimulation.hazardCount result.2.2 +
        (exactForgeryMissingPrimaryChains result.2.2
          ((result.1.1.1, result.1.2), result.2.1)).card := by
  simp [globalFirstLaneExactCoupledMissingPublicProjection,
    appendMissingExactPublicTrace, globalFirstLaneExactCoupledProjection,
    FirstLaneOracleSimulation.hazardCount_append]

noncomputable def exactForgeryTerminalProbeTrace
    (result : GlobalHighDirectExactTracedResult) :
    RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex :=
  (TargetSum.terminalChains (exactForgeryEncoding result)).toList.map fun chain =>
    .probe (chain, result.2.1.1.epoch, exactForgeryEncoding result chain)
      (result.2.1.1.signature.chainValue chain)

theorem exactForgeryTerminalProbeTrace_all_probes
    (result : GlobalHighDirectExactTracedResult)
    (action : RevealProbeOracleSimulation.ObservedAction GlobalChainValueIndex)
    (haction : action ∈ exactForgeryTerminalProbeTrace result) :
    ∃ index target, action = .probe index target := by
  unfold exactForgeryTerminalProbeTrace at haction
  rw [List.mem_map] at haction
  obtain ⟨chain, _hchain, rfl⟩ := haction
  exact ⟨_, _, rfl⟩

theorem exactForgeryTerminalProbeTrace_agrees
    (table : GlobalChainValueIndex → Digest)
    (result : GlobalHighDirectExactTracedResult) :
    RevealProbeOracleSimulation.TraceAgrees table
      (exactForgeryTerminalProbeTrace result) := by
  apply traceAgrees_of_all_probes
  intro action haction
  exact exactForgeryTerminalProbeTrace_all_probes result action haction

@[simp]
theorem observedProbeCount_exactForgeryTerminalProbeTrace
    (result : GlobalHighDirectExactTracedResult) :
    RevealProbeOracleSimulation.observedProbeCount
      (exactForgeryTerminalProbeTrace result) =
        (TargetSum.terminalChains (exactForgeryEncoding result)).card := by
  have hcount : ∀ trace : RevealProbeOracleSimulation.ActionTrace
      GlobalChainValueIndex,
      (∀ action ∈ trace, ∃ index target, action = .probe index target) →
      RevealProbeOracleSimulation.observedProbeCount trace = trace.length := by
    intro trace hprobes
    induction trace with
    | nil => rfl
    | cons action rest ih =>
        obtain ⟨index, target, rfl⟩ := hprobes action (by simp)
        simp only [RevealProbeOracleSimulation.observedProbeCount,
          List.length_cons, Nat.succ.injEq]
        apply ih
        intro candidate hcandidate
        exact hprobes candidate (by simp [hcandidate])
  rw [hcount]
  · simp [exactForgeryTerminalProbeTrace]
  · exact exactForgeryTerminalProbeTrace_all_probes result

noncomputable def globalFirstLaneExactTracedTerminalPublicProgram
    (adversary : Adversary Concrete.scheme) :
    OracleComp GlobalFirstLaneWorld GlobalFirstLaneExactTracedResult := do
  let result ← globalFirstLaneExactTracedProgram adversary
  let _ ← globalFirstLaneLiftRevealProbe
    (RevealProbeOracleSimulation.emitObservedTrace
      (exactForgeryTerminalProbeTrace result))
  pure result

noncomputable def appendTerminalExactPublicTrace
    (result : GlobalFirstLaneExactPublicEagerResult) :
    GlobalFirstLaneExactPublicEagerResult :=
  (result.1, (result.2.1, result.2.2 ++
    liftGlobalChainTrace (exactForgeryTerminalProbeTrace result.2.1)))

theorem eagerExperiment_globalFirstLaneExactTracedTerminalPublicProgram_eq_append
    (adversary : Adversary Concrete.scheme) :
    FirstLaneOracleSimulation.eagerExperiment
      (globalFirstLaneExactTracedTerminalPublicProgram adversary) =
    appendTerminalExactPublicTrace <$>
      FirstLaneOracleSimulation.eagerExperiment
        (globalFirstLaneExactTracedProgram adversary) := by
  unfold globalFirstLaneExactTracedTerminalPublicProgram
    FirstLaneOracleSimulation.eagerExperiment
  simp only [map_bind]
  apply bind_congr
  intro table
  rw [simulate_eagerTrace_bind_lift_emitObservedTrace_keep table
    (globalFirstLaneExactTracedProgram adversary)
    exactForgeryTerminalProbeTrace
    (exactForgeryTerminalProbeTrace_agrees table)]
  simp [appendTerminalExactPublicTrace, map_eq_bind_pure_comp, bind_assoc]

noncomputable def globalFirstLaneExactCoupledTerminalPublicProjection
    (result : GlobalFirstLaneExactCoupledProgramResult) :
    GlobalFirstLaneExactPublicEagerResult :=
  appendTerminalExactPublicTrace
    (globalFirstLaneExactCoupledProjection result)

theorem hazardCount_coupledTerminalPublicProjection
    (result : GlobalFirstLaneExactCoupledProgramResult) :
    FirstLaneOracleSimulation.hazardCount
        (globalFirstLaneExactCoupledTerminalPublicProjection result).2.2 =
      FirstLaneOracleSimulation.hazardCount result.2.2 +
        (TargetSum.terminalChains
          (exactForgeryEncoding
            ((result.1.1.1, result.1.2), result.2.1))).card := by
  simp [globalFirstLaneExactCoupledTerminalPublicProjection,
    appendTerminalExactPublicTrace, globalFirstLaneExactCoupledProjection,
    FirstLaneOracleSimulation.hazardCount_append,
    liftGlobalChainTrace_hazardCount]

theorem sourceUnloggedDetailedGameAfterKeygen_hashQueryBound_post
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hpost : HasPostKeygenHashQueryBound Concrete.scheme adversary q)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅)) :
    (sourceUnloggedDetailedGameAfterKeygen adversary keyResult.1.1 keyResult.1.2)
      |>.IsQueryBoundP (· matches .inr _) q := by
  have hkeySupport : keyResult.1 ∈ support Concrete.scheme.keygen := by
    apply support_simulateQ_run'_subset xmssRomImpl Concrete.scheme.keygen ∅
    rw [StateT.run'_eq, support_map]
    exact ⟨keyResult, hkeyResult, rfl⟩
  have hcontinuation :=
    (hasPostKeygenHashQueryBound_iff_detailedGameAfterKeygen
      Concrete.scheme adversary q).mp hpost keyResult.1 hkeySupport
  exact (OracleComp.isQueryBoundP_iff_of_map_eq
    (detailedGameAfterKeygen_unlogged_projection adversary keyResult.1.1
      keyResult.1.2)).mp hcontinuation

theorem relTriple_sourceGlobalExact_firstLane_program_boundedHit_post
    (q hitLimit : Nat) (adversary : Adversary Concrete.scheme)
    (hpost : HasPostKeygenHashQueryBound Concrete.scheme adversary q)
    (hlimits : q ≤ hitLimit) :
    OracleComp.ProgramLogic.Relational.RelTriple
      (sourceGlobalExactTracedProgram adversary)
      (globalFirstLaneExactCoupledProgram adversary)
      (SourceFirstLaneExactBoundedProgramRelation q hitLimit) := by
  unfold sourceGlobalExactTracedProgram globalFirstLaneExactCoupledProgram
  apply OracleComp.ProgramLogic.Relational.relTriple_bind
    (XmssSecurity.relTriple_with_support
      relTriple_trajectoryProgrammedGlobalChainKeygen_withBaseHigh_stable)
  intro left right hkeygen
  obtain ⟨hrel, hleftSupport, hrightSupport⟩ := hkeygen
  have hrightViewSupport :=
    coupledGlobalChainKeygenWithBaseHighFull_support_keyView right hrightSupport
  have hleftKeyResult :=
    trajectoryProgrammedGlobalChainKeygen_support_keyResult left hleftSupport
  have hmaterializedKeyResult :
      Concrete.materializeCachedKeyResult left.keyResult ∈ support
        ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅) :=
    Concrete.oldKeygen_support_materializedPrecomputedKeygen
      left.keyResult hleftKeyResult
  have hsourceBound :=
    sourceUnloggedDetailedGameAfterKeygen_hashQueryBound_post q adversary hpost
      (Concrete.materializeCachedKeyResult left.keyResult)
        hmaterializedKeyResult
  apply OracleComp.ProgramLogic.Relational.relTriple_bind
    (relTriple_sourceExact_firstLane_detailedExecution_boundedHit q hitLimit
      adversary left right hrel hleftSupport hrightViewSupport hsourceBound
        hlimits)
  intro leftExecution rightExecution hexecution
  apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure
  exact ⟨hrel, hexecution⟩

theorem sourceGlobalExactTracedProgram_attacker_reserve
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hpost : HasPostKeygenHashQueryBound Concrete.scheme adversary q)
    (result : SourceGlobalExactTracedProgramResult)
    (hresult : result ∈ support (sourceGlobalExactTracedProgram adversary)) :
    result.2.2.2.hashInputs.length +
        (1 + verificationChainHashes + 1 + treeHeight) ≤ q := by
  unfold sourceGlobalExactTracedProgram at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨keyView, hkeyView, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨execution, hexecution, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  have hkeyResult :=
    trajectoryProgrammedGlobalChainKeygen_support_keyResult keyView hkeyView
  have hmaterializedKeyResult :
      Concrete.materializeCachedKeyResult keyView.keyResult ∈ support
        ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅) :=
    Concrete.oldKeygen_support_materializedPrecomputedKeygen
      keyView.keyResult hkeyResult
  have hsourceBound :=
    sourceUnloggedDetailedGameAfterKeygen_hashQueryBound_post q adversary hpost
      (Concrete.materializeCachedKeyResult keyView.keyResult)
        hmaterializedKeyResult
  unfold sourceGlobalExactTracedDetailedExecution at hexecution
  rw [mem_support_bind_iff] at hexecution
  obtain ⟨handled, hhandled, hverifyBlock⟩ := hexecution
  rw [mem_support_bind_iff] at hverifyBlock
  obtain ⟨verified, hverified, hfinal⟩ := hverifyBlock
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst execution
  let finish : Forgery → OracleComp OracleWorld (Forgery × Bool) :=
    fun forgery => Prod.mk forgery <$> Concrete.scheme.verify keyView.publicKey
      forgery.epoch forgery.message forgery.signature
  have hfullBound : (simulateQ
      (sourceUnloggedMappedAdversaryImpl keyView.publicKey
        (Concrete.materializePrecomputation keyView.cache keyView.secretKey))
        (adversary.main keyView.publicKey) >>= finish).IsQueryBoundP
          (· matches .inr _) q := by
    unfold sourceUnloggedDetailedGameAfterKeygen at hsourceBound
    exact hsourceBound
  let initialState : SourceExactTracedState :=
    ((((keyView.cache, []), []), []))
  have hresidual :=
    cappedBothTracedMappedAdversaryImpl_residual_hashQueryBound
      keyView.publicKey
        (Concrete.materializePrecomputation keyView.cache keyView.secretKey)
      (adversary.main keyView.publicKey) finish q hfullBound initialState
        (by rfl) handled hhandled
  have hverifyBound :
      (Concrete.scheme.verify keyView.publicKey handled.1.epoch
        handled.1.message handled.1.signature).IsQueryBoundP
          (· matches .inr _) (q - handled.2.2.hashInputs.length) := by
    unfold finish at hresidual
    exact (OracleComp.isQueryBoundP_map_iff _ _ _).mp hresidual.2
  have hfloor := Concrete.verify_hashQueryBound_at_least_fullVerification
    keyView.publicKey handled.1.epoch handled.1.message handled.1.signature
      (q - handled.2.2.hashInputs.length) hverifyBound
  have htrace : verified.2.2 = handled.2.2 := by
    rw [sourceSigningTracedVerifierImpl_run_eq] at hverified
    rw [support_map] at hverified
    obtain ⟨baseResult, _hbase, heq⟩ := hverified
    simpa [sourceExactSigningProjection] using
      (congrArg (fun candidate => candidate.2.2) heq).symm
  simp only
  rw [htrace]
  omega

theorem sourceWinningExactFirstLane_right_encoding_valid
    (adversary : Adversary Concrete.scheme)
    (left : SourceGlobalExactTracedProgramResult)
    (right : GlobalFirstLaneExactCoupledProgramResult)
    (hleftSupport : left ∈ support
      (sourceGlobalExactTracedProgram adversary))
    (hrightSupport : right ∈ support
      (globalFirstLaneExactCoupledProgram adversary))
    (hkey : ProgrammedGlobalChainKeygenBaseHighStableRelation left.1 right.1)
    (hgood : left.2.1 = right.2.1.1 ∧
      SourceFirstLaneExactGoodStateRelation left.1 right.1.1 left.2.2
        right.2.1.2 right.2.2)
    (hevent : SourceWinningExactFirstLaneEvent left) :
    TargetSum.Valid
      (exactForgeryEncoding ((right.1.1.1, right.1.2), right.2.1)) := by
  let both := sourceGlobalExactProgramResult left
  have hdecodeBoth : ∃ encoding, TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash
        (cappedBothEncodingProjection both).2.1.1
        (cappedBothEncodingProjection both).1.secretKey.parameter
        (cappedBothEncodingProjection both).1.forgery.epoch
        ((cappedBothEncodingProjection both).1.forgery.message,
          (cappedBothEncodingProjection both).1.forgery.signature.randomness)) =
        some encoding := by
    unfold SourceWinningExactFirstLaneEvent WinningExactFirstLaneBadEventOccurs
      at hevent
    rcases hevent with hencoding | hchain
    · exact hencoding.1.forgery_decode
    · obtain ⟨chain, hwinning, _hrevealed⟩ := hchain
      exact hwinning.forgery_decode
  obtain ⟨encoding, hdecodeBoth⟩ := hdecodeBoth
  have hdecodeLeft : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash left.2.2.1.1.1
        left.1.secretKey.parameter left.2.1.1.epoch
        (left.2.1.1.message, left.2.1.1.signature.randomness)) =
        some encoding := by
    simpa [both, cappedBothEncodingProjection, sourceGlobalExactProgramResult,
      sourceGlobalExactExecutionResult, Concrete.materializePrecomputation,
      Concrete.precomputedSecretKey] using hdecodeBoth
  have hleftKeySupport : left.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen := by
    unfold sourceGlobalExactTracedProgram at hleftSupport
    rw [mem_support_bind_iff] at hleftSupport
    obtain ⟨keyView, hkeyView, hrest⟩ := hleftSupport
    rw [mem_support_bind_iff] at hrest
    obtain ⟨execution, _hexecution, hpure⟩ := hrest
    simp only [support_pure, Set.mem_singleton_iff] at hpure
    subst left
    exact hkeyView
  obtain ⟨hrightKeySupport, _hrightExecutionSupport⟩ :=
    globalFirstLaneExactCoupledProgram_support_info adversary right hrightSupport
  have hrightViewSupport : right.1.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen :=
    coupledGlobalChainKeygenWithBaseHighFull_support_keyView right.1
      hrightKeySupport
  have hparameter : left.1.secretKey.parameter =
      right.1.1.1.secretKey.parameter :=
    (programmedGlobal_secretKey_parameter_eq left.1 right.1 hkey
      hleftKeySupport hrightViewSupport).symm
  obtain ⟨highState, hsourceHigh, hfirstState, _hchainTrace,
    _hconsistent⟩ := hgood.2
  obtain ⟨_monitor, _hmonitor, _hagrees, _hrevealed, hcausal,
    _hretained⟩ := hsourceHigh.1.1
  have hcache : Concrete.CacheView.encodingHash left.2.2.1.1.1
        left.1.secretKey.parameter left.2.1.1.epoch
        (left.2.1.1.message, left.2.1.1.signature.randomness) =
      Concrete.CacheView.encodingHash right.2.1.2.causalState.cache
        right.1.1.1.secretKey.parameter right.2.1.1.1.epoch
        (right.2.1.1.1.message, right.2.1.1.1.signature.randomness) := by
    unfold Concrete.CacheView.encodingHash Concrete.CacheView.digestAt
    have hhighCache : highState.1.1.causal.cache =
        right.2.1.2.causalState.cache := by
      simpa [globalHighExactStateProjection] using
        (congrArg (fun state => state.causalState.cache) hfirstState).symm
    rw [← hgood.1, ← hparameter, ← hhighCache]
    have hcacheAt := hcausal.1
      (Concrete.CacheView.encodingInput left.1.secretKey.parameter
        left.2.1.1.epoch
        (left.2.1.1.message, left.2.1.1.signature.randomness))
      ⟨left.2.1.1.epoch, left.2.1.1.message,
        left.2.1.1.signature.randomness, rfl⟩
    change left.2.2.1.1.1
        (Concrete.CacheView.encodingInput left.1.secretKey.parameter
          left.2.1.1.epoch
          (left.2.1.1.message, left.2.1.1.signature.randomness)) =
      highState.1.1.causal.cache
        (Concrete.CacheView.encodingInput left.1.secretKey.parameter
          left.2.1.1.epoch
          (left.2.1.1.message, left.2.1.1.signature.randomness)) at hcacheAt
    rw [hcacheAt]
  have hdecodeRight : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash right.2.1.2.causalState.cache
        right.1.1.1.secretKey.parameter right.2.1.1.1.epoch
        (right.2.1.1.1.message, right.2.1.1.1.signature.randomness)) =
      some encoding := by
    rw [← hcache]
    exact hdecodeLeft
  have hencoding := exactForgeryEncoding_eq_of_decode
    ((right.1.1.1, right.1.2), right.2.1) encoding hdecodeRight
  rw [hencoding]
  exact (TargetSum.decodeDigest_eq_some_iff.mp hdecodeRight).2

theorem SourceWinningExactFirstLaneEvent.verified
    (result : SourceGlobalExactTracedProgramResult)
    (hevent : SourceWinningExactFirstLaneEvent result) :
    result.2.1.2 = true := by
  have hwon : (cappedBothEncodingProjection
      (sourceGlobalExactProgramResult result)).1.won = true := by
    unfold SourceWinningExactFirstLaneEvent WinningExactFirstLaneBadEventOccurs
      at hevent
    rcases hevent with hencoding | hchain
    · exact hencoding.1.1
    · obtain ⟨_chain, hwinning, _hrevealed⟩ := hchain
      exact hwinning.1
  have hverified := (GameOutcome.won_eq_true_iff _).mp hwon
  simpa [cappedBothEncodingProjection, sourceGlobalExactProgramResult,
    sourceGlobalExactExecutionResult] using hverified.2.2

theorem SourceFirstLaneExactGoodStateRelation.attackerTrace_eq
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftState : SourceExactTracedState)
    (firstLaneState : GlobalFirstLaneExactTracedState)
    (trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hrel : SourceFirstLaneExactGoodStateRelation left right leftState
      firstLaneState trace) :
    leftState.2 = firstLaneState.attackerTrace := by
  obtain ⟨highState, hhigh, hfirst, _htrace, _hconsistent⟩ := hrel
  have hsource : leftState.2 = highState.1.2 := by
    simpa [GlobalSigningExactMonitoredStateRelation,
      GlobalSigningMonitoredTracedStateRelation,
      GlobalMonitoredTracedStateRelation, sourceExactSigningProjection,
      sourceSigningTracedStateProjection] using hhigh.1.2
  rw [hsource, hfirst]
  rfl

theorem globalFirstLaneExactCoupled_missing_hazardCount_le
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hpost : HasPostKeygenHashQueryBound Concrete.scheme adversary q)
    (left : SourceGlobalExactTracedProgramResult)
    (right : GlobalFirstLaneExactCoupledProgramResult)
    (hleftSupport : left ∈ support
      (sourceGlobalExactTracedProgram adversary))
    (hrightSupport : right ∈ support
      (globalFirstLaneExactCoupledProgram adversary))
    (hgood : left.2.1 = right.2.1.1 ∧
      SourceFirstLaneExactGoodStateRelation left.1 right.1.1 left.2.2
        right.2.1.2 right.2.2)
    (hevent : SourceWinningExactFirstLaneEvent left) :
    FirstLaneOracleSimulation.hazardCount
      (globalFirstLaneExactCoupledMissingPublicProjection right).2.2 ≤ q := by
  have hrun := globalFirstLaneExactCoupled_run_mem_support adversary right
    hrightSupport
  have hverified : right.2.1.1.2 = true := by
    rw [← hgood.1]
    exact hevent.verified
  have hsharp := globalFirstLaneExactTracedProgram_hazard_add_missing_exact
    right.1.1.2 adversary
      (((right.1.1.1, right.1.2), right.2.1), right.2.2) hrun hverified
  change TargetSum.Valid
        (exactForgeryEncoding ((right.1.1.1, right.1.2), right.2.1)) ∧
      FirstLaneOracleSimulation.hazardCount right.2.2 +
          missingPrimaryCount
            (recoverChainPrimaryProbe? right.2.1.1.1.epoch
              (exactForgeryEncoding ((right.1.1.1, right.1.2), right.2.1))
              right.2.1.1.1.signature) right.2.2 ≤
        right.2.1.2.attackerTrace.hashInputs.length +
          (verificationChainHashes + 2) at hsharp
  have hmissing := exactForgeryMissingPrimaryChains_card_le right.2.2
    ((right.1.1.1, right.1.2), right.2.1)
  change (exactForgeryMissingPrimaryChains right.2.2
      ((right.1.1.1, right.1.2), right.2.1)).card ≤
    missingPrimaryCount
        (recoverChainPrimaryProbe? right.2.1.1.1.epoch
          (exactForgeryEncoding ((right.1.1.1, right.1.2), right.2.1))
          right.2.1.1.1.signature) right.2.2 +
      (TargetSum.terminalChains
        (exactForgeryEncoding ((right.1.1.1, right.1.2), right.2.1))).card at hmissing
  have hterminal := TargetSum.terminalChains_card_le_27
    (exactForgeryEncoding ((right.1.1.1, right.1.2), right.2.1)) hsharp.1
  have hreserve := sourceGlobalExactTracedProgram_attacker_reserve q adversary
    hpost left hleftSupport
  have hattacker := hgood.2.attackerTrace_eq
  rw [hazardCount_globalFirstLaneExactCoupledMissingPublicProjection]
  rw [← hattacker] at hsharp
  norm_num [verificationChainHashes, treeHeight] at hsharp hreserve ⊢
  omega

theorem sourceWinningExactFirstLane_good_implies_missing_combinedHit
    (adversary : Adversary Concrete.scheme)
    (left : SourceGlobalExactTracedProgramResult)
    (right : GlobalFirstLaneExactCoupledProgramResult)
    (hleftSupport : left ∈ support
      (sourceGlobalExactTracedProgram adversary))
    (hrightSupport : right ∈ support
      (globalFirstLaneExactCoupledProgram adversary))
    (hkey : ProgrammedGlobalChainKeygenBaseHighStableRelation left.1 right.1)
    (hgood : left.2.1 = right.2.1.1 ∧
      SourceFirstLaneExactGoodStateRelation left.1 right.1.1 left.2.2
        right.2.1.2 right.2.2)
    (hevent : SourceWinningExactFirstLaneEvent left) :
    FirstLaneOracleSimulation.CombinedHit
      (globalFirstLaneExactCoupledMissingPublicProjection right).1
      (globalFirstLaneExactCoupledMissingPublicProjection right).2.2 := by
  have hfull := sourceWinningExactFirstLane_good_implies_public_combinedHit
    adversary left right hleftSupport hrightSupport hkey hgood hevent
  exact (combinedHit_appendMissingExactPublicTrace_iff_full
    (globalFirstLaneExactCoupledProjection right)).mpr hfull

def GlobalFirstLaneExactCoupledMissingEnforcedHit
    (fuel : Nat) (result : GlobalFirstLaneExactCoupledProgramResult) : Prop :=
  FirstLaneOracleSimulation.CombinedHit
    (globalFirstLaneExactCoupledMissingPublicProjection result).1
    (FirstLaneOracleSimulation.enforceHazardTrace fuel
      (globalFirstLaneExactCoupledMissingPublicProjection result).2.2)

theorem sourceWinningExactFirstLane_implies_missing_enforcedHit
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hpost : HasPostKeygenHashQueryBound Concrete.scheme adversary q)
    (left : SourceGlobalExactTracedProgramResult)
    (right : GlobalFirstLaneExactCoupledProgramResult)
    (hleftSupport : left ∈ support
      (sourceGlobalExactTracedProgram adversary))
    (hrightSupport : right ∈ support
      (globalFirstLaneExactCoupledProgram adversary))
    (hrelation : SourceFirstLaneExactBoundedProgramRelation q q left right)
    (hevent : SourceWinningExactFirstLaneEvent left) :
    GlobalFirstLaneExactCoupledMissingEnforcedHit q right := by
  rcases hrelation with ⟨hkey, hgood | hhit⟩
  · have hraw := sourceWinningExactFirstLane_good_implies_missing_combinedHit
      adversary left right hleftSupport hrightSupport hkey
        ⟨hgood.1, hgood.2.1⟩ hevent
    have hcount := globalFirstLaneExactCoupled_missing_hazardCount_le q
      adversary hpost left right hleftSupport hrightSupport
        ⟨hgood.1, hgood.2.1⟩ hevent
    unfold GlobalFirstLaneExactCoupledMissingEnforcedHit
    rw [FirstLaneOracleSimulation.enforceHazardTrace_eq_self_of_count_le
      _ _ hcount]
    exact hraw
  · unfold GlobalFirstLaneExactCoupledMissingEnforcedHit
      globalFirstLaneExactCoupledMissingPublicProjection
      appendMissingExactPublicTrace globalFirstLaneExactCoupledProjection
    exact FirstLaneOracleSimulation.CombinedHit.enforce_append_of_prefix
      right.1.1.2 q right.2.2
        (liftGlobalChainTrace
          (exactForgeryMissingPrimaryProbeTrace right.2.2
            ((right.1.1.1, right.1.2), right.2.1))) hhit

theorem evalDist_globalFirstLaneExactCoupledMissingProjection_eq_eager
    (adversary : Adversary Concrete.scheme) :
    evalDist (globalFirstLaneExactCoupledMissingPublicProjection <$>
      globalFirstLaneExactCoupledProgram adversary) =
    evalDist (FirstLaneOracleSimulation.eagerExperiment
      (globalFirstLaneExactTracedMissingPublicProgram adversary)) := by
  calc
    _ = evalDist (appendMissingExactPublicTrace <$>
        (globalFirstLaneExactCoupledProjection <$>
          globalFirstLaneExactCoupledProgram adversary)) := by
      apply congrArg evalDist
      rw [Functor.map_map]
      rfl
    _ = evalDist (appendMissingExactPublicTrace <$>
        FirstLaneOracleSimulation.eagerExperiment
          (globalFirstLaneExactTracedProgram adversary)) := by
      exact evalDist_map_congr_of_evalDist_eq appendMissingExactPublicTrace _ _
        (evalDist_globalFirstLaneExactCoupledProjection_eq_eagerExperiment
          adversary)
    _ = _ := by
      rw [eagerExperiment_globalFirstLaneExactTracedMissingPublicProgram_eq_append]

def GlobalFirstLaneExactPublicMissingEnforcedHit
    (fuel : Nat) (result : GlobalFirstLaneExactPublicEagerResult) : Prop :=
  FirstLaneOracleSimulation.CombinedHit result.1
    (FirstLaneOracleSimulation.enforceHazardTrace fuel result.2.2)

theorem sourceWinningExactFirstLane_probability_le_missing_enforcedHit
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hpost : HasPostKeygenHashQueryBound Concrete.scheme adversary q) :
    Pr[SourceWinningExactFirstLaneEvent |
        sourceGlobalExactTracedProgram adversary] ≤
      Pr[GlobalFirstLaneExactCoupledMissingEnforcedHit q |
        globalFirstLaneExactCoupledProgram adversary] := by
  apply probEvent_le_of_relTriple
    (XmssSecurity.relTriple_with_support
      (relTriple_sourceGlobalExact_firstLane_program_boundedHit_post q q
        adversary hpost (Nat.le_refl _)))
  intro left right hrelation hevent
  exact sourceWinningExactFirstLane_implies_missing_enforcedHit q adversary
    hpost left right hrelation.2.1 hrelation.2.2 hrelation.1 hevent

theorem coupled_missing_enforcedHit_probability_eq_public_eager
    (fuel : Nat) (adversary : Adversary Concrete.scheme) :
    Pr[GlobalFirstLaneExactCoupledMissingEnforcedHit fuel |
        globalFirstLaneExactCoupledProgram adversary] =
      Pr[GlobalFirstLaneExactPublicMissingEnforcedHit fuel |
        FirstLaneOracleSimulation.eagerExperiment
          (globalFirstLaneExactTracedMissingPublicProgram adversary)] := by
  calc
    _ = Pr[GlobalFirstLaneExactPublicMissingEnforcedHit fuel |
        globalFirstLaneExactCoupledMissingPublicProjection <$>
          globalFirstLaneExactCoupledProgram adversary] := by
      rw [probEvent_map]
      rfl
    _ = _ := probEvent_eq_of_evalDist_eq _
      (evalDist_globalFirstLaneExactCoupledMissingProjection_eq_eager adversary)

theorem public_eager_missing_enforcedHit_probability_le
    (fuel : Nat) (adversary : Adversary Concrete.scheme) :
    Pr[GlobalFirstLaneExactPublicMissingEnforcedHit fuel |
        FirstLaneOracleSimulation.eagerExperiment
          (globalFirstLaneExactTracedMissingPublicProgram adversary)] ≤
      (fuel : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  have hbound :=
    FirstLaneOracleSimulation.eagerExperiment_enforced_combinedHit_probability_le
      fuel (globalFirstLaneExactTracedMissingPublicProgram adversary)
  rw [FirstLaneOracleSimulation.eagerExperiment_enforceHazardBound_eq_map,
    probEvent_map] at hbound
  exact hbound

theorem sourceWinningExactFirstLane_probability_le_postKeygen
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hpost : HasPostKeygenHashQueryBound Concrete.scheme adversary q) :
    Pr[SourceWinningExactFirstLaneEvent |
        sourceGlobalExactTracedProgram adversary] ≤
      (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  calc
    _ ≤ Pr[GlobalFirstLaneExactCoupledMissingEnforcedHit q |
        globalFirstLaneExactCoupledProgram adversary] :=
      sourceWinningExactFirstLane_probability_le_missing_enforcedHit q adversary
        hpost
    _ = Pr[GlobalFirstLaneExactPublicMissingEnforcedHit q |
        FirstLaneOracleSimulation.eagerExperiment
          (globalFirstLaneExactTracedMissingPublicProgram adversary)] :=
      coupled_missing_enforcedHit_probability_eq_public_eager q adversary
    _ ≤ _ := public_eager_missing_enforcedHit_probability_le q adversary

theorem hasPostKeygenExactFirstLaneBound
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hpost : HasPostKeygenHashQueryBound Concrete.scheme adversary q) :
    HasPostKeygenExactFirstLaneBound q adversary := by
  unfold HasPostKeygenExactFirstLaneBound
  rw [cappedExactFirstLane_probability_eq_sourceGlobalExact]
  exact sourceWinningExactFirstLane_probability_le_postKeygen q adversary hpost

theorem hasPostKeygenExactFirstLaneBounds :
    HasPostKeygenExactFirstLaneBounds := by
  intro q adversary hpost
  exact hasPostKeygenExactFirstLaneBound q adversary hpost

theorem concreteScheme_has_postKeygen_127_bits_of_classical_security :
    HasPostKeygenClassicalSecurityBits Concrete.scheme 127 :=
  concreteScheme_has_postKeygen_127_of_firstLaneBounds
    hasPostKeygenExactFirstLaneBounds

end XmssSecurity.CappedChain
