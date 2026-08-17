import XmssSecurity.CappedGlobalChainHighSigningCoupling

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

noncomputable def globalOutsideChainsOnly
    (parameter : PublicParameter) (cache : QueryCache HashSpec) :
    QueryCache HashSpec := fun input =>
  if globalChainInputProbe? parameter input = none then cache input else none

theorem globalOutsideChainsOnly_of_no_probe
    (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (input : HashInput)
    (hprobe : globalChainInputProbe? parameter input = none) :
    globalOutsideChainsOnly parameter cache input = cache input := by
  simp [globalOutsideChainsOnly, hprobe]

theorem globalOutsideChainsOnly_of_probe
    (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (input : HashInput) (probe : GlobalChainValueIndex × Digest)
    (hprobe : globalChainInputProbe? parameter input = some probe) :
    globalOutsideChainsOnly parameter cache input = none := by
  simp [globalOutsideChainsOnly, hprobe]

noncomputable def globalFilteredCausalKeygenState
    (view : ProgrammedGlobalChainKeygenView) : GlobalCausalHashState := by
  classical
  exact {
    cache := fun input =>
      if MerkleHashInput view.secretKey.parameter input then view.cache input
      else none
    keygenCache := view.cache
    revealed := fun _ => none
    probes := []
  }

@[simp]
theorem globalChainInputProbe?_encodingInput
    (parameter : PublicParameter) (epoch : Epoch)
    (input : Message × Randomness) :
    globalChainInputProbe? parameter
      (Concrete.CacheView.encodingInput parameter epoch input) = none := by
  unfold globalChainInputProbe?
  split
  · rename_i hexists
    obtain ⟨data, hdata⟩ := hexists
    have hchain : AtHashAddress parameter
        (.chain data.1 data.2.1 data.2.2.1)
        (Concrete.CacheView.encodingInput parameter epoch input) := by
      rw [hdata]
      simp [Concrete.CacheView.chainInput]
    have hencoding : AtHashAddress parameter (.encoding epoch)
        (Concrete.CacheView.encodingInput parameter epoch input) := by
      simp [Concrete.CacheView.encodingInput]
    have hdomain := atHashAddress_unique parameter
      (.chain data.1 data.2.1 data.2.2.1) (.encoding epoch)
      (Concrete.CacheView.encodingInput parameter epoch input) hchain
        hencoding
    simp at hdomain
  · rfl

@[simp]
theorem globalChainInputProbe?_leafInput
    (parameter : PublicParameter) (epoch : Epoch)
    (endpoints : ChainIndex → Digest) :
    globalChainInputProbe? parameter
      (Concrete.CacheView.leafInput parameter epoch endpoints) = none := by
  unfold globalChainInputProbe?
  split
  · rename_i hexists
    obtain ⟨data, hdata⟩ := hexists
    have hdomain := domain_eq_of_tweakableHashInput_eq parameter hdata
    simp at hdomain
  · rfl

def GlobalFilteredCausalStateRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftCache : QueryCache HashSpec)
    (rightState : GlobalCausalHashState) : Prop :=
  HashCachesAgreeOn
      (GlobalSigningComparableHashInput left.secretKey.parameter)
      leftCache rightState.cache ∧
    FilteredCacheExtensionRelation left.cache leftCache rightState.cache ∧
    left.cache ≤ leftCache ∧
    rightState.keygenCache = right.1.cache ∧
    GlobalSigningRevealsAgree right.2 rightState

theorem GlobalSigningRevealsAgree.globalCausalRecordedState
    {table : GlobalChainValueIndex → Digest}
    {state : GlobalCausalHashState}
    (hagrees : GlobalSigningRevealsAgree table state)
    (secretKey : SecretKey) (input : HashInput) :
    GlobalSigningRevealsAgree table
      (globalCausalRecordedState secretKey input state) := by
  intro index value hvalue
  rw [globalCausalRecordedState_revealed] at hvalue
  exact hagrees index value hvalue

theorem GlobalFilteredCausalStateRelation.recordedStateSetCache
    {left : ProgrammedGlobalChainKeygenView}
    {right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)}
    {leftCache : QueryCache HashSpec}
    {rightState : GlobalCausalHashState}
    (hstate : GlobalFilteredCausalStateRelation left right leftCache rightState)
    (secretKey : SecretKey) (input : HashInput)
    (newLeft newRight : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (GlobalSigningComparableHashInput left.secretKey.parameter)
      newLeft newRight)
    (hfiltered : FilteredCacheExtensionRelation left.cache newLeft newRight)
    (hle : leftCache ≤ newLeft) :
    GlobalFilteredCausalStateRelation left right newLeft
      { (globalCausalRecordedState secretKey input rightState) with
        cache := newRight } := by
  refine ⟨hagrees, hfiltered, hstate.2.2.1.trans hle, ?_, ?_⟩
  · simpa using hstate.2.2.2.1
  · exact ((hstate.2.2.2.2.globalCausalRecordedState secretKey input).setCache
      newRight)

theorem GlobalFilteredCausalStateRelation.recordedState
    {left : ProgrammedGlobalChainKeygenView}
    {right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)}
    {leftCache : QueryCache HashSpec}
    {rightState : GlobalCausalHashState}
    (hstate : GlobalFilteredCausalStateRelation left right leftCache rightState)
    (secretKey : SecretKey) (input : HashInput) :
    GlobalFilteredCausalStateRelation left right leftCache
      (globalCausalRecordedState secretKey input rightState) := by
  refine ⟨?_, ?_, hstate.2.2.1, ?_, ?_⟩
  · simpa using hstate.1
  · simpa using hstate.2.1
  · simpa using hstate.2.2.2.1
  · exact hstate.2.2.2.2.globalCausalRecordedState secretKey input

theorem GlobalFilteredCausalStateRelation.revealResultState
    {left : ProgrammedGlobalChainKeygenView}
    {right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)}
    {leftCache : QueryCache HashSpec}
    {rightState : GlobalCausalHashState}
    (hstate : GlobalFilteredCausalStateRelation left right leftCache rightState)
    (secretKey : SecretKey) (input : HashInput)
    (index : GlobalChainValueIndex) (value : Digest) (output : HashOutput)
    (hinput : ¬ GlobalSigningComparableHashInput
      left.secretKey.parameter input)
    (hleft : leftCache input = some output)
    (hvalue : right.2 index = value) :
    GlobalFilteredCausalStateRelation left right leftCache
      (globalCausalRevealResultState secretKey input rightState index value
        output) := by
  unfold GlobalFilteredCausalStateRelation
  refine ⟨?_, ?_, hstate.2.2.1, ?_, ?_⟩
  · intro candidate hcandidate
    have hne : candidate ≠ input := by
      intro heq
      subst candidate
      exact hinput hcandidate
    unfold globalCausalRevealResultState
    simp only [globalCausalRecordedState_cache]
    rw [QueryCache.cacheQuery_of_ne _ _ hne]
    exact hstate.1 candidate hcandidate
  · intro candidate
    by_cases heq : candidate = input
    · subst candidate
      left
      unfold globalCausalRevealResultState
      simp only [globalCausalRecordedState_cache]
      simp [hleft]
    · unfold globalCausalRevealResultState
      simp only [globalCausalRecordedState_cache]
      rw [QueryCache.cacheQuery_of_ne _ _ heq]
      exact hstate.2.1 candidate
  · unfold globalCausalRevealResultState
    change (globalCausalRecordedState secretKey input rightState).keygenCache =
      right.1.cache
    rw [globalCausalRecordedState_keygenCache]
    exact hstate.2.2.2.1
  · have hagrees := hstate.2.2.2.2.globalCausalRecordedState secretKey input
    have hrecorded := hagrees.recordReveal index
    rw [hvalue] at hrecorded
    exact hrecorded.setCache _

def GlobalFilteredHashResultRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftResult : HashOutput × QueryCache HashSpec)
    (rightResult : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) : Prop :=
  leftResult.1 = rightResult.1.1 ∧
    GlobalFilteredCausalStateRelation left right leftResult.2 rightResult.1.2

theorem programmedGlobal_filteredKeygen_stateRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen) :
    GlobalFilteredCausalStateRelation left right.1 left.cache
      (globalFilteredCausalKeygenState right.1.1) := by
  classical
  have hleftKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    left hleftSupport
  have hrightKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    right.1.1 hrightSupport
  have hparameter : left.secretKey.parameter =
      right.1.1.secretKey.parameter := by
    calc
      left.secretKey.parameter = left.publicKey.parameter :=
        (keygen_parameter_eq left.keyResult hleftKey).symm
      _ = right.1.1.publicKey.parameter :=
        congrArg PublicKey.parameter hrel.1.toStable.1.2.1
      _ = right.1.1.secretKey.parameter :=
        keygen_parameter_eq right.1.1.keyResult hrightKey
  obtain ⟨leftEndpoints, rightEndpoints, htree, _hleftReplay,
    _hrightReplay⟩ := hrel.1.1.2
  refine ⟨?_, ?_, le_rfl, rfl, ?_⟩
  · intro input hinput
    obtain ⟨epoch, message, randomness, rfl⟩ := hinput
    have hleftNone := Concrete.keygen_cache_none_encodingInput
      left.keyResult hleftKey epoch (message, randomness)
    change left.cache (Concrete.CacheView.encodingInput
      left.secretKey.parameter epoch (message, randomness)) = none at hleftNone
    have hnotMerkle : ¬ MerkleHashInput right.1.1.secretKey.parameter
        (Concrete.CacheView.encodingInput left.secretKey.parameter epoch
          (message, randomness)) := by
      rintro ⟨level, node, hmerkle⟩
      have hmerkleCanonical : AtHashAddress
          right.1.1.secretKey.parameter (.merkle level node)
          (Concrete.CacheView.encodingInput right.1.1.secretKey.parameter epoch
            (message, randomness)) := by
        simpa only [hparameter] using hmerkle
      have hencoding : AtHashAddress right.1.1.secretKey.parameter
          (.encoding epoch)
          (Concrete.CacheView.encodingInput right.1.1.secretKey.parameter epoch
            (message, randomness)) := by
        simp [Concrete.CacheView.encodingInput]
      have hdomain := atHashAddress_unique right.1.1.secretKey.parameter
        (.merkle level node) (.encoding epoch)
        (Concrete.CacheView.encodingInput right.1.1.secretKey.parameter epoch
          (message, randomness)) hmerkleCanonical hencoding
      simp at hdomain
    simpa [globalFilteredCausalKeygenState, hnotMerkle] using hleftNone
  · intro input
    by_cases hmerkle : MerkleHashInput right.1.1.secretKey.parameter input
    · left
      have hmerkleLeft : MerkleHashInput left.secretKey.parameter input := by
        rw [hparameter]
        exact hmerkle
      simpa [globalFilteredCausalKeygenState, hmerkle] using
        htree.merkle input hmerkleLeft
    · right
      exact ⟨rfl, by simp [globalFilteredCausalKeygenState, hmerkle]⟩
  · intro index value hvalue
    simp [globalFilteredCausalKeygenState] at hvalue

def GlobalEncodingFilteredResultRelation
    (parameter : PublicParameter)
    (leftBase initialLeft initialRight : QueryCache HashSpec)
    (epoch : Epoch) (message : Message) (randomness : Randomness)
    (leftResult rightResult : Digest × QueryCache HashSpec) : Prop :=
  leftResult.1 = rightResult.1 ∧
    HashCachesAgreeOn (GlobalSigningComparableHashInput parameter)
      leftResult.2 rightResult.2 ∧
    initialLeft ≤ leftResult.2 ∧ initialRight ≤ rightResult.2 ∧
    FilteredCacheExtensionRelation leftBase leftResult.2 rightResult.2 ∧
    Concrete.CacheView.encodingHash leftResult.2 parameter epoch
      (message, randomness) = leftResult.1 ∧
    Concrete.CacheView.encodingHash rightResult.2 parameter epoch
      (message, randomness) = rightResult.1

theorem relTriple_globalEncodingHash_run_filtered
    (parameter : PublicParameter)
    (leftBase left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (GlobalSigningComparableHashInput parameter) left right)
    (hfiltered : FilteredCacheExtensionRelation leftBase left right)
    (epoch : Epoch) (message : Message) (randomness : Randomness) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.encodingHash parameter epoch message randomness)).run left)
      ((simulateQ randomOracle
        (Concrete.encodingHash parameter epoch message randomness)).run right)
      (GlobalEncodingFilteredResultRelation parameter leftBase left right
        epoch message randomness) := by
  have hquery := relTriple_randomOracle_run_of_cachesAgreeOn_filtered
    (GlobalSigningComparableHashInput parameter) leftBase left right
      (Concrete.CacheView.encodingInput parameter epoch (message, randomness))
      ⟨epoch, message, randomness, rfl⟩ hagrees hfiltered
  have hmapped : RelTriple
      ((fun result : HashOutput × QueryCache HashSpec =>
        (truncateHash result.1, result.2)) <$> (randomOracle
          (Concrete.CacheView.encodingInput parameter epoch
            (message, randomness))).run left)
      ((fun result : HashOutput × QueryCache HashSpec =>
        (truncateHash result.1, result.2)) <$> (randomOracle
          (Concrete.CacheView.encodingInput parameter epoch
            (message, randomness))).run right)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          HashCachesAgreeOn (GlobalSigningComparableHashInput parameter)
            leftResult.2 rightResult.2 ∧
          left ≤ leftResult.2 ∧ right ≤ rightResult.2 ∧
          FilteredCacheExtensionRelation leftBase
            leftResult.2 rightResult.2) := by
    apply relTriple_map
    apply relTriple_post_mono hquery
    intro leftResult rightResult hresult
    exact ⟨congrArg truncateHash hresult.1, hresult.2⟩
  have hstrengthened := relTriple_strengthen_support hmapped
    (fun result hresult => encodingHash_run_cache_eq parameter left result.2
      epoch message randomness result.1 (by
        simpa [Concrete.encodingHash, Concrete.tweakableHash,
          Concrete.oracleHash, Concrete.CacheView.encodingInput,
          map_eq_bind_pure_comp] using hresult))
    (fun result hresult => encodingHash_run_cache_eq parameter right result.2
      epoch message randomness result.1 (by
        simpa [Concrete.encodingHash, Concrete.tweakableHash,
          Concrete.oracleHash, Concrete.CacheView.encodingInput,
          map_eq_bind_pure_comp] using hresult))
  apply relTriple_post_mono hstrengthened
  intro leftResult rightResult hresult
  exact ⟨hresult.1.1, hresult.1.2.1, hresult.1.2.2.1,
    hresult.1.2.2.2.1, hresult.1.2.2.2.2, hresult.2.1, hresult.2.2⟩

noncomputable def globalChainValueHighTableOfEdges
    (high : GlobalChainEdgeIndex → Digest) :
    GlobalChainValueIndex → Digest := fun index =>
  if hzero : index.2.2.val = 0 then
    0
  else
    high (index.1, index.2.1, ⟨index.2.2.val - 1, by omega⟩)

@[simp]
theorem globalChainValueHighTableOfEdges_next
    (high : GlobalChainEdgeIndex → Digest)
    (edge : GlobalChainEdgeIndex) :
    globalChainValueHighTableOfEdges high
        (edge.1, edge.2.1, chainStepNextDigit edge.2.2) =
      high edge := by
  unfold globalChainValueHighTableOfEdges
  simp only [chainStepNextDigit]
  rw [dif_neg (by omega)]
  congr 3

noncomputable def globalCausalRevealHashQueryFromHigh
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (HashOutput × GlobalCausalHashState) := do
  let value ← RevealProbeOracleSimulation.revealQuery index
  let output := Rom.hashOutputEquivDigestPair.symm (high index, value)
  pure (output, globalCausalRevealResultState secretKey input state
    index value output)

theorem simulate_eagerTrace_globalCausalRevealHashQueryFromHigh
    (table high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (globalCausalRevealHashQueryFromHigh high secretKey input state
        index)).run =
      pure ((Rom.hashOutputEquivDigestPair.symm
          (high index, table index),
        globalCausalRevealResultState secretKey input state index
          (table index) (Rom.hashOutputEquivDigestPair.symm
            (high index, table index))),
        [RevealProbeOracleSimulation.ObservedAction.reveal
          index (table index)]) := by
  unfold globalCausalRevealHashQueryFromHigh
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_revealQuery]
  simp

theorem globalChainEdgeOutputFromHigh_eq_revealOutput
    (high : GlobalChainEdgeIndex → Digest)
    (table : GlobalChainValueIndex → Digest)
    (edge : GlobalChainEdgeIndex) :
    Rom.hashOutputEquivDigestPair.symm
        (globalChainValueHighTableOfEdges high
          (edge.1, edge.2.1, chainStepNextDigit edge.2.2),
          table (edge.1, edge.2.1, chainStepNextDigit edge.2.2)) =
      globalChainEdgeOutputFromHigh high table edge := by
  simp [globalChainEdgeOutputFromHigh, globalChainTableEdgeTarget]

theorem globalChainTableEdgeInput_not_signingComparable
    (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest)
    (edge : GlobalChainEdgeIndex) :
    ¬ GlobalSigningComparableHashInput parameter
      (globalChainTableEdgeInput parameter table edge) := by
  rintro ⟨epoch, message, randomness, hencoding⟩
  have hchain : AtHashAddress parameter
      (.chain edge.2.1 edge.1 edge.2.2)
      (globalChainTableEdgeInput parameter table edge) := by
    simp [globalChainTableEdgeInput, Concrete.CacheView.chainInput]
  have hencodingAddress : AtHashAddress parameter (.encoding epoch)
      (globalChainTableEdgeInput parameter table edge) := by
    rw [hencoding]
    simp [Concrete.CacheView.encodingInput]
  have hdomain := atHashAddress_unique parameter
    (.chain edge.2.1 edge.1 edge.2.2) (.encoding epoch)
    (globalChainTableEdgeInput parameter table edge) hchain hencodingAddress
  simp at hdomain

theorem globalCausalAttackerHashPlan_eq_reveal_globalEdge
    (secretKey : SecretKey)
    (table : GlobalChainValueIndex → Digest)
    (edge : GlobalChainEdgeIndex) (state : GlobalCausalHashState)
    (hcache : state.cache
      (globalChainTableEdgeInput secretKey.parameter table edge) = none)
    (hrevealed : state.revealed
      (edge.1, edge.2.1, chainStepDigit edge.2.2) =
        some (table (edge.1, edge.2.1, chainStepDigit edge.2.2))) :
    globalCausalAttackerHashPlan secretKey
        (globalChainTableEdgeInput secretKey.parameter table edge) state =
      .reveal (edge.1, edge.2.1, chainStepNextDigit edge.2.2) := by
  rw [globalCausalAttackerHashPlan, hcache]
  unfold globalCausalUncachedAttackerHashPlan globalChainTableEdgeInput
  rw [globalChainInputProbe?_chainInput]
  simp [hrevealed, chainStepDigit, chainStepNextDigit]

noncomputable def globalCausalAttackerHashQueryFromHigh
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput) :
    StateT GlobalCausalHashState
      (OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex))
      HashOutput := fun state =>
  let recorded := globalCausalRecordedState secretKey input state
  match globalCausalAttackerHashPlan secretKey input state with
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
       match globalCausalAttackerHashPlan secretKey input state with
       | .cached output => pure (output, recorded)
       | .redirect output =>
           pure (output, { recorded with
             cache := recorded.cache.cacheQuery input output })
       | .fresh => (globalCausalHashQuery input).run recorded
       | .reveal index =>
           globalCausalRevealHashQueryFromHigh high secretKey input state
             index) := rfl

theorem relTriple_programmed_globalFilteredHashQuery_cached
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (leftCache : QueryCache HashSpec) (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right.1 leftCache
      rightState)
    (input : HashInput) (output : HashOutput)
    (hright : rightState.cache input = some output) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        ((globalCausalAttackerHashQueryFromHigh
          (globalChainValueHighTableOfEdges right.2) right.1.1.secretKey
            input).run rightState)).run)
      (GlobalFilteredHashResultRelation left right.1) := by
  have hleft : leftCache input = some output :=
    hstate.2.1.right_le_left hright
  have hplan : globalCausalAttackerHashPlan right.1.1.secretKey input
      rightState = .cached output := by
    simp [globalCausalAttackerHashPlan, hright]
  rw [randomOracle, QueryImpl.withCaching_run_some _ hleft,
    globalCausalAttackerHashQueryFromHigh_run, hplan, simulateQ_pure,
    WriterT.run_pure]
  apply relTriple_pure_pure
  exact ⟨rfl, hstate.recordedState right.1.1.secretKey input⟩

theorem relTriple_programmed_globalFilteredHashQuery_fresh
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (leftCache : QueryCache HashSpec) (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right.1 leftCache
      rightState)
    (input : HashInput)
    (hbaseNone : left.cache input = none)
    (hplan : globalCausalAttackerHashPlan right.1.1.secretKey input
      rightState = .fresh) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        ((globalCausalAttackerHashQueryFromHigh
          (globalChainValueHighTableOfEdges right.2) right.1.1.secretKey
            input).run rightState)).run)
      (GlobalFilteredHashResultRelation left right.1) := by
  have hcurrent : leftCache input = rightState.cache input := by
    rcases hstate.2.1 input with hagree | ⟨hleft, hright⟩
    · exact hagree
    · rw [hleft, hbaseNone, hright]
  have hcouple := relTriple_randomOracle_run_of_current_eq_filtered
    (GlobalSigningComparableHashInput left.secretKey.parameter) left.cache
      leftCache rightState.cache input hcurrent hstate.1 hstate.2.1
  let recorded :=
    globalCausalRecordedState right.1.1.secretKey input rightState
  let wrap := fun result : HashOutput × QueryCache HashSpec =>
    ((result.1, { recorded with cache := result.2 }),
      ([] : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
  have hprepared : RelTriple ((randomOracle input).run leftCache)
      ((randomOracle input).run rightState.cache)
      (fun leftResult rightResult =>
        GlobalFilteredHashResultRelation left right.1 leftResult
          (wrap rightResult)) := by
    apply relTriple_post_mono hcouple
    intro leftResult rightResult hresult
    refine ⟨hresult.1, ?_⟩
    exact hstate.recordedStateSetCache right.1.1.secretKey input
      leftResult.2 rightResult.2 hresult.2.1 hresult.2.2.2.2
        hresult.2.2.1
  have hmapped := relTriple_map
    (R := GlobalFilteredHashResultRelation left right.1)
    (f := id) (g := wrap) hprepared
  rw [globalCausalAttackerHashQueryFromHigh_run, hplan,
    simulate_eagerTrace_globalCausalHashQuery]
  simpa [wrap, recorded] using hmapped

theorem relTriple_programmed_globalFilteredHashQuery_revealEdge
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftCache : QueryCache HashSpec) (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right.1 leftCache
      rightState)
    (edge : GlobalChainEdgeIndex)
    (hrightCache : rightState.cache
      (globalChainTableEdgeInput left.secretKey.parameter left.table edge) =
        none)
    (hrevealed : rightState.revealed
      (edge.1, edge.2.1, chainStepDigit edge.2.2) =
        some (right.1.2
          (edge.1, edge.2.1, chainStepDigit edge.2.2))) :
    RelTriple
      ((randomOracle
        (globalChainTableEdgeInput left.secretKey.parameter left.table edge)).run
          leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        ((globalCausalAttackerHashQueryFromHigh
          (globalChainValueHighTableOfEdges right.2) right.1.1.secretKey
            (globalChainTableEdgeInput left.secretKey.parameter left.table
              edge)).run rightState)).run)
      (GlobalFilteredHashResultRelation left right.1) := by
  have hleftKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    left hleftSupport
  have hrightKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    right.1.1 hrightSupport
  have hparameter : left.secretKey.parameter =
      right.1.1.secretKey.parameter := by
    calc
      left.secretKey.parameter = left.publicKey.parameter :=
        (keygen_parameter_eq left.keyResult hleftKey).symm
      _ = right.1.1.publicKey.parameter :=
        congrArg PublicKey.parameter hrel.1.toStable.1.2.1
      _ = right.1.1.secretKey.parameter :=
        keygen_parameter_eq right.1.1.keyResult hrightKey
  have htable : left.table = right.1.2 := hrel.1.toStable.1.1
  have hedgeInput :
      globalChainTableEdgeInput left.secretKey.parameter left.table edge =
        globalChainTableEdgeInput right.1.1.secretKey.parameter right.1.2
          edge := by
    rw [hparameter, htable]
  have hrightCanonical : rightState.cache
      (globalChainTableEdgeInput right.1.1.secretKey.parameter right.1.2
        edge) = none := by
    rw [← hedgeInput]
    exact hrightCache
  have hplanCanonical := globalCausalAttackerHashPlan_eq_reveal_globalEdge
    right.1.1.secretKey right.1.2 edge rightState hrightCanonical hrevealed
  have hplan : globalCausalAttackerHashPlan right.1.1.secretKey
      (globalChainTableEdgeInput left.secretKey.parameter left.table edge)
        rightState =
      .reveal (edge.1, edge.2.1, chainStepNextDigit edge.2.2) := by
    rw [hedgeInput]
    exact hplanCanonical
  obtain ⟨output, hbase, htruncate⟩ := hrel.2.2 edge
  have hleft : leftCache
      (globalChainTableEdgeInput left.secretKey.parameter left.table edge) =
        some output := hstate.2.2.1 hbase
  rw [randomOracle, QueryImpl.withCaching_run_some _ hleft,
    globalCausalAttackerHashQueryFromHigh_run, hplan,
    simulate_eagerTrace_globalCausalRevealHashQueryFromHigh]
  apply relTriple_pure_pure
  have hconstructed :
      Rom.hashOutputEquivDigestPair.symm
          (globalChainValueHighTableOfEdges right.2
            (edge.1, edge.2.1, chainStepNextDigit edge.2.2),
            right.1.2
              (edge.1, edge.2.1, chainStepNextDigit edge.2.2)) =
        output := by
    calc
      _ = globalChainEdgeOutputFromHigh right.2 right.1.2 edge :=
        globalChainEdgeOutputFromHigh_eq_revealOutput right.2 right.1.2 edge
      _ = globalChainEdgeOutputFromHigh
          (globalChainEdgeHighTableOfCache left.cache
            left.secretKey.parameter left.table) left.table edge := by
        rw [hrel.2.1, htable]
      _ = output := globalChainEdgeOutputFromHigh_eq_cached left.cache
        left.secretKey.parameter left.table edge output hbase htruncate
  refine ⟨hconstructed.symm, ?_⟩
  rw [hconstructed]
  apply hstate.revealResultState right.1.1.secretKey
    (globalChainTableEdgeInput left.secretKey.parameter left.table edge)
    (edge.1, edge.2.1, chainStepNextDigit edge.2.2)
    (right.1.2 (edge.1, edge.2.1, chainStepNextDigit edge.2.2)) output
  · exact globalChainTableEdgeInput_not_signingComparable
      left.secretKey.parameter left.table edge
  · exact hleft
  · rfl

noncomputable def globalFilteredCausalSigningAttempt
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (Option Signature × GlobalCausalHashState) := do
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
      let result ← (revealGlobalSignatureChains request encoding allChains
        (Concrete.CacheReplay.signWithEncoding keyView.cache keyView.secretKey
          request.epoch randomness encoding)).run encodedState
      pure (some result.1, result.2)

noncomputable def globalFilteredCausalSignBoundedAttempts : Nat →
    ProgrammedGlobalChainKeygenView → SignRequest → GlobalCausalHashState →
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (Option Signature × GlobalCausalHashState)
  | 0, _keyView, _request, state => pure (none, state)
  | attempts + 1, keyView, request, state => do
      let result ← globalFilteredCausalSigningAttempt keyView request state
      match result.1 with
      | some signature => pure (some signature, result.2)
      | none =>
          globalFilteredCausalSignBoundedAttempts attempts keyView request
            result.2

noncomputable def globalFilteredCausalSigningQuery
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (Option Signature × GlobalCausalHashState) :=
  globalFilteredCausalSignBoundedAttempts signingAttemptLimit keyView request
    state

noncomputable def globalFilteredCausalSignTraceContinuation
    (attempts : Nat) (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView) (request : SignRequest)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :
    ProbComp ((Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  match result.1.1 with
  | some _signature => pure result
  | none =>
      (fun rest => (rest.1, result.2 ++ rest.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          (globalFilteredCausalSignBoundedAttempts attempts keyView request
            result.1.2)).run

theorem simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_succ
    (attempts : Nat) (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView) (request : SignRequest)
    (state : GlobalCausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (globalFilteredCausalSignBoundedAttempts (attempts + 1) keyView request
        state)).run =
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSigningAttempt keyView request state)).run >>=
          globalFilteredCausalSignTraceContinuation attempts table keyView
            request := by
  rw [globalFilteredCausalSignBoundedAttempts, simulateQ_bind,
    WriterT.run_bind']
  apply bind_congr
  intro result
  rcases result with ⟨⟨signatureOption, resultState⟩, trace⟩
  cases signatureOption with
  | none =>
      simp only [globalFilteredCausalSignTraceContinuation]
      congr 1
  | some signature =>
      simp [globalFilteredCausalSignTraceContinuation]

def GlobalFilteredSigningResultRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftResult : Option Signature × QueryCache HashSpec)
    (rightResult : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) : Prop :=
  leftResult.1 = rightResult.1.1 ∧
    GlobalFilteredCausalStateRelation left right leftResult.2 rightResult.1.2

def GlobalFilteredSigningAttemptResultRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftResult : Option Signature × QueryCache HashSpec)
    (rightResult : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) : Prop :=
  GlobalFilteredSigningResultRelation left right leftResult rightResult ∧
    (leftResult.1 = none → rightResult.2 = [])

theorem relTriple_programmed_globalFilteredCausalSigningAttempt
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftCache : QueryCache HashSpec) (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right.1 leftCache
      rightState)
    (request : SignRequest) :
    RelTriple
      ((simulateQ xmssRomImpl
        (Concrete.sign left.publicKey left.secretKey
          request.epoch request.message)).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        (globalFilteredCausalSigningAttempt right.1.1 request
          rightState)).run)
      (GlobalFilteredSigningAttemptResultRelation left right.1) := by
  have hleftKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    left hleftSupport
  have hrightKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    right.1.1 hrightSupport
  have hparameter : left.secretKey.parameter =
      right.1.1.secretKey.parameter := by
    calc
      left.secretKey.parameter = left.publicKey.parameter :=
        (keygen_parameter_eq left.keyResult hleftKey).symm
      _ = right.1.1.publicKey.parameter :=
        congrArg PublicKey.parameter hrel.1.toStable.1.2.1
      _ = right.1.1.secretKey.parameter :=
        keygen_parameter_eq right.1.1.keyResult hrightKey
  rw [Concrete.sign_run_eq]
  unfold globalFilteredCausalSigningAttempt
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, List.nil_append]
  rw [← Concrete.signingRandomness_eq]
  apply relTriple_bind (relTriple_refl Concrete.signingRandomness)
  intro leftRandomness rightRandomness hrandomness
  subst rightRandomness
  unfold Concrete.signAttempt
  simp only [simulateQ_bind, StateT.run_bind]
  rw [WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, List.nil_append]
  rw [← hparameter]
  apply relTriple_bind
    (relTriple_globalEncodingHash_run_filtered
      left.secretKey.parameter left.cache leftCache rightState.cache
        hstate.1 hstate.2.1 request.epoch request.message leftRandomness)
  intro leftEncoded rightEncoded hencoded
  have hdigestEq : leftEncoded.1 = rightEncoded.1 := hencoded.1
  rw [← hdigestEq]
  cases hdecode : TargetSum.decodeDigest leftEncoded.1 with
  | none =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure]
      apply relTriple_pure_pure
      unfold GlobalFilteredSigningAttemptResultRelation
        GlobalFilteredSigningResultRelation
        GlobalFilteredCausalStateRelation
      refine ⟨⟨rfl, hencoded.2.1, hencoded.2.2.2.2.1,
        hstate.2.2.1.trans hencoded.2.2.1, hstate.2.2.2.1, ?_⟩,
        fun _ => rfl⟩
      exact hstate.2.2.2.2.setCache rightEncoded.2
  | some encoding =>
      have hleftRun :
          (simulateQ randomOracle
            (Concrete.signWithEncoding left.secretKey request.epoch
              leftRandomness encoding)).run leftEncoded.2 =
            pure (Concrete.CacheReplay.signWithEncoding leftEncoded.2
              left.secretKey request.epoch leftRandomness encoding,
                leftEncoded.2) := by
        simpa [ProgrammedGlobalChainKeygenView.keyResult] using
          (Concrete.keygen_signWithEncoding_run_eq_pure left.keyResult hleftKey
            hrel.1.toStable.2.1 leftEncoded.2
            (hstate.2.2.1.trans hencoded.2.2.1) request.epoch
              leftRandomness encoding)
      rw [simulateQ_bind, StateT.run_bind, hleftRun]
      simp only [pure_bind, Function.comp_apply, simulateQ_pure,
        StateT.run_pure]
      rw [simulateQ_bind, WriterT.run_bind',
        simulate_eagerTrace_revealGlobalSignatureChains]
      simp [Prod.map]
      unfold GlobalFilteredSigningAttemptResultRelation
        GlobalFilteredSigningResultRelation
        GlobalFilteredCausalStateRelation
      let encodedState : GlobalCausalHashState :=
        { rightState with cache := rightEncoded.2 }
      let rightSignature := Concrete.CacheReplay.signWithEncoding
        right.1.1.cache right.1.1.secretKey request.epoch leftRandomness
          encoding
      have hleftStable := Concrete.keygen_signWithEncoding_eq_base
        left.keyResult hleftKey hrel.1.toStable.2.1 leftEncoded.2
          (hstate.2.2.1.trans hencoded.2.2.1) request.epoch
            leftRandomness encoding
      have hbase := keygenViews_signWithEncoding_eq_globalReveal
        left right.1 hrel.1.toStable hleftSupport hrightSupport left.cache
          right.1.1.cache le_rfl le_rfl request leftRandomness encoding
            encodedState
      have hsignature :
          Concrete.CacheReplay.signWithEncoding leftEncoded.2 left.secretKey
              request.epoch leftRandomness encoding =
            (globalSignatureRevealResult right.1.2 request encoding allChains
              rightSignature encodedState).1 := hleftStable.trans hbase
      have hcachesFinal : HashCachesAgreeOn
          (GlobalSigningComparableHashInput left.secretKey.parameter)
          leftEncoded.2
          (globalSignatureRevealResult right.1.2 request encoding allChains
            rightSignature encodedState).2.cache := by
        rw [globalSignatureRevealResult_cache]
        exact hencoded.2.1
      have hfilteredFinal : FilteredCacheExtensionRelation left.cache
          leftEncoded.2
          (globalSignatureRevealResult right.1.2 request encoding allChains
            rightSignature encodedState).2.cache := by
        rw [globalSignatureRevealResult_cache]
        exact hencoded.2.2.2.2.1
      refine ⟨⟨congrArg some hsignature, hcachesFinal,
        hfilteredFinal,
        hstate.2.2.1.trans hencoded.2.2.1, ?_, ?_⟩, ?_⟩
      · rw [globalSignatureRevealResult_keygenCache]
        exact hstate.2.2.2.1
      · have hagrees := hstate.2.2.2.2.setCache rightEncoded.2
        exact hagrees.globalSignatureRevealResult request encoding allChains
          rightSignature
      · intro hnone
        simp at hnone

theorem relTriple_programmed_globalFilteredCausalSignBoundedAttempts
    (attempts : Nat)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftCache : QueryCache HashSpec) (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right.1 leftCache
      rightState)
    (request : SignRequest) :
    RelTriple
      ((simulateQ xmssRomImpl
        (Concrete.signBoundedAttempts attempts left.secretKey
          request.epoch request.message)).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        (globalFilteredCausalSignBoundedAttempts attempts right.1.1 request
          rightState)).run)
      (GlobalFilteredSigningResultRelation left right.1) := by
  induction attempts generalizing leftCache rightState with
  | zero =>
      simp only [Concrete.signBoundedAttempts,
        globalFilteredCausalSignBoundedAttempts, simulateQ_pure,
        StateT.run_pure, WriterT.run_pure]
      apply relTriple_pure_pure
      exact ⟨rfl, hstate⟩
  | succ attempts ih =>
      rw [Concrete.signBoundedAttempts_run_succ_eq_sign_bind attempts
        left.publicKey left.secretKey request.epoch request.message leftCache]
      rw [simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_succ]
      apply relTriple_bind
        (relTriple_programmed_globalFilteredCausalSigningAttempt left right
          hrel hleftSupport hrightSupport leftCache rightState hstate request)
      intro leftAttempt rightAttempt hattempt
      rcases hattempt with ⟨hresult, hnil⟩
      rcases hresult with ⟨hoption, hstate'⟩
      cases hleft : leftAttempt.1 with
      | none =>
          have hright : rightAttempt.1.1 = none := by
            rw [← hoption, hleft]
          have htrace : rightAttempt.2 = [] := hnil hleft
          unfold Concrete.signBoundedAttemptsContinuation
          unfold globalFilteredCausalSignTraceContinuation
          rw [hleft, hright, htrace]
          simpa using ih leftAttempt.2 rightAttempt.1.2 hstate'
      | some signature =>
          have hright : rightAttempt.1.1 = some signature := by
            rw [← hoption, hleft]
          unfold Concrete.signBoundedAttemptsContinuation
          unfold globalFilteredCausalSignTraceContinuation
          rw [hleft, hright]
          apply relTriple_pure_pure
          exact ⟨hright.symm, hstate'⟩

theorem relTriple_programmed_globalFilteredCausalSigningQuery
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftCache : QueryCache HashSpec) (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right.1 leftCache
      rightState)
    (request : SignRequest) :
    RelTriple
      ((simulateQ xmssRomImpl
        (Concrete.cappedScheme.sign left.publicKey left.secretKey
          request.epoch request.message)).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        (globalFilteredCausalSigningQuery right.1.1 request
          rightState)).run)
      (GlobalFilteredSigningResultRelation left right.1) := by
  simp only [Concrete.cappedScheme, Concrete.cappedSign_eq,
    globalFilteredCausalSigningQuery]
  exact relTriple_programmed_globalFilteredCausalSignBoundedAttempts
    signingAttemptLimit left right hrel hleftSupport hrightSupport leftCache
      rightState hstate request

end XmssSecurity.CappedChain
