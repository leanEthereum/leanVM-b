import XmssSecurity.Proof.CappedGlobalChainHighSigningCoupling

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

def FilteredCacheExtensionRelation
    (leftBase left right : QueryCache HashSpec) : Prop :=
  ∀ input,
    left input = right input ∨
      (left input = leftBase input ∧ right input = none)

theorem FilteredCacheExtensionRelation.right_le_left
    {leftBase left right : QueryCache HashSpec}
    (hrel : FilteredCacheExtensionRelation leftBase left right) :
    right ≤ left := by
  intro input output hright
  rcases hrel input with hagrees | ⟨_hbase, hnone⟩
  · rw [hagrees]
    exact hright
  · rw [hnone] at hright
    simp at hright

theorem FilteredCacheExtensionRelation.cacheQuery
    {leftBase left right : QueryCache HashSpec}
    (hrel : FilteredCacheExtensionRelation leftBase left right)
    (input : HashInput) (output : HashOutput) :
    FilteredCacheExtensionRelation leftBase
      (left.cacheQuery input output) (right.cacheQuery input output) := by
  intro candidate
  by_cases heq : candidate = input
  · subst candidate
    simp
  · rw [QueryCache.cacheQuery_of_ne left output heq,
      QueryCache.cacheQuery_of_ne right output heq]
    exact hrel candidate

theorem relTriple_randomOracle_run_of_current_eq_filtered
    (inputs : HashInput → Prop)
    (leftBase left right : QueryCache HashSpec)
    (input : HashInput) (hcurrent : left input = right input)
    (hagrees : HashCachesAgreeOn inputs left right)
    (hfiltered : FilteredCacheExtensionRelation leftBase left right) :
    RelTriple
      ((randomOracle input).run left)
      ((randomOracle input).run right)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          HashCachesAgreeOn inputs leftResult.2 rightResult.2 ∧
          left ≤ leftResult.2 ∧ right ≤ rightResult.2 ∧
          FilteredCacheExtensionRelation leftBase
            leftResult.2 rightResult.2) := by
  cases hleft : left input with
  | none =>
      have hright : right input = none := by
        rw [← hcurrent]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_none _ hleft,
        QueryImpl.withCaching_run_none _ hright,
        map_eq_bind_pure_comp, map_eq_bind_pure_comp]
      apply relTriple_bind (relTriple_refl ($ᵗ HashOutput))
      intro leftOutput rightOutput houtput
      subst rightOutput
      exact relTriple_pure_pure ⟨rfl,
        HashCachesAgreeOn.cacheQuery inputs left right hagrees
          input leftOutput,
        QueryCache.le_cacheQuery left hleft,
        QueryCache.le_cacheQuery right hright,
        hfiltered.cacheQuery input leftOutput⟩
  | some output =>
      have hright : right input = some output := by
        rw [← hcurrent]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_some _ hleft,
        QueryImpl.withCaching_run_some _ hright]
      exact relTriple_pure_pure ⟨rfl, hagrees, le_rfl, le_rfl, hfiltered⟩

theorem simulate_eagerTrace_globalCausalHashQuery
    (table : GlobalChainValueIndex → Digest) (input : HashInput)
    (state : GlobalCausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((globalCausalHashQuery input).run state)).run =
      (fun result : HashOutput × QueryCache HashSpec =>
        ((result.1, state.setCache result.2),
          ([] : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))) <$>
        ((randomOracle input).run state.cache) := by
  rw [globalCausalHashQuery_run, simulateQ_map, WriterT.run_map',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp [Functor.map_map]

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

noncomputable def globalFilteredCausalRevealResultState
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (value : Digest) (output : HashOutput) : GlobalCausalHashState :=
  {
    cache := state.cache.cacheQuery input output
    keygenCache := state.keygenCache
    revealed := Function.update state.revealed index (some value)
    probes := (globalCausalRecordedState secretKey input state).probes
  }

theorem hashCachesAgreeOn_globalFilteredCausalRevealResultState
    {parameter : PublicParameter}
    {leftCache : QueryCache HashSpec} {rightState : GlobalCausalHashState}
    (hagrees : HashCachesAgreeOn
      (GlobalSigningComparableHashInput parameter) leftCache rightState.cache)
    (secretKey : SecretKey) (input : HashInput)
    (index : GlobalChainValueIndex) (value : Digest) (output : HashOutput)
    (hinput : ¬ GlobalSigningComparableHashInput parameter input) :
    HashCachesAgreeOn (GlobalSigningComparableHashInput parameter) leftCache
      (globalFilteredCausalRevealResultState secretKey input rightState index value
        output).cache := by
  intro candidate hcandidate
  have hne : candidate ≠ input := by
    intro heq
    subst candidate
    exact hinput hcandidate
  unfold globalFilteredCausalRevealResultState
  change leftCache candidate =
    rightState.cache.cacheQuery input output candidate
  rw [QueryCache.cacheQuery_of_ne _ _ hne]
  exact hagrees candidate hcandidate

theorem filteredCacheExtension_globalFilteredCausalRevealResultState
    {leftBase leftCache : QueryCache HashSpec}
    {rightState : GlobalCausalHashState}
    (hfiltered : FilteredCacheExtensionRelation leftBase leftCache
      rightState.cache)
    (secretKey : SecretKey) (input : HashInput)
    (index : GlobalChainValueIndex) (value : Digest) (output : HashOutput)
    (hleft : leftCache input = some output) :
    FilteredCacheExtensionRelation leftBase leftCache
      (globalFilteredCausalRevealResultState secretKey input rightState index value
      output).cache := by
  intro candidate
  change leftCache candidate =
      rightState.cache.cacheQuery input output candidate ∨
    (leftCache candidate = leftBase candidate ∧
      rightState.cache.cacheQuery input output candidate = none)
  by_cases heq : candidate = input
  · subst candidate
    left
    simp [hleft]
  · rw [QueryCache.cacheQuery_of_ne _ _ heq]
    exact hfiltered candidate

theorem globalFilteredCausalRevealResultState_keygenCache_eq
    {rightState : GlobalCausalHashState} {keygenCache : QueryCache HashSpec}
    (hkeygen : rightState.keygenCache = keygenCache)
    (secretKey : SecretKey) (input : HashInput)
    (index : GlobalChainValueIndex) (value : Digest) (output : HashOutput) :
    (globalFilteredCausalRevealResultState secretKey input rightState index value
      output).keygenCache = keygenCache := by
  unfold globalFilteredCausalRevealResultState
  exact hkeygen

theorem GlobalSigningRevealsAgree.globalFilteredCausalRevealResultState
    {table : GlobalChainValueIndex → Digest}
    {rightState : GlobalCausalHashState}
    (hagrees : GlobalSigningRevealsAgree table rightState)
    (secretKey : SecretKey) (input : HashInput)
    (index : GlobalChainValueIndex) (value : Digest) (output : HashOutput)
    (hvalue : table index = value) :
    GlobalSigningRevealsAgree table
      (globalFilteredCausalRevealResultState secretKey input rightState index value
        output) := by
  intro candidate candidateValue hcand
  by_cases heq : candidate = index
  · subst candidate
    simp only [XmssSecurity.CappedChain.globalFilteredCausalRevealResultState,
      Function.update_self, Option.some.injEq] at hcand
    exact hvalue.trans hcand
  · have hright : rightState.revealed candidate = some candidateValue := by
      simpa only [XmssSecurity.CappedChain.globalFilteredCausalRevealResultState,
        Function.update_of_ne heq] using hcand
    exact hagrees candidate candidateValue hright

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
      (globalFilteredCausalRevealResultState secretKey input rightState index value
        output) := by
  exact ⟨
    hashCachesAgreeOn_globalFilteredCausalRevealResultState hstate.1 secretKey input
      index value output hinput,
    filteredCacheExtension_globalFilteredCausalRevealResultState hstate.2.1 secretKey
      input index value output hleft,
    hstate.2.2.1,
    globalFilteredCausalRevealResultState_keygenCache_eq hstate.2.2.2.1 secretKey input
      index value output,
    hstate.2.2.2.2.globalFilteredCausalRevealResultState secretKey input index value
      output hvalue⟩

def GlobalFilteredHashResultRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftResult : HashOutput × QueryCache HashSpec)
    (rightResult : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) : Prop :=
  leftResult.1 = rightResult.1.1 ∧
    GlobalFilteredCausalStateRelation left right leftResult.2 rightResult.1.2

end XmssSecurity.CappedChain
