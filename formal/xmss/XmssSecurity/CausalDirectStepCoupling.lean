import XmssSecurity.CausalDirectReduction

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

def FilteredDirectMissHashResultRelation
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftBase rightBase : QueryCache HashSpec)
    (table : ChainValueIndex → Digest)
    (index : ChainValueIndex) (target : Digest)
    (leftResult : HashOutput × QueryCache HashSpec)
    (rightResult : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) : Prop :=
  leftResult.1 = rightResult.1.1 ∧
    rightResult.2 =
      [.probe index target] ∧
    FilteredCausalStateRelation parameter selected leftBase rightBase table
      leftResult.2 rightResult.1.2

set_option maxRecDepth 100000 in
theorem relTriple_filteredProbingAttackerHashQueryAt_of_hidden_miss
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenCacheRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (leftCache : QueryCache HashSpec) (rightState : CausalHashState)
    (hstate : FilteredCausalStateRelation left.secretKey.parameter selected
      left.cache right.1.cache right.2 leftCache rightState)
    (hparameter : left.secretKey.parameter = right.1.secretKey.parameter)
    (input : HashInput) (index : ChainValueIndex) (target : Digest)
    (hprobe : chainInputProbe? left.secretKey.parameter selected input =
      some (index, target))
    (hhidden : rightState.revealed index = none)
    (hmiss : right.2 index ≠ target) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.2)
        (filteredProbingAttackerHashQueryAt right.1.secretKey selected input
          rightState (some (index, target)))).run)
      (FilteredDirectMissHashResultRelation left.secretKey.parameter selected
        left.cache right.1.cache right.2 index target) := by
  have hcache : leftCache input = rightState.cache input :=
    programmedActual_current_caches_eq_of_probe_miss selected left right hrel
      hleftSupport leftCache rightState hstate input index target hprobe hmiss
  have hrightProbe :
      chainInputProbe? right.1.secretKey.parameter selected input =
        some (index, target) := by
    rw [← hparameter]
    exact hprobe
  cases hleft : leftCache input with
  | some output =>
      have hright : rightState.cache input = some output := by
        rw [← hcache]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_some _ hleft]
      rw [filteredProbingAttackerHashQueryAt, hhidden]
      rw [simulateQ_bind, WriterT.run_bind']
      simp only [RevealProbeOracleSimulation.probeQuery,
        RevealProbeOracleSimulation.eagerTraceImpl,
        RevealProbeOracleSimulation.eagerImpl,
        RevealProbeOracleSimulation.traceFragment,
        QueryImpl.withTraceAppend_apply, WriterT.run_tell]
      rw [filteredCausalAttackerHashQuery_run]
      simp only [filteredCausalAttackerHashPlan, hright]
      simp only [simulateQ_pure, WriterT.run_pure, pure_bind]
      apply relTriple_pure_pure
      refine ⟨rfl, rfl, ?_⟩
      unfold FilteredCausalStateRelation
      exact ⟨hstate.1, hstate.2.1, hstate.2.2.1,
        hstate.2.2.2.1, hstate.2.2.2.2.recordProbe _⟩
  | none =>
      have hright : rightState.cache input = none := by
        rw [← hcache]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_none _ hleft]
      rw [filteredProbingAttackerHashQueryAt, hhidden]
      rw [simulateQ_bind, WriterT.run_bind']
      simp only [RevealProbeOracleSimulation.probeQuery,
        RevealProbeOracleSimulation.eagerTraceImpl,
        RevealProbeOracleSimulation.eagerImpl,
        RevealProbeOracleSimulation.traceFragment,
        QueryImpl.withTraceAppend_apply, WriterT.run_tell]
      rw [filteredCausalAttackerHashQuery_run]
      simp only [filteredCausalAttackerHashPlan, hright,
        filteredCausalUncachedHashPlan, hrightProbe, hhidden]
      rw [simulate_eagerTrace_causalHashQuery]
      apply relTriple_map
      apply relTriple_refl
      intro result
      refine ⟨rfl, rfl, ?_⟩
      unfold FilteredCausalStateRelation
      refine ⟨hstate.1.cacheQuery input result,
        hstate.2.1.cacheQuery input result, ?_, ?_, ?_⟩
      · exact hstate.2.2.1.trans (QueryCache.le_cacheQuery leftCache hleft)
      · exact hstate.2.2.2.1
      · exact hstate.2.2.2.2.recordProbe _ |>.setCache _

set_option maxRecDepth 100000 in
theorem filteredProbingAttackerHashQueryAt_hidden_trace
    (table : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex)
    (input : HashInput) (state : CausalHashState)
    (index : ChainValueIndex) (target : Digest)
    (hprobe : chainInputProbe? secretKey.parameter selected input =
      some (index, target))
    (hhidden : state.revealed index = none)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredProbingAttackerHashQueryAt secretKey selected input state
          (some (index, target)))).run)) :
    result.2 = [.probe index target] := by
  rw [filteredProbingAttackerHashQueryAt, hhidden,
    simulateQ_bind, WriterT.run_bind'] at hresult
  simp only [RevealProbeOracleSimulation.probeQuery,
    RevealProbeOracleSimulation.eagerTraceImpl,
    RevealProbeOracleSimulation.eagerImpl,
    RevealProbeOracleSimulation.traceFragment,
    QueryImpl.withTraceAppend_apply, WriterT.run_tell,
    pure_bind] at hresult
  rw [filteredCausalAttackerHashQuery_run] at hresult
  cases hcache : state.cache input with
  | some output =>
      simp only [filteredCausalAttackerHashPlan, hcache, simulateQ_pure,
        WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      exact congrArg Prod.snd hresult
  | none =>
      simp only [filteredCausalAttackerHashPlan, hcache,
        filteredCausalUncachedHashPlan, hprobe, hhidden] at hresult
      rw [simulate_eagerTrace_causalHashQuery, support_map] at hresult
      obtain ⟨hashResult, _hhashResult, heq⟩ := hresult
      exact congrArg Prod.snd heq.symm

theorem filteredProbingAttackerHashQueryAt_hidden_hit
    (table : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex)
    (input : HashInput) (state : CausalHashState)
    (index : ChainValueIndex) (target : Digest)
    (hprobe : chainInputProbe? secretKey.parameter selected input =
      some (index, target))
    (hhidden : state.revealed index = none)
    (hhit : table index = target)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredProbingAttackerHashQueryAt secretKey selected input state
          (some (index, target)))).run)) :
    RevealProbeOracleSimulation.runObserved table
      AdaptiveRevealMonitor.State.empty result.2 = true := by
  rw [filteredProbingAttackerHashQueryAt_hidden_trace table secretKey selected
    input state index target hprobe hhidden result hresult]
  simp [RevealProbeOracleSimulation.runObserved,
    RevealProbeOracleSimulation.tableHits,
    AdaptiveRevealMonitor.State.empty,
    AdaptiveRevealMonitor.State.addPending, hhit]

def FilteredDirectHashStepRelation
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftBase rightBase : QueryCache HashSpec)
    (table : ChainValueIndex → Digest)
    (index : ChainValueIndex) (target : Digest)
    (leftResult : HashOutput × QueryCache HashSpec)
    (rightResult : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) : Prop :=
  RevealProbeOracleSimulation.runObserved table
      AdaptiveRevealMonitor.State.empty rightResult.2 = true ∨
    FilteredDirectMissHashResultRelation parameter selected leftBase rightBase
      table index target leftResult rightResult

def FilteredDirectNoProbeMissHashResultRelation
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftBase rightBase : QueryCache HashSpec)
    (table : ChainValueIndex → Digest)
    (leftResult : HashOutput × QueryCache HashSpec)
    (rightResult : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) : Prop :=
  leftResult.1 = rightResult.1.1 ∧
    rightResult.2 = [] ∧
    FilteredCausalStateRelation parameter selected leftBase rightBase table
      leftResult.2 rightResult.1.2

set_option maxRecDepth 100000 in
theorem relTriple_filteredProbingAttackerHashQueryAt_of_revealed_ne
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenCacheRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (leftCache : QueryCache HashSpec) (rightState : CausalHashState)
    (hstate : FilteredCausalStateRelation left.secretKey.parameter selected
      left.cache right.1.cache right.2 leftCache rightState)
    (hparameter : left.secretKey.parameter = right.1.secretKey.parameter)
    (input : HashInput) (index : ChainValueIndex) (target value : Digest)
    (hprobe : chainInputProbe? left.secretKey.parameter selected input =
      some (index, target))
    (hrevealed : rightState.revealed index = some value)
    (hne : value ≠ target) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.2)
        (filteredProbingAttackerHashQueryAt right.1.secretKey selected input
          rightState (some (index, target)))).run)
      (FilteredDirectNoProbeMissHashResultRelation
        left.secretKey.parameter selected left.cache right.1.cache right.2) := by
  have htable : right.2 index = value :=
    hstate.2.2.2.2 index value hrevealed
  have hmiss : right.2 index ≠ target := by
    rw [htable]
    exact hne
  have hcache : leftCache input = rightState.cache input :=
    programmedActual_current_caches_eq_of_probe_miss selected left right hrel
      hleftSupport leftCache rightState hstate input index target hprobe hmiss
  have hrightProbe :
      chainInputProbe? right.1.secretKey.parameter selected input =
        some (index, target) := by
    rw [← hparameter]
    exact hprobe
  cases hleft : leftCache input with
  | some output =>
      have hright : rightState.cache input = some output := by
        rw [← hcache]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_some _ hleft]
      rw [filteredProbingAttackerHashQueryAt, hrevealed]
      rw [filteredCausalAttackerHashQuery_run]
      simp only [filteredCausalAttackerHashPlan, hright, simulateQ_pure,
        WriterT.run_pure]
      apply relTriple_pure_pure
      refine ⟨rfl, rfl, ?_⟩
      unfold FilteredCausalStateRelation
      exact ⟨hstate.1, hstate.2.1, hstate.2.2.1,
        hstate.2.2.2.1, hstate.2.2.2.2.recordProbe _⟩
  | none =>
      have hright : rightState.cache input = none := by
        rw [← hcache]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_none _ hleft]
      rw [filteredProbingAttackerHashQueryAt, hrevealed]
      rw [filteredCausalAttackerHashQuery_run]
      simp only [filteredCausalAttackerHashPlan, hright,
        filteredCausalUncachedHashPlan, hrightProbe, hrevealed, hne]
      rw [simulate_eagerTrace_causalHashQuery]
      apply relTriple_map
      apply relTriple_refl
      intro result
      refine ⟨rfl, rfl, ?_⟩
      unfold FilteredCausalStateRelation
      refine ⟨hstate.1.cacheQuery input result,
        hstate.2.1.cacheQuery input result, ?_, ?_, ?_⟩
      · exact hstate.2.2.1.trans (QueryCache.le_cacheQuery leftCache hleft)
      · exact hstate.2.2.2.1
      · exact hstate.2.2.2.2.recordProbe _ |>.setCache _

theorem relTriple_filteredProbingAttackerHashQueryAt_of_hidden
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenCacheRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (leftCache : QueryCache HashSpec) (rightState : CausalHashState)
    (hstate : FilteredCausalStateRelation left.secretKey.parameter selected
      left.cache right.1.cache right.2 leftCache rightState)
    (hparameter : left.secretKey.parameter = right.1.secretKey.parameter)
    (input : HashInput) (index : ChainValueIndex) (target : Digest)
    (hprobe : chainInputProbe? left.secretKey.parameter selected input =
      some (index, target))
    (hhidden : rightState.revealed index = none) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.2)
        (filteredProbingAttackerHashQueryAt right.1.secretKey selected input
          rightState (some (index, target)))).run)
      (FilteredDirectHashStepRelation left.secretKey.parameter selected
        left.cache right.1.cache right.2 index target) := by
  by_cases hhit : right.2 index = target
  · apply relTriple_post_mono (relTriple_with_support (relTriple_true _ _))
    intro leftResult rightResult hsupport
    left
    apply filteredProbingAttackerHashQueryAt_hidden_hit right.2
      right.1.secretKey selected input rightState index target
    · rw [← hparameter]
      exact hprobe
    · exact hhidden
    · exact hhit
    · exact hsupport.2.2
  · apply relTriple_post_mono
      (relTriple_filteredProbingAttackerHashQueryAt_of_hidden_miss selected
        left right hrel hleftSupport leftCache rightState hstate hparameter
          input index target hprobe hhidden hhit)
    intro leftResult rightResult hresult
    exact Or.inr hresult

theorem relTriple_filteredKeygen_first_hidden_hash_step
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenStableRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1 ∈ support (actualFixedChainKeygen selected))
    (input : HashInput) (index : ChainValueIndex) (target : Digest)
    (hprobe : chainInputProbe? left.secretKey.parameter selected input =
      some (index, target)) :
    RelTriple
      ((randomOracle input).run left.cache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.2)
        (filteredProbingAttackerHashQueryAt right.1.secretKey selected input
          (filteredCausalKeygenState selected right.1)
            (some (index, target)))).run)
      (FilteredDirectHashStepRelation left.secretKey.parameter selected
        left.cache right.1.cache right.2 index target) := by
  have hleftKey := programmedWarmedFixedChainKeygen_support_keyResult
    selected left hleftSupport
  have hrightKey := actualFixedChainKeygen_support_keyResult
    selected right.1 hrightSupport
  have hparameter : left.secretKey.parameter =
      right.1.secretKey.parameter := by
    calc
      left.secretKey.parameter = left.publicKey.parameter :=
        (left.parameter_eq hleftKey).symm
      _ = right.1.publicKey.parameter :=
        congrArg PublicKey.parameter hrel.1.1.2.1
      _ = right.1.secretKey.parameter := right.1.parameter_eq hrightKey
  apply relTriple_filteredProbingAttackerHashQueryAt_of_hidden selected
    left right hrel.1 hleftSupport left.cache
      (filteredCausalKeygenState selected right.1)
  · exact programmedActual_filteredKeygen_stateRelation selected left right
      hrel hleftSupport hrightSupport
  · exact hparameter
  · exact hprobe
  · exact filteredCausalKeygenState_revealed selected right.1 index

end XmssSecurity
