import XmssSecurity.CappedGlobalChainHighHashRevealCoupling

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

def GlobalFilteredHashUntilHitRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (monitor : AdaptiveRevealMonitor.State GlobalChainValueIndex)
    (leftResult : HashOutput × QueryCache HashSpec)
    (rightResult : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) : Prop :=
  GlobalFilteredHashResultRelation left right leftResult rightResult ∨
    RevealProbeOracleSimulation.runObserved right.2 monitor rightResult.2 = true

theorem simulate_eagerTrace_globalProbeQuery
    (table : GlobalChainValueIndex → Digest)
    (index : GlobalChainValueIndex) (target : Digest) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (RevealProbeOracleSimulation.probeQuery index target)).run =
        pure ((), [RevealProbeOracleSimulation.ObservedAction.probe
          index target]) := by
  simp [RevealProbeOracleSimulation.probeQuery,
    RevealProbeOracleSimulation.eagerTraceImpl,
    RevealProbeOracleSimulation.eagerImpl,
    RevealProbeOracleSimulation.traceFragment,
    QueryImpl.withTraceAppend_apply, WriterT.run_tell]

theorem globalRunObserved_probe_hit_hidden
    (table : GlobalChainValueIndex → Digest)
    (state : AdaptiveRevealMonitor.State GlobalChainValueIndex)
    (index : GlobalChainValueIndex) (target : Digest)
    (suffix : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hhidden : state.revealed index = none)
    (hhit : table index = target) :
    RevealProbeOracleSimulation.runObserved table state
      (RevealProbeOracleSimulation.ObservedAction.probe index target :: suffix) =
        true := by
  rw [RevealProbeOracleSimulation.runObserved, hhidden]
  apply RevealProbeOracleSimulation.runObserved_eq_true_of_tableHits
  unfold RevealProbeOracleSimulation.tableHits
  simp only [decide_eq_true_eq]
  refine ⟨index, ?_⟩
  simp [AdaptiveRevealMonitor.State.addPending, hhit]

theorem simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_probeThenFresh
    (table high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (target : Digest)
    (hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
      .probeThenFresh index target) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((globalCausalAttackerHashQueryFromHigh high secretKey input).run
        state)).run =
      (fun result : HashOutput × QueryCache HashSpec =>
        ((result.1,
          (globalCausalRecordedState secretKey input state).setCache result.2),
          [RevealProbeOracleSimulation.ObservedAction.probe index target])) <$>
        ((randomOracle input).run state.cache) := by
  rw [globalCausalAttackerHashQueryFromHigh_run, hplan, simulateQ_bind,
    WriterT.run_bind', simulate_eagerTrace_globalProbeQuery]
  simp only [map_eq_bind_pure_comp]
  rw [simulate_eagerTrace_globalCausalHashQuery]
  rw [map_eq_bind_pure_comp]
  simp [Function.comp_def]

theorem relTriple_programmed_globalFilteredHashQuery_probeThenFresh_of_baseNone
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (leftCache : QueryCache HashSpec) (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right.1 leftCache
      rightState)
    (input : HashInput) (index : GlobalChainValueIndex) (target : Digest)
    (hbaseNone : left.cache input = none)
    (hplan : globalFilteredCausalAttackerHashPlan right.1.1.secretKey input
      rightState = .probeThenFresh index target) :
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
  let trace : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex :=
    [RevealProbeOracleSimulation.ObservedAction.probe index target]
  let wrap := fun result : HashOutput × QueryCache HashSpec =>
    ((result.1, recorded.setCache result.2), trace)
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
  rw [simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_probeThenFresh
    right.1.2 (globalChainValueHighTableOfEdges right.2)
      right.1.1.secretKey input rightState index target hplan]
  simpa [wrap, trace, recorded, GlobalCausalHashState.setCache] using hmapped

theorem relTriple_programmed_globalFilteredHashQuery_probeThenFresh_until_hit
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (leftCache : QueryCache HashSpec) (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right.1 leftCache
      rightState)
    (monitor : AdaptiveRevealMonitor.State GlobalChainValueIndex)
    (hmonitor : monitor.revealed = rightState.revealed)
    (input : HashInput) (index : GlobalChainValueIndex) (target : Digest)
    (hhidden : rightState.revealed index = none)
    (hplan : globalFilteredCausalAttackerHashPlan right.1.1.secretKey input
      rightState = .probeThenFresh index target)
    (hbaseNone : right.1.2 index ≠ target → left.cache input = none) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        ((globalCausalAttackerHashQueryFromHigh
          (globalChainValueHighTableOfEdges right.2) right.1.1.secretKey
            input).run rightState)).run)
      (GlobalFilteredHashUntilHitRelation left right.1 monitor) := by
  by_cases hhit : right.1.2 index = target
  · have hmonitorHidden : monitor.revealed index = none := by
      rw [hmonitor, hhidden]
    have hright : ∀ result ∈ support
        ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
          ((globalCausalAttackerHashQueryFromHigh
            (globalChainValueHighTableOfEdges right.2) right.1.1.secretKey
              input).run rightState)).run),
        RevealProbeOracleSimulation.runObserved right.1.2 monitor result.2 =
          true := by
      intro result hresult
      rw [simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_probeThenFresh
        right.1.2 (globalChainValueHighTableOfEdges right.2)
          right.1.1.secretKey input rightState index target hplan,
        support_map] at hresult
      obtain ⟨raw, _hraw, rfl⟩ := hresult
      exact globalRunObserved_probe_hit_hidden
        right.1.2 monitor index target [] hmonitorHidden hhit
    have hproduct := relTriple_prod
      (oa := (randomOracle input).run leftCache)
      (ob := (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        ((globalCausalAttackerHashQueryFromHigh
          (globalChainValueHighTableOfEdges right.2) right.1.1.secretKey
            input).run rightState)).run)
      (P := fun _ => True)
      (Q := fun result => RevealProbeOracleSimulation.runObserved
        right.1.2 monitor result.2 = true)
      (fun _ _ => True.intro) hright
    apply relTriple_post_mono hproduct
    intro _leftResult _rightResult hresult
    exact Or.inr hresult.2
  · apply relTriple_post_mono
      (relTriple_programmed_globalFilteredHashQuery_probeThenFresh_of_baseNone
        left right leftCache rightState hstate input index target
          (hbaseNone hhit) hplan)
    intro _leftResult _rightResult hresult
    exact Or.inl hresult

theorem globalChainInputProbe?_eq_some_iff
    (parameter : PublicParameter) (input : HashInput)
    (index : GlobalChainValueIndex) (target : Digest) :
    globalChainInputProbe? parameter input = some (index, target) ↔
      ∃ step : ChainStep,
        input = Concrete.CacheView.chainInput parameter index.2.1 index.1
          step target ∧ index.2.2 = chainStepDigit step := by
  constructor
  · intro hprobe
    unfold globalChainInputProbe? at hprobe
    split at hprobe
    · rename_i hexists
      let data := hexists.choose
      have hdata := hexists.choose_spec
      simp only [Option.some.injEq, Prod.mk.injEq] at hprobe
      obtain ⟨hindex, htarget⟩ := hprobe
      refine ⟨data.2.2.1, ?_, ?_⟩
      · rw [hdata]
        rw [← congrArg (fun value : GlobalChainValueIndex => value.2.1) hindex,
          ← congrArg (fun value : GlobalChainValueIndex => value.1) hindex,
          ← htarget]
      · exact (congrArg (fun value : GlobalChainValueIndex => value.2.2)
          hindex).symm
    · simp at hprobe
  · rintro ⟨step, rfl, hindex⟩
    rw [globalChainInputProbe?_chainInput]
    rw [← hindex]

theorem programmedGlobal_left_chainValue_eq_table
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (index : GlobalChainValueIndex) :
    Wots.walk
        (Concrete.CacheView.chainStep left.cache left.secretKey.parameter
          index.2.1 index.1)
        0 index.2.2.val (left.secretKey.chainStart index.2.1 index.1) =
      right.1.2 index := by
  change globalKeygenChainValueTable left.cache left.secretKey index =
    right.1.2 index
  rw [trajectoryProgrammedGlobalChainKeygen_support_table left hleftSupport]
  exact congrFun hrel.1.toStable.1.1 index

theorem programmedGlobal_left_cache_chainInput_eq_none_of_probe_miss
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (input : HashInput) (index : GlobalChainValueIndex) (target : Digest)
    (hprobe : globalChainInputProbe? left.secretKey.parameter input =
      some (index, target))
    (hmiss : right.1.2 index ≠ target) :
    left.cache input = none := by
  obtain ⟨step, hinput, hindex⟩ :=
    (globalChainInputProbe?_eq_some_iff left.secretKey.parameter input index
      target).mp hprobe
  rw [hinput]
  apply Concrete.keygen_cache_chainInput_eq_none_of_ne left.keyResult
    (trajectoryProgrammedGlobalChainKeygen_support_keyResult left hleftSupport)
  intro heq
  apply hmiss
  rw [← programmedGlobal_left_chainValue_eq_table left right hrel
    hleftSupport index]
  rw [hindex]
  simpa [ProgrammedGlobalChainKeygenView.keyResult, chainStepDigit] using
    heq.symm

theorem relTriple_programmed_globalFilteredChainHashQuery_until_hit
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
    (monitor : AdaptiveRevealMonitor.State GlobalChainValueIndex)
    (hmonitor : monitor.revealed = rightState.revealed)
    (input : HashInput) (index : GlobalChainValueIndex) (target : Digest)
    (hprobe : globalChainInputProbe? left.secretKey.parameter input =
      some (index, target)) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        ((globalCausalAttackerHashQueryFromHigh
          (globalChainValueHighTableOfEdges right.2) right.1.1.secretKey
            input).run rightState)).run)
      (GlobalFilteredHashUntilHitRelation left right.1 monitor) := by
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
  have hprobeRight : globalChainInputProbe?
      right.1.1.secretKey.parameter input = some (index, target) := by
    rw [← hparameter]
    exact hprobe
  cases hcache : rightState.cache input with
  | some output =>
      apply relTriple_post_mono
        (relTriple_programmed_globalFilteredHashQuery_cached left right
          leftCache rightState hstate input output hcache)
      intro _leftResult _rightResult hresult
      exact Or.inl hresult
  | none =>
      obtain ⟨step, hinput, hindex⟩ :=
        (globalChainInputProbe?_eq_some_iff left.secretKey.parameter input
          index target).mp hprobe
      have hnext : index.2.2.val + 1 < chainLength := by
        rw [hindex]
        exact (chainStepNextDigit step).isLt
      cases hhidden : rightState.revealed index with
      | none =>
          have hplan := globalFilteredCausalAttackerHashPlan_eq_probeThenFresh
            right.1.1.secretKey input rightState index target hcache hprobeRight
              hhidden hnext
          exact
            relTriple_programmed_globalFilteredHashQuery_probeThenFresh_until_hit
              left right leftCache rightState hstate monitor hmonitor input index
                target hhidden hplan
                  (programmedGlobal_left_cache_chainInput_eq_none_of_probe_miss
                    left right hrel hleftSupport input index target hprobe)
      | some value =>
          by_cases hvalue : value = target
          · subst value
            have hhit : right.1.2 index = target :=
              hstate.2.2.2.2 index target hhidden
            have htable : left.table = right.1.2 := hrel.1.toStable.1.1
            have htarget : left.table index = target :=
              (congrFun htable index).trans hhit
            have hedgeInput : input = globalChainTableEdgeInput
                left.secretKey.parameter left.table
                  (index.1, index.2.1, step) := by
              unfold globalChainTableEdgeInput
              rw [hinput]
              rw [← hindex, htarget]
            rw [hedgeInput] at hcache ⊢
            apply relTriple_post_mono
              (relTriple_programmed_globalFilteredHashQuery_revealEdge left
                right hrel hleftSupport hrightSupport leftCache rightState
                  hstate (index.1, index.2.1, step) hcache ?_)
            · intro _leftResult _rightResult hresult
              exact Or.inl hresult
            · rw [← hindex, hhit]
              exact hhidden
          · have hmiss : right.1.2 index ≠ target := by
              intro hhit
              exact hvalue ((hstate.2.2.2.2 index value hhidden).symm.trans
                hhit)
            have hbaseNone :=
              programmedGlobal_left_cache_chainInput_eq_none_of_probe_miss
                left right hrel hleftSupport input index target hprobe hmiss
            have hplan : globalFilteredCausalAttackerHashPlan
                right.1.1.secretKey input rightState = .fresh := by
              rw [globalFilteredCausalAttackerHashPlan, hcache, hprobeRight]
              simp [globalFilteredCausalUncachedAttackerHashPlan, hhidden,
                hvalue]
            apply relTriple_post_mono
              (relTriple_programmed_globalFilteredHashQuery_fresh left right
                leftCache rightState hstate input hbaseNone hplan)
            intro _leftResult _rightResult hresult
            exact Or.inl hresult

end XmssSecurity.CappedChain
