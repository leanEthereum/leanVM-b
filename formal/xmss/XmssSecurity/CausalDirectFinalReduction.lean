import XmssSecurity.CausalDirectLazyGame
import XmssSecurity.CausalViewCoupling

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

noncomputable local instance directFinalReductionSampleableChainTable :
    SampleableType (ChainValueIndex → Digest) :=
  SampleableType.ofFintype (ChainValueIndex → Digest)

namespace RevealProbeOracleSimulation

theorem runObserved_eq_true_of_tableHits
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (table : Index → Digest) (state : AdaptiveRevealMonitor.State Index)
    (trace : ActionTrace Index)
    (hhit : tableHits state table = true) :
    runObserved table state trace = true := by
  unfold tableHits at hhit
  simp only [decide_eq_true_eq] at hhit
  obtain ⟨index, hindex⟩ := hhit
  induction trace generalizing state index with
  | nil =>
      simp only [runObserved]
      unfold tableHits
      simp only [decide_eq_true_eq]
      exact ⟨index, hindex⟩
  | cons action trace ih =>
      cases action with
      | probe probeIndex target =>
          cases hrevealed : state.revealed probeIndex with
          | none =>
              rw [runObserved, hrevealed]
              apply ih (state.addPending probeIndex target) index
              by_cases heq : index = probeIndex
              · subst index
                simp [AdaptiveRevealMonitor.State.addPending, hindex]
              · simpa [AdaptiveRevealMonitor.State.addPending,
                  Function.update_of_ne heq] using hindex
          | some value =>
              rw [runObserved, hrevealed]
              exact ih state index hindex
      | reveal revealIndex value =>
          cases hrevealed : state.revealed revealIndex with
          | some revealedValue =>
              rw [runObserved, hrevealed]
              exact ih state index hindex
          | none =>
              rw [runObserved, hrevealed]
              by_cases hcontains : table revealIndex ∈ state.pending revealIndex
              · simp [hcontains]
              · rw [if_neg hcontains]
                apply ih (state.install revealIndex (table revealIndex)) index
                by_cases heq : index = revealIndex
                · subst index
                  exact False.elim (hcontains hindex)
                · simpa [AdaptiveRevealMonitor.State.install,
                    Function.update_of_ne heq] using hindex

theorem runObserved_append_eq_true
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (table : Index → Digest) (state : AdaptiveRevealMonitor.State Index)
    (trace suffix : ActionTrace Index)
    (hhit : runObserved table state trace = true) :
    runObserved table state (trace ++ suffix) = true := by
  induction trace generalizing state with
  | nil =>
      exact runObserved_eq_true_of_tableHits table state suffix hhit
  | cons action trace ih =>
      cases action with
      | probe index target =>
          cases hrevealed : state.revealed index with
          | none =>
              rw [runObserved, hrevealed] at hhit
              rw [List.cons_append, runObserved, hrevealed]
              exact ih (state.addPending index target) hhit
          | some value =>
              rw [runObserved, hrevealed] at hhit
              rw [List.cons_append, runObserved, hrevealed]
              exact ih state hhit
      | reveal index value =>
          cases hrevealed : state.revealed index with
          | some revealedValue =>
              rw [runObserved, hrevealed] at hhit
              rw [List.cons_append, runObserved, hrevealed]
              exact ih state hhit
          | none =>
              rw [runObserved, hrevealed] at hhit
              rw [List.cons_append, runObserved, hrevealed]
              by_cases hcontains : table index ∈ state.pending index
              · simp [hcontains]
              · rw [if_neg hcontains] at hhit ⊢
                exact ih (state.install index (table index)) hhit

end RevealProbeOracleSimulation

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

theorem filteredCausalAttackerHashPlan_eq_fresh_of_probe_miss
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenCacheRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1 ∈ support (actualFixedChainKeygen selected))
    (leftCache : QueryCache HashSpec) (rightState : CausalHashState)
    (hstate : FilteredCausalStateRelation left.secretKey.parameter selected
      left.cache right.1.cache right.2 leftCache rightState)
    (input : HashInput) (index : ChainValueIndex) (target : Digest)
    (hprobe : chainInputProbe? left.secretKey.parameter selected input =
      some (index, target))
    (hcache : leftCache input = none)
    (hmiss : right.2 index ≠ target) :
    filteredCausalAttackerHashPlan right.1.secretKey selected input rightState =
      .fresh := by
  have hcurrent := programmedActual_current_caches_eq_of_probe_miss selected
    left right hrel hleftSupport leftCache rightState hstate input index target
      hprobe hmiss
  have hrightNone : rightState.cache input = none := by
    rw [← hcurrent]
    exact hcache
  have hleftKey := programmedWarmedFixedChainKeygen_support_keyResult
    selected left hleftSupport
  have hrightKey := actualFixedChainKeygen_support_keyResult selected right.1
    hrightSupport
  have hparameter : right.1.secretKey.parameter = left.secretKey.parameter := by
    calc
      right.1.secretKey.parameter = right.1.publicKey.parameter :=
        (right.1.parameter_eq hrightKey).symm
      _ = left.publicKey.parameter := congrArg PublicKey.parameter hrel.1.2.1.symm
      _ = left.secretKey.parameter := left.parameter_eq hleftKey
  unfold filteredCausalAttackerHashPlan
  unfold filteredCausalUncachedHashPlan
  cases hrevealed : rightState.revealed index with
  | none => simp [hrightNone, hparameter, hprobe, hrevealed]
  | some value =>
      have hvalue : right.2 index = value := hstate.2.2.2.2 index value hrevealed
      have hvalueNe : value ≠ target := by
        intro heq
        apply hmiss
        rw [hvalue, heq]
      simp [hrightNone, hparameter, hprobe, hrevealed, hvalueNe]

theorem simulate_eagerTrace_filteredProbingAttackerHashQueryAt_fresh_hidden
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (selected : ChainIndex) (input : HashInput) (state : CausalHashState)
    (index : ChainValueIndex) (target : Digest)
    (hrevealed : state.revealed index = none)
    (hplan : filteredCausalAttackerHashPlan secretKey selected input state =
      .fresh) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (filteredProbingAttackerHashQueryAt secretKey selected input state
        (some (index, target)))).run =
      (fun result : HashOutput × QueryCache HashSpec =>
        ((result.1,
          { (causalRecordedState secretKey selected input state) with
            cache := result.2 }),
          [RevealProbeOracleSimulation.ObservedAction.probe index target])) <$>
        ((randomOracle input).run state.cache) := by
  rw [filteredProbingAttackerHashQueryAt, hrevealed, simulateQ_bind,
    WriterT.run_bind']
  simp only [RevealProbeOracleSimulation.probeQuery]
  simp [RevealProbeOracleSimulation.eagerTraceImpl,
    RevealProbeOracleSimulation.eagerImpl,
    RevealProbeOracleSimulation.traceFragment,
    QueryImpl.withTraceAppend_apply, WriterT.run_tell]
  rw [filteredCausalAttackerHashQuery_run, hplan,
    simulate_eagerTrace_causalHashQuery]
  simp [Functor.map_map]

theorem simulate_eagerTrace_filteredProbingAttackerHashQueryAt_fresh_revealed
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (selected : ChainIndex) (input : HashInput) (state : CausalHashState)
    (index : ChainValueIndex) (target value : Digest)
    (hrevealed : state.revealed index = some value)
    (hplan : filteredCausalAttackerHashPlan secretKey selected input state =
      .fresh) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (filteredProbingAttackerHashQueryAt secretKey selected input state
        (some (index, target)))).run =
      (fun result : HashOutput × QueryCache HashSpec =>
        ((result.1,
          { (causalRecordedState secretKey selected input state) with
            cache := result.2 }),
          ([] : RevealProbeOracleSimulation.ActionTrace ChainValueIndex))) <$>
        ((randomOracle input).run state.cache) := by
  rw [filteredProbingAttackerHashQueryAt, hrevealed,
    filteredCausalAttackerHashQuery_run, hplan,
    simulate_eagerTrace_causalHashQuery]

theorem simulate_eagerTrace_filteredProbingAttackerHashQueryAt_cached_hidden
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (selected : ChainIndex) (input : HashInput) (state : CausalHashState)
    (index : ChainValueIndex) (target : Digest) (output : HashOutput)
    (hrevealed : state.revealed index = none)
    (hcache : state.cache input = some output) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (filteredProbingAttackerHashQueryAt secretKey selected input state
        (some (index, target)))).run =
      pure ((output, causalRecordedState secretKey selected input state),
        [RevealProbeOracleSimulation.ObservedAction.probe index target]) := by
  have hplan : filteredCausalAttackerHashPlan secretKey selected input state =
      .cached output := by
    simp [filteredCausalAttackerHashPlan, hcache]
  rw [filteredProbingAttackerHashQueryAt, hrevealed, simulateQ_bind,
    WriterT.run_bind']
  simp only [RevealProbeOracleSimulation.probeQuery]
  simp [RevealProbeOracleSimulation.eagerTraceImpl,
    RevealProbeOracleSimulation.eagerImpl,
    RevealProbeOracleSimulation.traceFragment,
    QueryImpl.withTraceAppend_apply, WriterT.run_tell]
  rw [filteredCausalAttackerHashQuery_run, hplan]
  simp

theorem simulate_eagerTrace_filteredProbingAttackerHashQueryAt_cached_revealed
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (selected : ChainIndex) (input : HashInput) (state : CausalHashState)
    (index : ChainValueIndex) (target value : Digest) (output : HashOutput)
    (hrevealed : state.revealed index = some value)
    (hcache : state.cache input = some output) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (filteredProbingAttackerHashQueryAt secretKey selected input state
        (some (index, target)))).run =
      pure ((output, causalRecordedState secretKey selected input state),
        ([] : RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) := by
  have hplan : filteredCausalAttackerHashPlan secretKey selected input state =
      .cached output := by
    simp [filteredCausalAttackerHashPlan, hcache]
  rw [filteredProbingAttackerHashQueryAt, hrevealed,
    filteredCausalAttackerHashQuery_run, hplan]

theorem simulate_eagerTrace_filteredProbingAttackerHashQueryAt_hidden_eq_map
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (selected : ChainIndex) (input : HashInput) (state : CausalHashState)
    (index : ChainValueIndex) (target : Digest)
    (hrevealed : state.revealed index = none) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (filteredProbingAttackerHashQueryAt secretKey selected input state
        (some (index, target)))).run =
      (fun result => (result.1,
        RevealProbeOracleSimulation.ObservedAction.probe index target ::
          result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((filteredCausalAttackerHashQuery secretKey selected input).run
            state)).run := by
  rw [filteredProbingAttackerHashQueryAt, hrevealed, simulateQ_bind,
    WriterT.run_bind', simulate_eagerTrace_probeQuery]
  simp [map_eq_bind_pure_comp, Function.comp_apply]

theorem simulate_eagerTrace_filteredProbingAttackerHashQueryAt_hidden_support_trace
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (selected : ChainIndex) (input : HashInput) (state : CausalHashState)
    (index : ChainValueIndex) (target : Digest)
    (hrevealed : state.revealed index = none)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredProbingAttackerHashQueryAt secretKey selected input state
          (some (index, target)))).run)) :
    ∃ suffix, result.2 =
      RevealProbeOracleSimulation.ObservedAction.probe index target :: suffix := by
  rw [simulate_eagerTrace_filteredProbingAttackerHashQueryAt_hidden_eq_map
    table secretKey selected input state index target hrevealed,
      support_map] at hresult
  obtain ⟨rest, _hrest, hrestEq⟩ := hresult
  subst result
  exact ⟨rest.2, rfl⟩

theorem RevealProbeOracleSimulation.runObserved_probe_hit_hidden
    (table : ChainValueIndex → Digest)
    (state : AdaptiveRevealMonitor.State ChainValueIndex)
    (index : ChainValueIndex) (target : Digest)
    (suffix : RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
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

theorem relTriple_filteredProbingAttackerHashQueryAt_of_probe_hit_hidden
    (leftComputation : ProbComp α)
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (selected : ChainIndex) (input : HashInput) (state : CausalHashState)
    (monitor : AdaptiveRevealMonitor.State ChainValueIndex)
    (index : ChainValueIndex) (target : Digest)
    (hrevealed : state.revealed index = none)
    (hhidden : monitor.revealed index = none)
    (hhit : table index = target) :
    RelTriple leftComputation
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredProbingAttackerHashQueryAt secretKey selected input state
          (some (index, target)))).run)
      (fun _ rightResult =>
        RevealProbeOracleSimulation.runObserved table monitor rightResult.2 =
          true) := by
  apply relTriple_post_mono (relTriple_prod
    (fun _result _hresult => True.intro)
    (fun rightResult hrightResult => ?_))
  · obtain ⟨suffix, hsuffix⟩ :=
      simulate_eagerTrace_filteredProbingAttackerHashQueryAt_hidden_support_trace
        table secretKey selected input state index target hrevealed rightResult
          hrightResult
    rw [hsuffix]
    exact RevealProbeOracleSimulation.runObserved_probe_hit_hidden
      table monitor index target suffix hhidden hhit
  · intro _leftResult _rightResult hresult
    exact hresult.2

def FilteredHashResultRelation
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftBase rightBase : QueryCache HashSpec)
    (table : ChainValueIndex → Digest)
    (leftResult : HashOutput × QueryCache HashSpec)
    (rightResult : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) : Prop :=
  leftResult.1 = rightResult.1.1 ∧
    FilteredCausalStateRelation parameter selected leftBase rightBase table
      leftResult.2 rightResult.1.2

theorem filteredHashResultRelation_of_randomOracleRelation
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftBase rightBase : QueryCache HashSpec)
    (table : ChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (leftCache : QueryCache HashSpec) (rightState : CausalHashState)
    (hstate : FilteredCausalStateRelation parameter selected leftBase rightBase
      table leftCache rightState)
    (leftResult rightResult : HashOutput × QueryCache HashSpec)
    (hresult : leftResult.1 = rightResult.1 ∧
      HashCachesAgreeOn (SigningComparableHashInput parameter selected)
        leftResult.2 rightResult.2 ∧
      leftCache ≤ leftResult.2 ∧ rightState.cache ≤ rightResult.2 ∧
      FilteredCacheExtensionRelation leftBase leftResult.2 rightResult.2)
    (trace : RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :
    FilteredHashResultRelation parameter selected leftBase rightBase table
      leftResult
      ((rightResult.1,
        { (causalRecordedState secretKey selected input rightState) with
          cache := rightResult.2 }), trace) := by
  refine ⟨hresult.1, hresult.2.1, hresult.2.2.2.2,
    hstate.2.2.1.trans hresult.2.2.1, ?_, ?_⟩
  · simpa using hstate.2.2.2.1
  · exact (hstate.2.2.2.2.causalRecordedState secretKey selected input).setCache _

set_option maxRecDepth 100000 in
theorem relTriple_programmed_filteredProbingAttackerHashQueryAt_of_probe_miss
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenCacheRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1 ∈ support (actualFixedChainKeygen selected))
    (leftCache : QueryCache HashSpec) (rightState : CausalHashState)
    (hstate : FilteredCausalStateRelation left.secretKey.parameter selected
      left.cache right.1.cache right.2 leftCache rightState)
    (input : HashInput) (index : ChainValueIndex) (target : Digest)
    (hprobe : chainInputProbe? left.secretKey.parameter selected input =
      some (index, target))
    (hmiss : right.2 index ≠ target) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.2)
        (filteredProbingAttackerHashQueryAt right.1.secretKey selected input
          rightState (some (index, target)))).run)
      (FilteredHashResultRelation left.secretKey.parameter selected left.cache
        right.1.cache right.2) := by
  have hcurrent := programmedActual_current_caches_eq_of_probe_miss selected
    left right hrel hleftSupport leftCache rightState hstate input index target
      hprobe hmiss
  cases hleft : leftCache input with
  | none =>
      have hplan := filteredCausalAttackerHashPlan_eq_fresh_of_probe_miss
        selected left right hrel hleftSupport hrightSupport leftCache rightState
          hstate input index target hprobe hleft hmiss
      have hbase := relTriple_randomOracle_run_of_current_eq_filtered
        (SigningComparableHashInput left.secretKey.parameter selected)
          left.cache leftCache rightState.cache input hcurrent hstate.1 hstate.2.1
      cases hrevealed : rightState.revealed index with
      | none =>
          rw [simulate_eagerTrace_filteredProbingAttackerHashQueryAt_fresh_hidden
            right.2 right.1.secretKey selected input rightState index target
              hrevealed hplan]
          have hmapped := relTriple_map (relTriple_post_mono hbase
            (fun leftResult rightResult hresult =>
              filteredHashResultRelation_of_randomOracleRelation
                left.secretKey.parameter selected left.cache right.1.cache
                right.2 right.1.secretKey input leftCache rightState hstate
                leftResult rightResult hresult
                [RevealProbeOracleSimulation.ObservedAction.probe index target]))
          simpa only [id_map] using hmapped
      | some value =>
          rw [simulate_eagerTrace_filteredProbingAttackerHashQueryAt_fresh_revealed
            right.2 right.1.secretKey selected input rightState index target value
              hrevealed hplan]
          have hmapped := relTriple_map (relTriple_post_mono hbase
            (fun leftResult rightResult hresult =>
              filteredHashResultRelation_of_randomOracleRelation
                left.secretKey.parameter selected left.cache right.1.cache
                right.2 right.1.secretKey input leftCache rightState hstate
                leftResult rightResult hresult []))
          simpa only [id_map] using hmapped
  | some output =>
      have hright : rightState.cache input = some output := by
        rw [← hcurrent]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_some _ hleft]
      cases hrevealed : rightState.revealed index with
      | none =>
          rw [simulate_eagerTrace_filteredProbingAttackerHashQueryAt_cached_hidden
            right.2 right.1.secretKey selected input rightState index target output
              hrevealed hright]
          apply relTriple_pure_pure
          apply filteredHashResultRelation_of_randomOracleRelation
            left.secretKey.parameter selected left.cache right.1.cache right.2
              right.1.secretKey input leftCache rightState hstate
          exact ⟨rfl, hstate.1, le_rfl, le_rfl, hstate.2.1⟩
      | some value =>
          rw [simulate_eagerTrace_filteredProbingAttackerHashQueryAt_cached_revealed
            right.2 right.1.secretKey selected input rightState index target value
              output hrevealed hright]
          apply relTriple_pure_pure
          apply filteredHashResultRelation_of_randomOracleRelation
            left.secretKey.parameter selected left.cache right.1.cache right.2
              right.1.secretKey input leftCache rightState hstate
          exact ⟨rfl, hstate.1, le_rfl, le_rfl, hstate.2.1⟩

set_option maxRecDepth 1000000 in
theorem evalDist_actualFixedChainKeygen_uniformTable_eq_withBase
    (chain : ChainIndex) :
    𝒟[do
      let keyView ← actualFixedChainKeygen chain
      let table ← $ᵗ (ChainValueIndex → Digest)
      pure (keyView, table)] =
    𝒟[do
      let keyView ← actualFixedChainKeygen chain
      let table ← uniformChainValueTable chain
      pure (keyView, table)] := by
  apply evalDist_bind_congr
  intro keyView _hkeyView
  unfold uniformChainValueTable
  simpa [map_eq_bind_pure_comp] using
    congrArg (fun distribution =>
        (fun table => (keyView, table)) <$> distribution)
      (Concrete.evalDist_sampledAllEpochChainValueTableOnly_eq_uniform
        0 chain).symm

set_option maxRecDepth 1000000 in
theorem relTriple_programmedWarmedFixedChainKeygen_fullUniform
    (chain : ChainIndex) :
    RelTriple
      (programmedWarmedFixedChainKeygen chain)
      (do
        let keyView ← actualFixedChainKeygen chain
        let table ← $ᵗ (ChainValueIndex → Digest)
        pure (keyView, table))
      (ProgrammedActualKeygenFullRelation chain) := by
  exact relTriple_of_evalDist_eq_right
    (evalDist_actualFixedChainKeygen_uniformTable_eq_withBase chain).symm
      (relTriple_programmedWarmedFixedChainKeygen_withBase_full chain)

end XmssSecurity
