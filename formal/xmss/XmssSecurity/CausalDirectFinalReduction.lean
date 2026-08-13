import VCVio.ProgramLogic.Relational.FromUnary
import XmssSecurity.ChainEdgeHighUniformity
import XmssSecurity.CausalDirectLazyGame
import XmssSecurity.CausalViewCoupling

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

attribute [local instance] presamplingSampleableChainEdges

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

theorem filteredCausalAttackerHashPlan_of_cache_none
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (hcache : state.cache input = none) :
    filteredCausalAttackerHashPlan secretKey selected input state =
      filteredCausalUncachedHashPlan secretKey selected input state := by
  unfold filteredCausalAttackerHashPlan
  rw [hcache]

theorem filteredCausalUncachedHashPlan_eq_fresh_of_probe_miss
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex) (target : Digest)
    (hprobe : chainInputProbe? secretKey.parameter selected input =
      some (index, target))
    (hmiss : ∀ value, state.revealed index = some value → value ≠ target) :
    filteredCausalUncachedHashPlan secretKey selected input state = .fresh := by
  unfold filteredCausalUncachedHashPlan
  rw [hprobe]
  unfold filteredCausalUncachedHashPlanAt
  change (match state.revealed index with
    | some value =>
        if value = target then
          if hnext : index.2.val + 1 < chainLength then
            FilteredCausalHashPlan.reveal
              (index.1, ⟨index.2.val + 1, hnext⟩)
          else
            FilteredCausalHashPlan.fresh
        else
          FilteredCausalHashPlan.fresh
    | none => FilteredCausalHashPlan.fresh) = FilteredCausalHashPlan.fresh
  cases hrevealed : state.revealed index with
  | none => rfl
  | some value =>
      change (if value = target then
        if hnext : index.2.val + 1 < chainLength then
          FilteredCausalHashPlan.reveal
            (index.1, ⟨index.2.val + 1, hnext⟩)
        else
          FilteredCausalHashPlan.fresh
        else
          FilteredCausalHashPlan.fresh) = FilteredCausalHashPlan.fresh
      rw [if_neg (hmiss value hrevealed)]

theorem filteredCausalUncachedHashPlan_eq_reveal_of_probe_hit
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex) (target : Digest)
    (step : ChainStep)
    (hprobe : chainInputProbe? secretKey.parameter selected input =
      some (index, target))
    (hrevealed : state.revealed index = some target)
    (hindex : index.2 = chainStepDigit step) :
    filteredCausalUncachedHashPlan secretKey selected input state =
      .reveal (index.1, chainStepNextDigit step) := by
  unfold filteredCausalUncachedHashPlan
  rw [hprobe]
  unfold filteredCausalUncachedHashPlanAt
  change (match state.revealed index with
    | some value =>
        if value = target then
          if hnext : index.2.val + 1 < chainLength then
            FilteredCausalHashPlan.reveal
              (index.1, ⟨index.2.val + 1, hnext⟩)
          else
            FilteredCausalHashPlan.fresh
        else
          FilteredCausalHashPlan.fresh
    | none => FilteredCausalHashPlan.fresh) =
      .reveal (index.1, chainStepNextDigit step)
  rw [hrevealed]
  change (if target = target then
    if hnext : index.2.val + 1 < chainLength then
      FilteredCausalHashPlan.reveal
        (index.1, ⟨index.2.val + 1, hnext⟩)
    else
      FilteredCausalHashPlan.fresh
    else
      FilteredCausalHashPlan.fresh) =
        .reveal (index.1, chainStepNextDigit step)
  rw [if_pos rfl]
  split
  · rename_i hnext
    apply congrArg FilteredCausalHashPlan.reveal
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change index.2.val + 1 = (chainStepNextDigit step).val
      rw [congrArg Fin.val hindex]
      rfl
  · rename_i hnext
    apply False.elim
    apply hnext
    rw [hindex]
    exact (chainStepNextDigit step).isLt

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
  rw [filteredCausalAttackerHashPlan_of_cache_none
    right.1.secretKey selected input rightState hrightNone]
  apply filteredCausalUncachedHashPlan_eq_fresh_of_probe_miss
    right.1.secretKey selected input rightState index target
  · rw [hparameter]
    exact hprobe
  · intro value hrevealed heq
    apply hmiss
    rw [hstate.2.2.2.2 index value hrevealed, heq]

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
  rw [filteredCausalAttackerHashQuery_run, hplan]
  dsimp only
  change (Prod.map id (fun trace =>
      RevealProbeOracleSimulation.ObservedAction.probe index target :: trace) <$>
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((causalHashQuery input).run
        (causalRecordedState secretKey selected input state))).run) = _
  rw [simulate_eagerTrace_causalHashQuery table input
    (causalRecordedState secretKey selected input state)]
  simp only [causalRecordedState_cache, causalRecordedState_keygenCache,
    causalRecordedState_revealed]
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
    filteredCausalAttackerHashQuery_run, hplan]
  dsimp only
  rw [simulate_eagerTrace_causalHashQuery table input
    (causalRecordedState secretKey selected input state)]
  simp only [causalRecordedState_cache]

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
    unfold filteredCausalAttackerHashPlan
    rw [hcache]
  rw [filteredProbingAttackerHashQueryAt, hrevealed, simulateQ_bind,
    WriterT.run_bind']
  simp only [RevealProbeOracleSimulation.probeQuery]
  simp [RevealProbeOracleSimulation.eagerTraceImpl,
    RevealProbeOracleSimulation.eagerImpl,
    RevealProbeOracleSimulation.traceFragment,
    QueryImpl.withTraceAppend_apply, WriterT.run_tell]
  rw [filteredCausalAttackerHashQuery_run, hplan]
  dsimp only
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
    unfold filteredCausalAttackerHashPlan
    rw [hcache]
  rw [filteredProbingAttackerHashQueryAt, hrevealed,
    filteredCausalAttackerHashQuery_run, hplan]
  dsimp only
  simp

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
  simp only [map_eq_bind_pure_comp]
  apply congrArg (fun continuation =>
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((filteredCausalAttackerHashQuery secretKey selected input).run state)).run
        >>= continuation)
  funext result
  rfl

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
  have hright : ∀ rightResult ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredProbingAttackerHashQueryAt secretKey selected input state
          (some (index, target)))).run),
      RevealProbeOracleSimulation.runObserved table monitor rightResult.2 =
        true := by
    intro rightResult hrightResult
    obtain ⟨suffix, hsuffix⟩ :=
      simulate_eagerTrace_filteredProbingAttackerHashQueryAt_hidden_support_trace
        table secretKey selected input state index target hrevealed rightResult
          hrightResult
    rw [hsuffix]
    exact RevealProbeOracleSimulation.runObserved_probe_hit_hidden
      table monitor index target suffix hhidden hhit
  have hprod := relTriple_prod
    (oa := leftComputation)
    (ob := (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (filteredProbingAttackerHashQueryAt secretKey selected input state
        (some (index, target)))).run)
    (P := fun _ => True)
    (Q := fun rightResult =>
      RevealProbeOracleSimulation.runObserved table monitor rightResult.2 = true)
    (fun _result _hresult => True.intro) hright
  apply relTriple_post_mono hprod
  intro _leftResult _rightResult hresult
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
  exact ⟨hresult.1, hstate.causalRecordedStateSetCache secretKey input
    leftResult.2 rightResult.2 hresult.2.1 hresult.2.2.2.2
      hresult.2.2.1⟩

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
          simpa only [show (fun x : HashOutput × QueryCache HashSpec => x) = id
            from rfl, id_map] using hmapped
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
          simpa only [show (fun x : HashOutput × QueryCache HashSpec => x) = id
            from rfl, id_map] using hmapped
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
          refine ⟨rfl, ?_⟩
          exact hstate.causalRecordedState right.1.secretKey input
      | some value =>
          rw [simulate_eagerTrace_filteredProbingAttackerHashQueryAt_cached_revealed
            right.2 right.1.secretKey selected input rightState index target value
              output hrevealed hright]
          apply relTriple_pure_pure
          refine ⟨rfl, ?_⟩
          exact hstate.causalRecordedState right.1.secretKey input

theorem programmedCurrentCache_has_revealed_chain_edge
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
    (input : HashInput) (index : ChainValueIndex) (target : Digest)
    (hprobe : chainInputProbe? left.secretKey.parameter selected input =
      some (index, target))
    (hhit : right.2 index = target) :
    ∃ (step : ChainStep) (output : HashOutput),
      index.2 = chainStepDigit step ∧
      leftCache input = some output ∧
      truncateHash output = right.2 (index.1, chainStepNextDigit step) := by
  obtain ⟨step, hinput, hindex⟩ :=
    (chainInputProbe?_eq_some_iff left.secretKey.parameter selected input
      index target).mp hprobe
  have hleftKey := programmedWarmedFixedChainKeygen_support_keyResult
    selected left hleftSupport
  have htable := programmedWarmedFixedChainKeygen_support_table
    selected left hleftSupport
  have hmatches := left.chainTableMatches selected hleftKey htable
  obtain ⟨output, hbase, htruncate⟩ := hmatches.2 (index.1, step)
  have hvalue : left.table (index.1, chainStepDigit step) = target := by
    rw [hrel.1.1, ← hindex]
    exact hhit
  have hedgeInput :
      chainTableEdgeInput left.secretKey.parameter selected left.table
          (index.1, step) = input := by
    rw [hinput]
    simp only [chainTableEdgeInput]
    rw [hvalue]
  refine ⟨step, output, hindex, ?_, ?_⟩
  · apply hstate.2.2.1
    rwa [hedgeInput] at hbase
  · rw [htruncate, chainTableEdgeTarget, hrel.1.1]

theorem filteredCausalAttackerHashPlan_eq_reveal_of_probe_hit_revealed
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenCacheRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1 ∈ support (actualFixedChainKeygen selected))
    (input : HashInput) (state : CausalHashState)
    (index : ChainValueIndex) (target : Digest)
    (hprobe : chainInputProbe? left.secretKey.parameter selected input =
      some (index, target))
    (hcache : state.cache input = none)
    (hrevealed : state.revealed index = some target) :
    ∃ step : ChainStep,
      index.2 = chainStepDigit step ∧
      filteredCausalAttackerHashPlan right.1.secretKey selected input state =
        .reveal (index.1, chainStepNextDigit step) := by
  obtain ⟨step, _hinput, hindex⟩ :=
    (chainInputProbe?_eq_some_iff left.secretKey.parameter selected input
      index target).mp hprobe
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
  refine ⟨step, hindex, ?_⟩
  rw [filteredCausalAttackerHashPlan_of_cache_none
    right.1.secretKey selected input state hcache]
  apply filteredCausalUncachedHashPlan_eq_reveal_of_probe_hit
    right.1.secretKey selected input state index target step
  · rw [hparameter]
    exact hprobe
  · exact hrevealed
  · exact hindex

noncomputable def chainEdgeHighTableOfCache
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (selected : ChainIndex) (table : ChainValueIndex → Digest) :
    ChainEdgeIndex → Digest := fun edge =>
  match cache (chainTableEdgeInput parameter selected table edge) with
  | none => 0
  | some output => (Rom.hashOutputEquivDigestPair output).1

def chainEdgeOutputFromHigh
    (high : ChainEdgeIndex → Digest)
    (table : ChainValueIndex → Digest) (edge : ChainEdgeIndex) : HashOutput :=
  Rom.hashOutputEquivDigestPair.symm
    (high edge, chainTableEdgeTarget table edge)

theorem sampleHashOutputsWithDigests_support_info :
    ∀ (targets : List Digest) (outputs : List HashOutput),
      outputs ∈ support (sampleHashOutputsWithDigests targets) →
      outputs.length = targets.length ∧ outputs.map truncateHash = targets := by
  intro targets
  induction targets with
  | nil =>
      intro outputs houtputs
      simp only [sampleHashOutputsWithDigests_nil, support_pure,
        Set.mem_singleton_iff] at houtputs
      subst outputs
      simp
  | cons target targets ih =>
      intro outputs houtputs
      rw [sampleHashOutputsWithDigests_cons, mem_support_bind_iff] at houtputs
      obtain ⟨output, houtput, hrest⟩ := houtputs
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst outputs
      obtain ⟨hlength, htargets⟩ := ih rest hrest
      exact ⟨by simp [hlength], by
        simp [Rom.sampleHashOutputWithDigest_support_truncate
          target output houtput, htargets]⟩

theorem eq_on_list_of_map_eq
    {α β : Type} (left right : α → β) (values : List α)
    (heq : values.map left = values.map right) :
    ∀ value ∈ values, left value = right value := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.cons.injEq] at heq
      intro value hvalue
      rcases List.mem_cons.mp hvalue with rfl | htail
      · exact heq.1
      · exact ih heq.2 value htail

theorem chainEdgeHighTableOfCache_installChainTableEdgeOutputs
    (parameter : PublicParameter) (selected : ChainIndex)
    (table : ChainValueIndex → Digest) (outputs : List HashOutput)
    (hlength : outputs.length = allChainEdges.length)
    (htargets : outputs.map truncateHash = chainTableEdgeTargets table) :
    chainEdgeHighTableOfCache
        (installChainTableEdgeOutputs ∅ parameter selected table
          allChainEdges outputs)
        parameter selected table =
      chainEdgeHighTableOfTape outputs := by
  let installed := installChainTableEdgeOutputs ∅ parameter selected table
    allChainEdges outputs
  have hinfo := installChainTableEdgeOutputs_info parameter selected table
    allChainEdges outputs ∅ allChainEdges_nodup (by simp) hlength htargets
  have hpairs : List.Forall₂
      (fun edge output =>
        installed (chainTableEdgeInput parameter selected table edge) =
            some output ∧
          truncateHash output = chainTableEdgeTarget table edge)
      allChainEdges outputs := by
    simpa [installed] using hinfo.2
  have hpairsHigh : List.Forall₂
      (fun edge high =>
        chainEdgeHighTableOfCache installed parameter selected table edge = high)
      allChainEdges (outputs.map hashOutputHigh) := by
    rw [List.forall₂_map_right_iff]
    apply hpairs.imp
    intro edge output houtput
    simp [chainEdgeHighTableOfCache, installed, houtput.1, hashOutputHigh]
  have hmaps : allChainEdges.map
      (chainEdgeHighTableOfCache installed parameter selected table) =
      outputs.map hashOutputHigh := by
    rw [← List.forall₂_eq_eq_eq, List.forall₂_map_left_iff]
    exact hpairsHigh
  funext edge
  apply eq_on_list_of_map_eq
    (chainEdgeHighTableOfCache installed parameter selected table)
    (chainEdgeHighTableOfTape outputs) allChainEdges
  · rw [hmaps]
    unfold chainEdgeHighTableOfTape
    exact (map_chainEdgeTableOfTape (outputs.map hashOutputHigh)
      (by simpa using hlength)).symm
  · exact mem_allChainEdges edge

theorem evalDist_programChainTableEdgesTrace_highTable_eq_uniform
    (parameter : PublicParameter) (selected : ChainIndex)
    (table : ChainValueIndex → Digest) :
    𝒟[(fun result : List HashOutput × QueryCache HashSpec =>
      chainEdgeHighTableOfCache result.2 parameter selected table) <$>
        programChainTableEdgesTrace ∅ parameter selected table allChainEdges] =
    𝒟[$ᵗ (ChainEdgeIndex → Digest)] := by
  calc
    _ = 𝒟[(fun result : List HashOutput × QueryCache HashSpec =>
        chainEdgeHighTableOfCache result.2 parameter selected table) <$>
      ((fun outputs =>
        (outputs, installChainTableEdgeOutputs ∅ parameter selected table
          allChainEdges outputs)) <$>
        sampleHashOutputsWithDigests (chainTableEdgeTargets table))] := by
      unfold chainTableEdgeTargets
      rw [evalDist_map, evalDist_programChainTableEdgesTrace_eq_install,
        ← evalDist_map]
    _ = 𝒟[chainEdgeHighTableOfTape <$>
        sampleHashOutputsWithDigests (chainTableEdgeTargets table)] := by
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      apply RevealProbeOracleSimulation.evalDist_bind_congr_of_support
      intro outputs houtputs
      obtain ⟨hlength, htargets⟩ :=
        sampleHashOutputsWithDigests_support_info
          (chainTableEdgeTargets table) outputs houtputs
      have hlength' : outputs.length = allChainEdges.length := by
        calc
          outputs.length = (allChainEdges.map
              (chainTableEdgeTarget table)).length := by
            simpa only [chainTableEdgeTargets] using hlength
          _ = allChainEdges.length := by simp
      rw [chainEdgeHighTableOfCache_installChainTableEdgeOutputs
        parameter selected table outputs hlength' htargets]
      simp only [Function.comp_apply]
    _ = 𝒟[$ᵗ (ChainEdgeIndex → Digest)] :=
      evalDist_sampleChainEdgeOutputs_highTable_eq_uniform table

theorem truncateHash_chainEdgeOutputFromHigh
    (high : ChainEdgeIndex → Digest)
    (table : ChainValueIndex → Digest) (edge : ChainEdgeIndex) :
    truncateHash (chainEdgeOutputFromHigh high table edge) =
      chainTableEdgeTarget table edge := by
  simp [chainEdgeOutputFromHigh]

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
