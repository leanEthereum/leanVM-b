import XmssSecurity.Proof.CausalDirectFinalReduction

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

noncomputable def chainValueHighTableOfEdges
    (high : ChainEdgeIndex → Digest) : ChainValueIndex → Digest :=
  fun index =>
    if hzero : index.2.val = 0 then
      0
    else
      high (index.1, ⟨index.2.val - 1, by omega⟩)

@[simp]
theorem chainValueHighTableOfEdges_next
    (high : ChainEdgeIndex → Digest) (edge : ChainEdgeIndex) :
    chainValueHighTableOfEdges high
        (edge.1, chainStepNextDigit edge.2) =
      high edge := by
  unfold chainValueHighTableOfEdges
  simp only [chainStepNextDigit]
  rw [dif_neg (by omega)]
  congr 2

noncomputable def causalRevealHashQueryFromHigh
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex) :
    OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)
      (HashOutput × CausalHashState) := do
  let value ← RevealProbeOracleSimulation.revealQuery index
  let output := Rom.hashOutputEquivDigestPair.symm (high index, value)
  pure (output, causalRevealResultState secretKey selected input state
    index value output)

theorem simulate_eagerTrace_causalRevealHashQueryFromHigh
    (table high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (causalRevealHashQueryFromHigh high secretKey selected input state
        index)).run =
      pure ((Rom.hashOutputEquivDigestPair.symm
          (high index, table index),
        causalRevealResultState secretKey selected input state index
          (table index) (Rom.hashOutputEquivDigestPair.symm
            (high index, table index))),
        [RevealProbeOracleSimulation.ObservedAction.reveal
          index (table index)]) := by
  unfold causalRevealHashQueryFromHigh
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_revealQuery]
  simp

theorem chainEdgeOutputFromHigh_eq_revealOutput
    (high : ChainEdgeIndex → Digest)
    (table : ChainValueIndex → Digest) (edge : ChainEdgeIndex) :
    Rom.hashOutputEquivDigestPair.symm
        (chainValueHighTableOfEdges high
          (edge.1, chainStepNextDigit edge.2),
          table (edge.1, chainStepNextDigit edge.2)) =
      chainEdgeOutputFromHigh high table edge := by
  simp [chainEdgeOutputFromHigh, chainTableEdgeTarget]

theorem chainTableEdgeInput_not_signingComparable
    (parameter : PublicParameter) (selected : ChainIndex)
    (table : ChainValueIndex → Digest) (edge : ChainEdgeIndex) :
    ¬ SigningComparableHashInput parameter selected
      (chainTableEdgeInput parameter selected table edge) := by
  rintro (houtside | ⟨epoch, message, randomness, hencoding⟩)
  · exact chainTableEdgeInput_not_outside table parameter selected edge
      houtside
  · have hchain : AtHashAddress parameter (.chain edge.1 selected edge.2)
        (chainTableEdgeInput parameter selected table edge) := by
      simp [chainTableEdgeInput, Concrete.CacheView.chainInput]
    have hencodingAddress : AtHashAddress parameter (.encoding epoch)
        (chainTableEdgeInput parameter selected table edge) := by
      rw [hencoding]
      simp [Concrete.CacheView.encodingInput]
    have hdomain := atHashAddress_unique parameter
      (.chain edge.1 selected edge.2) (.encoding epoch)
      (chainTableEdgeInput parameter selected table edge)
      hchain hencodingAddress
    simp at hdomain

theorem FilteredCausalStateRelation.causalRevealResultState_right
    (hstate : FilteredCausalStateRelation parameter selected leftBase rightBase
      table leftCache rightState)
    (secretKey : SecretKey) (input : HashInput)
    (index : ChainValueIndex) (value : Digest) (output : HashOutput)
    (hinput : ¬ SigningComparableHashInput parameter selected input)
    (hleft : leftCache input = some output)
    (hvalue : table index = value) :
    FilteredCausalStateRelation parameter selected leftBase rightBase table
      leftCache
      (causalRevealResultState secretKey selected input rightState
        index value output) := by
  refine ⟨?_, ?_, hstate.2.2.1, ?_,
    hstate.2.2.2.2.causalRevealResultState secretKey selected input
      index value output hvalue⟩
  · intro candidate hcandidate
    have hne : candidate ≠ input := by
      intro heq
      subst candidate
      exact hinput hcandidate
    unfold causalRevealResultState
    simp only [causalRecordedState_cache]
    rw [QueryCache.cacheQuery_of_ne _ _ hne]
    exact hstate.1 candidate hcandidate
  · intro candidate
    by_cases heq : candidate = input
    · subst candidate
      left
      unfold causalRevealResultState
      simp only [causalRecordedState_cache]
      simp [hleft]
    · unfold causalRevealResultState
      simp only [causalRecordedState_cache]
      rw [QueryCache.cacheQuery_of_ne _ _ heq]
      exact hstate.2.1 candidate
  · unfold causalRevealResultState CausalHashState.recordReveal
    simpa only [causalRecordedState_keygenCache] using hstate.2.2.2.1

noncomputable def filteredCausalAttackerHashQueryFromHigh
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput) :
    StateT CausalHashState
      (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))
      HashOutput := fun state =>
  let recorded := causalRecordedState secretKey selected input state
  match filteredCausalAttackerHashPlan secretKey selected input state with
  | .cached output => pure (output, recorded)
  | .reveal index =>
      causalRevealHashQueryFromHigh high secretKey selected input state index
  | .conditioned digest => do
      let output ← RevealProbeOracleSimulation.liftProbComp
        (Rom.sampleHashOutputWithDigest digest)
      pure (output,
        { recorded with cache := recorded.cache.cacheQuery input output })
  | .fresh => (causalHashQuery input).run recorded

theorem filteredCausalAttackerHashQueryFromHigh_run
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) :
    (filteredCausalAttackerHashQueryFromHigh
      high secretKey selected input).run state =
      (let recorded := causalRecordedState secretKey selected input state
       match filteredCausalAttackerHashPlan secretKey selected input state with
       | .cached output => pure (output, recorded)
       | .reveal index =>
           causalRevealHashQueryFromHigh high secretKey selected input state index
       | .conditioned digest => do
           let output ← RevealProbeOracleSimulation.liftProbComp
             (Rom.sampleHashOutputWithDigest digest)
           pure (output,
             { recorded with cache := recorded.cache.cacheQuery input output })
       | .fresh => (causalHashQuery input).run recorded) := rfl

theorem filteredCausalAttackerHashQueryFromHigh_eq_of_plan_ne_reveal
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState)
    (hplan : ∀ index,
      filteredCausalAttackerHashPlan secretKey selected input state ≠
        .reveal index) :
    (filteredCausalAttackerHashQueryFromHigh
        high secretKey selected input).run state =
      (filteredCausalAttackerHashQuery secretKey selected input).run state := by
  rw [filteredCausalAttackerHashQueryFromHigh_run,
    filteredCausalAttackerHashQuery_run]
  generalize hcurrent :
    filteredCausalAttackerHashPlan secretKey selected input state = plan
  cases plan with
  | cached output => rfl
  | reveal index => exact (hplan index hcurrent).elim
  | conditioned digest => rfl
  | fresh => rfl

noncomputable def filteredProbingAttackerHashQueryAtFromHigh
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) : Option (ChainValueIndex × Digest) →
    OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)
      (HashOutput × CausalHashState)
  | none => (filteredCausalAttackerHashQueryFromHigh
      high secretKey selected input).run state
  | some probe =>
      match state.revealed probe.1 with
      | some _ => (filteredCausalAttackerHashQueryFromHigh
          high secretKey selected input).run state
      | none => do
          let _ ← RevealProbeOracleSimulation.probeQuery probe.1 probe.2
          (filteredCausalAttackerHashQueryFromHigh
            high secretKey selected input).run state

theorem filteredProbingAttackerHashQueryAtFromHigh_eq_of_plan_ne_reveal
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (probe : Option (ChainValueIndex × Digest))
    (hplan : ∀ index,
      filteredCausalAttackerHashPlan secretKey selected input state ≠
        .reveal index) :
    filteredProbingAttackerHashQueryAtFromHigh
        high secretKey selected input state probe =
      filteredProbingAttackerHashQueryAt
        secretKey selected input state probe := by
  have hquery := filteredCausalAttackerHashQueryFromHigh_eq_of_plan_ne_reveal
    high secretKey selected input state hplan
  cases probe with
  | none =>
      simpa [filteredProbingAttackerHashQueryAtFromHigh,
        filteredProbingAttackerHashQueryAt] using hquery
  | some probe =>
      cases hrevealed : state.revealed probe.1 with
      | some value =>
          simpa [filteredProbingAttackerHashQueryAtFromHigh,
            filteredProbingAttackerHashQueryAt, hrevealed] using hquery
      | none =>
          simp only [filteredProbingAttackerHashQueryAtFromHigh,
            filteredProbingAttackerHashQueryAt, hrevealed]
          rw [hquery]

theorem relTriple_programmed_filteredProbingAttackerHashQueryAtFromHigh_of_probe_miss
    (high : ChainValueIndex → Digest)
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
        (filteredProbingAttackerHashQueryAtFromHigh high
          right.1.secretKey selected input rightState
            (some (index, target)))).run)
      (FilteredHashResultRelation left.secretKey.parameter selected left.cache
        right.1.cache right.2) := by
  have hne : ∀ candidate,
      filteredCausalAttackerHashPlan right.1.secretKey selected input
          rightState ≠ .reveal candidate := by
    cases hleft : leftCache input with
    | none =>
        have hplan := filteredCausalAttackerHashPlan_eq_fresh_of_probe_miss
          selected left right hrel hleftSupport hrightSupport leftCache
            rightState hstate input index target hprobe hleft hmiss
        intro candidate hcand
        rw [hplan] at hcand
        cases hcand
    | some output =>
        have hcurrent := programmedActual_current_caches_eq_of_probe_miss
          selected left right hrel hleftSupport leftCache rightState hstate
            input index target hprobe hmiss
        have hright : rightState.cache input = some output := by
          rw [← hcurrent]
          exact hleft
        have hplan : filteredCausalAttackerHashPlan right.1.secretKey selected
            input rightState = .cached output := by
          unfold filteredCausalAttackerHashPlan
          rw [hright]
        intro candidate hcand
        rw [hplan] at hcand
        cases hcand
  rw [filteredProbingAttackerHashQueryAtFromHigh_eq_of_plan_ne_reveal
    high right.1.secretKey selected input rightState
      (some (index, target)) hne]
  exact relTriple_programmed_filteredProbingAttackerHashQueryAt_of_probe_miss
    selected left right hrel hleftSupport hrightSupport leftCache rightState
      hstate input index target hprobe hmiss

theorem simulate_eagerTrace_filteredProbingAttackerHashQueryAtFromHigh_hidden_eq_map
    (table high : ChainValueIndex → Digest) (secretKey : SecretKey)
    (selected : ChainIndex) (input : HashInput) (state : CausalHashState)
    (index : ChainValueIndex) (target : Digest)
    (hrevealed : state.revealed index = none) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (filteredProbingAttackerHashQueryAtFromHigh high secretKey selected input
        state (some (index, target)))).run =
      (fun result => (result.1,
        RevealProbeOracleSimulation.ObservedAction.probe index target ::
          result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((filteredCausalAttackerHashQueryFromHigh
            high secretKey selected input).run state)).run := by
  rw [filteredProbingAttackerHashQueryAtFromHigh, hrevealed, simulateQ_bind,
    WriterT.run_bind', simulate_eagerTrace_probeQuery]
  simp only [map_eq_bind_pure_comp]
  apply congrArg (fun continuation =>
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((filteredCausalAttackerHashQueryFromHigh
        high secretKey selected input).run state)).run >>= continuation)
  funext result
  rfl

theorem simulate_eagerTrace_filteredProbingAttackerHashQueryAtFromHigh_hidden_support_trace
    (table high : ChainValueIndex → Digest) (secretKey : SecretKey)
    (selected : ChainIndex) (input : HashInput) (state : CausalHashState)
    (index : ChainValueIndex) (target : Digest)
    (hrevealed : state.revealed index = none)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredProbingAttackerHashQueryAtFromHigh high secretKey selected input
          state (some (index, target)))).run)) :
    ∃ suffix, result.2 =
      RevealProbeOracleSimulation.ObservedAction.probe index target :: suffix := by
  rw [simulate_eagerTrace_filteredProbingAttackerHashQueryAtFromHigh_hidden_eq_map
    table high secretKey selected input state index target hrevealed,
      support_map] at hresult
  obtain ⟨rest, _hrest, hrestEq⟩ := hresult
  subst result
  exact ⟨rest.2, rfl⟩

theorem relTriple_filteredProbingAttackerHashQueryAtFromHigh_of_probe_hit_hidden
    (leftComputation : ProbComp α)
    (table high : ChainValueIndex → Digest) (secretKey : SecretKey)
    (selected : ChainIndex) (input : HashInput) (state : CausalHashState)
    (monitor : AdaptiveRevealMonitor.State ChainValueIndex)
    (index : ChainValueIndex) (target : Digest)
    (hrevealed : state.revealed index = none)
    (hhidden : monitor.revealed index = none)
    (hhit : table index = target) :
    RelTriple leftComputation
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredProbingAttackerHashQueryAtFromHigh high secretKey selected input
          state (some (index, target)))).run)
      (fun _ rightResult =>
        RevealProbeOracleSimulation.runObserved table monitor rightResult.2 =
          true) := by
  have hright : ∀ rightResult ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredProbingAttackerHashQueryAtFromHigh high secretKey selected input
          state (some (index, target)))).run),
      RevealProbeOracleSimulation.runObserved table monitor rightResult.2 =
        true := by
    intro rightResult hrightResult
    obtain ⟨suffix, hsuffix⟩ :=
      simulate_eagerTrace_filteredProbingAttackerHashQueryAtFromHigh_hidden_support_trace
        table high secretKey selected input state index target hrevealed
          rightResult hrightResult
    rw [hsuffix]
    exact RevealProbeOracleSimulation.runObserved_probe_hit_hidden
      table monitor index target suffix hhidden hhit
  have hprod := relTriple_prod
    (oa := leftComputation)
    (ob := (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (filteredProbingAttackerHashQueryAtFromHigh high secretKey selected input
        state (some (index, target)))).run)
    (P := fun _ => True)
    (Q := fun rightResult =>
      RevealProbeOracleSimulation.runObserved table monitor rightResult.2 = true)
    (fun _result _hresult => True.intro) hright
  apply relTriple_post_mono hprod
  intro _leftResult _rightResult hresult
  exact hresult.2

def FilteredHashUntilHitRelation
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftBase rightBase : QueryCache HashSpec)
    (table : ChainValueIndex → Digest)
    (monitor : AdaptiveRevealMonitor.State ChainValueIndex)
    (leftResult : HashOutput × QueryCache HashSpec)
    (rightResult : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) : Prop :=
  FilteredHashResultRelation parameter selected leftBase rightBase table
      leftResult rightResult ∨
    RevealProbeOracleSimulation.runObserved table monitor rightResult.2 = true

set_option maxRecDepth 100000 in
theorem relTriple_programmed_filteredProbingAttackerHashQueryAtFromHigh_of_hit_revealed
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
    (hhit : right.2 index = target)
    (hrevealed : rightState.revealed index = some target) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.2)
        (filteredProbingAttackerHashQueryAtFromHigh
          (chainValueHighTableOfEdges
            (chainEdgeHighTableOfCache left.cache
              left.secretKey.parameter selected left.table))
          right.1.secretKey selected input rightState
            (some (index, target)))).run)
      (FilteredHashResultRelation left.secretKey.parameter selected left.cache
        right.1.cache right.2) := by
  obtain ⟨step, hinput, hindex⟩ :=
    (chainInputProbe?_eq_some_iff left.secretKey.parameter selected input
      index target).mp hprobe
  have hleftKey := programmedWarmedFixedChainKeygen_support_keyResult
    selected left hleftSupport
  have hmatches := left.chainTableMatches selected hleftKey
    (programmedWarmedFixedChainKeygen_support_table
      selected left hleftSupport)
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
  have hleft : leftCache input = some output := by
    apply hstate.2.2.1
    rwa [hedgeInput] at hbase
  rw [randomOracle, QueryImpl.withCaching_run_some _ hleft]
  cases hright : rightState.cache input with
  | some rightOutput =>
      have hsame : leftCache input = rightState.cache input := by
        rcases hstate.2.1 input with hagree | ⟨_hbase, hnone⟩
        · exact hagree
        · rw [hright] at hnone
          simp at hnone
      have houtput : rightOutput = output := by
        rw [hleft, hright] at hsame
        exact Option.some.inj hsame.symm
      subst rightOutput
      have hplan : filteredCausalAttackerHashPlan right.1.secretKey selected
          input rightState = .cached output := by
        unfold filteredCausalAttackerHashPlan
        rw [hright]
      rw [filteredProbingAttackerHashQueryAtFromHigh, hrevealed,
        filteredCausalAttackerHashQueryFromHigh_run, hplan]
      apply relTriple_pure_pure
      exact ⟨rfl,
        hstate.causalRecordedState right.1.secretKey input⟩
  | none =>
      obtain ⟨revealStep, hrevealIndex, hplan⟩ :=
        filteredCausalAttackerHashPlan_eq_reveal_of_probe_hit_revealed
          selected left right hrel hleftSupport hrightSupport input rightState
            index target hprobe hright hrevealed
      have hstep : revealStep = step := by
        apply Fin.ext
        have hleftDigit := congrArg Fin.val hrevealIndex
        have hrightDigit := congrArg Fin.val hindex
        simp only [chainStepDigit] at hleftDigit hrightDigit
        omega
      subst revealStep
      rw [filteredProbingAttackerHashQueryAtFromHigh, hrevealed,
        filteredCausalAttackerHashQueryFromHigh_run, hplan,
        simulate_eagerTrace_causalRevealHashQueryFromHigh]
      apply relTriple_pure_pure
      have hconstructed :
          Rom.hashOutputEquivDigestPair.symm
              (chainValueHighTableOfEdges
                  (chainEdgeHighTableOfCache left.cache
                    left.secretKey.parameter selected left.table)
                  (index.1, chainStepNextDigit step),
                right.2 (index.1, chainStepNextDigit step)) = output := by
        calc
          _ = chainEdgeOutputFromHigh
                (chainEdgeHighTableOfCache left.cache
                  left.secretKey.parameter selected left.table)
                right.2 (index.1, step) :=
              chainEdgeOutputFromHigh_eq_revealOutput
                (chainEdgeHighTableOfCache left.cache
                  left.secretKey.parameter selected left.table)
                right.2 (index.1, step)
          _ = chainEdgeOutputFromHigh
                (chainEdgeHighTableOfCache left.cache
                  left.secretKey.parameter selected left.table)
                left.table (index.1, step) := by rw [hrel.1.1]
          _ = output := chainEdgeOutputFromHigh_eq_cached left.cache
            left.secretKey.parameter selected left.table (index.1, step) output
              hbase htruncate
      refine ⟨hconstructed.symm, ?_⟩
      rw [hconstructed]
      apply hstate.causalRevealResultState_right right.1.secretKey input
        (index.1, chainStepNextDigit step)
        (right.2 (index.1, chainStepNextDigit step)) output
      · rw [← hedgeInput]
        exact chainTableEdgeInput_not_signingComparable
          left.secretKey.parameter selected left.table (index.1, step)
      · exact hleft
      · rfl

set_option maxRecDepth 100000 in
theorem relTriple_programmed_filteredProbingAttackerHashQueryAtFromHigh_until_hit
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
    (monitor : AdaptiveRevealMonitor.State ChainValueIndex)
    (input : HashInput) (index : ChainValueIndex) (target : Digest)
    (hprobe : chainInputProbe? left.secretKey.parameter selected input =
      some (index, target))
    (hmonitor : monitor.revealed = rightState.revealed) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.2)
        (filteredProbingAttackerHashQueryAtFromHigh
          (chainValueHighTableOfEdges
            (chainEdgeHighTableOfCache left.cache
              left.secretKey.parameter selected left.table))
          right.1.secretKey selected input rightState
            (some (index, target)))).run)
      (FilteredHashUntilHitRelation left.secretKey.parameter selected
        left.cache right.1.cache right.2 monitor) := by
  by_cases hhit : right.2 index = target
  · cases hrevealed : rightState.revealed index with
    | none =>
        apply relTriple_post_mono
          (relTriple_filteredProbingAttackerHashQueryAtFromHigh_of_probe_hit_hidden
            ((randomOracle input).run leftCache) right.2
            (chainValueHighTableOfEdges
              (chainEdgeHighTableOfCache left.cache
                left.secretKey.parameter selected left.table))
            right.1.secretKey selected input rightState monitor index target
              hrevealed (by rw [hmonitor, hrevealed]) hhit)
        intro leftResult rightResult hresult
        exact Or.inr hresult
    | some value =>
        have hvalue : value = target := by
          have hagrees := hstate.2.2.2.2 index value hrevealed
          rw [hhit] at hagrees
          exact hagrees.symm
        subst value
        apply relTriple_post_mono
          (relTriple_programmed_filteredProbingAttackerHashQueryAtFromHigh_of_hit_revealed
            selected left right hrel hleftSupport hrightSupport leftCache
              rightState hstate input index target hprobe hhit hrevealed)
        intro leftResult rightResult hresult
        exact Or.inl hresult
  · apply relTriple_post_mono
      (relTriple_programmed_filteredProbingAttackerHashQueryAtFromHigh_of_probe_miss
        (chainValueHighTableOfEdges
          (chainEdgeHighTableOfCache left.cache left.secretKey.parameter
            selected left.table))
        selected left right hrel hleftSupport hrightSupport leftCache rightState
          hstate input index target hprobe hhit)
    intro leftResult rightResult hresult
    exact Or.inl hresult

end XmssSecurity
