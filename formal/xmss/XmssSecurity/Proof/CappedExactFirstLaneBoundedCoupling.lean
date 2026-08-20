import XmssSecurity.Proof.CappedExactFirstLaneAccounting
import XmssSecurity.Proof.CappedGlobalChainHighActionTrace
import XmssSecurity.Proof.CappedExactFirstLaneEager
import XmssSecurity.Proof.FirstLaneEagerBound
import XmssSecurity.Proof.MarginalCoupling

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000

def globalHighExactStateProjection
    (state : GlobalHighExactMonitoredState) :
    GlobalExactTracedState :=
  GlobalExactTracedState.mk state.1.1.causal state.1.2 state.2

theorem verifierHashQueryCost_eq_if (input : OracleWorld.Domain) :
    verifierHashQueryCost input =
      (if input matches .inr _ then 1 else 0) := by
  rcases input with n | hashInput <;> rfl

def globalFirstLaneExactFullProjection {α : Type}
    (chainPrefix : RevealProbeOracleSimulation.ActionTrace
      GlobalChainValueIndex)
    (result : (α × GlobalExactTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) :
    (α × GlobalExactTracedState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex :=
  (result.1, chainPrefix ++ result.2.chainActions)

theorem map_eagerTrace_erasure_eq {α : Type}
    (base : GlobalChainValueIndex → Digest)
    (chainPrefix : RevealProbeOracleSimulation.ActionTrace
      GlobalChainValueIndex)
    (firstLane : OracleComp GlobalFirstLaneWorld
      (α × GlobalExactTracedState))
    (direct : OracleComp
      (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (α × GlobalExactTracedState))
    (herase : GlobalFirstLaneErases firstLane direct) :
    (fun result => (result.1, chainPrefix ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          direct).run =
      globalFirstLaneExactFullProjection chainPrefix <$>
        (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
          firstLane).run := by
  have htarget :=
    simulate_globalFirstLaneEagerTrace_chainProjection base firstLane
  rw [herase] at htarget
  have htarget' := congrArg
    (fun computation =>
      (fun result => (result.1, chainPrefix ++ result.2)) <$> computation)
    htarget
  unfold globalFirstLaneExactFullProjection
  simpa [Functor.map_map, Function.comp_def] using htarget'.symm

theorem map_globalHighExactMonitored_action_eq_firstLane
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (highState : GlobalHighExactMonitoredState) :
    globalHighExactFullProjection <$>
        (globalHighExactMonitoredMappedAdversaryImpl
          ((keyView, base), edgeHigh) input).run highState =
      globalFirstLaneExactFullProjection highState.1.1.trace <$>
        (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
          ((globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh
            input).run (globalHighExactStateProjection highState))).run := by
  classical
  have hhigh := map_globalHighExactMonitored_adversary_full_query keyView
    base edgeHigh input highState
  have herase := globalFirstLaneErase_exactTracedMappedAdversaryImpl keyView
    edgeHigh input (globalHighExactStateProjection highState)
  rw [hhigh]
  exact map_eagerTrace_erasure_eq base highState.1.1.trace _ _ herase

theorem relTriple_globalHighExactMonitored_firstLane_action
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (highState : GlobalHighExactMonitoredState) :
    RelTriple
      ((globalHighExactMonitoredMappedAdversaryImpl
        ((keyView, base), edgeHigh) input).run highState)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
        ((globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh
          input).run (globalHighExactStateProjection highState))).run)
      (fun highResult firstLaneResult =>
        globalHighExactFullProjection highResult =
          globalFirstLaneExactFullProjection highState.1.1.trace
            firstLaneResult ∧
        highResult ∈ support
          ((globalHighExactMonitoredMappedAdversaryImpl
            ((keyView, base), edgeHigh) input).run highState) ∧
        firstLaneResult ∈ support
          ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
            ((globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh
              input).run (globalHighExactStateProjection highState))).run)) := by
  classical
  letI : DecidableEq
      (((OracleWorld + SigningSpec).Range input ×
        GlobalExactTracedState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
    Classical.decEq _
  apply relTriple_of_evalDist_map_eq_with_support_general
  exact congrArg evalDist
    (map_globalHighExactMonitored_action_eq_firstLane keyView base edgeHigh
      input highState)

theorem globalHighExactMonitoredMappedAdversaryImpl_preserves_traceConsistent
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalHighExactMonitoredState)
    (hconsistent : state.1.1.TraceConsistent right.1.2)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalHighExactMonitoredState)
    (hresult : result ∈ support
      ((globalHighExactMonitoredMappedAdversaryImpl right input).run state)) :
    result.2.1.1.TraceConsistent right.1.2 := by
  rw [globalHighExactMonitoredMappedAdversaryImpl_query_eq_map,
    support_map] at hresult
  obtain ⟨baseResult, hbase, rfl⟩ := hresult
  exact globalHighMonitoredMappedAdversaryImpl_preserves_traceConsistent
    right input state.1 hconsistent baseResult hbase

theorem globalHighExactMonitoredMappedAdversaryImpl_support_actionTrace_eq
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalHighExactMonitoredState)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalHighExactMonitoredState)
    (hresult : result ∈ support
      ((globalHighExactMonitoredMappedAdversaryImpl right input).run state)) :
    result.2.1.2 =
      state.1.2 ++ attackerActionFragment input result.1 := by
  rw [globalHighExactMonitoredMappedAdversaryImpl_query_eq_map,
    support_map] at hresult
  obtain ⟨baseResult, hbase, rfl⟩ := hresult
  exact globalHighMonitoredMappedAdversaryImpl_support_actionTrace_eq right
    input state.1 baseResult hbase

def SourceFirstLaneExactGoodStateRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftState : SourceExactTracedState)
    (firstLaneState : GlobalExactTracedState)
    (trace : FirstLaneOracleSimulation.ActionTrace
      GlobalChainValueIndex) : Prop :=
  ∃ highState : GlobalHighExactMonitoredState,
    GlobalSigningExactMonitoredStateRelation left right leftState highState ∧
    firstLaneState = globalHighExactStateProjection highState ∧
    trace.chainActions = highState.1.1.trace ∧
    highState.1.1.TraceConsistent right.2

theorem cappedBothTracedMappedAdversaryImpl_support_unlogged_output
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : SourceExactTracedState)
    (result : (OracleWorld + SigningSpec).Range input ×
      SourceExactTracedState)
    (hresult : result ∈ support
      ((cappedBothTracedMappedAdversaryImpl publicKey secretKey input).run
        state)) :
    result.1 ∈ support
      (sourceUnloggedMappedAdversaryImpl publicKey secretKey input) := by
  rw [cappedBothTracedMappedAdversaryImpl_query_eq_sourceExactMap,
    support_map] at hresult
  obtain ⟨signingResult, hsigning, rfl⟩ := hresult
  have hdirect : (signingResult.1,
      sourceSigningTracedStateProjection signingResult.2) ∈ support
      ((sourceDirectTracedMappedAdversaryImpl publicKey secretKey input).run
        (sourceSigningTracedStateProjection
          (sourceExactSigningProjection state))) := by
    rw [← sourceSigningTracedMappedAdversaryImpl_query_projection,
      support_map]
    exact ⟨signingResult, hsigning, rfl⟩
  exact (sourceDirectTracedMappedAdversaryImpl_support_info publicKey
    secretKey input
      (sourceSigningTracedStateProjection
        (sourceExactSigningProjection state))
      (signingResult.1,
        sourceSigningTracedStateProjection signingResult.2) hdirect).1

theorem cappedBothTracedMappedAdversaryImpl_run_signingProjection
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : SourceExactTracedState) :
    (fun result => (result.1, sourceExactSigningProjection result.2)) <$>
        (simulateQ
          (cappedBothTracedMappedAdversaryImpl publicKey secretKey)
          computation).run initialState =
      (simulateQ
        (sourceSigningTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (sourceExactSigningProjection initialState) := by
  induction computation using OracleComp.inductionOn generalizing
      initialState with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, StateT.run_bind, map_bind]
      simp only [id_map]
      simp_rw [ih]
      rw [cappedBothTracedMappedAdversaryImpl_query_eq_sourceExactMap]
      simp [sourceExactQueryResult, sourceExactSigningProjection]

theorem sourceSigningTracedMappedAdversaryImpl_run_projection
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : SourceSigningTracedState) :
    (fun result =>
        (result.1, sourceSigningTracedStateProjection result.2)) <$>
        (simulateQ
          (sourceSigningTracedMappedAdversaryImpl publicKey secretKey)
          computation).run initialState =
      (simulateQ
        (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (sourceSigningTracedStateProjection initialState) := by
  induction computation using OracleComp.inductionOn generalizing
      initialState with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, StateT.run_bind, map_bind]
      simp only [id_map]
      simp_rw [ih]
      calc
        _ = (do
            let head ← (fun result => (result.1,
              sourceSigningTracedStateProjection result.2)) <$>
                (sourceSigningTracedMappedAdversaryImpl publicKey secretKey
                  input).run initialState
            (simulateQ
              (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
              (next head.1)).run head.2) := by rw [bind_map_left]
        _ = _ := by
          rw [sourceSigningTracedMappedAdversaryImpl_query_projection]

theorem cappedBothTracedMappedAdversaryImpl_run_directProjection
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : SourceExactTracedState) :
    (fun result => (result.1, (result.2.1.1.1, result.2.2))) <$>
        (simulateQ
          (cappedBothTracedMappedAdversaryImpl publicKey secretKey)
          computation).run initialState =
      (simulateQ
        (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialState.1.1.1, initialState.2) := by
  calc
    _ = (fun result => (result.1,
          sourceSigningTracedStateProjection result.2)) <$>
        ((fun result => (result.1,
          sourceExactSigningProjection result.2)) <$>
          (simulateQ
            (cappedBothTracedMappedAdversaryImpl publicKey secretKey)
            computation).run initialState) := by
      simp [Functor.map_map, sourceExactSigningProjection,
        sourceSigningTracedStateProjection]
    _ = _ := by
      rw [cappedBothTracedMappedAdversaryImpl_run_signingProjection,
        sourceSigningTracedMappedAdversaryImpl_run_projection]
      rfl

theorem cappedBothTracedMappedAdversaryImpl_residual_hashQueryBound
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (finish : α → OracleComp OracleWorld β) (queries : Nat)
    (hbound : (simulateQ
      (sourceUnloggedMappedAdversaryImpl publicKey secretKey) computation >>=
        finish).IsQueryBoundP (· matches .inr _) queries)
    (initialState : SourceExactTracedState)
    (hempty : initialState.2 = [])
    (result : α × SourceExactTracedState)
    (hresult : result ∈ support
      ((simulateQ
        (cappedBothTracedMappedAdversaryImpl publicKey secretKey)
          computation).run initialState)) :
    result.2.2.hashInputs.length ≤ queries ∧
      (finish result.1).IsQueryBoundP (· matches .inr _)
        (queries - result.2.2.hashInputs.length) := by
  have hprojected : (result.1, (result.2.1.1.1, result.2.2)) ∈ support
      ((simulateQ
        (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
          computation).run (initialState.1.1.1, initialState.2)) := by
    rw [← cappedBothTracedMappedAdversaryImpl_run_directProjection,
      support_map]
    exact ⟨result, hresult, rfl⟩
  exact sourceDirectTracedMappedAdversary_residual_hashQueryBound publicKey
    secretKey computation finish queries hbound initialState.1.1.1
      (result.1, (result.2.1.1.1, result.2.2)) (by simpa [hempty] using hprojected)

theorem relTriple_sourceExact_firstLane_action
    (used : Nat)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (input : (OracleWorld + SigningSpec).Domain)
    (leftState : SourceExactTracedState)
    (firstLaneState : GlobalExactTracedState)
    (trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hstate : SourceFirstLaneExactGoodStateRelation left right.1 leftState
      firstLaneState trace)
    (hcount : FirstLaneOracleSimulation.hazardCount trace ≤ used)
    (hused : leftState.2.hashInputs.length = used) :
    RelTriple
      ((cappedBothTracedMappedAdversaryImpl left.publicKey
        (Concrete.materializePrecomputation left.cache left.secretKey)
          input).run leftState)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
        ((globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2
          input).run firstLaneState)).run)
      (fun leftResult firstLaneResult =>
        (leftResult.1 = firstLaneResult.1.1 ∧
          SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2
            firstLaneResult.1.2 (trace ++ firstLaneResult.2) ∧
          FirstLaneOracleSimulation.hazardCount
              (trace ++ firstLaneResult.2) ≤
            used + directHashActionCost input ∧
          leftResult.2.2.hashInputs.length =
            used + directHashActionCost input) ∨
        (FirstLaneOracleSimulation.CombinedHit right.1.2
            (trace ++ firstLaneResult.2) ∧
          FirstLaneOracleSimulation.hazardCount
              (trace ++ firstLaneResult.2) ≤
            used + directHashActionCost input)) := by
  rcases hstate with ⟨highState, hsourceHigh, hfirstLaneState,
    hchainTrace, hconsistent⟩
  subst firstLaneState
  have hsource :=
    relTriple_programmed_globalHighExactMonitored_action left right hrel
      hleftSupport hrightSupport leftState highState hsourceHigh input
  have hhigh := relTriple_globalHighExactMonitored_firstLane_action
    right.1.1 right.1.2 right.2 input highState
  apply relTriple_post_mono (relTriple_trans_exists hsource hhigh)
  intro leftResult firstLaneResult hglued
  obtain ⟨highResult, hsourceResult, hhighResult⟩ := hglued
  obtain ⟨hprojection, hhighSupport, hfirstLaneSupport⟩ := hhighResult
  have hfragmentCount : FirstLaneOracleSimulation.hazardCount
      firstLaneResult.2 ≤ directHashActionCost input :=
    FirstLaneOracleSimulation.simulate_eagerTrace_support_hazardCount_le
      right.1.2
      ((globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2
        input).run (globalHighExactStateProjection highState))
      (directHashActionCost input)
      (globalFirstLaneExactTracedMappedAdversaryImpl_hazardBound right.1.1
        right.2 input (globalHighExactStateProjection highState))
      firstLaneResult hfirstLaneSupport
  have htotalCount : FirstLaneOracleSimulation.hazardCount
      (trace ++ firstLaneResult.2) ≤
        used + directHashActionCost input := by
    rw [FirstLaneOracleSimulation.hazardCount_append]
    omega
  have hnextConsistent :=
    globalHighExactMonitoredMappedAdversaryImpl_preserves_traceConsistent
      right input highState hconsistent highResult hhighSupport
  have hhighActionTrace :=
    globalHighExactMonitoredMappedAdversaryImpl_support_actionTrace_eq right
      input highState highResult hhighSupport
  rcases hsourceResult with hgood | hbad
  · apply Or.inl
    refine ⟨hgood.1.trans ?_, ?_, htotalCount, ?_⟩
    · exact congrArg (fun result => result.1.1) hprojection
    · refine ⟨highResult.2, hgood.2, ?_, ?_, hnextConsistent⟩
      · exact congrArg (fun result => result.1.2) hprojection |>.symm
      · rw [FirstLaneOracleSimulation.ActionTrace.chainActions_append,
          hchainTrace]
        exact congrArg Prod.snd hprojection |>.symm
    · have hinitialTrace : leftState.2 = highState.1.2 := hsourceHigh.1.2
      have hfinalTrace : leftResult.2.2 = highResult.2.1.2 := hgood.2.1.2
      rw [hfinalTrace, hhighActionTrace, ← hinitialTrace,
        AttackerActionTrace.hashInputs_append, List.length_append,
        attackerActionFragment_hashInputs_length, hused]
  · apply Or.inr
    have hchainProjection : highResult.2.1.1.trace =
        highState.1.1.trace ++ firstLaneResult.2.chainActions := by
      simpa [globalHighExactFullProjection,
        globalFirstLaneExactFullProjection] using
          congrArg Prod.snd hprojection
    have hchainHit : RevealProbeOracleSimulation.runObserved right.1.2
        AdaptiveRevealMonitor.State.empty
          (trace ++ firstLaneResult.2).chainActions = true := by
      rw [FirstLaneOracleSimulation.ActionTrace.chainActions_append,
        hchainTrace]
      rw [← hchainProjection]
      exact highResult.2.1.1.bad_implies_runObserved right.1.2
        hnextConsistent hbad
    have hhit : FirstLaneOracleSimulation.CombinedHit right.1.2
        (trace ++ firstLaneResult.2) := Or.inr hchainHit
    exact ⟨hhit, htotalCount⟩

theorem relTriple_sourceExact_firstLane_adversary_boundedHit
    (countLimit hitLimit used fuel : Nat)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (finish : α → OracleComp OracleWorld β)
    (hbound : (simulateQ
      (sourceUnloggedMappedAdversaryImpl left.publicKey
        (Concrete.materializePrecomputation left.cache left.secretKey))
        computation >>= finish).IsQueryBoundP (· matches .inr _) fuel)
    (leftState : SourceExactTracedState)
    (firstLaneState : GlobalExactTracedState)
    (trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hstate : SourceFirstLaneExactGoodStateRelation left right.1 leftState
      firstLaneState trace)
    (hcount : FirstLaneOracleSimulation.hazardCount trace ≤ used)
    (hused : leftState.2.hashInputs.length = used)
    (htotal : used + fuel ≤ countLimit)
    (hlimits : countLimit ≤ hitLimit) :
    RelTriple
      ((simulateQ
        (cappedBothTracedMappedAdversaryImpl left.publicKey
          (Concrete.materializePrecomputation left.cache left.secretKey))
          computation).run leftState)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
        ((simulateQ
          (globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2)
          computation).run firstLaneState)).run)
      (fun leftResult firstLaneResult =>
        (leftResult.1 = firstLaneResult.1.1 ∧
          SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2
            firstLaneResult.1.2 (trace ++ firstLaneResult.2) ∧
          FirstLaneOracleSimulation.hazardCount
              (trace ++ firstLaneResult.2) ≤
                leftResult.2.2.hashInputs.length ∧
          leftResult.2.2.hashInputs.length ≤ countLimit) ∨
        FirstLaneOracleSimulation.CombinedHit right.1.2
          (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
            (trace ++ firstLaneResult.2))) := by
  induction computation using OracleComp.inductionOn generalizing leftState
      firstLaneState trace used fuel finish with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure']
      apply relTriple_pure_pure
      apply Or.inl
      refine ⟨rfl, ?_, ?_, ?_⟩
      · simpa [FirstLaneOracleSimulation.ActionTrace.chainActions] using hstate
      · simpa [FirstLaneOracleSimulation.hazardCount, hused] using hcount
      · have : used ≤ countLimit := by omega
        simpa [hused] using this
  | query_bind input next ih =>
      rw [simulateQ_query_bind, bind_assoc] at hbound
      simp only [StateT.run_bind, simulateQ_bind,
        WriterT.run_bind', simulateQ_spec_query]
      apply relTriple_bind (relTriple_with_support
        (relTriple_sourceExact_firstLane_action used left right hrel
          hleftSupport hrightSupport input leftState firstLaneState trace
            hstate hcount hused))
      intro headLeft headFirstLane hhead
      have houtput :=
        cappedBothTracedMappedAdversaryImpl_support_unlogged_output
          left.publicKey
          (Concrete.materializePrecomputation left.cache left.secretKey)
          input leftState headLeft hhead.2.1
      let continuation := fun response =>
        simulateQ
          (sourceUnloggedMappedAdversaryImpl left.publicKey
            (Concrete.materializePrecomputation left.cache left.secretKey))
            (next ((OracleSpec.query input).cont response)) >>= finish
      have hstepBound :
          (liftM (sourceUnloggedMappedAdversaryImpl left.publicKey
            (Concrete.materializePrecomputation left.cache left.secretKey)
              input) >>= continuation).IsQueryBoundP
              (· matches .inr _) fuel := by
        exact hbound
      have hrestBound :=
        sourceUnloggedMappedAdversaryImpl_continuation_hashQueryBound
          left.publicKey
            (Concrete.materializePrecomputation left.cache left.secretKey)
              input continuation fuel hstepBound headLeft.1 houtput
      rw [attackerActionFragment_hashInputs_length] at hrestBound
      rcases hhead.1 with hgood | hhit
      · obtain ⟨hvalue, hnextState, hnextCount, hnextUsed⟩ := hgood
        have hrestBoundFirstLane :
            (continuation headFirstLane.1.1).IsQueryBoundP
              (· matches .inr _)
                (fuel - directHashActionCost input) := by
          rw [← hvalue]
          exact hrestBound.2
        let appendTrace := fun result :
            ((α × GlobalExactTracedState) ×
              FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) =>
          Prod.map id (fun tail => headFirstLane.2 ++ tail) result
        have hrec := ih headFirstLane.1.1
          (used + directHashActionCost input)
            (fuel - directHashActionCost input) finish hrestBoundFirstLane
            headLeft.2 headFirstLane.1.2 (trace ++ headFirstLane.2)
              hnextState hnextCount hnextUsed (by omega)
        change RelTriple _ _ _ at hrec
        have hlifted : RelTriple
            (id <$> (simulateQ
              (cappedBothTracedMappedAdversaryImpl left.publicKey
                (Concrete.materializePrecomputation left.cache left.secretKey))
                (next headFirstLane.1.1)).run headLeft.2)
            (appendTrace <$>
              (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
                ((simulateQ
                  (globalFirstLaneExactTracedMappedAdversaryImpl right.1.1
                    right.2) (next headFirstLane.1.1)).run
                      headFirstLane.1.2)).run)
            (fun leftResult firstLaneResult =>
              (leftResult.1 = firstLaneResult.1.1 ∧
                SourceFirstLaneExactGoodStateRelation left right.1
                  leftResult.2 firstLaneResult.1.2
                    (trace ++ firstLaneResult.2) ∧
                FirstLaneOracleSimulation.hazardCount
                  (trace ++ firstLaneResult.2) ≤
                    leftResult.2.2.hashInputs.length ∧
                leftResult.2.2.hashInputs.length ≤ countLimit) ∨
              FirstLaneOracleSimulation.CombinedHit right.1.2
                (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
                  (trace ++ firstLaneResult.2))) := by
          apply relTriple_map
          apply relTriple_post_mono hrec
          intro leftResult firstLaneResult hresult
          simpa [appendTrace, Prod.map, List.append_assoc] using hresult
        rw [hvalue]
        change RelTriple _ (appendTrace <$> _) _
        simpa only [id_map] using hlifted
      · obtain ⟨hhit, hnextCount⟩ := hhit
        have hnextLimit : FirstLaneOracleSimulation.hazardCount
            (trace ++ headFirstLane.2) ≤ hitLimit :=
          hnextCount.trans (by omega)
        have henforced : FirstLaneOracleSimulation.CombinedHit right.1.2
            (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
              (trace ++ headFirstLane.2)) := by
          rw [FirstLaneOracleSimulation.enforceHazardTrace_eq_self_of_count_le
            (trace ++ headFirstLane.2) hitLimit hnextLimit]
          exact hhit
        let appendTrace := fun result :
            ((α × GlobalExactTracedState) ×
              FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) =>
          Prod.map id (fun tail => headFirstLane.2 ++ tail) result
        have hlifted : RelTriple
            (id <$> (simulateQ
              (cappedBothTracedMappedAdversaryImpl left.publicKey
                (Concrete.materializePrecomputation left.cache left.secretKey))
                (next headLeft.1)).run headLeft.2)
            (appendTrace <$>
              (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
                ((simulateQ
                  (globalFirstLaneExactTracedMappedAdversaryImpl right.1.1
                    right.2) (next headFirstLane.1.1)).run
                      headFirstLane.1.2)).run)
            (fun _leftResult firstLaneResult =>
              FirstLaneOracleSimulation.CombinedHit right.1.2
                (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
                  (trace ++ firstLaneResult.2))) := by
          apply relTriple_map
          apply relTriple_post_mono
            (relTriple_prod (fun _ _ => True.intro) (fun _ _ => True.intro))
          intro _leftResult firstLaneResult _hresults
          simpa [appendTrace, Prod.map, List.append_assoc] using
            FirstLaneOracleSimulation.CombinedHit.enforce_append_of_prefix
              right.1.2 hitLimit (trace ++ headFirstLane.2)
                firstLaneResult.2 henforced
        change RelTriple _ (appendTrace <$> _) _
        apply relTriple_post_mono (by simpa only [id_map] using hlifted)
        intro _leftResult _firstLaneResult hresult
        exact Or.inr hresult

def sourceExactVerifierResult
    (initialState : SourceExactTracedState)
    (result : OracleWorld.Range input × SourceSigningTracedState) :
    OracleWorld.Range input × SourceExactTracedState :=
  (result.1, ((result.2.1, initialState.1.2), result.2.2))

noncomputable def sourceExactTracedVerifierImpl : QueryImpl OracleWorld
    (StateT SourceExactTracedState ProbComp) := fun input =>
  StateT.mk fun state => sourceExactVerifierResult state <$>
    (sourceSigningTracedVerifierImpl input).run
      (sourceExactSigningProjection state)

theorem sourceExactTracedVerifierImpl_run_eq
    (computation : OracleComp OracleWorld α)
    (initialState : SourceExactTracedState) :
    (simulateQ sourceExactTracedVerifierImpl computation).run initialState =
      (fun result : α × SourceSigningTracedState =>
        (result.1, ((result.2.1, initialState.1.2), result.2.2))) <$>
        (simulateQ sourceSigningTracedVerifierImpl computation).run
          (sourceExactSigningProjection initialState) := by
  induction computation using OracleComp.inductionOn generalizing
      initialState with
  | pure value => simp [sourceExactSigningProjection]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, StateT.run_bind, map_bind]
      unfold sourceExactTracedVerifierImpl
      simp only [id_map, StateT.run_mk, bind_map_left]
      apply bind_congr
      intro head
      change (simulateQ sourceExactTracedVerifierImpl
          (next head.1)).run ((head.2.1, initialState.1.2), head.2.2) = _
      rw [ih]
      simp [sourceExactSigningProjection]

def globalHighExactVerifierResult
    (initialState : GlobalHighExactMonitoredState)
    (result : OracleWorld.Range input × GlobalMonitoredTracedState) :
    OracleWorld.Range input × GlobalHighExactMonitoredState :=
  (result.1, (result.2, initialState.2))

noncomputable def globalHighExactMonitoredVerifierImpl
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) : QueryImpl OracleWorld
        (StateT GlobalHighExactMonitoredState ProbComp) := fun input =>
  StateT.mk fun state => globalHighExactVerifierResult state <$>
    (globalHighMonitoredVerifierImpl right input).run state.1

theorem relTriple_programmed_globalHighExactMonitored_verifier_action
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftState : SourceExactTracedState)
    (highState : GlobalHighExactMonitoredState)
    (hstate : GlobalSigningExactMonitoredStateRelation left right.1
      leftState highState)
    (input : OracleWorld.Domain) :
    RelTriple
      ((sourceExactTracedVerifierImpl input).run leftState)
      ((globalHighExactMonitoredVerifierImpl right input).run highState)
      (fun leftResult highResult =>
        (leftResult.1 = highResult.1 ∧
          GlobalSigningExactMonitoredStateRelation left right.1
            leftResult.2 highResult.2) ∨ highResult.2.1.1.bad) := by
  have hbase :=
    relTriple_programmed_globalHighMonitored_signingVerifierQuery left right
      hrel hleftSupport hrightSupport
        (sourceExactSigningProjection leftState) highState.1 hstate.1 input
  unfold sourceExactTracedVerifierImpl
    globalHighExactMonitoredVerifierImpl
  simp only [StateT.run_mk]
  apply relTriple_map
  apply relTriple_post_mono hbase
  intro leftResult highResult hresult
  rcases hresult with hgood | hbad
  · exact Or.inl ⟨hgood.1, hgood.2, hstate.2⟩
  · exact Or.inr hbad

theorem map_globalHighExactMonitored_verifier_action_eq_firstLane
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : OracleWorld.Domain)
    (highState : GlobalHighExactMonitoredState) :
    globalHighExactFullProjection <$>
        (globalHighExactMonitoredVerifierImpl
          ((keyView, base), edgeHigh) input).run highState =
      globalFirstLaneExactFullProjection highState.1.1.trace <$>
        (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
          ((globalFirstLaneExactTracedVerifierImpl keyView edgeHigh input).run
            (globalHighExactStateProjection highState))).run := by
  classical
  have hhigh :=
    map_simulate_globalHighExactMonitored_verifier_full_projection keyView
      base edgeHigh (liftM (OracleWorld.query input)) highState
  simp only [simulateQ_spec_query] at hhigh
  have herase := globalFirstLaneErase_exactTracedVerifierImpl keyView edgeHigh
    input (globalHighExactStateProjection highState)
  have hhigh' : globalHighExactFullProjection <$>
        (globalHighExactMonitoredVerifierImpl
          ((keyView, base), edgeHigh) input).run highState =
      (fun result => (result.1, highState.1.1.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((globalHighDirectExactTracedVerifierImpl keyView edgeHigh input).run
            (globalHighExactStateProjection highState))).run := by
    unfold globalHighExactMonitoredVerifierImpl
    simp only [StateT.run_mk, Functor.map_map]
    simpa [globalHighExactFullProjection,
      globalHighExactVerifierResult, globalHighExactStateProjection,
      Function.comp_def] using hhigh
  rw [hhigh']
  exact map_eagerTrace_erasure_eq base highState.1.1.trace _ _ herase

theorem relTriple_globalHighExactMonitored_firstLane_verifier_action
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : OracleWorld.Domain)
    (highState : GlobalHighExactMonitoredState) :
    RelTriple
      ((globalHighExactMonitoredVerifierImpl
        ((keyView, base), edgeHigh) input).run highState)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
        ((globalFirstLaneExactTracedVerifierImpl keyView edgeHigh input).run
          (globalHighExactStateProjection highState))).run)
      (fun highResult firstLaneResult =>
        globalHighExactFullProjection highResult =
          globalFirstLaneExactFullProjection highState.1.1.trace
            firstLaneResult ∧
        highResult ∈ support
          ((globalHighExactMonitoredVerifierImpl
            ((keyView, base), edgeHigh) input).run highState) ∧
        firstLaneResult ∈ support
          ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
            ((globalFirstLaneExactTracedVerifierImpl keyView edgeHigh input).run
              (globalHighExactStateProjection highState))).run)) := by
  classical
  letI : DecidableEq
      ((OracleWorld.Range input × GlobalExactTracedState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
    Classical.decEq _
  apply relTriple_of_evalDist_map_eq_with_support_general
  exact congrArg evalDist
    (map_globalHighExactMonitored_verifier_action_eq_firstLane keyView base
      edgeHigh input highState)

theorem globalHighExactMonitoredVerifierImpl_preserves_traceConsistent
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : OracleWorld.Domain)
    (state : GlobalHighExactMonitoredState)
    (hconsistent : state.1.1.TraceConsistent right.1.2)
    (result : OracleWorld.Range input × GlobalHighExactMonitoredState)
    (hresult : result ∈ support
      ((globalHighExactMonitoredVerifierImpl right input).run state)) :
    result.2.1.1.TraceConsistent right.1.2 := by
  unfold globalHighExactMonitoredVerifierImpl at hresult
  rw [StateT.run_mk, support_map] at hresult
  obtain ⟨baseResult, hbase, rfl⟩ := hresult
  exact globalHighMonitoredVerifierImpl_preserves_traceConsistent right input
    state.1 hconsistent baseResult hbase

theorem relTriple_sourceExact_firstLane_verifier_action
    (used : Nat)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (input : OracleWorld.Domain)
    (leftState : SourceExactTracedState)
    (firstLaneState : GlobalExactTracedState)
    (trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hstate : SourceFirstLaneExactGoodStateRelation left right.1 leftState
      firstLaneState trace)
    (hcount : FirstLaneOracleSimulation.hazardCount trace ≤ used) :
    RelTriple
      ((sourceExactTracedVerifierImpl input).run leftState)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
        ((globalFirstLaneExactTracedVerifierImpl right.1.1 right.2 input).run
          firstLaneState)).run)
      (fun leftResult firstLaneResult =>
        (leftResult.1 = firstLaneResult.1.1 ∧
          SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2
            firstLaneResult.1.2 (trace ++ firstLaneResult.2) ∧
          FirstLaneOracleSimulation.hazardCount
              (trace ++ firstLaneResult.2) ≤
            used + verifierHashQueryCost input) ∨
        (FirstLaneOracleSimulation.CombinedHit right.1.2
            (trace ++ firstLaneResult.2) ∧
          FirstLaneOracleSimulation.hazardCount
              (trace ++ firstLaneResult.2) ≤
            used + verifierHashQueryCost input)) := by
  rcases hstate with ⟨highState, hsourceHigh, hfirstLaneState,
    hchainTrace, hconsistent⟩
  subst firstLaneState
  have hsource :=
    relTriple_programmed_globalHighExactMonitored_verifier_action left right
      hrel hleftSupport hrightSupport leftState highState hsourceHigh input
  have hhigh :=
    relTriple_globalHighExactMonitored_firstLane_verifier_action right.1.1
      right.1.2 right.2 input highState
  apply relTriple_post_mono (relTriple_trans_exists hsource hhigh)
  intro leftResult firstLaneResult hglued
  obtain ⟨highResult, hsourceResult, hhighResult⟩ := hglued
  obtain ⟨hprojection, hhighSupport, hfirstLaneSupport⟩ := hhighResult
  have hfragmentCount : FirstLaneOracleSimulation.hazardCount
      firstLaneResult.2 ≤ verifierHashQueryCost input := by
    apply FirstLaneOracleSimulation.simulate_eagerTrace_support_hazardCount_le
      right.1.2
      ((globalFirstLaneExactTracedVerifierImpl right.1.1 right.2 input).run
        (globalHighExactStateProjection highState))
      (verifierHashQueryCost input) _ firstLaneResult hfirstLaneSupport
    change ((globalFirstLaneExactTracedVerifierImpl right.1.1 right.2 input
      ).run (globalHighExactStateProjection highState)).IsQueryBoundP
        FirstLaneOracleSimulation.IsHazardQuery (verifierHashQueryCost input)
    rw [verifierHashQueryCost_eq_if]
    exact globalFirstLaneExactTracedVerifierImpl_hazardBound right.1.1
      right.2 input (globalHighExactStateProjection highState)
  have htotalCount : FirstLaneOracleSimulation.hazardCount
      (trace ++ firstLaneResult.2) ≤
        used + verifierHashQueryCost input := by
    rw [FirstLaneOracleSimulation.hazardCount_append]
    omega
  have hnextConsistent :=
    globalHighExactMonitoredVerifierImpl_preserves_traceConsistent right input
      highState hconsistent highResult hhighSupport
  rcases hsourceResult with hgood | hbad
  · apply Or.inl
    refine ⟨hgood.1.trans ?_, ?_, htotalCount⟩
    · exact congrArg (fun result => result.1.1) hprojection
    · refine ⟨highResult.2, hgood.2, ?_, ?_, hnextConsistent⟩
      · exact congrArg (fun result => result.1.2) hprojection |>.symm
      · rw [FirstLaneOracleSimulation.ActionTrace.chainActions_append,
          hchainTrace]
        exact congrArg Prod.snd hprojection |>.symm
  · apply Or.inr
    have hchainProjection : highResult.2.1.1.trace =
        highState.1.1.trace ++ firstLaneResult.2.chainActions := by
      simpa [globalHighExactFullProjection,
        globalFirstLaneExactFullProjection] using
          congrArg Prod.snd hprojection
    have hchainHit : RevealProbeOracleSimulation.runObserved right.1.2
        AdaptiveRevealMonitor.State.empty
          (trace ++ firstLaneResult.2).chainActions = true := by
      rw [FirstLaneOracleSimulation.ActionTrace.chainActions_append,
        hchainTrace, ← hchainProjection]
      exact highResult.2.1.1.bad_implies_runObserved right.1.2
        hnextConsistent hbad
    exact ⟨Or.inr hchainHit, htotalCount⟩

theorem relTriple_sourceExact_firstLane_verifier_boundedHit
    (countLimit hitLimit used fuel : Nat)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (computation : OracleComp OracleWorld α)
    (hbound : computation.IsQueryBoundP (· matches .inr _) fuel)
    (leftState : SourceExactTracedState)
    (firstLaneState : GlobalExactTracedState)
    (trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hstate : SourceFirstLaneExactGoodStateRelation left right.1 leftState
      firstLaneState trace)
    (hcount : FirstLaneOracleSimulation.hazardCount trace ≤ used)
    (htotal : used + fuel ≤ countLimit)
    (hlimits : countLimit ≤ hitLimit) :
    RelTriple
      ((simulateQ sourceExactTracedVerifierImpl computation).run leftState)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
        ((simulateQ
          (globalFirstLaneExactTracedVerifierImpl right.1.1 right.2)
          computation).run firstLaneState)).run)
      (fun leftResult firstLaneResult =>
        (leftResult.1 = firstLaneResult.1.1 ∧
          SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2
            firstLaneResult.1.2 (trace ++ firstLaneResult.2) ∧
          FirstLaneOracleSimulation.hazardCount
              (trace ++ firstLaneResult.2) ≤ countLimit) ∨
        FirstLaneOracleSimulation.CombinedHit right.1.2
          (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
            (trace ++ firstLaneResult.2))) := by
  induction computation using OracleComp.inductionOn generalizing leftState
      firstLaneState trace used fuel with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure']
      apply relTriple_pure_pure
      apply Or.inl
      refine ⟨rfl, ?_, ?_⟩
      · simpa [FirstLaneOracleSimulation.ActionTrace.chainActions] using hstate
      · simpa [FirstLaneOracleSimulation.hazardCount] using
          hcount.trans (by omega)
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      have hcostLe : verifierHashQueryCost input ≤ fuel := by
        rcases input with n | hashInput
        · simp [verifierHashQueryCost]
        · simp only [verifierHashQueryCost]
          exact Nat.succ_le_iff.2 (hbound.1.resolve_left (by simp))
      have hnextBound : ∀ output,
          (next output).IsQueryBoundP (· matches .inr _)
            (fuel - verifierHashQueryCost input) := by
        intro output
        rcases input with n | hashInput
        · simpa [verifierHashQueryCost] using hbound.2 output
        · simpa [verifierHashQueryCost] using hbound.2 output
      simp only [StateT.run_bind, simulateQ_bind,
        WriterT.run_bind', simulateQ_spec_query]
      apply relTriple_bind (relTriple_with_support
        (relTriple_sourceExact_firstLane_verifier_action used left right hrel
          hleftSupport hrightSupport input leftState firstLaneState trace
            hstate hcount))
      intro headLeft headFirstLane hhead
      rcases hhead.1 with hgood | hhit
      · obtain ⟨hvalue, hnextState, hnextCount⟩ := hgood
        let appendTrace := fun result :
            ((α × GlobalExactTracedState) ×
              FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) =>
          Prod.map id (fun tail => headFirstLane.2 ++ tail) result
        have hrec := ih headFirstLane.1.1
          (used + verifierHashQueryCost input)
          (fuel - verifierHashQueryCost input)
          (hnextBound headFirstLane.1.1) headLeft.2 headFirstLane.1.2
            (trace ++ headFirstLane.2) hnextState hnextCount (by omega)
        change RelTriple _ _ _ at hrec
        have hlifted : RelTriple
            (id <$> (simulateQ sourceExactTracedVerifierImpl
              (next headFirstLane.1.1)).run headLeft.2)
            (appendTrace <$>
              (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
                ((simulateQ
                  (globalFirstLaneExactTracedVerifierImpl right.1.1 right.2)
                  (next headFirstLane.1.1)).run headFirstLane.1.2)).run)
            (fun leftResult firstLaneResult =>
              (leftResult.1 = firstLaneResult.1.1 ∧
                SourceFirstLaneExactGoodStateRelation left right.1
                  leftResult.2 firstLaneResult.1.2
                    (trace ++ firstLaneResult.2) ∧
                FirstLaneOracleSimulation.hazardCount
                  (trace ++ firstLaneResult.2) ≤ countLimit) ∨
              FirstLaneOracleSimulation.CombinedHit right.1.2
                (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
                  (trace ++ firstLaneResult.2))) := by
          apply relTriple_map
          apply relTriple_post_mono hrec
          intro leftResult firstLaneResult hresult
          simpa [appendTrace, Prod.map, List.append_assoc] using hresult
        rw [hvalue]
        change RelTriple _ (appendTrace <$> _) _
        simpa only [id_map] using hlifted
      · obtain ⟨hhit, hnextCount⟩ := hhit
        have hnextLimit : FirstLaneOracleSimulation.hazardCount
            (trace ++ headFirstLane.2) ≤ hitLimit :=
          hnextCount.trans (by omega)
        have henforced : FirstLaneOracleSimulation.CombinedHit right.1.2
            (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
              (trace ++ headFirstLane.2)) := by
          rw [FirstLaneOracleSimulation.enforceHazardTrace_eq_self_of_count_le
            (trace ++ headFirstLane.2) hitLimit hnextLimit]
          exact hhit
        let appendTrace := fun result :
            ((α × GlobalExactTracedState) ×
              FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) =>
          Prod.map id (fun tail => headFirstLane.2 ++ tail) result
        have hlifted : RelTriple
            (id <$> (simulateQ sourceExactTracedVerifierImpl
              (next headLeft.1)).run headLeft.2)
            (appendTrace <$>
              (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
                ((simulateQ
                  (globalFirstLaneExactTracedVerifierImpl right.1.1 right.2)
                  (next headFirstLane.1.1)).run headFirstLane.1.2)).run)
            (fun _leftResult firstLaneResult =>
              FirstLaneOracleSimulation.CombinedHit right.1.2
                (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
                  (trace ++ firstLaneResult.2))) := by
          apply relTriple_map
          apply relTriple_post_mono
            (relTriple_prod (fun _ _ => True.intro) (fun _ _ => True.intro))
          intro _leftResult firstLaneResult _hresults
          simpa [appendTrace, Prod.map, List.append_assoc] using
            FirstLaneOracleSimulation.CombinedHit.enforce_append_of_prefix
              right.1.2 hitLimit (trace ++ headFirstLane.2)
                firstLaneResult.2 henforced
        change RelTriple _ (appendTrace <$> _) _
        apply relTriple_post_mono (by simpa only [id_map] using hlifted)
        intro _leftResult _firstLaneResult hresult
        exact Or.inr hresult

def sourceAppendVerificationState
    (secretKey : SecretKey) (forgery : Forgery)
    (initialState finalState : SourceExactTracedState) :
    SourceExactTracedState :=
  ((finalState.1.1,
    appendVerificationEncodingObservation secretKey forgery
      initialState.1.1.1 finalState.1.1.1 finalState.1.2), finalState.2)

def firstLaneAppendVerificationState
    (secretKey : SecretKey) (forgery : Forgery)
    (initialState finalState : GlobalExactTracedState) :
    GlobalExactTracedState :=
  GlobalExactTracedState.mk finalState.causalState finalState.attackerTrace
    (appendVerificationEncodingObservation secretKey forgery
      initialState.causalState.cache finalState.causalState.cache
        finalState.encodingTrace)

theorem SourceFirstLaneExactGoodStateRelation.appendVerification
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (forgery : Forgery)
    (leftInitial leftFinal : SourceExactTracedState)
    (firstLaneInitial firstLaneFinal : GlobalExactTracedState)
    (initialTrace finalTrace :
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hinitial : SourceFirstLaneExactGoodStateRelation left right.1
      leftInitial firstLaneInitial initialTrace)
    (hfinal : SourceFirstLaneExactGoodStateRelation left right.1
      leftFinal firstLaneFinal finalTrace) :
    SourceFirstLaneExactGoodStateRelation left right.1
      (sourceAppendVerificationState
        (Concrete.materializePrecomputation left.cache left.secretKey)
          forgery leftInitial leftFinal)
      (firstLaneAppendVerificationState right.1.1.secretKey forgery
        firstLaneInitial firstLaneFinal) finalTrace := by
  rcases hinitial with ⟨highInitial, hsourceInitial, hfirstInitial,
    _hchainInitial, _hconsistentInitial⟩
  rcases hfinal with ⟨highFinal, hsourceFinal, hfirstFinal,
    hchainFinal, hconsistentFinal⟩
  subst firstLaneInitial
  subst firstLaneFinal
  obtain ⟨_monitorInitial, _hmonitorInitial, _hagreesInitial,
    _hrevealedInitial, hinitialCausal, _hretainedInitial⟩ :=
      hsourceInitial.1.1
  obtain ⟨_monitorFinal, _hmonitorFinal, _hagreesFinal,
    _hrevealedFinal, hfinalCausal, _hretainedFinal⟩ :=
      hsourceFinal.1.1
  let leftSecret :=
    Concrete.materializePrecomputation left.cache left.secretKey
  have hparameter := programmedGlobal_secretKey_parameter_eq left right hrel
    hleftSupport hrightSupport
  have happend :=
    appendVerificationEncodingObservation_eq_of_globalSigningCachesAgree
      leftSecret right.1.1.secretKey
      (by simpa [leftSecret, Concrete.materializePrecomputation,
        Concrete.precomputedSecretKey] using hparameter.symm)
      forgery leftInitial.1.1.1 highInitial.1.1.causal.cache
        leftFinal.1.1.1 highFinal.1.1.causal.cache
      (by simpa [leftSecret, Concrete.materializePrecomputation,
        Concrete.precomputedSecretKey, sourceSigningTracedStateProjection,
        sourceExactSigningProjection] using hinitialCausal.1)
      (by simpa [leftSecret, Concrete.materializePrecomputation,
        Concrete.precomputedSecretKey, sourceSigningTracedStateProjection,
        sourceExactSigningProjection] using hfinalCausal.1)
      leftFinal.1.2
  let nextEncodingTrace := appendVerificationEncodingObservation leftSecret
    forgery leftInitial.1.1.1 leftFinal.1.1.1 leftFinal.1.2
  let highNext : GlobalHighExactMonitoredState :=
    (highFinal.1, nextEncodingTrace)
  refine ⟨highNext, ?_, ?_, ?_, ?_⟩
  · exact ⟨hsourceFinal.1, rfl⟩
  · simp [firstLaneAppendVerificationState, globalHighExactStateProjection,
      highNext, nextEncodingTrace, leftSecret, hsourceFinal.2] at happend ⊢
    exact happend.symm
  · exact hchainFinal
  · exact hconsistentFinal

theorem relTriple_sourceExact_firstLane_detailedExecution_boundedHit
    (countLimit hitLimit : Nat)
    (adversary : Adversary Concrete.scheme)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (hsourceBound :
      (sourceUnloggedDetailedGameAfterKeygen adversary
        (Concrete.materializeCachedKeyResult left.keyResult).1.1
        (Concrete.materializeCachedKeyResult left.keyResult).1.2).IsQueryBoundP
          (· matches .inr _) countLimit)
    (hlimits : countLimit ≤ hitLimit) :
    RelTriple
      (sourceGlobalExactTracedDetailedExecution adversary left)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
        ((globalFirstLaneExactTracedDetailedExecution adversary right.1.1
          right.2).run (GlobalExactTracedState.mk
            (globalFilteredCausalKeygenState right.1.1) [] []))).run)
      (fun leftResult firstLaneResult =>
        ((leftResult.1 = firstLaneResult.1.1 ∧
          SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2
            firstLaneResult.1.2 firstLaneResult.2 ∧
          FirstLaneOracleSimulation.hazardCount firstLaneResult.2 ≤
            countLimit) ∨
        FirstLaneOracleSimulation.CombinedHit right.1.2
          (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
            firstLaneResult.2))) := by
  let sourceInitial : SourceExactTracedState :=
    ((((left.cache, []), []), []))
  let highInitial : GlobalHighExactMonitoredState :=
    (((⟨globalFilteredCausalKeygenState right.1.1,
      some AdaptiveRevealMonitor.State.empty, []⟩, []), []))
  let firstLaneInitial : GlobalExactTracedState :=
    GlobalExactTracedState.mk
      (globalFilteredCausalKeygenState right.1.1) [] []
  have hinitialSourceHigh : GlobalSigningExactMonitoredStateRelation left
      right.1 sourceInitial highInitial := by
    simpa [sourceInitial, highInitial] using
      globalSigningExactMonitoredStateRelation_initial left right hrel
        hleftSupport hrightSupport
  have hinitialConsistent : highInitial.1.1.TraceConsistent right.1.2 := by
    simpa [highInitial] using
      globalMonitoredCausalState_initial_traceConsistent right.1.2
        (globalFilteredCausalKeygenState right.1.1)
  have hinitial : SourceFirstLaneExactGoodStateRelation left right.1
      sourceInitial firstLaneInitial [] := by
    exact ⟨highInitial, hinitialSourceHigh, by rfl, by rfl,
      hinitialConsistent⟩
  let finish : Forgery → OracleComp OracleWorld (Forgery × Bool) :=
    fun forgery => Prod.mk forgery <$> Concrete.scheme.verify
      left.publicKey forgery.epoch forgery.message forgery.signature
  have hfullBound : (simulateQ
      (sourceUnloggedMappedAdversaryImpl left.publicKey
        (Concrete.materializePrecomputation left.cache left.secretKey))
        (adversary.main left.publicKey) >>= finish).IsQueryBoundP
          (· matches .inr _) countLimit := by
    unfold sourceUnloggedDetailedGameAfterKeygen at hsourceBound
    exact hsourceBound
  have hpublicKey : left.publicKey = right.1.1.publicKey :=
    hrel.1.toStable.1.2.1
  unfold sourceGlobalExactTracedDetailedExecution
    globalFirstLaneExactTracedDetailedExecution
  simp only [StateT.run_mk]
  rw [← hpublicKey]
  rw [simulateQ_bind, WriterT.run_bind']
  apply relTriple_bind (relTriple_with_support
    (relTriple_sourceExact_firstLane_adversary_boundedHit countLimit hitLimit
      0 countLimit left right hrel hleftSupport hrightSupport
        (adversary.main left.publicKey) finish hfullBound sourceInitial
          firstLaneInitial [] hinitial (by simp
            [FirstLaneOracleSimulation.hazardCount]) (by rfl)
              (by omega) hlimits))
  intro leftHandled firstLaneHandled hhandled
  rcases firstLaneHandled with ⟨⟨firstForgery, firstState⟩, firstTrace⟩
  rcases hhandled.1 with hgood | hhit
  · obtain ⟨hforgery, hstates, htargetCount, hsourceCount⟩ := hgood
    have hforgery' : leftHandled.1 = firstForgery := by simpa using hforgery
    have hstates' : SourceFirstLaneExactGoodStateRelation left right.1
        leftHandled.2 firstState firstTrace := by simpa using hstates
    have htargetCount' : FirstLaneOracleSimulation.hazardCount firstTrace ≤
        leftHandled.2.2.hashInputs.length := by simpa using htargetCount
    have hresidual :=
      cappedBothTracedMappedAdversaryImpl_residual_hashQueryBound
        left.publicKey
          (Concrete.materializePrecomputation left.cache left.secretKey)
            (adversary.main left.publicKey) finish countLimit hfullBound
              sourceInitial (by rfl) leftHandled hhandled.2.1
    have hverifyBound :
        (Concrete.scheme.verify left.publicKey leftHandled.1.epoch
          leftHandled.1.message leftHandled.1.signature).IsQueryBoundP
            (· matches .inr _)
              (countLimit - leftHandled.2.2.hashInputs.length) := by
      unfold finish at hresidual
      exact (OracleComp.isQueryBoundP_map_iff _ _ _).mp hresidual.2
    rw [← hforgery']
    have hverifier :=
      relTriple_sourceExact_firstLane_verifier_boundedHit countLimit hitLimit
        leftHandled.2.2.hashInputs.length
          (countLimit - leftHandled.2.2.hashInputs.length) left right hrel
            hleftSupport hrightSupport
              (Concrete.scheme.verify left.publicKey leftHandled.1.epoch
                leftHandled.1.message leftHandled.1.signature)
              hverifyBound leftHandled.2 firstState firstTrace hstates'
                htargetCount' (by omega) hlimits
    let sourceFinish := fun verified : Bool × SourceExactTracedState =>
      ((leftHandled.1, verified.1),
        sourceAppendVerificationState
          (Concrete.materializePrecomputation left.cache left.secretKey)
            leftHandled.1 leftHandled.2 verified.2)
    let firstLaneFinish := fun verified :
        ((Bool × GlobalExactTracedState) ×
          FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) =>
      (((leftHandled.1, verified.1.1),
        firstLaneAppendVerificationState right.1.1.secretKey leftHandled.1
          firstState verified.1.2), firstTrace ++ verified.2)
    have hlifted : RelTriple
        (sourceFinish <$>
          (simulateQ sourceExactTracedVerifierImpl
            (Concrete.scheme.verify left.publicKey leftHandled.1.epoch
              leftHandled.1.message leftHandled.1.signature)).run
                leftHandled.2)
        (firstLaneFinish <$>
          (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
            ((simulateQ
              (globalFirstLaneExactTracedVerifierImpl right.1.1 right.2)
              (Concrete.scheme.verify left.publicKey leftHandled.1.epoch
                leftHandled.1.message leftHandled.1.signature)).run
                  firstState)).run)
        (fun leftResult firstLaneResult =>
          (leftResult.1 = firstLaneResult.1.1 ∧
            SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2
              firstLaneResult.1.2 firstLaneResult.2 ∧
            FirstLaneOracleSimulation.hazardCount firstLaneResult.2 ≤
              countLimit) ∨
          FirstLaneOracleSimulation.CombinedHit right.1.2
            (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
              firstLaneResult.2)) := by
      apply relTriple_map
      apply relTriple_post_mono hverifier
      intro leftVerified firstLaneVerified hvertified
      rcases hvertified with hvertifiedGood | hvertifiedHit
      · apply Or.inl
        refine ⟨congrArg (Prod.mk leftHandled.1) hvertifiedGood.1, ?_,
          hvertifiedGood.2.2⟩
        exact SourceFirstLaneExactGoodStateRelation.appendVerification left
          right hrel hleftSupport hrightSupport leftHandled.1 leftHandled.2
            leftVerified.2 firstState firstLaneVerified.1.2
              firstTrace (firstTrace ++ firstLaneVerified.2) hstates'
                hvertifiedGood.2.1
      · exact Or.inr hvertifiedHit
    have hsourceTail :
        (do
          let verified ← (simulateQ sourceSigningTracedVerifierImpl
            (Concrete.scheme.verify left.publicKey leftHandled.1.epoch
              leftHandled.1.message leftHandled.1.signature)).run
                (sourceExactSigningProjection leftHandled.2)
          pure ((leftHandled.1, verified.1),
            ((verified.2.1,
              appendVerificationEncodingObservation
                (Concrete.materializePrecomputation left.cache left.secretKey)
                  leftHandled.1 leftHandled.2.1.1.1 verified.2.1.1
                    leftHandled.2.1.2), verified.2.2))) =
          sourceFinish <$>
            (simulateQ sourceExactTracedVerifierImpl
              (Concrete.scheme.verify left.publicKey leftHandled.1.epoch
                leftHandled.1.message leftHandled.1.signature)).run
                  leftHandled.2 := by
      rw [sourceExactTracedVerifierImpl_run_eq]
      simp [sourceFinish, sourceAppendVerificationState, Functor.map_map]
    have hfirstLaneTail :
        (Prod.map id (fun tail => firstTrace ++ tail) <$>
          (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
            (do
              let verified ← (simulateQ
                (globalFirstLaneExactTracedVerifierImpl right.1.1 right.2)
                (Concrete.scheme.verify left.publicKey leftHandled.1.epoch
                  leftHandled.1.message leftHandled.1.signature)).run
                    firstState
              pure ((leftHandled.1, verified.1),
                firstLaneAppendVerificationState right.1.1.secretKey
                  leftHandled.1 firstState verified.2))).run) =
          firstLaneFinish <$>
            (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
              ((simulateQ
                (globalFirstLaneExactTracedVerifierImpl right.1.1 right.2)
                (Concrete.scheme.verify left.publicKey leftHandled.1.epoch
                  leftHandled.1.message leftHandled.1.signature)).run
                    firstState)).run := by
      rw [simulateQ_bind, WriterT.run_bind']
      simp [firstLaneFinish, firstLaneAppendVerificationState,
        Functor.map_map]
    rw [hsourceTail]
    change RelTriple _
      (Prod.map id (fun tail => firstTrace ++ tail) <$>
        (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
          (do
            let verified ← (simulateQ
              (globalFirstLaneExactTracedVerifierImpl right.1.1 right.2)
              (Concrete.scheme.verify left.publicKey leftHandled.1.epoch
                leftHandled.1.message leftHandled.1.signature)).run firstState
            pure ((leftHandled.1, verified.1),
              firstLaneAppendVerificationState right.1.1.secretKey
                leftHandled.1 firstState verified.2))).run) _
    rw [hfirstLaneTail]
    exact hlifted
  · have hhit' : FirstLaneOracleSimulation.CombinedHit right.1.2
        (FirstLaneOracleSimulation.enforceHazardTrace hitLimit firstTrace) := by
      simpa using hhit
    apply relTriple_post_mono
      (relTriple_with_support
        (relTriple_prod (fun _ _ => True.intro) (fun _ _ => True.intro)))
    intro _leftResult firstLaneResult hresults
    apply Or.inr
    have htargetSupport := hresults.2.2
    change firstLaneResult ∈ support
      ((Prod.map id (fun tail => firstTrace ++ tail)) <$>
        (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
          (do
            let verified ← (simulateQ
              (globalFirstLaneExactTracedVerifierImpl right.1.1 right.2)
              (Concrete.scheme.verify left.publicKey firstForgery.epoch
                firstForgery.message firstForgery.signature)).run firstState
            pure ((firstForgery, verified.1),
              firstLaneAppendVerificationState right.1.1.secretKey
                firstForgery firstState verified.2))).run) at htargetSupport
    rw [support_map] at htargetSupport
    obtain ⟨rawResult, _hrawResult, rfl⟩ := htargetSupport
    exact FirstLaneOracleSimulation.CombinedHit.enforce_append_of_prefix
      right.1.2 hitLimit firstTrace rawResult.2 hhit'

end XmssSecurity.CappedChain
