import XmssSecurity.Proof.CappedGlobalChainHighSigningReplay
import XmssSecurity.Proof.CappedGlobalChainHighKeygenRelation
import XmssSecurity.Proof.CappedGlobalCausalUniformTrace
import XmssSecurity.Proof.CappedChain.SourceDirectTrace

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

theorem relTriple_programmed_monitoredGlobalUniformQuery
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftCache : QueryCache HashSpec)
    (rightState : GlobalMonitoredCausalState)
    (hstate : GlobalMonitoredFilteredStateRelation left right leftCache
      rightState)
    (n : Nat) :
    RelTriple
      ((fun output : Fin (n + 1) => (output, leftCache)) <$>
        (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
      ((monitorGlobalCausalTrace fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.2)
          ((globalCausalUniformImpl n).run causalState)).run).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredFilteredStateRelation left right leftResult.2
            rightResult.2) ∨ rightResult.2.bad right.2) := by
  rcases hstate with
    ⟨monitor, hmonitor, hmonitorAgrees, hrevealed, hcausal, hretained⟩
  apply relTriple_monitorGlobalCausalTrace_of_filtered_until_hit left right
    _ _ rightState monitor hmonitor hmonitorAgrees hrevealed
  · rw [simulate_eagerTrace_globalCausalUniformImpl]
    have hmapped : RelTriple
        ((fun output : Fin (n + 1) => (output, leftCache)) <$>
          (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
        ((fun output : Fin (n + 1) =>
          ((output, rightState.causal),
            ([] : RevealProbeOracleSimulation.ActionTrace
              GlobalChainValueIndex))) <$>
          (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
        (fun leftResult rightResult =>
          leftResult.1 = rightResult.1.1 ∧
            GlobalFilteredCausalStateRelation left right leftResult.2
              rightResult.1.2) := by
      apply relTriple_map
      apply relTriple_post_mono
        (relTriple_refl
          (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
      intro leftOutput rightOutput houtput
      subst rightOutput
      exact ⟨rfl, hcausal⟩
    apply relTriple_post_mono hmapped
    intro leftResult rightResult hresult
    exact Or.inl hresult
  · intro result hresult
    rw [simulate_eagerTrace_globalCausalUniformImpl, support_map] at hresult
    obtain ⟨output, _houtput, rfl⟩ := hresult
    exact ⟨by trivial, ReplaysCausalReveals.nil rightState.causal.revealed⟩
  · intro result hresult
    rw [simulate_eagerTrace_globalCausalUniformImpl, support_map] at hresult
    obtain ⟨output, _houtput, rfl⟩ := hresult
    exact hretained

abbrev GlobalMonitoredTracedState :=
  GlobalMonitoredCausalState × AttackerActionTrace

def GlobalMonitoredTracedStateRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftState : SourceTracedState)
    (rightState : GlobalMonitoredTracedState) : Prop :=
  GlobalMonitoredFilteredStateRelation left right leftState.1 rightState.1 ∧
    leftState.2 = rightState.2

noncomputable def globalHighMonitoredBaseMappedAdversaryImpl
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalMonitoredCausalState ProbComp) := fun input =>
  match input with
  | .inl (.inl n) =>
      monitorGlobalCausalTrace fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
          ((globalCausalUniformImpl n).run causalState)).run
  | .inl (.inr hashInput) =>
      monitorGlobalCausalTrace fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
          ((globalCausalAttackerHashQueryFromHigh
            (globalChainValueHighTableOfEdges right.2)
              right.1.1.secretKey hashInput).run causalState)).run
  | .inr request =>
      monitorGlobalCausalTrace fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
          (globalFilteredCausalSigningQuery right.1.1 request
            causalState)).run

noncomputable def globalHighMonitoredMappedAdversaryImpl
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalMonitoredTracedState ProbComp) :=
  actionTracedStateImpl (globalHighMonitoredBaseMappedAdversaryImpl right)
    attackerActionFragment

theorem relTriple_globalActionTracedState_until_bad
    (input : (OracleWorld + SigningSpec).Domain)
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftImpl : QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec) ProbComp))
    (rightImpl : QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalMonitoredCausalState ProbComp))
    (leftState : SourceTracedState)
    (rightState : GlobalMonitoredTracedState)
    (htrace : leftState.2 = rightState.2)
    (hcouple : RelTriple
      ((leftImpl input).run leftState.1)
      ((rightImpl input).run rightState.1)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredFilteredStateRelation left right leftResult.2
            rightResult.2) ∨ rightResult.2.bad right.2)) :
    RelTriple
      ((actionTracedStateImpl leftImpl attackerActionFragment input).run
        leftState)
      ((actionTracedStateImpl rightImpl attackerActionFragment input).run
        rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredTracedStateRelation left right leftResult.2
            rightResult.2) ∨ rightResult.2.1.bad right.2) := by
  let wrapLeft := fun result : (OracleWorld + SigningSpec).Range input ×
      QueryCache HashSpec => (result.1,
    (result.2, leftState.2 ++ attackerActionFragment input result.1))
  let wrapRight := fun result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredCausalState => (result.1,
    (result.2, rightState.2 ++ attackerActionFragment input result.1))
  let post := fun leftResult : (OracleWorld + SigningSpec).Range input ×
      SourceTracedState => fun rightResult :
      (OracleWorld + SigningSpec).Range input × GlobalMonitoredTracedState =>
    (leftResult.1 = rightResult.1 ∧
      GlobalMonitoredTracedStateRelation left right leftResult.2
        rightResult.2) ∨ rightResult.2.1.bad right.2
  have hprepared : RelTriple
      ((leftImpl input).run leftState.1)
      ((rightImpl input).run rightState.1)
      (fun leftResult rightResult =>
        post (wrapLeft leftResult) (wrapRight rightResult)) := by
    apply relTriple_post_mono hcouple
    intro leftResult rightResult hresult
    rcases hresult with hgood | hbad
    · refine Or.inl ⟨hgood.1, hgood.2, ?_⟩
      change leftState.2 ++ attackerActionFragment input leftResult.1 =
        rightState.2 ++ attackerActionFragment input rightResult.1
      rw [htrace, hgood.1]
    · exact Or.inr hbad
  unfold actionTracedStateImpl
  simpa [wrapLeft, wrapRight, post, map_eq_bind_pure_comp] using
    (relTriple_map (R := post) (f := wrapLeft) (g := wrapRight) hprepared)

theorem relTriple_programmed_globalHighMonitored_action
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftState : SourceTracedState)
    (rightState : GlobalMonitoredTracedState)
    (hstate : GlobalMonitoredTracedStateRelation left right.1 leftState
      rightState)
    (input : (OracleWorld + SigningSpec).Domain) :
    RelTriple
      ((sourceDirectTracedMappedAdversaryImpl left.publicKey
        (Concrete.materializePrecomputation left.cache left.secretKey)
          input).run leftState)
      ((globalHighMonitoredMappedAdversaryImpl right input).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredTracedStateRelation left right.1 leftResult.2
            rightResult.2) ∨ rightResult.2.1.bad right.1.2) := by
  have liftBase := relTriple_globalActionTracedState_until_bad input left
    right.1 (sourceDirectMappedAdversaryImpl left.publicKey
      (Concrete.materializePrecomputation left.cache left.secretKey))
      (globalHighMonitoredBaseMappedAdversaryImpl right) leftState rightState
        hstate.2
  rcases input with (worldInput | request)
  · rcases worldInput with n | hashInput
    · apply liftBase
      simpa [sourceDirectMappedAdversaryImpl,
        unloggedMappedAdversaryImpl_apply_inl,
        globalHighMonitoredBaseMappedAdversaryImpl, romImpl, unifFwdImpl,
        OracleComp.liftM_run_StateT] using
        (relTriple_programmed_monitoredGlobalUniformQuery left right.1
          leftState.1 rightState.1 hstate.1 n)
    · apply liftBase
      simpa [sourceDirectMappedAdversaryImpl,
        unloggedMappedAdversaryImpl_apply_inl,
        globalHighMonitoredBaseMappedAdversaryImpl, romImpl] using
        (relTriple_programmed_monitoredGlobalAttackerHashQuery_until_hit left
          right hrel hleftSupport hrightSupport leftState.1 rightState.1
            hstate.1 hashInput)
  · apply liftBase
    simpa [sourceDirectMappedAdversaryImpl,
      unloggedMappedAdversaryImpl_apply_inr,
      globalHighMonitoredBaseMappedAdversaryImpl] using
      (relTriple_programmed_monitoredGlobalSigningQuery left right hrel
        hleftSupport hrightSupport leftState.1 rightState.1 hstate.1 request)

noncomputable def globalHighMonitoredVerifierImpl
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    QueryImpl OracleWorld (StateT GlobalMonitoredTracedState ProbComp) :=
  fun input => StateT.mk fun state =>
    (fun result => (result.1, (result.2, state.2))) <$>
      ((globalHighMonitoredBaseMappedAdversaryImpl right (.inl input)).run
        state.1)

theorem relTriple_keepGlobalAttackerTrace_until_bad
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftTrace rightTrace : AttackerActionTrace)
    (htrace : leftTrace = rightTrace)
    (leftComputation : ProbComp (α × QueryCache HashSpec))
    (rightComputation : ProbComp (α × GlobalMonitoredCausalState))
    (hcouple : RelTriple leftComputation rightComputation
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredFilteredStateRelation left right leftResult.2
            rightResult.2) ∨ rightResult.2.bad right.2)) :
    RelTriple
      ((fun result => (result.1, (result.2, leftTrace))) <$> leftComputation)
      ((fun result => (result.1, (result.2, rightTrace))) <$> rightComputation)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredTracedStateRelation left right leftResult.2
            rightResult.2) ∨ rightResult.2.1.bad right.2) := by
  let wrapLeft := fun result : α × QueryCache HashSpec =>
    (result.1, (result.2, leftTrace))
  let wrapRight := fun result : α × GlobalMonitoredCausalState =>
    (result.1, (result.2, rightTrace))
  let post := fun leftResult : α × SourceTracedState =>
    fun rightResult : α × GlobalMonitoredTracedState =>
      (leftResult.1 = rightResult.1 ∧
        GlobalMonitoredTracedStateRelation left right leftResult.2
          rightResult.2) ∨ rightResult.2.1.bad right.2
  have hprepared : RelTriple leftComputation rightComputation
      (fun leftResult rightResult =>
        post (wrapLeft leftResult) (wrapRight rightResult)) := by
    apply relTriple_post_mono hcouple
    intro leftResult rightResult hresult
    rcases hresult with hgood | hbad
    · exact Or.inl ⟨hgood.1, hgood.2, htrace⟩
    · exact Or.inr hbad
  simpa [wrapLeft, wrapRight, post] using
    (relTriple_map (R := post) (f := wrapLeft) (g := wrapRight) hprepared)

theorem relTriple_programmed_globalHighMonitored_verifier_query
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftState : SourceTracedState)
    (rightState : GlobalMonitoredTracedState)
    (hstate : GlobalMonitoredTracedStateRelation left right.1 leftState
      rightState)
    (input : OracleWorld.Domain) :
    RelTriple
      ((sourceDirectTracedVerifierImpl input).run leftState)
      ((globalHighMonitoredVerifierImpl right input).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredTracedStateRelation left right.1 leftResult.2
            rightResult.2) ∨ rightResult.2.1.bad right.1.2) := by
  rw [sourceDirectTracedVerifierImpl_query_run_eq]
  unfold globalHighMonitoredVerifierImpl
  rw [StateT.run_mk]
  apply relTriple_keepGlobalAttackerTrace_until_bad left right.1 leftState.2
    rightState.2 hstate.2
  rcases input with n | hashInput
  · simpa [sourceDirectTracedVerifierImpl,
      globalHighMonitoredVerifierImpl,
      globalHighMonitoredBaseMappedAdversaryImpl, romImpl, unifFwdImpl,
      OracleComp.liftM_run_StateT] using
      (relTriple_programmed_monitoredGlobalUniformQuery left right.1
        leftState.1 rightState.1 hstate.1 n)
  · simpa [sourceDirectTracedVerifierImpl,
      globalHighMonitoredVerifierImpl,
      globalHighMonitoredBaseMappedAdversaryImpl, romImpl] using
      (relTriple_programmed_monitoredGlobalAttackerHashQuery_until_hit left
        right hrel hleftSupport hrightSupport leftState.1 rightState.1 hstate.1
          hashInput)

theorem globalMonitoredTracedStateRelation_initial
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen) :
    GlobalMonitoredTracedStateRelation left right.1 (left.cache, [])
      (⟨globalFilteredCausalKeygenState right.1.1, []⟩, []) := by
  refine ⟨globalMonitoredFilteredStateRelation_initial left right.1 left.cache
    (globalFilteredCausalKeygenState right.1.1) ?_ ?_ ?_, rfl⟩
  · exact programmedGlobal_filteredKeygen_stateRelation left right hrel
      hleftSupport hrightSupport
  · exact globalFilteredCausalKeygenState_merkleRetained right.1.1
  · intro index
    simp [globalFilteredCausalKeygenState]

noncomputable def sourceGlobalTracedDetailedExecution
    (adversary : Adversary)
    (keyView : ProgrammedGlobalChainKeygenView) :
    ProbComp ((Forgery × Bool) × SourceTracedState) := do
  let handled ← (simulateQ
    (sourceDirectTracedMappedAdversaryImpl keyView.publicKey
      (Concrete.materializePrecomputation keyView.cache keyView.secretKey))
      (adversary.main keyView.publicKey)).run (keyView.cache, [])
  let verified ← (simulateQ sourceDirectTracedVerifierImpl
    (Concrete.scheme.verify keyView.publicKey handled.1.epoch
      handled.1.message handled.1.signature)).run handled.2
  pure ((handled.1, verified.1), verified.2)

noncomputable def globalHighMonitoredDetailedExecution
    (adversary : Adversary)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    ProbComp ((Forgery × Bool) × GlobalMonitoredTracedState) := do
  let initial : GlobalMonitoredTracedState :=
    (⟨globalFilteredCausalKeygenState right.1.1, []⟩, [])
  let handled ← (simulateQ (globalHighMonitoredMappedAdversaryImpl right)
    (adversary.main right.1.1.publicKey)).run initial
  let verified ← (simulateQ (globalHighMonitoredVerifierImpl right)
    (Concrete.scheme.verify right.1.1.publicKey handled.1.epoch
      handled.1.message handled.1.signature)).run handled.2
  pure ((handled.1, verified.1), verified.2)

def sourceGlobalExecutionResult
    (keyView : ProgrammedGlobalChainKeygenView)
    (execution : (Forgery × Bool) × SourceTracedState) :
    (GameOutcome × QueryCache HashSpec) × AttackerActionTrace :=
  ((actionTraceOutcome keyView.publicKey
    (Concrete.materializePrecomputation keyView.cache keyView.secretKey)
    (execution.1, execution.2.2), execution.2.1), execution.2.2)

abbrev SourceGlobalTracedProgramResult :=
  ProgrammedGlobalChainKeygenView ×
    ((Forgery × Bool) × SourceTracedState)

abbrev GlobalHighMonitoredProgramResult :=
  ((ProgrammedGlobalChainKeygenView ×
    (GlobalChainValueIndex → Digest)) ×
    (GlobalChainEdgeIndex → Digest)) ×
      ((Forgery × Bool) × GlobalMonitoredTracedState)

noncomputable def sourceGlobalTracedProgram
    (adversary : Adversary) :
    ProbComp SourceGlobalTracedProgramResult := do
  let keyView ← trajectoryProgrammedGlobalChainKeygen
  let execution ← sourceGlobalTracedDetailedExecution adversary keyView
  pure (keyView, execution)

def sourceGlobalProgramResult
    (result : SourceGlobalTracedProgramResult) :
    GlobalChainActionTracedResult :=
  let execution := sourceGlobalExecutionResult result.1 result.2
  ((result.1, execution.1), execution.2)

noncomputable def globalHighMonitoredProgram
    (adversary : Adversary) :
    ProbComp GlobalHighMonitoredProgramResult := do
  let right ← coupledGlobalChainKeygenWithBaseHighFull
  let execution ← globalHighMonitoredDetailedExecution adversary right
  pure (right, execution)

def SourceGlobalHighMonitoredProgramRelation
    (left : SourceGlobalTracedProgramResult)
    (right : GlobalHighMonitoredProgramResult) : Prop :=
  ProgrammedGlobalChainKeygenBaseHighStableRelation left.1 right.1 ∧
    ((left.2.1 = right.2.1 ∧
      GlobalMonitoredTracedStateRelation left.1 right.1.1 left.2.2
        right.2.2) ∨ right.2.2.1.bad right.1.1.2)

end XmssSecurity.CappedChain
