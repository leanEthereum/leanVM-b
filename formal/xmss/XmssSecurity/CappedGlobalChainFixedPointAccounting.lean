import XmssSecurity.CappedGlobalChainExpectedAccounting
import XmssSecurity.CappedVerifierUpperBound

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem RevealProbeOracleSimulation.exists_isProbeQueryBoundP
    (computation : OracleComp
      (RevealProbeOracleSimulation.World Index) α) :
    ∃ fuel, computation.IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery fuel := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value => exact ⟨0, by simp⟩
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          let continuationFuel := fun output => Classical.choose (ih output)
          let fuel := ∑ output, continuationFuel output
          refine ⟨fuel, ?_⟩
          rw [OracleComp.isQueryBoundP_query_bind_iff]
          refine ⟨by simp [RevealProbeOracleSimulation.IsProbeQuery], fun output => ?_⟩
          have hcontinuation := Classical.choose_spec (ih output)
          have hle : continuationFuel output ≤
              ∑ candidate, continuationFuel candidate := by
            exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ output)
          exact hcontinuation.mono (by
            simpa [fuel, RevealProbeOracleSimulation.IsProbeQuery] using hle)

      | probe index target =>
          let continuationFuel := fun output => Classical.choose (ih output)
          let fuel := 1 + ∑ output, continuationFuel output
          refine ⟨fuel, ?_⟩
          rw [OracleComp.isQueryBoundP_query_bind_iff]
          refine ⟨by simp [fuel, RevealProbeOracleSimulation.IsProbeQuery],
            fun output => ?_⟩
          have hcontinuation := Classical.choose_spec (ih output)
          have hle : continuationFuel output ≤
              ∑ candidate, continuationFuel candidate := by
            exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ output)
          rw [show (if RevealProbeOracleSimulation.IsProbeQuery
              (.probe index target) then fuel - 1 else fuel) =
              ∑ candidate, continuationFuel candidate by
            simp [fuel, RevealProbeOracleSimulation.IsProbeQuery]]
          exact hcontinuation.mono hle
      | reveal index =>
          let continuationFuel := fun output => Classical.choose (ih output)
          let fuel := ∑ output, continuationFuel output
          refine ⟨fuel, ?_⟩
          rw [OracleComp.isQueryBoundP_query_bind_iff]
          refine ⟨by simp [RevealProbeOracleSimulation.IsProbeQuery], fun output => ?_⟩
          have hcontinuation := Classical.choose_spec (ih output)
          have hle : continuationFuel output ≤
              ∑ candidate, continuationFuel candidate := by
            exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ output)
          exact hcontinuation.mono (by
            simpa [fuel, RevealProbeOracleSimulation.IsProbeQuery] using hle)

theorem RevealProbeOracleSimulation.observedProbeCount_enforceProbeTrace_le_fuel
    (fuel : Nat)
    (trace : RevealProbeOracleSimulation.ActionTrace Index) :
    RevealProbeOracleSimulation.observedProbeCount
      (RevealProbeOracleSimulation.enforceProbeTrace fuel trace) ≤ fuel := by
  induction trace generalizing fuel with
  | nil => simp [RevealProbeOracleSimulation.enforceProbeTrace,
      RevealProbeOracleSimulation.observedProbeCount]
  | cons action trace ih =>
      cases action with
      | reveal index value =>
          simp only [RevealProbeOracleSimulation.enforceProbeTrace,
            RevealProbeOracleSimulation.observedProbeCount]
          exact ih fuel
      | probe index target =>
          cases fuel with
          | zero =>
              simpa [RevealProbeOracleSimulation.enforceProbeTrace,
                RevealProbeOracleSimulation.observedProbeCount] using ih 0
          | succ fuel =>
              simp only [RevealProbeOracleSimulation.enforceProbeTrace,
                RevealProbeOracleSimulation.observedProbeCount,
                Nat.succ_le_succ_iff]
              exact ih fuel

theorem globalHighMonitoredVerifierImpl_support_actionTrace_eq
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : OracleWorld.Domain)
    (state : GlobalMonitoredTracedState)
    (result : OracleWorld.Range input × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((globalHighMonitoredVerifierImpl right input).run state)) :
    result.2.2 = state.2 := by
  unfold globalHighMonitoredVerifierImpl at hresult
  simp only [StateT.run_mk, support_map] at hresult
  obtain ⟨baseResult, _hbaseResult, rfl⟩ := hresult
  rfl

theorem globalHighMonitoredVerifier_simulation_actionTrace_eq
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (computation : OracleComp OracleWorld α)
    (state : GlobalMonitoredTracedState)
    (result : α × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ (globalHighMonitoredVerifierImpl right)
        computation).run state)) :
    result.2.2 = state.2 := by
  exact OracleComp.simulateQ_run_preservesInv
    (globalHighMonitoredVerifierImpl right)
    (fun candidate : GlobalMonitoredTracedState => candidate.2 = state.2)
    (fun input current hcurrent output houtput => by
      change output.2.2 = state.2
      rw [globalHighMonitoredVerifierImpl_support_actionTrace_eq right input
        current output houtput, hcurrent])
    computation state rfl result hresult

theorem globalHighMonitoredVerifier_simulation_probeCount_growth
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (computation : OracleComp OracleWorld α) (fuel : Nat)
    (hbound : computation.IsQueryBoundP (· matches .inr _) fuel)
    (state : GlobalMonitoredTracedState)
    (result : α × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ (globalHighMonitoredVerifierImpl right)
        computation).run state)) :
    RevealProbeOracleSimulation.observedProbeCount result.2.1.trace ≤
      RevealProbeOracleSimulation.observedProbeCount state.1.trace + fuel := by
  induction computation using OracleComp.inductionOn generalizing state fuel
      result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      simp
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      simp only [simulateQ_query_bind, StateT.run_bind] at hresult
      rw [mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, hrest⟩ := hresult
      have hstep := globalHighMonitoredVerifierImpl_support_probeCount_growth
        right input state head hhead
      cases input with
      | inl uniformIndex =>
          simp only [verifierHashQueryCost] at hstep
          have hrec := ih head.1 fuel (by simpa using hbound.2 head.1)
            head.2 result hrest
          omega
      | inr hashInput =>
          have hfuel : 0 < fuel := hbound.1.resolve_left (by simp)
          simp only [verifierHashQueryCost] at hstep
          have hrec := ih head.1 (fuel - 1)
            (by simpa using hbound.2 head.1) head.2 result hrest
          omega

def globalHighRuntimeProbeCost
    (result : GlobalHighMonitoredProgramResult) : ENNReal :=
  RevealProbeOracleSimulation.observedProbeCount result.2.2.1.trace

noncomputable def globalHighRelevantAttackerCost
    (result : GlobalHighMonitoredProgramResult) : ENNReal :=
  (result.2.2.2.globalChainProbeRelevantInputs
    result.1.1.1.secretKey).length

noncomputable def sourceGlobalRelevantAttackerCost
    (result : SourceGlobalTracedProgramResult) : ENNReal :=
  (result.2.2.2.globalChainProbeRelevantInputs result.1.secretKey).length

def IsGlobalChainProbeAction (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) : Prop :=
  globalChainProbeActionCost secretKey input = 1

noncomputable instance (secretKey : SecretKey) :
    DecidablePred (IsGlobalChainProbeAction secretKey) := by
  intro input
  unfold IsGlobalChainProbeAction
  exact Nat.decEq _ _

noncomputable def sourceRelevantTraceResource
    (secretKey : SecretKey) (state : SourceTracedState) : ENNReal :=
  (state.2.globalChainProbeRelevantInputs secretKey).length

theorem globalChainProbeActionCost_eq_indicator
    (secretKey : SecretKey) (input : (OracleWorld + SigningSpec).Domain) :
    (globalChainProbeActionCost secretKey input : ENNReal) =
      if IsGlobalChainProbeAction secretKey input then 1 else 0 := by
  rcases input with (uniformOrHash | request)
  · rcases uniformOrHash with uniformIndex | hashInput
    · simp [globalChainProbeActionCost, IsGlobalChainProbeAction]
    · by_cases hrelevant : GlobalChainProbeRelevantInput secretKey hashInput <;>
        simp [globalChainProbeActionCost, IsGlobalChainProbeAction, hrelevant]
  · simp [globalChainProbeActionCost, IsGlobalChainProbeAction]

theorem sourceDirectTracedMappedAdversaryImpl_resource_step_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : SourceTracedState)
    (result : (OracleWorld + SigningSpec).Range input × SourceTracedState)
    (hresult : result ∈ support
      ((sourceDirectTracedMappedAdversaryImpl publicKey secretKey input).run
        initialState)) :
    sourceRelevantTraceResource secretKey result.2 ≤
      sourceRelevantTraceResource secretKey initialState +
        if IsGlobalChainProbeAction secretKey input then 1 else 0 := by
  have htrace :=
    (sourceDirectTracedMappedAdversaryImpl_support_info publicKey secretKey
      input initialState result hresult).2
  unfold sourceRelevantTraceResource
  rw [htrace, AttackerActionTrace.globalChainProbeRelevantInputs_append,
    List.length_append,
    attackerActionFragment_globalChainProbeRelevantInputs_length]
  rw [← globalChainProbeActionCost_eq_indicator]
  rw [Nat.cast_add]

theorem expectedSimulatedQueryCount_sourceDirectTraced_eq
    (publicKey : PublicKey) (secretKey : SecretKey)
    (predicate : (OracleWorld + SigningSpec).Domain → Prop)
    [DecidablePred predicate]
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (trace : AttackerActionTrace) :
    expectedSimulatedQueryCount
        (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
        predicate computation (cache, trace) =
      expectedSimulatedQueryCount
        (sourceDirectMappedAdversaryImpl publicKey secretKey)
        predicate computation cache := by
  induction computation using OracleComp.inductionOn generalizing cache trace with
  | pure value => rfl
  | query_bind input next ih =>
      rw [expectedSimulatedQueryCount_query_bind,
        expectedSimulatedQueryCount_query_bind]
      have hrun :
          (sourceDirectTracedMappedAdversaryImpl publicKey secretKey input).run
              (cache, trace) =
            (fun result =>
              (result.1,
                (result.2, trace ++ attackerActionFragment input result.1))) <$>
              (sourceDirectMappedAdversaryImpl publicKey secretKey input).run
                cache := by
        unfold sourceDirectTracedMappedAdversaryImpl actionTracedStateImpl
        simp [map_eq_bind_pure_comp]
      rw [hrun, tsum_probOutput_map_mul]
      congr 1
      apply tsum_congr
      intro result
      rw [ih]

theorem expectedSourceTracedAdversaryRelevantCost_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (adversary : Adversary Concrete.scheme)
    (cache : QueryCache HashSpec) :
    (∑' result,
        Pr[= result |
          (simulateQ
            (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
            (adversary.main publicKey)).run (cache, [])] *
          sourceRelevantTraceResource secretKey result.2) ≤
      expectedSimulatedQueryCount xmssRomImpl
        (Rom.IsRelevantHashQuery
          (GlobalChainProbeRelevantInput secretKey))
        (simulateQ (sourceUnloggedMappedAdversaryImpl publicKey secretKey)
          (adversary.main publicKey)) cache := by
  let outerPredicate := IsGlobalChainProbeAction secretKey
  let innerPredicate := Rom.IsRelevantHashQuery
    (GlobalChainProbeRelevantInput secretKey)
  letI : DecidablePred outerPredicate := by
    simpa [outerPredicate] using
      (inferInstance : DecidablePred (IsGlobalChainProbeAction secretKey))
  have hresource := expectedResource_le_initial_add_expectedSimulatedQueryCount
    (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
    outerPredicate (sourceRelevantTraceResource secretKey)
    (sourceDirectTracedMappedAdversaryImpl_resource_step_le publicKey secretKey)
    (adversary.main publicKey) (cache, [])
  have hcompose :
      expectedSimulatedQueryCount
          (sourceDirectMappedAdversaryImpl publicKey secretKey)
          outerPredicate (adversary.main publicKey) cache ≤
        expectedSimulatedQueryCount xmssRomImpl innerPredicate
          (simulateQ (sourceUnloggedMappedAdversaryImpl publicKey secretKey)
            (adversary.main publicKey)) cache := by
    rw [sourceDirectMappedAdversaryImpl_eq_compose]
    apply expectedSimulatedQueryCount_compose_le
    intro input initialCache
    rcases input with (uniformOrHash | request)
    · rcases uniformOrHash with uniformIndex | hashInput
      · simp [outerPredicate, IsGlobalChainProbeAction,
          globalChainProbeActionCost]
      · by_cases hrelevant : GlobalChainProbeRelevantInput secretKey hashInput
        · simp only [outerPredicate, IsGlobalChainProbeAction,
            globalChainProbeActionCost, hrelevant, if_true]
          rw [sourceUnloggedMappedAdversaryImpl_apply_inl]
          change (1 : ENNReal) ≤ expectedSimulatedQueryCount xmssRomImpl
            innerPredicate
              (liftM (OracleWorld.query (.inr hashInput)) :
                OracleComp OracleWorld
                  (OracleWorld.Range (.inr hashInput))) initialCache
          rw [expectedSimulatedQueryCount_query]
          simp [innerPredicate, Rom.IsRelevantHashQuery, hrelevant]
        · simp [outerPredicate, IsGlobalChainProbeAction,
            globalChainProbeActionCost, hrelevant]
    · simp [outerPredicate, IsGlobalChainProbeAction,
        globalChainProbeActionCost]
  calc
    _ ≤ sourceRelevantTraceResource secretKey (cache, []) +
        expectedSimulatedQueryCount
          (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
          outerPredicate (adversary.main publicKey) (cache, []) := hresource
    _ = expectedSimulatedQueryCount
          (sourceDirectMappedAdversaryImpl publicKey secretKey)
          outerPredicate (adversary.main publicKey) cache := by
      rw [expectedSimulatedQueryCount_sourceDirectTraced_eq]
      simp [sourceRelevantTraceResource]
    _ ≤ _ := hcompose

theorem sourceDirectTracedVerifier_simulation_trace_eq
    (computation : OracleComp OracleWorld α)
    (initialState : SourceTracedState)
    (result : α × SourceTracedState)
    (hresult : result ∈ support
      ((simulateQ sourceDirectTracedVerifierImpl computation).run
        initialState)) :
    result.2.2 = initialState.2 := by
  rw [sourceDirectTracedVerifierImpl_run_eq] at hresult
  rw [support_map] at hresult
  obtain ⟨baseResult, _hbaseResult, heq⟩ := hresult
  simpa using (congrArg (fun candidate => candidate.2.2) heq).symm

@[simp]
theorem sourceRelevantTraceResource_materializePrecomputation
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (state : SourceTracedState) :
    sourceRelevantTraceResource
        (Concrete.materializePrecomputation cache secretKey) state =
      sourceRelevantTraceResource secretKey state := by
  unfold sourceRelevantTraceResource
    AttackerActionTrace.globalChainProbeRelevantInputs
    GlobalChainProbeRelevantInput Concrete.materializePrecomputation
    Concrete.precomputedSecretKey
  rfl

theorem expectedSourceGlobalTracedDetailedExecutionRelevantCost_le_adversary
    (adversary : Adversary Concrete.scheme)
    (keyView : ProgrammedGlobalChainKeygenView) :
    (∑' result,
        Pr[= result | sourceGlobalTracedDetailedExecution adversary keyView] *
          sourceRelevantTraceResource keyView.secretKey result.2) ≤
      ∑' result,
        Pr[= result |
          (simulateQ
            (sourceDirectTracedMappedAdversaryImpl keyView.publicKey
              (Concrete.materializePrecomputation keyView.cache
                keyView.secretKey))
            (adversary.main keyView.publicKey)).run (keyView.cache, [])] *
          sourceRelevantTraceResource
            (Concrete.materializePrecomputation keyView.cache
              keyView.secretKey) result.2 := by
  unfold sourceGlobalTracedDetailedExecution
  rw [tsum_probOutput_bind_mul]
  apply ENNReal.tsum_le_tsum
  intro handled
  apply mul_le_mul_right
  rw [tsum_probOutput_bind_mul]
  calc
    (∑' verified,
        Pr[= verified |
          (simulateQ sourceDirectTracedVerifierImpl
            (Concrete.scheme.verify keyView.publicKey handled.1.epoch
              handled.1.message handled.1.signature)).run handled.2] *
          ∑' finalResult,
            Pr[= finalResult | pure ((handled.1, verified.1), verified.2)] *
              sourceRelevantTraceResource keyView.secretKey finalResult.2) =
      ∑' verified,
        Pr[= verified |
          (simulateQ sourceDirectTracedVerifierImpl
            (Concrete.scheme.verify keyView.publicKey handled.1.epoch
              handled.1.message handled.1.signature)).run handled.2] *
          sourceRelevantTraceResource keyView.secretKey verified.2 := by
      apply tsum_congr
      intro verified
      rw [tsum_probOutput_pure_mul]
    _ ≤ ∑' verified,
        Pr[= verified |
          (simulateQ sourceDirectTracedVerifierImpl
            (Concrete.scheme.verify keyView.publicKey handled.1.epoch
              handled.1.message handled.1.signature)).run handled.2] *
          sourceRelevantTraceResource keyView.secretKey handled.2 := by
      apply ENNReal.tsum_le_tsum
      intro verified
      by_cases hvertified : verified ∈ support
          ((simulateQ sourceDirectTracedVerifierImpl
            (Concrete.scheme.verify keyView.publicKey handled.1.epoch
              handled.1.message handled.1.signature)).run handled.2)
      · have htrace := sourceDirectTracedVerifier_simulation_trace_eq
          _ _ _ hvertified
        have hresource :
            sourceRelevantTraceResource keyView.secretKey verified.2 =
              sourceRelevantTraceResource keyView.secretKey handled.2 := by
          unfold sourceRelevantTraceResource
          rw [htrace]
        rw [hresource]
      · rw [probOutput_eq_zero_of_not_mem_support hvertified]
        simp
    _ = (∑' verified,
          Pr[= verified |
            (simulateQ sourceDirectTracedVerifierImpl
              (Concrete.scheme.verify keyView.publicKey handled.1.epoch
                handled.1.message handled.1.signature)).run handled.2]) *
          sourceRelevantTraceResource keyView.secretKey handled.2 := by
      rw [ENNReal.tsum_mul_right]
    _ ≤ sourceRelevantTraceResource keyView.secretKey handled.2 := by
      calc
        _ ≤ 1 * sourceRelevantTraceResource keyView.secretKey handled.2 := by
          gcongr
          exact tsum_probOutput_le_one
        _ = _ := one_mul _
    _ = sourceRelevantTraceResource
        (Concrete.materializePrecomputation keyView.cache keyView.secretKey)
          handled.2 := by
      rw [sourceRelevantTraceResource_materializePrecomputation]

theorem expectedSourceGlobalTracedDetailedExecutionRelevantCost_le
    (adversary : Adversary Concrete.scheme)
    (keyView : ProgrammedGlobalChainKeygenView) :
    (∑' result,
        Pr[= result | sourceGlobalTracedDetailedExecution adversary keyView] *
          sourceRelevantTraceResource keyView.secretKey result.2) ≤
      expectedSimulatedQueryCount xmssRomImpl
        (Rom.IsRelevantHashQuery
          (GlobalChainProbeRelevantInput
            (Concrete.materializePrecomputation keyView.cache
              keyView.secretKey)))
        (cappedSourceUnloggedDetailedGameAfterKeygen adversary
          keyView.publicKey
            (Concrete.materializePrecomputation keyView.cache
              keyView.secretKey)) keyView.cache := by
  let materialized :=
    Concrete.materializePrecomputation keyView.cache keyView.secretKey
  let adversaryComputation :=
    simulateQ (sourceUnloggedMappedAdversaryImpl keyView.publicKey materialized)
      (adversary.main keyView.publicKey)
  calc
    _ ≤ ∑' result,
        Pr[= result |
          (simulateQ
            (sourceDirectTracedMappedAdversaryImpl keyView.publicKey
              materialized) (adversary.main keyView.publicKey)).run
                (keyView.cache, [])] *
          sourceRelevantTraceResource materialized result.2 := by
      exact
        expectedSourceGlobalTracedDetailedExecutionRelevantCost_le_adversary
          adversary keyView
    _ ≤ expectedSimulatedQueryCount xmssRomImpl
        (Rom.IsRelevantHashQuery
          (GlobalChainProbeRelevantInput materialized))
        adversaryComputation keyView.cache := by
      exact expectedSourceTracedAdversaryRelevantCost_le keyView.publicKey
        materialized adversary keyView.cache
    _ ≤ expectedSimulatedQueryCount xmssRomImpl
        (Rom.IsRelevantHashQuery
          (GlobalChainProbeRelevantInput materialized))
        (cappedSourceUnloggedDetailedGameAfterKeygen adversary
          keyView.publicKey materialized) keyView.cache := by
      unfold cappedSourceUnloggedDetailedGameAfterKeygen
      rw [expectedSimulatedQueryCount_bind]
      exact le_add_right le_rfl

noncomputable def globalHighBadRelevantAttackerCost
    (result : GlobalHighMonitoredProgramResult) : ENNReal := by
  classical
  exact if result.2.2.1.bad then globalHighRelevantAttackerCost result else 0

noncomputable def globalHighBoundedPublicProbeCost
    (queries : Nat) (result : GlobalHighMonitoredProgramResult) : ENNReal :=
  RevealProbeOracleSimulation.observedProbeCount
    (RevealProbeOracleSimulation.enforceEagerResult (queries + numChains)
      (globalHighMonitoredPublicProjection result)).2.2

noncomputable def globalHighBoundedPublicHitCost
    (queries : Nat) (result : GlobalHighMonitoredProgramResult) : ENNReal := by
  classical
  exact if GlobalHighBoundedPublicObservedHit queries result then
    ((queries + numChains : Nat) : ENNReal) else 0

theorem globalChainProbeRelevantInput_eq_of_parameter_eq
    (left right : SecretKey) (hparameter : left.parameter = right.parameter) :
    GlobalChainProbeRelevantInput left = GlobalChainProbeRelevantInput right := by
  funext input
  unfold GlobalChainProbeRelevantInput
  rw [hparameter]

theorem sourceGlobalHighMonitoredProgramRelation_relevantAttackerCost_le
    (left : SourceGlobalTracedProgramResult)
    (right : GlobalHighMonitoredProgramResult)
    (hleftSupport : left ∈ support (sourceGlobalTracedProgram adversary))
    (hrightSupport : right ∈ support (globalHighMonitoredProgram adversary))
    (hrel : SourceGlobalHighMonitoredProgramRelation left right) :
    globalHighRelevantAttackerCost right ≤
      sourceGlobalRelevantAttackerCost left +
        globalHighBadRelevantAttackerCost right := by
  rcases hrel.2.1 with hgood | hbad
  · have hleftKeySupport := sourceGlobalTracedProgram_support_keyView adversary
      left hleftSupport
    have hrightKeySupport :=
      (globalHighMonitoredProgram_support_info adversary right
        hrightSupport).1
    have hleftParameter : left.1.secretKey.parameter =
        right.1.1.1.secretKey.parameter :=
      (programmedGlobal_secretKey_parameter_eq left.1 right.1 hrel.1
        hleftKeySupport hrightKeySupport).symm
    have hpredicate := globalChainProbeRelevantInput_eq_of_parameter_eq
      left.1.secretKey right.1.1.1.secretKey hleftParameter
    have hnotBad : ¬right.2.2.1.bad := by
      obtain ⟨monitor, hmonitor, _⟩ := hgood.2.1
      intro hbad
      unfold GlobalMonitoredCausalState.bad at hbad
      rw [hmonitor] at hbad
      cases hbad
    unfold globalHighRelevantAttackerCost sourceGlobalRelevantAttackerCost
      globalHighBadRelevantAttackerCost
    rw [if_neg hnotBad]
    rw [← hgood.2.2]
    unfold AttackerActionTrace.globalChainProbeRelevantInputs
    have hfilter :
        left.2.2.2.hashInputs.filter
            (GlobalChainProbeRelevantInput right.1.1.1.secretKey) =
          left.2.2.2.hashInputs.filter
            (GlobalChainProbeRelevantInput left.1.secretKey) := by
      apply List.filter_congr
      intro input _hinput
      rw [Bool.eq_iff_iff]
      simpa only [decide_eq_true_eq] using
        iff_of_eq (congrFun hpredicate input).symm
    rw [hfilter]
    simp
  · unfold globalHighBadRelevantAttackerCost
    rw [if_pos hbad]
    exact le_add_left le_rfl

theorem globalHighMonitoredProgram_support_runtimeProbeCost_le
    (adversary : Adversary Concrete.scheme)
    (result : GlobalHighMonitoredProgramResult)
    (hresult : result ∈ support (globalHighMonitoredProgram adversary)) :
    globalHighRuntimeProbeCost result ≤
      globalHighRelevantAttackerCost result + verifierHashQueryUpperBound := by
  unfold globalHighMonitoredProgram at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨right, _hright, hresult⟩ := hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨execution, hexecution, hpure⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  unfold globalHighMonitoredDetailedExecution at hexecution
  rw [mem_support_bind_iff] at hexecution
  obtain ⟨handled, hhandled, hexecution⟩ := hexecution
  rw [mem_support_bind_iff] at hexecution
  obtain ⟨verified, hvertified, hpure⟩ := hexecution
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst execution
  have hcovered := globalHighMonitoredAdversary_simulation_relevantProbeCountCovered
    right (adversary.main right.1.1.publicKey)
      (⟨globalFilteredCausalKeygenState right.1.1,
        some AdaptiveRevealMonitor.State.empty, []⟩, [])
      (by simp [GlobalMonitoredProbeCountCoveredByRelevantAttackerTrace,
        RevealProbeOracleSimulation.observedProbeCount,
        AttackerActionTrace.globalChainProbeRelevantInputs]) handled hhandled
  have hgrowth := globalHighMonitoredVerifier_simulation_probeCount_growth
    right
      (Concrete.scheme.verify right.1.1.publicKey handled.1.epoch
        handled.1.message handled.1.signature)
      verifierHashQueryUpperBound
      (Concrete.scheme_verify_hashQueryBound_upper right.1.1.publicKey
        handled.1.epoch handled.1.message handled.1.signature)
      handled.2 verified hvertified
  have htrace := globalHighMonitoredVerifier_simulation_actionTrace_eq right
    (Concrete.scheme.verify right.1.1.publicKey handled.1.epoch
      handled.1.message handled.1.signature)
    handled.2 verified hvertified
  unfold GlobalMonitoredProbeCountCoveredByRelevantAttackerTrace at hcovered
  unfold globalHighRuntimeProbeCost globalHighRelevantAttackerCost
  dsimp only
  rw [htrace]
  have hnat : RevealProbeOracleSimulation.observedProbeCount
        verified.2.1.trace ≤
      (handled.2.2.globalChainProbeRelevantInputs
        right.1.1.secretKey).length + verifierHashQueryUpperBound := by
    exact hgrowth.trans (by omega)
  exact_mod_cast hnat

theorem sourceGlobalHighBoundedProgramRelation_publicProbeCost_le
    (queries : Nat) (adversary : Adversary Concrete.scheme)
    (left : SourceGlobalTracedProgramResult)
    (right : GlobalHighMonitoredProgramResult)
    (hleftSupport : left ∈ support (sourceGlobalTracedProgram adversary))
    (hrightSupport : right ∈ support (globalHighMonitoredProgram adversary))
    (hrel : SourceGlobalHighBoundedProgramRelation queries
      (queries + numChains) left right) :
    globalHighBoundedPublicProbeCost queries right ≤
      sourceGlobalRelevantAttackerCost left +
        (verifierHashQueryUpperBound + numChains : Nat) +
          globalHighBoundedPublicHitCost queries right := by
  classical
  rcases hrel with ⟨hkey, hgoodOrHit, hconsistent⟩
  rcases hgoodOrHit with hgood | hhit
  · have hunbounded : SourceGlobalHighMonitoredProgramRelation left right :=
      ⟨hkey, Or.inl hgood.1, hconsistent⟩
    have hnotBad : ¬right.2.2.1.bad := by
      obtain ⟨monitor, hmonitor, _⟩ := hgood.1.2.1
      intro hbad
      unfold GlobalMonitoredCausalState.bad at hbad
      rw [hmonitor] at hbad
      cases hbad
    have hrelevant :=
      sourceGlobalHighMonitoredProgramRelation_relevantAttackerCost_le
        left right hleftSupport hrightSupport hunbounded
    unfold globalHighBadRelevantAttackerCost at hrelevant
    rw [if_neg hnotBad, add_zero] at hrelevant
    have hruntime := globalHighMonitoredProgram_support_runtimeProbeCost_le
      adversary right hrightSupport
    have henforced :=
      RevealProbeOracleSimulation.observedProbeCount_enforceProbeTrace_le
        (queries + numChains)
        (globalHighMonitoredPublicProjection right).2.2
    have hraw :
        (RevealProbeOracleSimulation.observedProbeCount
          (globalHighMonitoredPublicProjection right).2.2 : ENNReal) =
        globalHighRuntimeProbeCost right + numChains := by
      unfold globalHighMonitoredPublicProjection globalHighRuntimeProbeCost
      dsimp only
      rw [RevealProbeOracleSimulation.observedProbeCount_append,
        observedProbeCount_globalForgeryPrimaryProbeTrace]
      exact_mod_cast rfl
    unfold globalHighBoundedPublicProbeCost
    dsimp only [RevealProbeOracleSimulation.enforceEagerResult]
    calc
      _ ≤ (RevealProbeOracleSimulation.observedProbeCount
          (globalHighMonitoredPublicProjection right).2.2 : ENNReal) := by
        exact_mod_cast henforced
      _ = globalHighRuntimeProbeCost right + numChains := hraw
      _ ≤ globalHighRelevantAttackerCost right +
          verifierHashQueryUpperBound + numChains := by gcongr
      _ ≤ sourceGlobalRelevantAttackerCost left +
          verifierHashQueryUpperBound + numChains := by gcongr
      _ = sourceGlobalRelevantAttackerCost left +
          (verifierHashQueryUpperBound + numChains : Nat) := by
        simp only [Nat.cast_add, add_assoc]
      _ ≤ sourceGlobalRelevantAttackerCost left +
          (verifierHashQueryUpperBound + numChains : Nat) +
            globalHighBoundedPublicHitCost queries right :=
        le_add_right le_rfl
  · have hboundedPublic : GlobalHighBoundedPublicObservedHit queries right := by
      unfold GlobalHighBoundedPublicObservedHit
      unfold RevealProbeOracleSimulation.ObservedHit
      dsimp only [globalHighMonitoredPublicProjection,
        RevealProbeOracleSimulation.enforceEagerResult]
      exact
        RevealProbeOracleSimulation.runObserved_enforceProbeTrace_append_eq_true_of_prefix
          right.1.1.2 AdaptiveRevealMonitor.State.empty right.2.2.1.trace
            (globalForgeryPrimaryProbeTrace
              (globalHighMonitoredErasedResult right)) (queries + numChains)
                hhit
    have hcap :=
      RevealProbeOracleSimulation.observedProbeCount_enforceProbeTrace_le_fuel
        (queries + numChains)
        (globalHighMonitoredPublicProjection right).2.2
    unfold globalHighBoundedPublicProbeCost
      globalHighBoundedPublicHitCost
    dsimp only [RevealProbeOracleSimulation.enforceEagerResult]
    rw [if_pos hboundedPublic]
    calc
      _ ≤ ((queries + numChains : Nat) : ENNReal) := by exact_mod_cast hcap
      _ ≤ sourceGlobalRelevantAttackerCost left +
          (verifierHashQueryUpperBound + numChains : Nat) +
            ((queries + numChains : Nat) : ENNReal) := le_add_left le_rfl

noncomputable def expectedGlobalHighRuntimeProbeCost
    (adversary : Adversary Concrete.scheme) : ENNReal :=
  ∑' result, Pr[= result | globalHighMonitoredProgram adversary] *
    globalHighRuntimeProbeCost result

noncomputable def expectedGlobalHighRelevantAttackerCost
    (adversary : Adversary Concrete.scheme) : ENNReal :=
  ∑' result, Pr[= result | globalHighMonitoredProgram adversary] *
    globalHighRelevantAttackerCost result

noncomputable def expectedGlobalHighBadRelevantAttackerCost
    (adversary : Adversary Concrete.scheme) : ENNReal :=
  ∑' result, Pr[= result | globalHighMonitoredProgram adversary] *
    globalHighBadRelevantAttackerCost result

noncomputable def expectedSourceGlobalRelevantAttackerCost
    (adversary : Adversary Concrete.scheme) : ENNReal :=
  ∑' result, Pr[= result | sourceGlobalTracedProgram adversary] *
    sourceGlobalRelevantAttackerCost result

theorem evalDist_materializedTrajectoryGlobalChainKeygen_eq_schemeKeygen :
    evalDist
        ((fun view : ProgrammedGlobalChainKeygenView =>
          Concrete.materializeCachedKeyResult view.keyResult) <$>
            trajectoryProgrammedGlobalChainKeygen) =
      evalDist ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅) := by
  calc
    _ = evalDist
        ((fun view : ProgrammedGlobalChainKeygenView =>
          Concrete.materializeCachedKeyResult view.keyResult) <$>
            actualGlobalChainKeygen) := by
      apply evalDist_map_congr_of_evalDist_eq
      exact evalDist_actualGlobalChainKeygen_eq_trajectoryProgrammed.symm
    _ = evalDist
        (Concrete.materializeCachedKeyResult <$>
          (simulateQ xmssRomImpl Concrete.keygen).run ∅) := by
      unfold actualGlobalChainKeygen
      simp [ProgrammedGlobalChainKeygenView.keyResult,
        map_eq_bind_pure_comp]
    _ = evalDist
        ((simulateQ xmssRomImpl Concrete.precomputedKeygen).run ∅) :=
      Concrete.evalDist_materialized_keygen_eq_precomputedKeygen
    _ = _ := by rfl

theorem expectedSourceGlobalRelevantAttackerCost_le
    (adversary : Adversary Concrete.scheme) :
    expectedSourceGlobalRelevantAttackerCost adversary ≤
      expectedPostKeygenGlobalChainRelevantQueries adversary := by
  let project := fun view : ProgrammedGlobalChainKeygenView =>
    Concrete.materializeCachedKeyResult view.keyResult
  let keyCost := fun keyResult :
      (PublicKey × SecretKey) × QueryCache HashSpec =>
    expectedSimulatedQueryCount xmssRomImpl
      (Rom.IsRelevantHashQuery
        (GlobalChainProbeRelevantInput keyResult.1.2))
      (cappedSourceUnloggedDetailedGameAfterKeygen adversary
        keyResult.1.1 keyResult.1.2) keyResult.2
  unfold expectedSourceGlobalRelevantAttackerCost sourceGlobalTracedProgram
  rw [tsum_probOutput_bind_mul]
  calc
    (∑' keyView,
        Pr[= keyView | trajectoryProgrammedGlobalChainKeygen] *
          ∑' result,
            Pr[= result |
              sourceGlobalTracedDetailedExecution adversary keyView >>= fun execution =>
                pure (keyView, execution)] *
              sourceGlobalRelevantAttackerCost result) ≤
      ∑' keyView,
        Pr[= keyView | trajectoryProgrammedGlobalChainKeygen] *
          keyCost (project keyView) := by
      apply ENNReal.tsum_le_tsum
      intro keyView
      apply mul_le_mul_right
      calc
        (∑' result,
            Pr[= result |
              sourceGlobalTracedDetailedExecution adversary keyView >>= fun execution =>
                pure (keyView, execution)] *
              sourceGlobalRelevantAttackerCost result) =
          ∑' execution,
            Pr[= execution |
              sourceGlobalTracedDetailedExecution adversary keyView] *
              sourceRelevantTraceResource keyView.secretKey execution.2 := by
          rw [tsum_probOutput_bind_mul]
          apply tsum_congr
          intro execution
          rw [tsum_probOutput_pure_mul]
          rfl
        _ ≤ keyCost (project keyView) := by
          exact expectedSourceGlobalTracedDetailedExecutionRelevantCost_le
            adversary keyView
    _ = ∑' keyResult,
        Pr[= keyResult | project <$> trajectoryProgrammedGlobalChainKeygen] *
          keyCost keyResult :=
      (tsum_probOutput_map_mul trajectoryProgrammedGlobalChainKeygen project
        keyCost).symm
    _ = ∑' keyResult,
        Pr[= keyResult |
          (simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅] *
            keyCost keyResult := by
      apply RevealProbeOracleSimulation.tsum_probOutput_mul_congr_evalDist
      exact evalDist_materializedTrajectoryGlobalChainKeygen_eq_schemeKeygen
    _ = expectedPostKeygenGlobalChainRelevantQueries adversary := by
      rfl

noncomputable def expectedGlobalHighBoundedPublicProbeCost
    (queries : Nat) (adversary : Adversary Concrete.scheme) : ENNReal :=
  ∑' result, Pr[= result | globalHighMonitoredProgram adversary] *
    globalHighBoundedPublicProbeCost queries result

noncomputable def expectedGlobalHighBoundedPublicHitCost
    (queries : Nat) (adversary : Adversary Concrete.scheme) : ENNReal :=
  ∑' result, Pr[= result | globalHighMonitoredProgram adversary] *
    globalHighBoundedPublicHitCost queries result

noncomputable def globalHighBoundedPublicObservedHitProbability
    (queries : Nat) (adversary : Adversary Concrete.scheme) : ENNReal :=
  Pr[GlobalHighBoundedPublicObservedHit queries |
    globalHighMonitoredProgram adversary]

theorem expectedGlobalHighBoundedPublicProbeCost_eq_expectedProbes
    (queries : Nat) (adversary : Adversary Concrete.scheme) :
    expectedGlobalHighBoundedPublicProbeCost queries adversary =
      expectedSimulatedQueryCount
        RevealProbeOracleSimulation.lazyMonitorImpl
        RevealProbeOracleSimulation.IsProbeQuery
        (globalHighBoundedPublicProgram queries adversary)
        AdaptiveRevealMonitor.State.empty := by
  let cost := fun result :
      (GlobalChainValueIndex → Digest) ×
        (Unit × RevealProbeOracleSimulation.ActionTrace
          GlobalChainValueIndex) =>
    (RevealProbeOracleSimulation.observedProbeCount result.2.2 : ENNReal)
  calc
    expectedGlobalHighBoundedPublicProbeCost queries adversary =
        ∑' result, Pr[= result | globalHighMonitoredProgram adversary] *
          cost ((RevealProbeOracleSimulation.enforceEagerResult
            (queries + numChains) ∘
              globalHighMonitoredPublicProjection) result) := by rfl
    _ = ∑' result,
        Pr[= result |
          (RevealProbeOracleSimulation.enforceEagerResult
            (queries + numChains) ∘
              globalHighMonitoredPublicProjection) <$>
                globalHighMonitoredProgram adversary] * cost result :=
      (tsum_probOutput_map_mul (globalHighMonitoredProgram adversary)
        (RevealProbeOracleSimulation.enforceEagerResult
          (queries + numChains) ∘ globalHighMonitoredPublicProjection)
        cost).symm
    _ = ∑' result,
        Pr[= result | RevealProbeOracleSimulation.eagerExperiment
          (globalHighBoundedPublicProgram queries adversary)] *
            cost result := by
      apply RevealProbeOracleSimulation.tsum_probOutput_mul_congr_evalDist
      exact evalDist_globalHighBoundedPublicProjection_eq_boundedExperiment
        queries adversary
    _ = ∑' result,
        Pr[= result | Prod.snd <$>
          RevealProbeOracleSimulation.eagerExperiment
            (globalHighBoundedPublicProgram queries adversary)] *
          (RevealProbeOracleSimulation.observedProbeCount result.2 : ENNReal) :=
      (tsum_probOutput_map_mul
        (RevealProbeOracleSimulation.eagerExperiment
          (globalHighBoundedPublicProgram queries adversary)) Prod.snd
          (fun result =>
            (RevealProbeOracleSimulation.observedProbeCount result.2 :
              ENNReal))).symm
    _ = RevealProbeOracleSimulation.expectedEagerObservedProbeCount
        AdaptiveRevealMonitor.State.empty
          (globalHighBoundedPublicProgram queries adversary) := by
      unfold RevealProbeOracleSimulation.expectedEagerObservedProbeCount
        RevealProbeOracleSimulation.eagerExperiment
      simp [map_eq_bind_pure_comp,
        RevealProbeOracleSimulation.extendTable_empty]
    _ = _ := by
      rw [RevealProbeOracleSimulation.expectedEagerObservedProbeCount_eq_expectedSimulatedQueryCount]

theorem expectedGlobalHighBoundedPublicHitCost_eq
    (queries : Nat) (adversary : Adversary Concrete.scheme) :
    expectedGlobalHighBoundedPublicHitCost queries adversary =
      ((queries + numChains : Nat) : ENNReal) *
        globalHighBoundedPublicObservedHitProbability queries adversary := by
  classical
  unfold expectedGlobalHighBoundedPublicHitCost
    globalHighBoundedPublicHitCost
    globalHighBoundedPublicObservedHitProbability
  calc
    (∑' result, Pr[= result | globalHighMonitoredProgram adversary] *
        if GlobalHighBoundedPublicObservedHit queries result then
          ((queries + numChains : Nat) : ENNReal) else 0) =
      ((queries + numChains : Nat) : ENNReal) *
        ∑' result, Pr[= result | globalHighMonitoredProgram adversary] *
          if GlobalHighBoundedPublicObservedHit queries result then 1 else 0 := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro result
      by_cases hhit : GlobalHighBoundedPublicObservedHit queries result <;>
        simp [hhit, mul_comm]
    _ = ((queries + numChains : Nat) : ENNReal) *
        Pr[GlobalHighBoundedPublicObservedHit queries |
          globalHighMonitoredProgram adversary] := by
      congr 1
      rw [probEvent_eq_tsum_indicator]
      apply tsum_congr
      intro result
      by_cases hhit : GlobalHighBoundedPublicObservedHit queries result <;>
        simp [Set.indicator, hhit]

theorem expectedGlobalHighBoundedPublicProbeCost_le_of_relTriple
    (queries : Nat) (adversary : Adversary Concrete.scheme)
    (hrel : RelTriple (sourceGlobalTracedProgram adversary)
      (globalHighMonitoredProgram adversary)
      (SourceGlobalHighBoundedProgramRelation queries
        (queries + numChains))) :
    expectedGlobalHighBoundedPublicProbeCost queries adversary ≤
      expectedSourceGlobalRelevantAttackerCost adversary +
        (verifierHashQueryUpperBound + numChains : Nat) +
          ((queries + numChains : Nat) : ENNReal) *
            globalHighBoundedPublicObservedHitProbability queries adversary := by
  have hcoupled :
      expectedGlobalHighBoundedPublicProbeCost queries adversary ≤
        expectedSourceGlobalRelevantAttackerCost adversary +
          ∑' result, Pr[= result | globalHighMonitoredProgram adversary] *
            ((verifierHashQueryUpperBound + numChains : Nat) +
              globalHighBoundedPublicHitCost queries result) := by
    unfold expectedGlobalHighBoundedPublicProbeCost
      expectedSourceGlobalRelevantAttackerCost
    apply expectedCost_le_add_of_relTriple
      (sourceGlobalTracedProgram adversary)
      (globalHighMonitoredProgram adversary)
      (fun left right =>
        SourceGlobalHighBoundedProgramRelation queries
          (queries + numChains) left right ∧
            left ∈ support (sourceGlobalTracedProgram adversary) ∧
              right ∈ support (globalHighMonitoredProgram adversary))
      sourceGlobalRelevantAttackerCost
      (globalHighBoundedPublicProbeCost queries)
      (fun result => (verifierHashQueryUpperBound + numChains : Nat) +
        globalHighBoundedPublicHitCost queries result)
    · simpa [and_assoc] using relTriple_with_support hrel
    · intro left right hrelation
      simpa only [add_assoc] using
        (sourceGlobalHighBoundedProgramRelation_publicProbeCost_le
          queries adversary left right hrelation.2.1 hrelation.2.2
            hrelation.1)
  calc
    expectedGlobalHighBoundedPublicProbeCost queries adversary ≤
        expectedSourceGlobalRelevantAttackerCost adversary +
          ∑' result, Pr[= result | globalHighMonitoredProgram adversary] *
            ((verifierHashQueryUpperBound + numChains : Nat) +
              globalHighBoundedPublicHitCost queries result) := hcoupled
    _ = expectedSourceGlobalRelevantAttackerCost adversary +
        ((∑' result, Pr[= result | globalHighMonitoredProgram adversary]) *
            (verifierHashQueryUpperBound + numChains : Nat) +
          expectedGlobalHighBoundedPublicHitCost queries adversary) := by
      unfold expectedGlobalHighBoundedPublicHitCost
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ expectedSourceGlobalRelevantAttackerCost adversary +
        (1 * (verifierHashQueryUpperBound + numChains : Nat) +
          expectedGlobalHighBoundedPublicHitCost queries adversary) := by
      gcongr
      exact tsum_probOutput_le_one
    _ = expectedSourceGlobalRelevantAttackerCost adversary +
        (verifierHashQueryUpperBound + numChains : Nat) +
          ((queries + numChains : Nat) : ENNReal) *
            globalHighBoundedPublicObservedHitProbability queries adversary := by
      rw [expectedGlobalHighBoundedPublicHitCost_eq]
      simp only [one_mul, add_assoc]

theorem expectedGlobalHighBoundedPublicProbeCost_le_sub_keygen
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    expectedGlobalHighBoundedPublicProbeCost
        (q - treeHashQueryCount treeHeight) adversary ≤
      expectedSourceGlobalRelevantAttackerCost adversary +
        (verifierHashQueryUpperBound + numChains : Nat) +
          ((q - treeHashQueryCount treeHeight + numChains : Nat) : ENNReal) *
            globalHighBoundedPublicObservedHitProbability
              (q - treeHashQueryCount treeHeight) adversary := by
  apply expectedGlobalHighBoundedPublicProbeCost_le_of_relTriple
  exact
    relTriple_sourceGlobal_globalHighMonitored_program_boundedHit_sub_keygen
      q (q - treeHashQueryCount treeHeight + numChains) adversary hbound
        (by omega)

theorem globalHighBoundedPublicObservedHitProbability_le_expectedProbes
    (queries : Nat) (adversary : Adversary Concrete.scheme) :
    globalHighBoundedPublicObservedHitProbability queries adversary ≤
      expectedGlobalHighBoundedPublicProbeCost queries adversary /
        ((2 ^ digestBits : Nat) : ENNReal) := by
  unfold globalHighBoundedPublicObservedHitProbability
  calc
    Pr[GlobalHighBoundedPublicObservedHit queries |
        globalHighMonitoredProgram adversary] =
      Pr[RevealProbeOracleSimulation.ObservedHit |
        RevealProbeOracleSimulation.eagerExperiment
          (globalHighBoundedPublicProgram queries adversary)] := by
      rw [show Pr[GlobalHighBoundedPublicObservedHit queries |
          globalHighMonitoredProgram adversary] =
        Pr[RevealProbeOracleSimulation.ObservedHit |
          (RevealProbeOracleSimulation.enforceEagerResult
            (queries + numChains) ∘ globalHighMonitoredPublicProjection) <$>
              globalHighMonitoredProgram adversary] by
        rw [probEvent_map]
        rfl]
      exact probEvent_congr' (fun _ _ => Iff.rfl)
        (evalDist_globalHighBoundedPublicProjection_eq_boundedExperiment
          queries adversary)
    _ ≤ expectedSimulatedQueryCount
          RevealProbeOracleSimulation.lazyMonitorImpl
          RevealProbeOracleSimulation.IsProbeQuery
          (globalHighBoundedPublicProgram queries adversary)
          AdaptiveRevealMonitor.State.empty /
        ((2 ^ digestBits : Nat) : ENNReal) :=
      RevealProbeOracleSimulation.eagerExperiment_observedHit_probability_le_expectedProbeCount
        (queries + numChains)
        (globalHighBoundedPublicProgram queries adversary)
        (globalHighBoundedPublicProgram_isProbeQueryBoundP queries adversary)
    _ = _ := by
      rw [expectedGlobalHighBoundedPublicProbeCost_eq_expectedProbes]

theorem expectedGlobalHighRuntimeProbeCost_le
    (adversary : Adversary Concrete.scheme) :
    expectedGlobalHighRuntimeProbeCost adversary ≤
      expectedGlobalHighRelevantAttackerCost adversary +
        verifierHashQueryUpperBound := by
  unfold expectedGlobalHighRuntimeProbeCost
    expectedGlobalHighRelevantAttackerCost
  calc
    _ ≤ ∑' result, Pr[= result | globalHighMonitoredProgram adversary] *
        (globalHighRelevantAttackerCost result +
          verifierHashQueryUpperBound) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support
          (globalHighMonitoredProgram adversary)
      · gcongr
        exact globalHighMonitoredProgram_support_runtimeProbeCost_le adversary
          result hresult
      · rw [probOutput_eq_zero_of_not_mem_support hresult]
        simp
    _ = (∑' result, Pr[= result | globalHighMonitoredProgram adversary] *
          globalHighRelevantAttackerCost result) +
        (∑' result, Pr[= result | globalHighMonitoredProgram adversary]) *
          verifierHashQueryUpperBound := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ (∑' result, Pr[= result | globalHighMonitoredProgram adversary] *
          globalHighRelevantAttackerCost result) +
        1 * verifierHashQueryUpperBound := by
      gcongr
      exact tsum_probOutput_le_one
    _ = _ := by simp

theorem expectedGlobalHighRelevantAttackerCost_le
    (adversary : Adversary Concrete.scheme) :
    expectedGlobalHighRelevantAttackerCost adversary ≤
      expectedSourceGlobalRelevantAttackerCost adversary +
        expectedGlobalHighBadRelevantAttackerCost adversary := by
  unfold expectedGlobalHighRelevantAttackerCost
    expectedSourceGlobalRelevantAttackerCost
    expectedGlobalHighBadRelevantAttackerCost
  apply expectedCost_le_add_of_relTriple
    (sourceGlobalTracedProgram adversary)
    (globalHighMonitoredProgram adversary)
    (fun left right =>
      SourceGlobalHighMonitoredProgramRelation left right ∧
        left ∈ support (sourceGlobalTracedProgram adversary) ∧
        right ∈ support (globalHighMonitoredProgram adversary))
    sourceGlobalRelevantAttackerCost globalHighRelevantAttackerCost
    globalHighBadRelevantAttackerCost
  · simpa [and_assoc] using
      (relTriple_with_support
        (relTriple_sourceGlobal_globalHighMonitored_program adversary))
  · intro left right hrel
    exact sourceGlobalHighMonitoredProgramRelation_relevantAttackerCost_le
      left right hrel.2.1 hrel.2.2 hrel.1

theorem expectedGlobalHighRuntimeProbeCost_eq_expectedGlobalHighDirectProbeQueries
    (adversary : Adversary Concrete.scheme) :
    expectedGlobalHighRuntimeProbeCost adversary =
      expectedGlobalHighDirectProbeQueries adversary := by
  let cost := fun result : GlobalHighEagerResult =>
    (RevealProbeOracleSimulation.observedProbeCount result.2.2 : ENNReal)
  calc
    expectedGlobalHighRuntimeProbeCost adversary =
        ∑' result, Pr[= result | globalHighMonitoredProgram adversary] *
          cost (globalHighMonitoredDirectProjection result) := by rfl
    _ = ∑' result,
        Pr[= result | globalHighMonitoredDirectProjection <$>
          globalHighMonitoredProgram adversary] * cost result :=
      (tsum_probOutput_map_mul (globalHighMonitoredProgram adversary)
        globalHighMonitoredDirectProjection cost).symm
    _ = ∑' result, Pr[= result | globalHighDirectEagerExperiment adversary] *
        cost result := by
      apply RevealProbeOracleSimulation.tsum_probOutput_mul_congr_evalDist
      exact evalDist_globalHighMonitoredDirectProjection_eq_eagerExperiment
        adversary
    _ = ∑' result,
        Pr[= result | Prod.snd <$> globalHighDirectEagerExperiment adversary] *
          (RevealProbeOracleSimulation.observedProbeCount result.2 : ENNReal) :=
      (tsum_probOutput_map_mul (globalHighDirectEagerExperiment adversary)
        Prod.snd (fun result =>
          (RevealProbeOracleSimulation.observedProbeCount result.2 : ENNReal)
        )).symm
    _ = RevealProbeOracleSimulation.expectedEagerObservedProbeCount
        AdaptiveRevealMonitor.State.empty
          (globalHighDirectProgram adversary) := by
      unfold RevealProbeOracleSimulation.expectedEagerObservedProbeCount
        globalHighDirectEagerExperiment RevealProbeOracleSimulation.eagerExperiment
      simp [map_eq_bind_pure_comp,
        RevealProbeOracleSimulation.extendTable_empty]
    _ = expectedGlobalHighDirectProbeQueries adversary := by
      rw [RevealProbeOracleSimulation.expectedEagerObservedProbeCount_eq_expectedSimulatedQueryCount]
      rfl

noncomputable def globalHighBadProbability
    (adversary : Adversary Concrete.scheme) : ENNReal :=
  Pr[fun result : GlobalHighMonitoredProgramResult => result.2.2.1.bad |
    globalHighMonitoredProgram adversary]

noncomputable def globalHighPublicObservedHitProbability
    (adversary : Adversary Concrete.scheme) : ENNReal :=
  Pr[RevealProbeOracleSimulation.ObservedHit |
    RevealProbeOracleSimulation.eagerExperiment
      (globalHighDirectPublicProgram adversary)]

theorem expectedGlobalHighBadRelevantAttackerCost_le
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hcost : ∀ result ∈ support (globalHighMonitoredProgram adversary),
      globalHighRelevantAttackerCost result ≤ q) :
    expectedGlobalHighBadRelevantAttackerCost adversary ≤
      (q : ENNReal) * globalHighBadProbability adversary := by
  classical
  unfold expectedGlobalHighBadRelevantAttackerCost globalHighBadProbability
  calc
    _ ≤ ∑' result, Pr[= result | globalHighMonitoredProgram adversary] *
        ((q : ENNReal) * if result.2.2.1.bad then 1 else 0) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support
          (globalHighMonitoredProgram adversary)
      · by_cases hbad : result.2.2.1.bad
        · simp [globalHighBadRelevantAttackerCost, hbad]
          gcongr
          exact hcost result hresult
        · simp [globalHighBadRelevantAttackerCost, hbad]
      · rw [probOutput_eq_zero_of_not_mem_support hresult]
        simp
    _ = (q : ENNReal) *
        ∑' result, Pr[= result | globalHighMonitoredProgram adversary] *
          if result.2.2.1.bad then 1 else 0 := by
      calc
        _ = ∑' result, (q : ENNReal) *
            (Pr[= result | globalHighMonitoredProgram adversary] *
              if result.2.2.1.bad then 1 else 0) := by
          apply tsum_congr
          intro result
          ring
        _ = _ := ENNReal.tsum_mul_left
    _ = (q : ENNReal) *
        Pr[fun result : GlobalHighMonitoredProgramResult => result.2.2.1.bad |
          globalHighMonitoredProgram adversary] := by
      congr 1
      rw [probEvent_eq_tsum_indicator]
      apply tsum_congr
      intro result
      by_cases hbad : result.2.2.1.bad <;> simp [Set.indicator, hbad]

theorem globalHighBadProbability_le_publicObservedHitProbability
    (adversary : Adversary Concrete.scheme) :
    globalHighBadProbability adversary ≤
      globalHighPublicObservedHitProbability adversary := by
  classical
  unfold globalHighBadProbability globalHighPublicObservedHitProbability
  calc
    Pr[fun result : GlobalHighMonitoredProgramResult => result.2.2.1.bad |
        globalHighMonitoredProgram adversary] ≤
      Pr[fun result : GlobalHighMonitoredProgramResult =>
          RevealProbeOracleSimulation.ObservedHit
            (globalHighMonitoredPublicProjection result) |
        globalHighMonitoredProgram adversary] := by
      apply probEvent_mono
      intro result hresult hbad
      have hconsistent := globalHighMonitoredDetailedExecution_traceConsistent
        adversary result.1 result.2
          (globalHighMonitoredProgram_support_info adversary result hresult).2
      unfold RevealProbeOracleSimulation.ObservedHit
      dsimp only [globalHighMonitoredPublicProjection]
      apply RevealProbeOracleSimulation.runObserved_append_eq_true_of_prefix
      exact result.2.2.1.bad_implies_runObserved result.1.1.2 hconsistent hbad
    _ = Pr[RevealProbeOracleSimulation.ObservedHit |
        globalHighMonitoredPublicProjection <$>
          globalHighMonitoredProgram adversary] := by
      rw [probEvent_map]
      rfl
    _ = _ := by
      exact probEvent_congr' (fun _ _ => Iff.rfl)
        (evalDist_globalHighMonitoredPublicProjection_eq_publicExperiment
          adversary)

theorem globalHighPublicObservedHitProbability_le_expectedProbes
    (adversary : Adversary Concrete.scheme) :
    globalHighPublicObservedHitProbability adversary ≤
      (expectedGlobalHighDirectProbeQueries adversary + numChains) /
        ((2 ^ digestBits : Nat) : ENNReal) := by
  obtain ⟨fuel, hbound⟩ :=
    RevealProbeOracleSimulation.exists_isProbeQueryBoundP
      (globalHighDirectPublicProgram adversary)
  unfold globalHighPublicObservedHitProbability
  calc
    _ ≤ expectedSimulatedQueryCount
          RevealProbeOracleSimulation.lazyMonitorImpl
          RevealProbeOracleSimulation.IsProbeQuery
          (globalHighDirectPublicProgram adversary)
          AdaptiveRevealMonitor.State.empty /
        ((2 ^ digestBits : Nat) : ENNReal) :=
      RevealProbeOracleSimulation.eagerExperiment_observedHit_probability_le_expectedProbeCount
        fuel (globalHighDirectPublicProgram adversary) hbound
    _ ≤ _ := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      gcongr
      exact expectedGlobalHighDirectPublicProbeQueries_le adversary

def HasSourceGlobalRelevantAttackerExpectedAccounting
    (adversary : Adversary Concrete.scheme) : Prop :=
  expectedSourceGlobalRelevantAttackerCost adversary ≤
    expectedPostKeygenGlobalChainRelevantQueries adversary

def HasGlobalHighRelevantAttackerBound
    (q : Nat) (adversary : Adversary Concrete.scheme) : Prop :=
  ∀ result ∈ support (globalHighMonitoredProgram adversary),
    globalHighRelevantAttackerCost result ≤ q

theorem expectedGlobalHighDirectProbeQueries_le_source_add_hit
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hsource : HasSourceGlobalRelevantAttackerExpectedAccounting adversary)
    (hbound : HasGlobalHighRelevantAttackerBound q adversary) :
    expectedGlobalHighDirectProbeQueries adversary ≤
      expectedPostKeygenGlobalChainRelevantQueries adversary +
        verifierHashQueryUpperBound +
          (q : ENNReal) * globalHighPublicObservedHitProbability adversary := by
  rw [← expectedGlobalHighRuntimeProbeCost_eq_expectedGlobalHighDirectProbeQueries]
  calc
    expectedGlobalHighRuntimeProbeCost adversary ≤
        expectedGlobalHighRelevantAttackerCost adversary +
          verifierHashQueryUpperBound :=
      expectedGlobalHighRuntimeProbeCost_le adversary
    _ ≤ (expectedSourceGlobalRelevantAttackerCost adversary +
          expectedGlobalHighBadRelevantAttackerCost adversary) +
        verifierHashQueryUpperBound := by
      gcongr
      exact expectedGlobalHighRelevantAttackerCost_le adversary
    _ ≤ (expectedPostKeygenGlobalChainRelevantQueries adversary +
          ((q : ENNReal) * globalHighBadProbability adversary)) +
        verifierHashQueryUpperBound := by
      gcongr
      · exact hsource
      · exact expectedGlobalHighBadRelevantAttackerCost_le q adversary hbound
    _ ≤ (expectedPostKeygenGlobalChainRelevantQueries adversary +
          ((q : ENNReal) * globalHighPublicObservedHitProbability adversary)) +
        verifierHashQueryUpperBound := by
      gcongr
      exact globalHighBadProbability_le_publicObservedHitProbability adversary
    _ = _ := by ring

theorem expected_probe_fixedPoint_le
    (q modulus : Nat) (probe source verifier primary : ENNReal)
    (hq : q < modulus)
    (hprobeOne : probe ≤ 1)
    (hsourceFinite : source ≠ ∞)
    (hprimaryFinite : primary ≠ ∞)
    (hprobe : probe ≤ (primary + verifier) / (modulus : ENNReal))
    (hverifier : verifier ≤ source + verifierHashQueryUpperBound +
      (q : ENNReal) * probe) :
    probe ≤
      (source + verifierHashQueryUpperBound + primary) /
        ((modulus - q : Nat) : ENNReal) := by
  have hprobeFinite : probe ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hprobeOne
  have hverifierFinite : verifier ≠ ∞ := by
    apply ne_top_of_le_ne_top _ hverifier
    finiteness
  have hprobeRhsFinite : (primary + verifier) / (modulus : ENNReal) ≠ ∞ := by
    apply ENNReal.div_ne_top
    · exact ENNReal.add_ne_top.mpr ⟨hprimaryFinite, hverifierFinite⟩
    · exact_mod_cast (show modulus ≠ 0 by omega)
  have hfinalRhsFinite :
      (source + verifierHashQueryUpperBound + primary) /
          ((modulus - q : Nat) : ENNReal) ≠ ∞ := by
    apply ENNReal.div_ne_top
    · exact ENNReal.add_ne_top.mpr
        ⟨ENNReal.add_ne_top.mpr ⟨hsourceFinite, by finiteness⟩,
          hprimaryFinite⟩
    · exact_mod_cast (show modulus - q ≠ 0 by omega)
  have hprobeReal := ENNReal.toReal_mono hprobeRhsFinite hprobe
  have hverifierReal := ENNReal.toReal_mono (by finiteness) hverifier
  apply (ENNReal.toReal_le_toReal hprobeFinite hfinalRhsFinite).mp
  rw [ENNReal.toReal_div, ENNReal.toReal_add hprimaryFinite hverifierFinite,
    ENNReal.toReal_natCast] at hprobeReal
  rw [ENNReal.toReal_add
      (ENNReal.add_ne_top.mpr ⟨hsourceFinite, by finiteness⟩)
      (ENNReal.mul_ne_top (by finiteness) hprobeFinite),
    ENNReal.toReal_add hsourceFinite (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_natCast] at hverifierReal
  rw [ENNReal.toReal_div,
    ENNReal.toReal_add
      (ENNReal.add_ne_top.mpr ⟨hsourceFinite, by finiteness⟩)
      hprimaryFinite,
    ENNReal.toReal_add hsourceFinite (by finiteness),
    ENNReal.toReal_natCast]
  have hdenominator : (0 : ℝ) < (modulus - q : Nat) := by
    exact_mod_cast (Nat.sub_pos_of_lt hq)
  have hmodulus : (0 : ℝ) < modulus := by exact_mod_cast (by omega)
  simp only [ENNReal.toReal_natCast] at hverifierReal ⊢
  field_simp at hprobeReal ⊢
  rw [Nat.cast_sub (Nat.le_of_lt hq)] at hdenominator ⊢
  nlinarith

theorem globalHighPublicObservedHitProbability_le_fixedPoint
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hq : q < 2 ^ digestBits)
    (hsource : HasSourceGlobalRelevantAttackerExpectedAccounting adversary)
    (hbound : HasGlobalHighRelevantAttackerBound q adversary)
    (hsourceFinite :
      expectedPostKeygenGlobalChainRelevantQueries adversary ≠ ∞) :
    globalHighPublicObservedHitProbability adversary ≤
      (expectedPostKeygenGlobalChainRelevantQueries adversary +
          verifierHashQueryUpperBound + numChains) /
        ((2 ^ digestBits - q : Nat) : ENNReal) := by
  apply expected_probe_fixedPoint_le q (2 ^ digestBits)
    (globalHighPublicObservedHitProbability adversary)
    (expectedPostKeygenGlobalChainRelevantQueries adversary)
    (expectedGlobalHighDirectProbeQueries adversary) numChains hq
    probEvent_le_one hsourceFinite (by finiteness)
  · simpa [add_comm] using
      globalHighPublicObservedHitProbability_le_expectedProbes adversary
  · exact expectedGlobalHighDirectProbeQueries_le_source_add_hit q adversary
      hsource hbound

theorem globalHighBoundedPublicObservedHitProbability_le_fixedPoint_sub_keygen
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (hbudget : q - treeHashQueryCount treeHeight + numChains <
      2 ^ digestBits)
    (hsource : HasSourceGlobalRelevantAttackerExpectedAccounting adversary)
    (hsourceFinite :
      expectedPostKeygenGlobalChainRelevantQueries adversary ≠ ∞) :
    globalHighBoundedPublicObservedHitProbability
        (q - treeHashQueryCount treeHeight) adversary ≤
      (expectedPostKeygenGlobalChainRelevantQueries adversary + numChains +
          verifierHashQueryUpperBound) /
        ((2 ^ digestBits -
          (q - treeHashQueryCount treeHeight + numChains) : Nat) : ENNReal) := by
  let remaining := q - treeHashQueryCount treeHeight
  let probe := globalHighBoundedPublicObservedHitProbability remaining adversary
  let verifier := expectedGlobalHighBoundedPublicProbeCost remaining adversary
  have hverifier : verifier ≤
      (expectedPostKeygenGlobalChainRelevantQueries adversary + numChains) +
        verifierHashQueryUpperBound +
          ((remaining + numChains : Nat) : ENNReal) * probe := by
    calc
      verifier ≤ expectedSourceGlobalRelevantAttackerCost adversary +
          (verifierHashQueryUpperBound + numChains : Nat) +
            ((remaining + numChains : Nat) : ENNReal) * probe := by
        exact expectedGlobalHighBoundedPublicProbeCost_le_sub_keygen
          q adversary hbound
      _ ≤ expectedPostKeygenGlobalChainRelevantQueries adversary +
          (verifierHashQueryUpperBound + numChains : Nat) +
            ((remaining + numChains : Nat) : ENNReal) * probe := by
        gcongr
        exact hsource
      _ = (expectedPostKeygenGlobalChainRelevantQueries adversary +
            numChains) + verifierHashQueryUpperBound +
          ((remaining + numChains : Nat) : ENNReal) * probe := by
        simp only [Nat.cast_add]
        ring
  have hfixed := expected_probe_fixedPoint_le
    (remaining + numChains) (2 ^ digestBits) probe
    (expectedPostKeygenGlobalChainRelevantQueries adversary + numChains)
    verifier 0 (by simpa [remaining] using hbudget) probEvent_le_one
    (ENNReal.add_ne_top.mpr ⟨hsourceFinite, by finiteness⟩) (by finiteness)
    (by
      simpa [probe, verifier, add_comm] using
        (globalHighBoundedPublicObservedHitProbability_le_expectedProbes
          remaining adversary))
    hverifier
  change probe ≤
    (expectedPostKeygenGlobalChainRelevantQueries adversary + numChains +
        verifierHashQueryUpperBound) /
      ((2 ^ digestBits - (remaining + numChains) : Nat) : ENNReal)
  simpa only [add_zero] using hfixed

theorem globalWinningChainOrigin_probability_le_fixedPoint_sub_keygen
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (hbudget : q - treeHashQueryCount treeHeight + numChains <
      2 ^ digestBits)
    (hsource : HasSourceGlobalRelevantAttackerExpectedAccounting adversary)
    (hsourceFinite :
      expectedPostKeygenGlobalChainRelevantQueries adversary ≠ ∞) :
    Pr[fun result =>
        GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.2 result.2.2
          result.1.1.2 result.2.1 |
      detailedGameWithKeygenCache adversary] ≤
      (expectedPostKeygenGlobalChainRelevantQueries adversary + numChains +
          verifierHashQueryUpperBound) /
        ((2 ^ digestBits -
          (q - treeHashQueryCount treeHeight + numChains) : Nat) : ENNReal) := by
  exact
    (globalWinningChainOrigin_probability_le_boundedPublicObservedHit_sub_keygen
      q adversary hbound).trans
        (globalHighBoundedPublicObservedHitProbability_le_fixedPoint_sub_keygen
          q adversary hbound hbudget hsource hsourceFinite)

end XmssSecurity.CappedChain
