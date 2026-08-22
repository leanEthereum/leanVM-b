import XmssSecurity.Proof.CappedExactFirstLaneSourceTrace
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

theorem encodingObservation?_eq_of_globalSigningCachesAgree
    (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialLeft initialRight finalLeft finalRight : QueryCache HashSpec)
    (hinitial : HashCachesAgreeOn
      (GlobalSigningComparableHashInput secretKey.parameter)
      initialLeft initialRight)
    (hfinal : HashCachesAgreeOn
      (GlobalSigningComparableHashInput secretKey.parameter)
      finalLeft finalRight)
    (output : (OracleWorld + SigningSpec).Range input) :
    encodingObservation? secretKey input (initialLeft, []) output
        (finalLeft, []) =
      encodingObservation? secretKey input (initialRight, []) output
        (finalRight, []) := by
  classical
  rcases input with (uniformOrHash | request)
  · rcases uniformOrHash with n | hashInput
    · rfl
    · cases hepoch : encodingInputEpoch? secretKey.parameter hashInput with
      | none => simp [encodingObservation?, hepoch]
      | some epoch =>
          obtain ⟨payload, hpayload⟩ :=
            exists_encodingInput_of_encodingInputEpoch?_eq_some
              secretKey.parameter hashInput epoch hepoch
          subst hashInput
          have hcache := hinitial _
            ⟨epoch, payload.1, payload.2, rfl⟩
          simp [encodingObservation?, hcache]
  · cases output with
    | none => rfl
    | some signature =>
        let hashInput := Concrete.CacheView.encodingInput
          secretKey.parameter request.epoch
          (request.message, signature.randomness)
        have hinitialCache : initialLeft hashInput = initialRight hashInput :=
          hinitial hashInput ⟨request.epoch, request.message,
            signature.randomness, rfl⟩
        have hfinalCache : finalLeft hashInput = finalRight hashInput :=
          hfinal hashInput ⟨request.epoch, request.message,
            signature.randomness, rfl⟩
        simp [encodingObservation?, hashInput, hinitialCache, hfinalCache]

theorem encodingActionTraceUpdate_eq_of_globalSigningCachesAgree
    (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialLeft initialRight finalLeft finalRight : QueryCache HashSpec)
    (hinitial : HashCachesAgreeOn
      (GlobalSigningComparableHashInput secretKey.parameter)
      initialLeft initialRight)
    (hfinal : HashCachesAgreeOn
      (GlobalSigningComparableHashInput secretKey.parameter)
      finalLeft finalRight)
    (output : (OracleWorld + SigningSpec).Range input)
    (trace : EncodingActionTrace) :
    encodingActionTraceUpdate secretKey input (initialLeft, []) output
        (finalLeft, []) trace =
      encodingActionTraceUpdate secretKey input (initialRight, []) output
        (finalRight, []) trace := by
  unfold encodingActionTraceUpdate
  rw [encodingObservation?_eq_of_globalSigningCachesAgree secretKey input
    initialLeft initialRight finalLeft finalRight hinitial hfinal output]

abbrev SourceExactTracedState :=
  (((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) ×
    AttackerActionTrace)

def sourceExactSigningProjection
    (state : SourceExactTracedState) : SourceSigningTracedState :=
  ((state.1.1.1, state.1.1.2), state.2)

noncomputable def sourceExactQueryResult
    (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : SourceExactTracedState)
    (result : (OracleWorld + SigningSpec).Range input ×
      SourceSigningTracedState) :
    (OracleWorld + SigningSpec).Range input × SourceExactTracedState :=
  (result.1,
    (((result.2.1,
      encodingActionTraceUpdate secretKey input
        (initialState.1.1.1, []) result.1 (result.2.1.1, [])
          initialState.1.2)), result.2.2))

theorem cappedBothTracedMappedAdversaryImpl_query_eq_sourceExactMap
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : SourceExactTracedState) :
    (cappedBothTracedMappedAdversaryImpl publicKey secretKey input).run
        initialState =
      sourceExactQueryResult secretKey input initialState <$>
        (sourceSigningTracedMappedAdversaryImpl publicKey secretKey input).run
          (sourceExactSigningProjection initialState) := by
  unfold cappedBothTracedMappedAdversaryImpl
    QueryImpl.extendState appendAttackerActionTrace
    sourceSigningTracedMappedAdversaryImpl actionTracedStateImpl
    sourceExactQueryResult sourceExactSigningProjection
    cappedEncodingTracedMappedAdversaryImpl QueryImpl.extendState
  simp only [StateT.run_mk, map_bind, bind_assoc, pure_bind]
  apply bind_congr
  intro result
  rfl

theorem encodingActionTraceUpdate_eq_of_parameter_eq
    (leftSecret rightSecret : SecretKey)
    (hparameter : leftSecret.parameter = rightSecret.parameter)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache finalCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (trace : EncodingActionTrace) :
    encodingActionTraceUpdate leftSecret input (initialCache, []) output
        (finalCache, []) trace =
      encodingActionTraceUpdate rightSecret input (initialCache, []) output
        (finalCache, []) trace := by
  unfold encodingActionTraceUpdate encodingObservation?
  rcases input with (uniformOrHash | request)
  · rcases uniformOrHash with n | hashInput
    · rfl
    · rw [hparameter]
  · cases output with
    | none => rfl
    | some signature => rw [hparameter]

theorem relTriple_programmed_globalHighMonitored_sourceExact_action
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftState : SourceExactTracedState)
    (rightState : GlobalMonitoredTracedState)
    (hstate : GlobalSigningMonitoredTracedStateRelation left right.1
      (sourceExactSigningProjection leftState) rightState)
    (input : (OracleWorld + SigningSpec).Domain) :
    RelTriple
      ((cappedBothTracedMappedAdversaryImpl left.publicKey
        (Concrete.materializePrecomputation left.cache left.secretKey)
          input).run leftState)
      ((globalHighMonitoredMappedAdversaryImpl right input).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalSigningMonitoredTracedStateRelation left right.1
            (sourceExactSigningProjection leftResult.2) rightResult.2 ∧
          leftResult.2.1.2 =
            encodingActionTraceUpdate right.1.1.secretKey input
              (rightState.1.causal.cache, []) rightResult.1
              (rightResult.2.1.causal.cache, []) leftState.1.2) ∨
        rightResult.2.1.bad) := by
  let leftSecret :=
    Concrete.materializePrecomputation left.cache left.secretKey
  have hbase := relTriple_programmed_globalHighMonitored_signingAction left
    right hrel hleftSupport hrightSupport
    (sourceExactSigningProjection leftState) rightState hstate input
  have hlifted : RelTriple
      (sourceExactQueryResult leftSecret input leftState <$>
        (sourceSigningTracedMappedAdversaryImpl left.publicKey leftSecret
          input).run (sourceExactSigningProjection leftState))
      (id <$> (globalHighMonitoredMappedAdversaryImpl right input).run
        rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalSigningMonitoredTracedStateRelation left right.1
            (sourceExactSigningProjection leftResult.2) rightResult.2 ∧
          leftResult.2.1.2 =
            encodingActionTraceUpdate right.1.1.secretKey input
              (rightState.1.causal.cache, []) rightResult.1
              (rightResult.2.1.causal.cache, []) leftState.1.2) ∨
        rightResult.2.1.bad) := by
    apply relTriple_map
    apply relTriple_post_mono hbase
    intro leftResult rightResult hresult
    rcases hresult with hgood | hbad
    · apply Or.inl
      refine ⟨hgood.1, hgood.2, ?_⟩
      obtain ⟨_monitorInitial, _hmonitorInitial, _hagreesInitial,
        _hrevealedInitial, hinitialCausal, _hretainedInitial⟩ := hstate.1
      obtain ⟨_monitorFinal, _hmonitorFinal, _hagreesFinal,
        _hrevealedFinal, hfinalCausal, _hretainedFinal⟩ := hgood.2.1
      have hcacheUpdate :=
        encodingActionTraceUpdate_eq_of_globalSigningCachesAgree
          leftSecret input leftState.1.1.1 rightState.1.causal.cache
          leftResult.2.1.1 rightResult.2.1.causal.cache
          (by simpa [leftSecret, Concrete.materializePrecomputation,
            Concrete.precomputedSecretKey, sourceSigningTracedStateProjection,
            sourceExactSigningProjection] using hinitialCausal.1)
          (by simpa [leftSecret, Concrete.materializePrecomputation,
            Concrete.precomputedSecretKey, sourceSigningTracedStateProjection,
            sourceExactSigningProjection] using hfinalCausal.1)
          leftResult.1 leftState.1.2
      have hparameter := programmedGlobal_secretKey_parameter_eq left right
        hrel hleftSupport hrightSupport
      have hsecretUpdate := encodingActionTraceUpdate_eq_of_parameter_eq
        leftSecret right.1.1.secretKey
        (by simpa [leftSecret, Concrete.materializePrecomputation,
          Concrete.precomputedSecretKey] using hparameter.symm)
        input rightState.1.causal.cache rightResult.2.1.causal.cache
        leftResult.1 leftState.1.2
      simpa [sourceExactQueryResult, hgood.1] using
        hcacheUpdate.trans hsecretUpdate
    · exact Or.inr hbad
  rw [cappedBothTracedMappedAdversaryImpl_query_eq_sourceExactMap]
  simpa using hlifted


theorem appendVerificationEncodingObservation_eq_of_globalSigningCachesAgree
    (leftSecret rightSecret : SecretKey)
    (hparameter : leftSecret.parameter = rightSecret.parameter)
    (forgery : Forgery)
    (initialLeft initialRight finalLeft finalRight : QueryCache HashSpec)
    (hinitial : HashCachesAgreeOn
      (GlobalSigningComparableHashInput leftSecret.parameter)
      initialLeft initialRight)
    (hfinal : HashCachesAgreeOn
      (GlobalSigningComparableHashInput leftSecret.parameter)
      finalLeft finalRight)
    (trace : EncodingActionTrace) :
    appendVerificationEncodingObservation leftSecret forgery
        initialLeft finalLeft trace =
      appendVerificationEncodingObservation rightSecret forgery
        initialRight finalRight trace := by
  let input := Concrete.CacheView.encodingInput leftSecret.parameter
    forgery.epoch (forgery.message, forgery.signature.randomness)
  let rightInput := Concrete.CacheView.encodingInput rightSecret.parameter
    forgery.epoch (forgery.message, forgery.signature.randomness)
  have hinput : input = rightInput := by simp [input, rightInput, hparameter]
  have hinitialCache : initialLeft input = initialRight input :=
    hinitial input ⟨forgery.epoch, forgery.message,
      forgery.signature.randomness, rfl⟩
  have hfinalCache : finalLeft input = finalRight input :=
    hfinal input ⟨forgery.epoch, forgery.message,
      forgery.signature.randomness, rfl⟩
  unfold appendVerificationEncodingObservation
  change (if initialLeft input = none then
      match finalLeft input with
      | none => trace
      | some output => trace ++ [.query forgery.epoch output]
    else trace) =
    (if initialRight rightInput = none then
      match finalRight rightInput with
      | none => trace
      | some output => trace ++ [.query forgery.epoch output]
    else trace)
  rw [← hinput, hinitialCache, hfinalCache]

noncomputable def sourceGlobalExactTracedDetailedExecution
    (adversary : Adversary)
    (keyView : ProgrammedGlobalChainKeygenView) :
    ProbComp ((Forgery × Bool) × SourceExactTracedState) := do
  let handled ← (simulateQ
    (cappedBothTracedMappedAdversaryImpl keyView.publicKey
      (Concrete.materializePrecomputation keyView.cache keyView.secretKey))
      (adversary.main keyView.publicKey)).run ((((keyView.cache, []), []), []))
  let verified ← (simulateQ sourceSigningTracedVerifierImpl
    (Concrete.scheme.verify keyView.publicKey handled.1.epoch
      handled.1.message handled.1.signature)).run
        (sourceExactSigningProjection handled.2)
  let finalEncodingTrace := appendVerificationEncodingObservation
    (Concrete.materializePrecomputation keyView.cache keyView.secretKey)
    handled.1 handled.2.1.1.1 verified.2.1.1 handled.2.1.2
  pure ((handled.1, verified.1),
    ((verified.2.1, finalEncodingTrace), verified.2.2))

def sourceGlobalExactErasedExecution
    (result : (Forgery × Bool) × SourceExactTracedState) :
    (Forgery × Bool) × SourceTracedState :=
  (result.1, (result.2.1.1.1, result.2.2))

abbrev SourceGlobalExactTracedProgramResult :=
  ProgrammedGlobalChainKeygenView ×
    ((Forgery × Bool) × SourceExactTracedState)

noncomputable def sourceGlobalExactTracedProgram
    (adversary : Adversary) :
    ProbComp SourceGlobalExactTracedProgramResult := do
  let keyView ← trajectoryProgrammedGlobalChainKeygen
  let execution ← sourceGlobalExactTracedDetailedExecution adversary keyView
  pure (keyView, execution)

def sourceGlobalExactErasedResult
    (result : SourceGlobalExactTracedProgramResult) :
    SourceGlobalTracedProgramResult :=
  (result.1, sourceGlobalExactErasedExecution result.2)

theorem sourceGlobalExactTracedDetailedExecution_projection
    (adversary : Adversary)
    (keyView : ProgrammedGlobalChainKeygenView) :
    sourceGlobalExactErasedExecution <$>
        sourceGlobalExactTracedDetailedExecution adversary keyView =
      sourceGlobalTracedDetailedExecution adversary keyView := by
  unfold sourceGlobalExactTracedDetailedExecution
    sourceGlobalTracedDetailedExecution
  let secretKey :=
    Concrete.materializePrecomputation keyView.cache keyView.secretKey
  let finish : Forgery × SourceTracedState →
      ProbComp ((Forgery × Bool) × SourceTracedState) := fun handled => do
    let verified ← (simulateQ sourceDirectTracedVerifierImpl
      (Concrete.scheme.verify keyView.publicKey handled.1.epoch
        handled.1.message handled.1.signature)).run handled.2
    pure ((handled.1, verified.1), verified.2)
  have hprojection := cappedBothTracedMappedAdversaryImpl_actionProjection
    keyView.publicKey secretKey (adversary.main keyView.publicKey)
      (((keyView.cache, []), [])) []
  have hbound := congrArg (fun computation => computation >>= finish)
    hprojection
  simpa [secretKey, finish, sourceGlobalExactErasedExecution, map_bind,
    bind_map_left, bind_assoc, sourceSigningTracedVerifierImpl_run_eq,
    sourceDirectTracedVerifierImpl_run_eq, sourceExactSigningProjection,
    Prod.map]
    using hbound

theorem sourceGlobalExactTracedProgram_projection
    (adversary : Adversary) :
    sourceGlobalExactErasedResult <$>
        sourceGlobalExactTracedProgram adversary =
      sourceGlobalTracedProgram adversary := by
  unfold sourceGlobalExactTracedProgram sourceGlobalTracedProgram
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro keyView
  rw [← sourceGlobalExactTracedDetailedExecution_projection]
  simp [sourceGlobalExactErasedResult, map_eq_bind_pure_comp]

theorem sourceGlobalExactErasedResult_mem_support
    (adversary : Adversary)
    {left : SourceGlobalExactTracedProgramResult}
    (hleft : left ∈ support (sourceGlobalExactTracedProgram adversary)) :
    sourceGlobalExactErasedResult left ∈
      support (sourceGlobalTracedProgram adversary) := by
  rw [← sourceGlobalExactTracedProgram_projection, support_map]
  exact ⟨left, hleft, rfl⟩

def sourceGlobalExactExecutionResult
    (keyView : ProgrammedGlobalChainKeygenView)
    (execution : (Forgery × Bool) × SourceExactTracedState) :
    CappedBothTraceExecution :=
  (⟨keyView.publicKey,
    Concrete.materializePrecomputation keyView.cache keyView.secretKey,
    execution.1.1, execution.2.1.1.2.toSigningLog, execution.1.2⟩,
    execution.2)

def sourceGlobalExactProgramResult
    (result : SourceGlobalExactTracedProgramResult) :
    CappedBothTraceGameResult :=
  (Concrete.materializeCachedKeyResult result.1.keyResult,
    sourceGlobalExactExecutionResult result.1 result.2)

theorem sourceGlobalExactTracedDetailedExecution_eq_bothTraces
    (adversary : Adversary)
    (keyView : ProgrammedGlobalChainKeygenView) :
    sourceGlobalExactExecutionResult keyView <$>
        sourceGlobalExactTracedDetailedExecution adversary keyView =
      cappedDetailedGameAfterKeygenWithBothTraces adversary keyView.publicKey
        (Concrete.materializePrecomputation keyView.cache keyView.secretKey)
        keyView.cache := by
  unfold sourceGlobalExactTracedDetailedExecution
    cappedDetailedGameAfterKeygenWithBothTraces
  simp only [map_bind, map_pure]
  apply bind_congr
  intro handled
  rw [sourceSigningTracedVerifierImpl_run_eq]
  simp [sourceGlobalExactExecutionResult, sourceExactSigningProjection,
    map_eq_bind_pure_comp]

theorem sourceGlobalExactTracedProgram_eq_trajectoryBothTraces
    (adversary : Adversary) :
    sourceGlobalExactProgramResult <$>
        sourceGlobalExactTracedProgram adversary = (do
      let keyView ← trajectoryProgrammedGlobalChainKeygen
      let execution ← cappedDetailedGameAfterKeygenWithBothTraces adversary
        keyView.publicKey
        (Concrete.materializePrecomputation keyView.cache keyView.secretKey)
        keyView.cache
      pure (Concrete.materializeCachedKeyResult keyView.keyResult,
        execution)) := by
  unfold sourceGlobalExactTracedProgram
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro keyView
  rw [← sourceGlobalExactTracedDetailedExecution_eq_bothTraces]
  simp [sourceGlobalExactProgramResult, map_eq_bind_pure_comp]

theorem evalDist_sourceGlobalExact_eq_cappedBothTraces
    (adversary : Adversary) :
    evalDist (sourceGlobalExactProgramResult <$>
        sourceGlobalExactTracedProgram adversary) =
      evalDist (cappedDetailedGameWithKeygenCacheAndBothTraces adversary) := by
  rw [sourceGlobalExactTracedProgram_eq_trajectoryBothTraces]
  unfold cappedDetailedGameWithKeygenCacheAndBothTraces
  rw [evalDist_bind, evalDist_bind]
  let project := fun view : ProgrammedGlobalChainKeygenView =>
    Concrete.materializeCachedKeyResult view.keyResult
  calc
    _ = evalDist (project <$> trajectoryProgrammedGlobalChainKeygen) >>=
        fun keyResult => evalDist
          ((fun execution => (keyResult, execution)) <$>
            cappedDetailedGameAfterKeygenWithBothTraces adversary
              keyResult.1.1 keyResult.1.2 keyResult.2) := by
      rw [evalDist_map, map_eq_bind_pure_comp, bind_assoc]
      simp [project, ProgrammedGlobalChainKeygenView.keyResult,
        Concrete.materializeCachedKeyResult]
    _ = evalDist ((simulateQ romImpl Concrete.scheme.keygen).run ∅) >>=
        fun keyResult => evalDist
          ((fun execution => (keyResult, execution)) <$>
            cappedDetailedGameAfterKeygenWithBothTraces adversary
              keyResult.1.1 keyResult.1.2 keyResult.2) := by
      rw [evalDist_materializedTrajectoryGlobalChainKeygen_eq_cappedKeygen]
    _ = _ := rfl

def SourceWinningExactFirstLaneEvent
    (result : SourceGlobalExactTracedProgramResult) : Prop :=
  WinningExactFirstLaneBadEventOccurs
    (cappedBothEncodingProjection (sourceGlobalExactProgramResult result))

theorem cappedExactFirstLane_probability_eq_sourceGlobalExact
    (adversary : Adversary) :
    Pr[WinningExactFirstLaneBadEventOccurs |
        cappedDetailedGameWithEncodingTrace adversary] =
      Pr[SourceWinningExactFirstLaneEvent |
        sourceGlobalExactTracedProgram adversary] := by
  calc
    _ = Pr[WinningExactFirstLaneBadEventOccurs ∘ cappedBothEncodingProjection |
        cappedDetailedGameWithKeygenCacheAndBothTraces adversary] := by
      rw [← probEvent_map]
      exact probEvent_congr' (fun _ _ => Iff.rfl)
        (congrArg evalDist
          (cappedDetailedGameWithKeygenCacheAndBothTraces_encodingProjection_eq
            adversary)).symm
    _ = Pr[WinningExactFirstLaneBadEventOccurs ∘ cappedBothEncodingProjection |
        sourceGlobalExactProgramResult <$>
          sourceGlobalExactTracedProgram adversary] :=
      probEvent_eq_of_evalDist_eq _
        (evalDist_sourceGlobalExact_eq_cappedBothTraces adversary).symm
    _ = _ := by
      rw [probEvent_map]
      rfl

theorem cappedExactEncodingBranch_implies_monitorHit
    (adversary : Adversary)
    (execution : CappedEncodingTraceExecution)
    (hmem : execution ∈ support
      (cappedDetailedGameWithEncodingTrace adversary))
    (hbranch : WinningOutcomeBadEventOccurs execution.2.1.1 execution.1
        .encoding ∧ ¬WinningEncodingPrehitOccurs execution) :
    CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
      execution.2.2 = true := by
  have hsigningMem : (execution.1, execution.2.1) ∈
      support (cappedDetailedGameWithSigningTrace adversary) := by
    rw [← cappedDetailedGameWithEncodingTrace_projection, support_map]
    exact ⟨execution, hmem, rfl⟩
  obtain ⟨entry, hentry, hprehit | hsigning | hpostSigning⟩ :=
    cappedWinning_encoding_event_trace_postSigning_decomposition adversary
      (execution.1, execution.2.1) hsigningMem hbranch.1
  · exact (hbranch.2 ⟨hbranch.1, entry, hentry, hprehit⟩).elim
  · exact cappedDetailedGameWithEncodingTrace_freshSigningCollision_monitorHit
      adversary execution hmem hbranch.1 ⟨entry, hentry, hsigning⟩
  · obtain ⟨encoding, hdecode⟩ := hbranch.1.forgery_decode
    exact
      cappedDetailedGameWithEncodingTrace_postSigningFreshForgedCollision_monitorHit
        adversary execution hmem hbranch.1 encoding hdecode
          ⟨entry, hentry, hpostSigning⟩

theorem cappedBothTraceGameResult_keyResult_mem_support
    (adversary : Adversary)
    (result : CappedBothTraceGameResult)
    (hresult : result ∈ support
      (cappedDetailedGameWithKeygenCacheAndBothTraces adversary)) :
    result.1 ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅) := by
  unfold cappedDetailedGameWithKeygenCacheAndBothTraces at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨keyResult, hkeyResult, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨execution, _hexecution, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact hkeyResult

theorem cappedBothTraceGameResult_cacheExecution_mem_support
    (adversary : Adversary)
    (result : CappedBothTraceGameResult)
    (hresult : result ∈ support
      (cappedDetailedGameWithKeygenCacheAndBothTraces adversary)) :
    (result.2.1, result.2.2.1.1.1) ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary result.1.1.1
          result.1.1.2)).run result.1.2) := by
  have hboth :=
    cappedDetailedGameWithKeygenCacheAndBothTraces_support_execution
      adversary result hresult
  have hencoding : (result.2.1, result.2.2.1) ∈ support
      (cappedDetailedGameAfterKeygenWithEncodingTrace adversary
        result.1.1.1 result.1.1.2 result.1.2) := by
    rw [← cappedDetailedGameAfterKeygenWithBothTraces_encodingProjection,
      support_map]
    exact ⟨result.2, hboth, rfl⟩
  have hsigning : (result.2.1, result.2.2.1.1) ∈ support
      (cappedDetailedGameAfterKeygenWithSigningTrace adversary
        result.1.1.1 result.1.1.2 result.1.2) := by
    rw [← cappedDetailedGameAfterKeygenWithEncodingTrace_projection,
      support_map]
    exact ⟨(result.2.1, result.2.2.1), hencoding, rfl⟩
  rw [← cappedDetailedGameAfterKeygenWithSigningTrace_cache_projection,
    support_map]
  exact ⟨(result.2.1, result.2.2.1.1), hsigning, rfl⟩

end XmssSecurity.CappedChain
