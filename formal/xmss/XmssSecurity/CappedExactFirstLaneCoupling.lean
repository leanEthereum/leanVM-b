import XmssSecurity.CappedExactFirstLaneSourceTrace
import XmssSecurity.CappedGlobalFirstLaneActionTrace

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

abbrev GlobalHighExactMonitoredState :=
  GlobalMonitoredTracedState × EncodingActionTrace

def sourceExactSigningProjection
    (state : SourceExactTracedState) : SourceSigningTracedState :=
  ((state.1.1.1, state.1.1.2), state.2)

def GlobalSigningExactMonitoredStateRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftState : SourceExactTracedState)
    (rightState : GlobalHighExactMonitoredState) : Prop :=
  GlobalSigningMonitoredTracedStateRelation left right
      (sourceExactSigningProjection leftState) rightState.1 ∧
    leftState.1.2 = rightState.2

noncomputable def globalHighExactMonitoredMappedAdversaryImpl
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalHighExactMonitoredState ProbComp) :=
  fun input => StateT.mk fun state => do
    let result ← (globalHighMonitoredMappedAdversaryImpl right input).run state.1
    let nextTrace := encodingActionTraceUpdate right.1.1.secretKey input
      (state.1.1.causal.cache, []) result.1
      (result.2.1.causal.cache, []) state.2
    pure (result.1, (result.2, nextTrace))

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

noncomputable def globalHighExactQueryResult
    (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : GlobalHighExactMonitoredState)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredTracedState) :
    (OracleWorld + SigningSpec).Range input × GlobalHighExactMonitoredState :=
  (result.1, (result.2,
    encodingActionTraceUpdate secretKey input
      (initialState.1.1.causal.cache, []) result.1
      (result.2.1.causal.cache, []) initialState.2))

theorem globalHighExactMonitoredMappedAdversaryImpl_query_eq_map
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : GlobalHighExactMonitoredState) :
    (globalHighExactMonitoredMappedAdversaryImpl right input).run
        initialState =
      globalHighExactQueryResult right.1.1.secretKey input initialState <$>
        (globalHighMonitoredMappedAdversaryImpl right input).run
          initialState.1 := by
  unfold globalHighExactMonitoredMappedAdversaryImpl
    globalHighExactQueryResult
  simp [StateT.run_mk, map_eq_bind_pure_comp]

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

theorem relTriple_programmed_globalHighExactMonitored_action
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftState : SourceExactTracedState)
    (rightState : GlobalHighExactMonitoredState)
    (hstate : GlobalSigningExactMonitoredStateRelation left right.1
      leftState rightState)
    (input : (OracleWorld + SigningSpec).Domain) :
    RelTriple
      ((cappedBothTracedMappedAdversaryImpl left.publicKey
        (Concrete.materializePrecomputation left.cache left.secretKey)
          input).run leftState)
      ((globalHighExactMonitoredMappedAdversaryImpl right input).run
        rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalSigningExactMonitoredStateRelation left right.1
            leftResult.2 rightResult.2) ∨ rightResult.2.1.1.bad) := by
  let leftSecret :=
    Concrete.materializePrecomputation left.cache left.secretKey
  have hbase := relTriple_programmed_globalHighMonitored_signingAction left
    right hrel hleftSupport hrightSupport
    (sourceExactSigningProjection leftState) rightState.1 hstate.1 input
  have hlifted : RelTriple
      (sourceExactQueryResult leftSecret input leftState <$>
        (sourceSigningTracedMappedAdversaryImpl left.publicKey leftSecret
          input).run (sourceExactSigningProjection leftState))
      (globalHighExactQueryResult right.1.1.secretKey input rightState <$>
        (globalHighMonitoredMappedAdversaryImpl right input).run rightState.1)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalSigningExactMonitoredStateRelation left right.1
            leftResult.2 rightResult.2) ∨ rightResult.2.1.1.bad) := by
    apply relTriple_map
    apply relTriple_post_mono hbase
    intro leftResult rightResult hresult
    rcases hresult with hgood | hbad
    · apply Or.inl
      refine ⟨hgood.1, hgood.2, ?_⟩
      obtain ⟨_monitorInitial, _hmonitorInitial, _hagreesInitial,
        _hrevealedInitial, hinitialCausal, _hretainedInitial⟩ :=
          hstate.1.1
      obtain ⟨_monitorFinal, _hmonitorFinal, _hagreesFinal,
        _hrevealedFinal, hfinalCausal, _hretainedFinal⟩ :=
          hgood.2.1
      have hinitial := hinitialCausal.1
      have hfinal := hfinalCausal.1
      have hcacheUpdate :=
        encodingActionTraceUpdate_eq_of_globalSigningCachesAgree
          leftSecret input leftState.1.1.1 rightState.1.1.causal.cache
          leftResult.2.1.1 rightResult.2.1.causal.cache
          (by simpa [leftSecret, Concrete.materializePrecomputation,
            Concrete.precomputedSecretKey, sourceSigningTracedStateProjection,
            sourceExactSigningProjection] using hinitial)
          (by simpa [leftSecret, Concrete.materializePrecomputation,
            Concrete.precomputedSecretKey, sourceSigningTracedStateProjection,
            sourceExactSigningProjection] using hfinal)
          leftResult.1 leftState.1.2
      have hparameter := programmedGlobal_secretKey_parameter_eq left right
        hrel hleftSupport hrightSupport
      have hsecretUpdate := encodingActionTraceUpdate_eq_of_parameter_eq
        leftSecret right.1.1.secretKey
        (by simpa [leftSecret, Concrete.materializePrecomputation,
          Concrete.precomputedSecretKey] using hparameter.symm)
        input rightState.1.1.causal.cache rightResult.2.1.causal.cache
        leftResult.1 leftState.1.2
      simpa [sourceExactQueryResult, globalHighExactQueryResult, hstate.2,
        hgood.1] using
        hcacheUpdate.trans hsecretUpdate
    · exact Or.inr hbad
  rw [cappedBothTracedMappedAdversaryImpl_query_eq_sourceExactMap,
    globalHighExactMonitoredMappedAdversaryImpl_query_eq_map]
  exact hlifted

theorem relTriple_programmed_globalHighExactMonitored_adversary
    (adversary : Adversary Concrete.scheme)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftState : SourceExactTracedState)
    (rightState : GlobalHighExactMonitoredState)
    (hstate : GlobalSigningExactMonitoredStateRelation left right.1
      leftState rightState) :
    RelTriple
      ((simulateQ
        (cappedBothTracedMappedAdversaryImpl left.publicKey
          (Concrete.materializePrecomputation left.cache left.secretKey))
          (adversary.main left.publicKey)).run leftState)
      ((simulateQ (globalHighExactMonitoredMappedAdversaryImpl right)
        (adversary.main left.publicKey)).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalSigningExactMonitoredStateRelation left right.1
            leftResult.2 rightResult.2) ∨ rightResult.2.1.1.bad) := by
  exact relTriple_simulateQ_run_until_bad_right
    (cappedBothTracedMappedAdversaryImpl left.publicKey
      (Concrete.materializePrecomputation left.cache left.secretKey))
    (globalHighExactMonitoredMappedAdversaryImpl right)
    (GlobalSigningExactMonitoredStateRelation left right.1)
    (fun state : GlobalHighExactMonitoredState => state.1.1.bad)
    (fun input leftState rightState hstate =>
      relTriple_programmed_globalHighExactMonitored_action left right hrel
        hleftSupport hrightSupport leftState rightState hstate input)
    (fun input state hbad result hresult => by
      unfold globalHighExactMonitoredMappedAdversaryImpl at hresult
      rw [StateT.run_mk, mem_support_bind_iff] at hresult
      obtain ⟨baseResult, hbase, hpure⟩ := hresult
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      exact globalHighMonitoredMappedAdversaryImpl_preserves_bad right input
        state.1 hbad baseResult hbase)
    (adversary.main left.publicKey) leftState rightState hstate

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
    (adversary : Adversary Concrete.scheme)
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

noncomputable def globalHighExactMonitoredDetailedExecution
    (adversary : Adversary Concrete.scheme)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    ProbComp ((Forgery × Bool) × GlobalHighExactMonitoredState) := do
  let initial : GlobalHighExactMonitoredState :=
    ((⟨globalFilteredCausalKeygenState right.1.1,
      some AdaptiveRevealMonitor.State.empty, []⟩, []), [])
  let handled ← (simulateQ
    (globalHighExactMonitoredMappedAdversaryImpl right)
      (adversary.main right.1.1.publicKey)).run initial
  let verified ← (simulateQ (globalHighMonitoredVerifierImpl right)
    (Concrete.scheme.verify right.1.1.publicKey handled.1.epoch
      handled.1.message handled.1.signature)).run handled.2.1
  let finalEncodingTrace := appendVerificationEncodingObservation
    right.1.1.secretKey handled.1 handled.2.1.1.causal.cache
      verified.2.1.causal.cache handled.2.2
  pure ((handled.1, verified.1), (verified.2, finalEncodingTrace))

theorem globalSigningExactMonitoredStateRelation_initial
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen) :
    GlobalSigningExactMonitoredStateRelation left right.1
      ((((left.cache, []), []), []))
      (((⟨globalFilteredCausalKeygenState right.1.1,
        some AdaptiveRevealMonitor.State.empty, []⟩, []), [])) := by
  constructor
  · exact globalSigningMonitoredTracedStateRelation_initial left right hrel
      hleftSupport hrightSupport
  · rfl

theorem relTriple_sourceGlobalExact_globalHighExactMonitored_detailedExecution
    (adversary : Adversary Concrete.scheme)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen) :
    RelTriple (sourceGlobalExactTracedDetailedExecution adversary left)
      (globalHighExactMonitoredDetailedExecution adversary right)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalSigningExactMonitoredStateRelation left right.1
            leftResult.2 rightResult.2) ∨ rightResult.2.1.1.bad) := by
  have hinitial := globalSigningExactMonitoredStateRelation_initial left right
    hrel hleftSupport hrightSupport
  have hpublicKey : left.publicKey = right.1.1.publicKey :=
    hrel.1.toStable.1.2.1
  unfold sourceGlobalExactTracedDetailedExecution
    globalHighExactMonitoredDetailedExecution
  simp only
  rw [← hpublicKey]
  apply relTriple_bind
    (relTriple_programmed_globalHighExactMonitored_adversary adversary left
      right hrel hleftSupport hrightSupport ((((left.cache, []), []), []))
      (((⟨globalFilteredCausalKeygenState right.1.1,
        some AdaptiveRevealMonitor.State.empty, []⟩, []), [])) hinitial)
  intro leftHandled rightHandled hhandled
  rcases hhandled with hgood | hbad
  · obtain ⟨hforgery, hstates⟩ := hgood
    rw [← hforgery]
    apply relTriple_bind
      (relTriple_programmed_globalHighMonitored_signingVerifier left right hrel
        hleftSupport hrightSupport
        (Concrete.scheme.verify left.publicKey leftHandled.1.epoch
          leftHandled.1.message leftHandled.1.signature)
        (sourceExactSigningProjection leftHandled.2) rightHandled.2.1
          hstates.1)
    intro leftVerified rightVerified hvertified
    apply relTriple_pure_pure
    rcases hvertified with hverifiedGood | hverifiedBad
    · apply Or.inl
      refine ⟨congrArg (Prod.mk leftHandled.1) hverifiedGood.1,
        hverifiedGood.2, ?_⟩
      obtain ⟨_monitorInitial, _hmonitorInitial, _hagreesInitial,
        _hrevealedInitial, hinitialCausal, _hretainedInitial⟩ :=
          hstates.1.1
      obtain ⟨_monitorFinal, _hmonitorFinal, _hagreesFinal,
        _hrevealedFinal, hfinalCausal, _hretainedFinal⟩ :=
          hverifiedGood.2.1
      have hinitialCaches := hinitialCausal.1
      have hfinalCaches := hfinalCausal.1
      let leftSecret :=
        Concrete.materializePrecomputation left.cache left.secretKey
      have hparameter := programmedGlobal_secretKey_parameter_eq left right
        hrel hleftSupport hrightSupport
      have happend :=
        appendVerificationEncodingObservation_eq_of_globalSigningCachesAgree
          leftSecret right.1.1.secretKey
          (by simpa [leftSecret, Concrete.materializePrecomputation,
            Concrete.precomputedSecretKey] using hparameter.symm)
          leftHandled.1 leftHandled.2.1.1.1
          rightHandled.2.1.1.causal.cache leftVerified.2.1.1
          rightVerified.2.1.causal.cache
          (by simpa [leftSecret, Concrete.materializePrecomputation,
            Concrete.precomputedSecretKey, sourceSigningTracedStateProjection,
            sourceExactSigningProjection] using hinitialCaches)
          (by simpa [leftSecret, Concrete.materializePrecomputation,
            Concrete.precomputedSecretKey, sourceSigningTracedStateProjection,
            sourceExactSigningProjection] using hfinalCaches)
          leftHandled.2.1.2
      simpa [hstates.2] using happend
    · exact Or.inr hverifiedBad
  · apply relTriple_bind
      (relTriple_prod (fun _result _hresult => True.intro)
        (fun rightResult hrightResult =>
          OracleComp.simulateQ_run_preservesInv
            (globalHighMonitoredVerifierImpl right)
            (fun state : GlobalMonitoredTracedState => state.1.bad)
            (globalHighMonitoredVerifierImpl_preserves_bad right)
            (Concrete.scheme.verify left.publicKey rightHandled.1.epoch
              rightHandled.1.message rightHandled.1.signature)
            rightHandled.2.1 hbad rightResult hrightResult))
    intro leftVerified rightVerified hvertified
    apply relTriple_pure_pure
    exact Or.inr hvertified.2

def sourceGlobalExactErasedExecution
    (result : (Forgery × Bool) × SourceExactTracedState) :
    (Forgery × Bool) × SourceTracedState :=
  (result.1, (result.2.1.1.1, result.2.2))

abbrev SourceGlobalExactTracedProgramResult :=
  ProgrammedGlobalChainKeygenView ×
    ((Forgery × Bool) × SourceExactTracedState)

noncomputable def sourceGlobalExactTracedProgram
    (adversary : Adversary Concrete.scheme) :
    ProbComp SourceGlobalExactTracedProgramResult := do
  let keyView ← trajectoryProgrammedGlobalChainKeygen
  let execution ← sourceGlobalExactTracedDetailedExecution adversary keyView
  pure (keyView, execution)

abbrev GlobalHighExactMonitoredProgramResult :=
  (((ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) ×
    ((Forgery × Bool) × GlobalHighExactMonitoredState))

def sourceGlobalExactErasedResult
    (result : SourceGlobalExactTracedProgramResult) :
    SourceGlobalTracedProgramResult :=
  (result.1, sourceGlobalExactErasedExecution result.2)

def globalHighExactErasedResult
    (result : GlobalHighExactMonitoredProgramResult) :
    GlobalHighMonitoredProgramResult :=
  (result.1, (result.2.1, result.2.2.1))

noncomputable def globalHighExactMonitoredProgram
    (adversary : Adversary Concrete.scheme) :
    ProbComp GlobalHighExactMonitoredProgramResult := do
  let keyResult ← coupledGlobalChainKeygenWithBaseHighFull
  let execution ← globalHighExactMonitoredDetailedExecution adversary keyResult
  pure (keyResult, execution)

theorem globalHighExactMonitoredMappedAdversaryImpl_run_projection
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : GlobalHighExactMonitoredState) :
    (fun result => (result.1, result.2.1)) <$>
        (simulateQ (globalHighExactMonitoredMappedAdversaryImpl right)
          computation).run initialState =
      (simulateQ (globalHighMonitoredMappedAdversaryImpl right)
        computation).run initialState.1 := by
  induction computation using OracleComp.inductionOn generalizing
      initialState with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, StateT.run_bind, map_bind]
      simp only [id_map]
      simp_rw [ih]
      rw [globalHighExactMonitoredMappedAdversaryImpl_query_eq_map]
      simp [globalHighExactQueryResult, Functor.map_map]

theorem globalHighExactMonitoredDetailedExecution_projection
    (adversary : Adversary Concrete.scheme)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    (fun result => (result.1, result.2.1)) <$>
        globalHighExactMonitoredDetailedExecution adversary right =
      globalHighMonitoredDetailedExecution adversary right := by
  unfold globalHighExactMonitoredDetailedExecution
    globalHighMonitoredDetailedExecution
  simp only [map_bind, map_pure]
  let initial : GlobalHighExactMonitoredState :=
    ((⟨globalFilteredCausalKeygenState right.1.1,
      some AdaptiveRevealMonitor.State.empty, []⟩, []), [])
  let tail := fun handled : Forgery × GlobalMonitoredTracedState => do
    let verified ← (simulateQ (globalHighMonitoredVerifierImpl right)
      (Concrete.scheme.verify right.1.1.publicKey handled.1.epoch
        handled.1.message handled.1.signature)).run handled.2
    pure ((handled.1, verified.1), verified.2)
  change (do
    let handled ← (simulateQ
      (globalHighExactMonitoredMappedAdversaryImpl right)
      (adversary.main right.1.1.publicKey)).run initial
    tail (handled.1, handled.2.1)) = _
  rw [← bind_map_left,
    globalHighExactMonitoredMappedAdversaryImpl_run_projection]

theorem sourceGlobalExactTracedDetailedExecution_projection
    (adversary : Adversary Concrete.scheme)
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
    Prod.map] using hbound

theorem sourceGlobalExactTracedProgram_projection
    (adversary : Adversary Concrete.scheme) :
    sourceGlobalExactErasedResult <$>
        sourceGlobalExactTracedProgram adversary =
      sourceGlobalTracedProgram adversary := by
  unfold sourceGlobalExactTracedProgram sourceGlobalTracedProgram
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro keyView
  rw [← sourceGlobalExactTracedDetailedExecution_projection]
  simp [sourceGlobalExactErasedResult, map_eq_bind_pure_comp]

theorem globalHighExactMonitoredProgram_projection
    (adversary : Adversary Concrete.scheme) :
    globalHighExactErasedResult <$>
        globalHighExactMonitoredProgram adversary =
      globalHighMonitoredProgram adversary := by
  unfold globalHighExactMonitoredProgram globalHighMonitoredProgram
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro right
  rw [← globalHighExactMonitoredDetailedExecution_projection]
  simp [globalHighExactErasedResult, map_eq_bind_pure_comp]

def SourceGlobalExactHighMonitoredProgramRelation
    (left : SourceGlobalExactTracedProgramResult)
    (right : GlobalHighExactMonitoredProgramResult) : Prop :=
  ProgrammedGlobalChainKeygenBaseHighStableRelation left.1 right.1 ∧
    ((left.2.1 = right.2.1 ∧
      GlobalSigningExactMonitoredStateRelation left.1 right.1.1 left.2.2
        right.2.2) ∨ right.2.2.1.1.bad) ∧
    right.2.2.1.1.TraceConsistent right.1.1.2

theorem sourceGlobalExactHighMonitoredProgramRelation_projection
    {left : SourceGlobalExactTracedProgramResult}
    {right : GlobalHighExactMonitoredProgramResult}
    (hrel : SourceGlobalExactHighMonitoredProgramRelation left right) :
    SourceGlobalHighMonitoredProgramRelation
      (sourceGlobalExactErasedResult left)
      (globalHighExactErasedResult right) := by
  refine ⟨hrel.1, ?_, hrel.2.2⟩
  rcases hrel.2.1 with hgood | hbad
  · apply Or.inl
    refine ⟨hgood.1, ?_⟩
    simpa [sourceGlobalExactErasedResult, globalHighExactErasedResult,
      sourceGlobalExactErasedExecution,
      GlobalSigningExactMonitoredStateRelation,
      GlobalSigningMonitoredTracedStateRelation,
      sourceExactSigningProjection, sourceSigningTracedStateProjection]
      using hgood.2.1
  · exact Or.inr hbad

theorem sourceGlobalExactErasedResult_mem_support
    (adversary : Adversary Concrete.scheme)
    {left : SourceGlobalExactTracedProgramResult}
    (hleft : left ∈ support (sourceGlobalExactTracedProgram adversary)) :
    sourceGlobalExactErasedResult left ∈
      support (sourceGlobalTracedProgram adversary) := by
  rw [← sourceGlobalExactTracedProgram_projection, support_map]
  exact ⟨left, hleft, rfl⟩

theorem globalHighExactErasedResult_mem_support
    (adversary : Adversary Concrete.scheme)
    {right : GlobalHighExactMonitoredProgramResult}
    (hright : right ∈ support (globalHighExactMonitoredProgram adversary)) :
    globalHighExactErasedResult right ∈
      support (globalHighMonitoredProgram adversary) := by
  rw [← globalHighExactMonitoredProgram_projection, support_map]
  exact ⟨right, hright, rfl⟩

theorem relTriple_sourceGlobalExact_globalHighExactMonitored_program
    (adversary : Adversary Concrete.scheme) :
    RelTriple (sourceGlobalExactTracedProgram adversary)
      (globalHighExactMonitoredProgram adversary)
      SourceGlobalExactHighMonitoredProgramRelation := by
  unfold sourceGlobalExactTracedProgram globalHighExactMonitoredProgram
  apply relTriple_bind
    (relTriple_with_support
      relTriple_trajectoryProgrammedGlobalChainKeygen_withBaseHigh_stable)
  intro left right hkeygen
  obtain ⟨hrel, hleftSupport, hrightSupport⟩ := hkeygen
  have hrightViewSupport :=
    coupledGlobalChainKeygenWithBaseHighFull_support_keyView right
      hrightSupport
  apply relTriple_bind
    (relTriple_with_support
      (relTriple_sourceGlobalExact_globalHighExactMonitored_detailedExecution
        adversary left right hrel hleftSupport hrightViewSupport))
  intro leftExecution rightExecution hexecution
  apply relTriple_pure_pure
  have hrightExecution : (rightExecution.1, rightExecution.2.1) ∈
      support (globalHighMonitoredDetailedExecution adversary right) := by
    rw [← globalHighExactMonitoredDetailedExecution_projection,
      support_map]
    exact ⟨rightExecution, hexecution.2.2, rfl⟩
  exact ⟨hrel, hexecution.1,
    globalHighMonitoredDetailedExecution_traceConsistent adversary right
      (rightExecution.1, rightExecution.2.1) hrightExecution⟩

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
    (adversary : Adversary Concrete.scheme)
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
    Functor.map_map, map_eq_bind_pure_comp]

theorem sourceGlobalExactTracedProgram_eq_trajectoryBothTraces
    (adversary : Adversary Concrete.scheme) :
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
    (adversary : Adversary Concrete.scheme) :
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
    _ = evalDist ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅) >>=
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
    (adversary : Adversary Concrete.scheme) :
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
    (adversary : Adversary Concrete.scheme)
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
    (adversary : Adversary Concrete.scheme)
    (result : CappedBothTraceGameResult)
    (hresult : result ∈ support
      (cappedDetailedGameWithKeygenCacheAndBothTraces adversary)) :
    result.1 ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅) := by
  unfold cappedDetailedGameWithKeygenCacheAndBothTraces at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨keyResult, hkeyResult, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨execution, _hexecution, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact hkeyResult

theorem cappedBothTraceGameResult_cacheExecution_mem_support
    (adversary : Adversary Concrete.scheme)
    (result : CappedBothTraceGameResult)
    (hresult : result ∈ support
      (cappedDetailedGameWithKeygenCacheAndBothTraces adversary)) :
    (result.2.1, result.2.2.1.1.1) ∈ support
      ((simulateQ xmssRomImpl
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

def GlobalHighExactFirstLaneEvent
    (result : GlobalHighExactMonitoredProgramResult) : Prop :=
  (SigningTranscript.Valid result.2.2.1.2.toSigningLog ∧
    CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
      result.2.2.2 = true) ∨
    RevealProbeOracleSimulation.ObservedHit
      (globalHighMonitoredPublicProjection
        (globalHighExactErasedResult result))

set_option maxRecDepth 1000000 in
theorem sourceWinningExactFirstLane_implies_globalHighExact
    (adversary : Adversary Concrete.scheme)
    (left : SourceGlobalExactTracedProgramResult)
    (right : GlobalHighExactMonitoredProgramResult)
    (hleftSupport : left ∈ support
      (sourceGlobalExactTracedProgram adversary))
    (hrightSupport : right ∈ support
      (globalHighExactMonitoredProgram adversary))
    (hrel : SourceGlobalExactHighMonitoredProgramRelation left right)
    (hevent : SourceWinningExactFirstLaneEvent left) :
    GlobalHighExactFirstLaneEvent right := by
  let both := sourceGlobalExactProgramResult left
  have hbothMapped : both ∈ support
      (sourceGlobalExactProgramResult <$>
        sourceGlobalExactTracedProgram adversary) := by
    rw [support_map]
    exact ⟨left, hleftSupport, rfl⟩
  have hboth : both ∈ support
      (cappedDetailedGameWithKeygenCacheAndBothTraces adversary) :=
    (mem_support_iff_of_evalDist_eq
      (evalDist_sourceGlobalExact_eq_cappedBothTraces adversary) both).mp
        hbothMapped
  have hencodingSupport : cappedBothEncodingProjection both ∈ support
      (cappedDetailedGameWithEncodingTrace adversary) := by
    rw [← cappedDetailedGameWithKeygenCacheAndBothTraces_encodingProjection_eq,
      support_map]
    exact ⟨both, hboth, rfl⟩
  unfold SourceWinningExactFirstLaneEvent at hevent
  unfold WinningExactFirstLaneBadEventOccurs at hevent
  rcases hevent with hencoding | hchain
  · have hhit := cappedExactEncodingBranch_implies_monitorHit adversary
      (cappedBothEncodingProjection both) hencodingSupport hencoding
    rcases hrel.2.1 with hgood | hbad
    · apply Or.inl
      constructor
      · have hbothExecution :=
          cappedDetailedGameWithKeygenCacheAndBothTraces_support_execution
            adversary both hboth
        have hlogs := cappedDetailedGameAfterKeygenWithBothTraces_logs_eq
          adversary both.1.1.1 both.1.1.2 both.1.2 both.2 hbothExecution
        have hvalidBoth : SigningTranscript.Valid
            both.2.2.2.toSigningLog := by
          rw [← hlogs]
          exact hencoding.1.signingTranscript_valid
        have hvalidLeft : SigningTranscript.Valid
            left.2.2.2.toSigningLog := by
          simpa [both, sourceGlobalExactProgramResult,
            sourceGlobalExactExecutionResult] using hvalidBoth
        have htraceEq : left.2.2.2 = right.2.2.1.2 := by
          simpa [GlobalSigningExactMonitoredStateRelation,
            GlobalSigningMonitoredTracedStateRelation,
            GlobalMonitoredTracedStateRelation, sourceExactSigningProjection,
            sourceSigningTracedStateProjection] using hgood.2.1.2
        rw [← htraceEq]
        exact hvalidLeft
      · rw [← hgood.2.2]
        simpa [both, cappedBothEncodingProjection,
          sourceGlobalExactProgramResult, sourceGlobalExactExecutionResult]
          using hhit
    · apply Or.inr
      unfold RevealProbeOracleSimulation.ObservedHit
      dsimp only [globalHighMonitoredPublicProjection,
        globalHighExactErasedResult]
      apply RevealProbeOracleSimulation.runObserved_append_eq_true_of_prefix
      exact right.2.2.1.1.bad_implies_runObserved right.1.1.2 hrel.2.2 hbad
  · obtain ⟨chain, hwinning, hrevealed⟩ := hchain
    have hkeygen := cappedBothTraceGameResult_keyResult_mem_support
      adversary both hboth
    have hafter := cappedBothTraceGameResult_cacheExecution_mem_support
      adversary both hboth
    have horiginChain := chainValueRevealed_afterKeygen_has_origin adversary
      both.1 hkeygen (both.2.1, both.2.2.1.1.1) hafter chain hrevealed
    let leftOld := sourceGlobalExactErasedResult left
    let rightOld := globalHighExactErasedResult right
    have hleftOld : leftOld ∈ support
        (sourceGlobalTracedProgram adversary) :=
      sourceGlobalExactErasedResult_mem_support adversary hleftSupport
    have hrightOld : rightOld ∈ support
        (globalHighMonitoredProgram adversary) :=
      globalHighExactErasedResult_mem_support adversary hrightSupport
    have hrelOld : SourceGlobalHighMonitoredProgramRelation leftOld rightOld :=
      sourceGlobalExactHighMonitoredProgramRelation_projection hrel
    have houtcome :=
      cappedDetailedGameWithKeygenCacheAndBothTraces_outcome_eq
        adversary both hboth
    have hwinningAction : WinningOutcomeBadEventOccurs
        (cappedBothActionProjection both).1.2.2
        (cappedBothActionProjection both).1.2.1 (.chain chain) := by
      rw [← houtcome]
      exact hwinning
    have horiginAction : OutcomeChainValueHasKeygenOrigin
        both.1.2 (cappedBothActionProjection both).1.2.2
        both.1.1.2 (cappedBothActionProjection both).1.2.1 chain := by
      rw [← houtcome]
      exact horiginChain
    have horiginOld : GlobalWinningOutcomeChainValueHasKeygenOrigin
        (eraseGlobalChainKeygenView (sourceGlobalProgramResult leftOld)).1.1.2
        (eraseGlobalChainKeygenView (sourceGlobalProgramResult leftOld)).1.2.2
        (eraseGlobalChainKeygenView (sourceGlobalProgramResult leftOld)).1.1.1.2
        (eraseGlobalChainKeygenView (sourceGlobalProgramResult leftOld)).1.2.1 := by
      refine ⟨chain, ?_, ?_⟩
      · simpa [leftOld, both, sourceGlobalExactErasedResult,
          sourceGlobalExactErasedExecution, sourceGlobalProgramResult,
          sourceGlobalExecutionResult, eraseGlobalChainKeygenView,
          cappedBothActionProjection, sourceGlobalExactProgramResult,
          sourceGlobalExactExecutionResult,
          ProgrammedGlobalChainKeygenView.keyResult,
          Concrete.materializeCachedKeyResult, Prod.eta] using hwinningAction
      · simpa [leftOld, both, sourceGlobalExactErasedResult,
          sourceGlobalExactErasedExecution, sourceGlobalProgramResult,
          sourceGlobalExecutionResult, eraseGlobalChainKeygenView,
          cappedBothActionProjection, sourceGlobalExactProgramResult,
          sourceGlobalExactExecutionResult,
          ProgrammedGlobalChainKeygenView.keyResult,
          Concrete.materializeCachedKeyResult, Prod.eta]
          using horiginAction
    apply Or.inr
    exact sourceGlobal_origin_implies_right_publicObservedHit adversary
      leftOld rightOld hleftOld hrightOld hrelOld horiginOld

theorem sourceWinningExactFirstLane_probability_le_globalHighExact
    (adversary : Adversary Concrete.scheme) :
    Pr[SourceWinningExactFirstLaneEvent |
        sourceGlobalExactTracedProgram adversary] ≤
      Pr[GlobalHighExactFirstLaneEvent |
        globalHighExactMonitoredProgram adversary] := by
  apply probEvent_le_of_relTriple
    (relTriple_with_support
      (relTriple_sourceGlobalExact_globalHighExactMonitored_program adversary))
  intro left right hrel hevent
  exact sourceWinningExactFirstLane_implies_globalHighExact adversary
    left right hrel.2.1 hrel.2.2 hrel.1 hevent

end XmssSecurity.CappedChain
