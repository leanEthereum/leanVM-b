import XmssSecurity.Proof.CappedExactFirstLaneCoupling
import XmssSecurity.Proof.CappedGlobalFirstLaneBounds
import XmssSecurity.Proof.CappedGlobalFirstLaneTrace
import XmssSecurity.Proof.StateLens
import XmssSecurity.Proof.EagerTraceInvariant

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option linter.constructorNameAsVariable false

structure GlobalExactTracedState where
  causalState : GlobalCausalHashState
  attackerTrace : AttackerActionTrace
  encodingTrace : EncodingActionTrace

@[simp] def GlobalExactTracedState.initial (causalState : GlobalCausalHashState) :
    GlobalExactTracedState :=
  ⟨causalState, [], []⟩

@[simp] def GlobalExactTracedState.withCausalState (state : GlobalExactTracedState)
    (causalState : GlobalCausalHashState) : GlobalExactTracedState :=
  { state with causalState }

def globalHighExactStateProjection
    (state : GlobalHighExactMonitoredState) : GlobalExactTracedState :=
  ⟨state.1.1.causal, state.1.2, state.2⟩

def globalExactTracedCausalLens :
    StateLens GlobalExactTracedState GlobalCausalHashState where
  get := GlobalExactTracedState.causalState
  set := GlobalExactTracedState.withCausalState
  set_get state := by cases state; rfl
  get_set state nextCausal := by cases state; rfl
  set_set state left right := by cases state; rfl

@[irreducible]
noncomputable def globalExactTracedNextState
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalExactTracedState)
    (output : (OracleWorld + SigningSpec).Range input)
    (causalState : GlobalCausalHashState) : GlobalExactTracedState :=
  GlobalExactTracedState.mk causalState
    (state.attackerTrace ++ attackerActionFragment input output)
    (encodingActionTraceUpdate keyView.secretKey input
      (state.causalState.cache, []) output (causalState.cache, [])
        state.encodingTrace)

theorem globalExactTracedNextState_encodingTrace
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalExactTracedState)
    (output : (OracleWorld + SigningSpec).Range input)
    (causalState : GlobalCausalHashState) :
    (globalExactTracedNextState keyView input state output causalState
      ).encodingTrace =
      encodingActionTraceUpdate keyView.secretKey input
        (state.causalState.cache, []) output (causalState.cache, [])
          state.encodingTrace := by
  unfold globalExactTracedNextState
  rfl

noncomputable def globalExactTracedLift {ι : Type} {world : OracleSpec ι}
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (base : StateT GlobalCausalHashState
      (OracleComp world)
      ((OracleWorld + SigningSpec).Range input)) :
    StateT GlobalExactTracedState
      (OracleComp world)
      ((OracleWorld + SigningSpec).Range input) :=
  StateT.mk fun state =>
    (fun result => (result.1,
      globalExactTracedNextState keyView input state result.1 result.2)) <$>
      base.run state.causalState

noncomputable def globalHighDirectExactTracedSigningImpl
    (keyView : ProgrammedGlobalChainKeygenView) : QueryImpl SigningSpec
      (StateT GlobalExactTracedState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  fun request => globalExactTracedLift keyView (.inr request)
    (globalHighDirectSigningImpl keyView request)

noncomputable def globalHighDirectExactTracedOracleImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) : QueryImpl OracleWorld
      (StateT GlobalExactTracedState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  fun input => globalExactTracedLift keyView (.inl input)
    (StateT.mk fun state =>
      globalHighDirectOracleExecution keyView edgeHigh input state)

noncomputable def globalHighDirectExactTracedMappedAdversaryImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalExactTracedState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  globalHighDirectExactTracedOracleImpl keyView edgeHigh +
    globalHighDirectExactTracedSigningImpl keyView

noncomputable def globalFirstLaneExactTracedSigningImpl
    (keyView : ProgrammedGlobalChainKeygenView) : QueryImpl SigningSpec
      (StateT GlobalExactTracedState
        (OracleComp GlobalFirstLaneWorld)) :=
  fun request => globalExactTracedLift keyView (.inr request)
    (globalFirstLaneSigningImpl keyView request)

noncomputable def globalFirstLaneExactTracedOracleImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) : QueryImpl OracleWorld
      (StateT GlobalExactTracedState
        (OracleComp GlobalFirstLaneWorld)) :=
  fun input => globalExactTracedLift keyView (.inl input)
    (StateT.mk fun state =>
      globalFirstLaneOracleExecution keyView edgeHigh input state)

noncomputable def globalFirstLaneExactTracedMappedAdversaryImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalExactTracedState
        (OracleComp GlobalFirstLaneWorld)) :=
  globalFirstLaneExactTracedOracleImpl keyView edgeHigh +
    globalFirstLaneExactTracedSigningImpl keyView

noncomputable def globalHighDirectExactTracedVerifierImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl OracleWorld
      (StateT GlobalExactTracedState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  fun input => StateT.mk fun state =>
    (fun result => (result.1, state.withCausalState result.2)) <$>
      (globalHighDirectVerifierImpl keyView edgeHigh input).run
        state.causalState

noncomputable def globalFirstLaneExactTracedVerifierImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl OracleWorld
      (StateT GlobalExactTracedState
        (OracleComp GlobalFirstLaneWorld)) :=
  fun input => StateT.mk fun state =>
    (fun result => (result.1, state.withCausalState result.2)) <$>
      (globalFirstLaneVerifierImpl keyView edgeHigh input).run
        state.causalState

noncomputable def globalHighDirectExactTracedDetailedExecution
    (adversary : Adversary)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    StateT GlobalExactTracedState
      (OracleComp
        (RevealProbeOracleSimulation.World GlobalChainValueIndex))
      (Forgery × Bool) := StateT.mk fun initial => do
  let handled ← (simulateQ
    (globalHighDirectExactTracedMappedAdversaryImpl keyView edgeHigh)
      (adversary.main keyView.publicKey)).run initial
  let verified ← (simulateQ
    (globalHighDirectExactTracedVerifierImpl keyView edgeHigh)
      (Concrete.scheme.verify keyView.publicKey handled.1.epoch
        handled.1.message handled.1.signature)).run handled.2
  let finalTrace := appendVerificationEncodingObservation keyView.secretKey
    handled.1 handled.2.causalState.cache verified.2.causalState.cache
      verified.2.encodingTrace
  pure ((handled.1, verified.1),
    { verified.2 with encodingTrace := finalTrace })

noncomputable def globalFirstLaneExactTracedDetailedExecution
    (adversary : Adversary)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    StateT GlobalExactTracedState
      (OracleComp GlobalFirstLaneWorld) (Forgery × Bool) :=
  StateT.mk fun initial => do
    let handled ← (simulateQ
      (globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh)
        (adversary.main keyView.publicKey)).run initial
    let verified ← (simulateQ
      (globalFirstLaneExactTracedVerifierImpl keyView edgeHigh)
        (Concrete.scheme.verify keyView.publicKey handled.1.epoch
          handled.1.message handled.1.signature)).run handled.2
    let finalTrace := appendVerificationEncodingObservation keyView.secretKey
      handled.1 handled.2.causalState.cache verified.2.causalState.cache
        verified.2.encodingTrace
    pure ((handled.1, verified.1),
      { verified.2 with encodingTrace := finalTrace })

abbrev GlobalExactTracedResult :=
  GlobalHighDirectKeyResult ×
    ((Forgery × Bool) × GlobalExactTracedState)

noncomputable def globalFirstLaneExactTracedProgram
    (adversary : Adversary) :
    OracleComp GlobalFirstLaneWorld GlobalExactTracedResult := do
  let keyResult ← FirstLaneOracleSimulation.liftProbComp
    globalHighDirectKeygen
  let execution ← (globalFirstLaneExactTracedDetailedExecution adversary
    keyResult.1 keyResult.2).run
      (GlobalExactTracedState.initial
        (globalFilteredCausalKeygenState keyResult.1))
  pure (keyResult, execution)

theorem globalFirstLaneErase_exactTracedLift
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (sourceBase : StateT GlobalCausalHashState
      (OracleComp GlobalFirstLaneWorld)
      ((OracleWorld + SigningSpec).Range input))
    (targetBase : StateT GlobalCausalHashState
      (OracleComp
        (RevealProbeOracleSimulation.World GlobalChainValueIndex))
      ((OracleWorld + SigningSpec).Range input))
    (state : GlobalExactTracedState)
    (hbase : GlobalFirstLaneErases
      (sourceBase.run state.causalState)
      (targetBase.run state.causalState)) :
    GlobalFirstLaneErases
      ((globalExactTracedLift keyView input sourceBase).run state)
      ((globalExactTracedLift keyView input targetBase).run state) := by
  unfold globalExactTracedLift
  simp only [StateT.run_mk]
  apply hbase.bind
  intro result
  exact GlobalFirstLaneErases.pure _

theorem globalFirstLaneErase_exactTracedSigningImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest)
    (state : GlobalExactTracedState) :
    GlobalFirstLaneErases
      ((globalFirstLaneExactTracedSigningImpl keyView request).run state)
      ((globalHighDirectExactTracedSigningImpl keyView request).run state) := by
  exact globalFirstLaneErase_exactTracedLift keyView (.inr request)
    (globalFirstLaneSigningImpl keyView request)
    (globalHighDirectSigningImpl keyView request) state
      (globalFirstLaneErase_directSigningImpl keyView request
        state.causalState)

theorem globalFirstLaneErase_exactTracedMappedAdversaryImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalExactTracedState) :
    GlobalFirstLaneErases
      ((globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh input
        ).run state)
      ((globalHighDirectExactTracedMappedAdversaryImpl keyView edgeHigh input
        ).run state) := by
  unfold globalFirstLaneExactTracedMappedAdversaryImpl
    globalHighDirectExactTracedMappedAdversaryImpl
  apply globalFirstLaneErases_add
  · intro worldInput worldState
    exact globalFirstLaneErase_exactTracedLift keyView (.inl worldInput)
      (StateT.mk fun state =>
        globalFirstLaneOracleExecution keyView edgeHigh worldInput state)
      (StateT.mk fun state =>
        globalHighDirectOracleExecution keyView edgeHigh worldInput state)
      worldState
        (globalFirstLaneOracleErasure keyView edgeHigh worldInput
          worldState.causalState)
  · exact globalFirstLaneErase_exactTracedSigningImpl keyView

theorem globalFirstLaneErase_exactTracedVerifierImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : OracleWorld.Domain)
    (state : GlobalExactTracedState) :
    GlobalFirstLaneErases
      ((globalFirstLaneExactTracedVerifierImpl keyView edgeHigh input).run
        state)
      ((globalHighDirectExactTracedVerifierImpl keyView edgeHigh input).run
        state) := by
  unfold globalFirstLaneExactTracedVerifierImpl
    globalHighDirectExactTracedVerifierImpl
  simp only [StateT.run_mk]
  apply (globalFirstLaneOracleErasure keyView edgeHigh input
    state.causalState).bind
  intro result
  exact GlobalFirstLaneErases.pure _

theorem globalFirstLaneErase_exactTracedDetailedExecution
    (adversary : Adversary)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (state : GlobalExactTracedState) :
    GlobalFirstLaneErases
      ((globalFirstLaneExactTracedDetailedExecution adversary keyView edgeHigh
        ).run state)
      ((globalHighDirectExactTracedDetailedExecution adversary keyView
        edgeHigh).run state) := by
  unfold globalFirstLaneExactTracedDetailedExecution
    globalHighDirectExactTracedDetailedExecution
  simp only [StateT.run_mk]
  apply (globalFirstLaneErases_simulateQ_run _ _
    (globalFirstLaneErase_exactTracedMappedAdversaryImpl keyView edgeHigh)
    (adversary.main keyView.publicKey) state).bind
  intro handled
  apply (globalFirstLaneErases_simulateQ_run _ _
    (globalFirstLaneErase_exactTracedVerifierImpl keyView edgeHigh)
    (Concrete.scheme.verify keyView.publicKey handled.1.epoch
      handled.1.message handled.1.signature) handled.2).bind
  intro verified
  exact GlobalFirstLaneErases.pure _

noncomputable def firstLaneValidEncodingActions
    (trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) :
    EncodingActionTrace :=
  CappedEncodingMonitor.validActions trace.encodingActions

theorem encodingActionTraceUpdate_sign_some
    (secretKey : SecretKey) (request : SignRequest)
    (signature : Signature)
    (initialCache finalCache : QueryCache HashSpec)
    (trace : EncodingActionTrace) :
    encodingActionTraceUpdate secretKey
        (.inr request : (OracleWorld + SigningSpec).Domain)
        (initialCache, []) (some signature) (finalCache, []) trace =
      let input := Concrete.CacheView.encodingInput secretKey.parameter
        request.epoch (request.message, signature.randomness)
      if initialCache input = none then
        match finalCache input with
        | none => trace
        | some output => trace ++ [.sign request.epoch output]
      else trace := by
  unfold encodingActionTraceUpdate
  simp only [encodingObservation?]
  let input := Concrete.CacheView.encodingInput secretKey.parameter
    request.epoch (request.message, signature.randomness)
  by_cases hinitial : initialCache input = none
  · rw [if_pos hinitial]
    cases hfinal : finalCache input <;> simp [hinitial, input]
  · simp [hinitial, input]

theorem globalFirstLaneEncodingHashQuery_validTrace
    (table : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (randomness : Randomness) (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneEncodingHashQuery secretKey epoch message randomness
          state)).run)) :
    firstLaneValidEncodingActions result.2 =
      CappedEncodingMonitor.validActions
        (if state.cache (Concrete.CacheView.encodingInput secretKey.parameter
            epoch (message, randomness)) = none then
          [.sign epoch result.1.1]
        else []) := by
  unfold globalFirstLaneEncodingHashQuery at hresult
  cases hcache : state.cache
      (Concrete.CacheView.encodingInput secretKey.parameter epoch
        (message, randomness)) with
  | some output =>
      simp [hcache, firstLaneValidEncodingActions] at hresult ⊢
      exact hresult ▸ rfl
  | none =>
      simp only [if_pos]
      dsimp only at hresult
      simp only [hcache] at hresult
      unfold globalFirstLaneFreshEncodingQuery at hresult
      simp [FirstLaneOracleSimulation.encodingSignAttemptQuery,
        FirstLaneOracleSimulation.eagerTraceImpl,
        FirstLaneOracleSimulation.eagerImpl,
        FirstLaneOracleSimulation.traceFragment,
        QueryImpl.withTraceAppend_apply, WriterT.run_tell,
        firstLaneValidEncodingActions] at hresult ⊢
      obtain ⟨output, _houtput, rfl⟩ := hresult
      rfl

theorem globalFirstLaneEncodingHashQuery_cache_eq_some
    (table : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (randomness : Randomness) (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneEncodingHashQuery secretKey epoch message randomness
          state)).run)) :
    result.1.2.cache (Concrete.CacheView.encodingInput secretKey.parameter
      epoch (message, randomness)) = some result.1.1 := by
  unfold globalFirstLaneEncodingHashQuery at hresult
  cases hcache : state.cache
      (Concrete.CacheView.encodingInput secretKey.parameter epoch
        (message, randomness)) with
  | some output =>
      simp [hcache] at hresult
      subst result
      exact hcache
  | none =>
      dsimp only at hresult
      simp only [hcache] at hresult
      unfold globalFirstLaneFreshEncodingQuery at hresult
      simp [FirstLaneOracleSimulation.encodingSignAttemptQuery,
        FirstLaneOracleSimulation.eagerTraceImpl,
        FirstLaneOracleSimulation.eagerImpl,
        FirstLaneOracleSimulation.traceFragment,
        QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hresult
      obtain ⟨output, _houtput, rfl⟩ := hresult
      exact QueryCache.cacheQuery_self _ _ _

theorem globalFirstLaneEncodingHashQuery_cache_le
    (table : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (randomness : Randomness) (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneEncodingHashQuery secretKey epoch message randomness
          state)).run)) :
    state.cache ≤ result.1.2.cache := by
  unfold globalFirstLaneEncodingHashQuery at hresult
  cases hcache : state.cache
      (Concrete.CacheView.encodingInput secretKey.parameter epoch
        (message, randomness)) with
  | some output =>
      simp [hcache] at hresult
      subst result
      exact le_rfl
  | none =>
      dsimp only at hresult
      simp only [hcache] at hresult
      unfold globalFirstLaneFreshEncodingQuery at hresult
      simp [FirstLaneOracleSimulation.encodingSignAttemptQuery,
        FirstLaneOracleSimulation.eagerTraceImpl,
        FirstLaneOracleSimulation.eagerImpl,
        FirstLaneOracleSimulation.traceFragment,
        QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hresult
      obtain ⟨output, _houtput, rfl⟩ := hresult
      exact QueryCache.le_cacheQuery state.cache hcache

theorem globalFirstLaneEncodingHashQuery_freshTarget_mem_trace
    (table : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (randomness : Randomness) (state : GlobalCausalHashState)
    (targetPayload : Message × Randomness) (targetOutput : HashOutput)
    (result : (HashOutput × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (htargetInitial : state.cache
      (Concrete.CacheView.encodingInput secretKey.parameter epoch
        targetPayload) = none)
    (htargetFinal : result.1.2.cache
      (Concrete.CacheView.encodingInput secretKey.parameter epoch
        targetPayload) = some targetOutput)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneEncodingHashQuery secretKey epoch message randomness
          state)).run)) :
    .sign epoch targetOutput ∈ result.2.encodingActions := by
  let sampledInput := Concrete.CacheView.encodingInput secretKey.parameter
    epoch (message, randomness)
  let targetInput := Concrete.CacheView.encodingInput secretKey.parameter
    epoch targetPayload
  unfold globalFirstLaneEncodingHashQuery at hresult
  cases hcache : state.cache sampledInput with
  | some output =>
      simp [sampledInput, hcache] at hresult
      subst result
      exact (Option.some_ne_none targetOutput
        (htargetFinal.symm.trans htargetInitial)).elim
  | none =>
      dsimp only at hresult
      simp only [sampledInput] at hcache
      simp only [hcache] at hresult
      unfold globalFirstLaneFreshEncodingQuery at hresult
      simp [FirstLaneOracleSimulation.encodingSignAttemptQuery,
        FirstLaneOracleSimulation.eagerTraceImpl,
        FirstLaneOracleSimulation.eagerImpl,
        FirstLaneOracleSimulation.traceFragment,
        QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hresult
      obtain ⟨output, _houtput, rfl⟩ := hresult
      dsimp only [GlobalCausalHashState.setCache] at htargetFinal
      change state.cache targetInput = none at htargetInitial
      change (state.cache.cacheQuery sampledInput output) targetInput =
        some targetOutput at htargetFinal
      by_cases heq : sampledInput = targetInput
      · rw [← heq, QueryCache.cacheQuery_self] at htargetFinal
        have houtput : output = targetOutput := by
          exact Option.some.inj htargetFinal
        subst targetOutput
        simp [FirstLaneOracleSimulation.ActionTrace.encodingActions]
      · have hstillNone :
            (state.cache.cacheQuery sampledInput output) targetInput = none := by
          rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm heq)]
          exact htargetInitial
        have hstillNone' : state.cache.cacheQuery sampledInput output
            (Concrete.CacheView.encodingInput secretKey.parameter epoch
              targetPayload) = none := by
          simpa [targetInput] using hstillNone
        rw [hstillNone'] at htargetFinal
        contradiction

theorem globalFirstLaneLiftRevealProbe_encodingActions_eq_nil
    (table : GlobalChainValueIndex → Digest)
    (computation : OracleComp
      (RevealProbeOracleSimulation.World GlobalChainValueIndex) α)
    (result : α ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneLiftRevealProbe computation)).run)) :
    result.2.encodingActions = [] := by
  induction computation using OracleComp.inductionOn generalizing result with
  | pure value =>
      simp [globalFirstLaneLiftRevealProbe] at hresult
      subst result
      rfl
  | query_bind input next ih =>
      unfold globalFirstLaneLiftRevealProbe at hresult
      rw [simulateQ_bind, simulateQ_bind, WriterT.run_bind',
        mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      cases input with
      | uniform n =>
          simp [globalFirstLaneRevealProbeImpl,
            FirstLaneOracleSimulation.uniformQuery,
            FirstLaneOracleSimulation.eagerTraceImpl,
            FirstLaneOracleSimulation.eagerImpl,
            FirstLaneOracleSimulation.traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hhead
          obtain ⟨output, rfl⟩ := hhead
          rw [support_map] at htail
          obtain ⟨tail, htail, rfl⟩ := htail
          simpa using ih output tail htail
      | probe index target =>
          simp [globalFirstLaneRevealProbeImpl,
            FirstLaneOracleSimulation.probeQuery,
            FirstLaneOracleSimulation.eagerTraceImpl,
            FirstLaneOracleSimulation.eagerImpl,
            FirstLaneOracleSimulation.traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hhead
          subst head
          rw [support_map] at htail
          obtain ⟨tail, htail, rfl⟩ := htail
          simpa [FirstLaneOracleSimulation.ActionTrace.encodingActions] using
            ih () tail htail
      | reveal index =>
          simp [globalFirstLaneRevealProbeImpl,
            FirstLaneOracleSimulation.revealQuery,
            FirstLaneOracleSimulation.eagerTraceImpl,
            FirstLaneOracleSimulation.eagerImpl,
            FirstLaneOracleSimulation.traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hhead
          subst head
          rw [support_map] at htail
          obtain ⟨tail, htail, rfl⟩ := htail
          simpa [FirstLaneOracleSimulation.ActionTrace.encodingActions] using
            ih (table index) tail htail

theorem globalFirstLaneSignatureReveal_result_eq
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : Encoding)
    (signature : Signature) (state : GlobalCausalHashState)
    (result : (Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneLiftRevealProbe
          ((revealGlobalSignatureChains request encoding allChains signature).run
            state))).run)) :
    result.1 = globalSignatureRevealResult table request encoding allChains
      signature state := by
  have hprojected : (result.1, result.2.chainActions) ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneErase
          (globalFirstLaneLiftRevealProbe
            ((revealGlobalSignatureChains request encoding allChains
              signature).run state)))).run) := by
    rw [← simulate_globalFirstLaneEagerTrace_chainProjection, support_map]
    exact ⟨result, hresult, rfl⟩
  rw [globalFirstLaneErase_liftRevealProbe,
    simulate_eagerTrace_revealGlobalSignatureChains] at hprojected
  simp only [support_pure, Set.mem_singleton_iff] at hprojected
  exact congrArg Prod.fst hprojected

theorem globalFirstLaneSigningAttempt_support_decompose
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneSigningAttempt keyView request state)).run)) :
    ∃ randomness encodedHead,
      encodedHead ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (globalFirstLaneEncodingHashQuery keyView.secretKey request.epoch
            request.message randomness state)).run) ∧
      ((TargetSum.decodeDigest (truncateHash encodedHead.1.1) = none ∧
          result = ((none, encodedHead.1.2), encodedHead.2)) ∨
        ∃ encoding revealedHead,
          TargetSum.decodeDigest (truncateHash encodedHead.1.1) =
              some encoding ∧
            revealedHead ∈ support
              ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
                (globalFirstLaneLiftRevealProbe
                  ((revealGlobalSignatureChains request encoding allChains
                    (Concrete.CacheReplay.signWithEncoding keyView.cache
                      keyView.secretKey request.epoch randomness encoding)).run
                        encodedHead.1.2))).run) ∧
            revealedHead.1 =
              globalSignatureRevealResult table request encoding allChains
                (Concrete.CacheReplay.signWithEncoding keyView.cache
                  keyView.secretKey request.epoch randomness encoding)
                encodedHead.1.2 ∧
            result = ((some revealedHead.1.1, revealedHead.1.2),
              encodedHead.2 ++ revealedHead.2)) := by
  unfold globalFirstLaneSigningAttempt at hresult
  rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hresult
  obtain ⟨randomHead, hrandom, hrest⟩ := hresult
  rw [FirstLaneOracleSimulation.simulate_eagerTrace_liftProbComp,
    support_map] at hrandom
  obtain ⟨randomness, _hrandomness, rfl⟩ := hrandom
  simp only [List.nil_append] at hrest
  rw [show Prod.map id (fun x => x) =
    (id : ((Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) → _)
    from Prod.map_id, id_map, simulateQ_bind, WriterT.run_bind',
    mem_support_bind_iff] at hrest
  obtain ⟨encodedHead, hencoded, htail⟩ := hrest
  rw [support_map] at htail
  obtain ⟨tailResult, htail, rfl⟩ := htail
  refine ⟨randomness, encodedHead, hencoded, ?_⟩
  cases hdecode : TargetSum.decodeDigest (truncateHash encodedHead.1.1) with
  | none =>
      simp [hdecode] at htail
      subst tailResult
      refine Or.inl ⟨rfl, ?_⟩
      simp [Prod.map]
  | some encoding =>
      simp only [hdecode] at htail
      rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at htail
      obtain ⟨revealedHead, hrevealed, hpure⟩ := htail
      simp only at hpure
      subst tailResult
      have hrevealedResult := globalFirstLaneSignatureReveal_result_eq table
        request encoding
          (Concrete.CacheReplay.signWithEncoding keyView.cache keyView.secretKey
            request.epoch randomness encoding)
          encodedHead.1.2 revealedHead hrevealed
      refine Or.inr
        ⟨encoding, revealedHead, rfl, hrevealed, hrevealedResult, ?_⟩
      simp [Prod.map]

set_option maxRecDepth 1000000 in
theorem globalFirstLaneSigningAttempt_freshTarget_mem_trace
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (targetPayload : Message × Randomness) (targetOutput : HashOutput)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (htargetInitial : state.cache
      (Concrete.CacheView.encodingInput keyView.secretKey.parameter
        request.epoch targetPayload) = none)
    (htargetFinal : result.1.2.cache
      (Concrete.CacheView.encodingInput keyView.secretKey.parameter
        request.epoch targetPayload) = some targetOutput)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneSigningAttempt keyView request state)).run)) :
    .sign request.epoch targetOutput ∈ result.2.encodingActions := by
  obtain ⟨randomness, encodedHead, hencoded, hcases⟩ :=
    globalFirstLaneSigningAttempt_support_decompose table keyView request state
      result hresult
  rcases hcases with hreject | haccept
  · rw [hreject.2] at htargetFinal ⊢
    exact globalFirstLaneEncodingHashQuery_freshTarget_mem_trace table
      keyView.secretKey request.epoch request.message randomness state
        targetPayload targetOutput encodedHead htargetInitial htargetFinal hencoded
  · obtain ⟨encoding, revealedHead, _hdecode, hrevealed,
      hrevealedResult, hresultEq⟩ := haccept
    have hfinalCache : revealedHead.1.2.cache = encodedHead.1.2.cache := by
      rw [hrevealedResult, globalSignatureRevealResult_cache]
    rw [hresultEq] at htargetFinal ⊢
    rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append]
    apply List.mem_append_left
    apply globalFirstLaneEncodingHashQuery_freshTarget_mem_trace table
      keyView.secretKey request.epoch request.message randomness state
        targetPayload targetOutput encodedHead htargetInitial
    · rw [← hfinalCache]
      exact htargetFinal
    · exact hencoded

set_option maxRecDepth 1000000 in
theorem globalFirstLaneSigningAttempt_cache_le
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneSigningAttempt keyView request state)).run)) :
    state.cache ≤ result.1.2.cache := by
  obtain ⟨randomness, encodedHead, hencoded, hcases⟩ :=
    globalFirstLaneSigningAttempt_support_decompose table keyView request state
      result hresult
  have hencodedLe := globalFirstLaneEncodingHashQuery_cache_le table
    keyView.secretKey request.epoch request.message randomness state
      encodedHead hencoded
  rcases hcases with hreject | haccept
  · rw [hreject.2]
    exact hencodedLe
  · obtain ⟨encoding, revealedHead, _hdecode, _hrevealed,
      hrevealedResult, hresultEq⟩ := haccept
    have hfinalCache : revealedHead.1.2.cache = encodedHead.1.2.cache := by
      rw [hrevealedResult, globalSignatureRevealResult_cache]
    rw [hresultEq, hfinalCache]
    exact hencodedLe

theorem globalFirstLaneSignBoundedAttempts_cache_le
    (attempts : Nat)
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneSignBoundedAttempts attempts keyView request state)
        ).run)) :
    state.cache ≤ result.1.2.cache := by
  induction attempts generalizing state result with
  | zero =>
      simp [globalFirstLaneSignBoundedAttempts] at hresult
      subst result
      exact le_rfl
  | succ attempts ih =>
      rw [globalFirstLaneSignBoundedAttempts, simulateQ_bind,
        WriterT.run_bind', mem_support_bind_iff] at hresult
      obtain ⟨attemptHead, hattempt, hcontinuation⟩ := hresult
      have hattemptLe := globalFirstLaneSigningAttempt_cache_le table keyView
        request state attemptHead hattempt
      rw [support_map] at hcontinuation
      obtain ⟨tailResult, htail, rfl⟩ := hcontinuation
      cases hoption : attemptHead.1.1 with
      | some signature =>
          simp [hoption] at htail
          subst tailResult
          exact hattemptLe
      | none =>
          simp only [hoption] at htail
          exact le_trans hattemptLe
            (ih attemptHead.1.2 tailResult htail)

theorem globalFirstLaneSignBoundedAttempts_freshTarget_mem_trace
    (attempts : Nat)
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (targetPayload : Message × Randomness) (targetOutput : HashOutput)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (htargetInitial : state.cache
      (Concrete.CacheView.encodingInput keyView.secretKey.parameter
        request.epoch targetPayload) = none)
    (htargetFinal : result.1.2.cache
      (Concrete.CacheView.encodingInput keyView.secretKey.parameter
        request.epoch targetPayload) = some targetOutput)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneSignBoundedAttempts attempts keyView request state)
        ).run)) :
    .sign request.epoch targetOutput ∈ result.2.encodingActions := by
  induction attempts generalizing state result with
  | zero =>
      simp [globalFirstLaneSignBoundedAttempts] at hresult
      subst result
      exact (Option.some_ne_none targetOutput
        (htargetFinal.symm.trans htargetInitial)).elim
  | succ attempts ih =>
      rw [globalFirstLaneSignBoundedAttempts, simulateQ_bind,
        WriterT.run_bind', mem_support_bind_iff] at hresult
      obtain ⟨attemptHead, hattempt, hcontinuation⟩ := hresult
      rw [support_map] at hcontinuation
      obtain ⟨tailResult, htail, rfl⟩ := hcontinuation
      cases hoption : attemptHead.1.1 with
      | some signature =>
          simp [hoption] at htail
          subst tailResult
          dsimp only [Prod.map]
          rw [List.append_nil]
          exact globalFirstLaneSigningAttempt_freshTarget_mem_trace table
            keyView request state targetPayload targetOutput attemptHead
              htargetInitial htargetFinal hattempt
      | none =>
          simp only [hoption] at htail
          dsimp only [Prod.map]
          rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append]
          let targetInput := Concrete.CacheView.encodingInput
            keyView.secretKey.parameter request.epoch targetPayload
          cases hmid : attemptHead.1.2.cache targetInput with
          | none =>
              apply List.mem_append_right
              exact ih attemptHead.1.2 tailResult hmid htargetFinal htail
          | some middleOutput =>
              have htailLe := globalFirstLaneSignBoundedAttempts_cache_le
                attempts table keyView request attemptHead.1.2 tailResult htail
              have hmiddleFinal : tailResult.1.2.cache targetInput =
                  some middleOutput := htailLe hmid
              have houtputs : middleOutput = targetOutput := by
                exact Option.some.inj (hmiddleFinal.symm.trans htargetFinal)
              subst middleOutput
              apply List.mem_append_left
              exact globalFirstLaneSigningAttempt_freshTarget_mem_trace table
                keyView request state targetPayload targetOutput attemptHead
                  htargetInitial hmid hattempt

theorem globalFirstLaneSigningQuery_freshTarget_mem_trace
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (targetPayload : Message × Randomness) (targetOutput : HashOutput)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (htargetInitial : state.cache
      (Concrete.CacheView.encodingInput keyView.secretKey.parameter
        request.epoch targetPayload) = none)
    (htargetFinal : result.1.2.cache
      (Concrete.CacheView.encodingInput keyView.secretKey.parameter
        request.epoch targetPayload) = some targetOutput)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneSigningQuery keyView request state)).run)) :
    .sign request.epoch targetOutput ∈ result.2.encodingActions := by
  exact globalFirstLaneSignBoundedAttempts_freshTarget_mem_trace
    signingAttemptLimit table keyView request state targetPayload targetOutput
      result htargetInitial htargetFinal hresult

theorem globalFirstLaneAttackerHashQueryAtEpoch_trace
    (table : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (epoch : Epoch)
    (result : (HashOutput × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneAttackerHashQueryAtEpoch secretKey input state epoch)
        ).run)) :
    result.2.encodingActions =
      if state.cache input = none then [.query epoch result.1.1] else [] := by
  cases hcache : state.cache input with
  | some output =>
      rw [globalFirstLaneAttackerHashQueryAtEpoch_eq_cached _ _ _ _ _ hcache]
        at hresult
      simp only [simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      simp [FirstLaneOracleSimulation.ActionTrace.encodingActions]
  | none =>
      rw [globalFirstLaneAttackerHashQueryAtEpoch_eq_fresh _ _ _ _ hcache]
        at hresult
      unfold globalFirstLaneFreshEncodingQuery at hresult
      simp [FirstLaneOracleSimulation.encodingQuery,
        FirstLaneOracleSimulation.eagerTraceImpl,
        FirstLaneOracleSimulation.eagerImpl,
        FirstLaneOracleSimulation.traceFragment,
        QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hresult
      obtain ⟨output, _houtput, rfl⟩ := hresult
      simp [FirstLaneOracleSimulation.ActionTrace.encodingActions]

theorem globalFirstLaneAttackerHashQueryAtEpoch_cache_le
    (table : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (epoch : Epoch)
    (result : (HashOutput × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneAttackerHashQueryAtEpoch secretKey input state epoch)
        ).run)) :
    state.cache ≤ result.1.2.cache := by
  cases hcache : state.cache input with
  | some output =>
      rw [globalFirstLaneAttackerHashQueryAtEpoch_eq_cached _ _ _ _ _ hcache]
        at hresult
      simp at hresult
      subst result
      simpa only [globalCausalRecordedState_cache] using
        (le_refl state.cache)
  | none =>
      rw [globalFirstLaneAttackerHashQueryAtEpoch_eq_fresh _ _ _ _ hcache]
        at hresult
      unfold globalFirstLaneFreshEncodingQuery at hresult
      simp [FirstLaneOracleSimulation.encodingQuery,
        FirstLaneOracleSimulation.eagerTraceImpl,
        FirstLaneOracleSimulation.eagerImpl,
        FirstLaneOracleSimulation.traceFragment,
        QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hresult
      obtain ⟨output, _houtput, rfl⟩ := hresult
      simpa [GlobalCausalHashState.setCache, globalCausalRecordedState_cache]
        using QueryCache.le_cacheQuery state.cache hcache

theorem globalFirstLaneAttackerHashQueryAtEpoch_cache_eq_some
    (table : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (epoch : Epoch)
    (result : (HashOutput × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneAttackerHashQueryAtEpoch secretKey input state epoch)
        ).run)) :
    result.1.2.cache input = some result.1.1 := by
  cases hcache : state.cache input with
  | some output =>
      rw [globalFirstLaneAttackerHashQueryAtEpoch_eq_cached _ _ _ _ _ hcache]
        at hresult
      simp only [simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      simpa only [globalCausalRecordedState_cache] using hcache
  | none =>
      rw [globalFirstLaneAttackerHashQueryAtEpoch_eq_fresh _ _ _ _ hcache]
        at hresult
      unfold globalFirstLaneFreshEncodingQuery at hresult
      simp [FirstLaneOracleSimulation.encodingQuery,
        FirstLaneOracleSimulation.eagerTraceImpl,
        FirstLaneOracleSimulation.eagerImpl,
        FirstLaneOracleSimulation.traceFragment,
        QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hresult
      obtain ⟨output, _houtput, rfl⟩ := hresult
      exact QueryCache.cacheQuery_self _ _ _

set_option maxRecDepth 1000000 in
theorem globalFirstLaneSigningAttempt_validTrace
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneSigningAttempt keyView request state)).run)) :
    firstLaneValidEncodingActions result.2 =
      CappedEncodingMonitor.validActions
        (encodingActionTraceUpdate keyView.secretKey
          (.inr request : (OracleWorld + SigningSpec).Domain)
          (state.cache, []) result.1.1 (result.1.2.cache, []) []) := by
  obtain ⟨randomness, encodedHead, hencoded, hcases⟩ :=
    globalFirstLaneSigningAttempt_support_decompose table keyView request state
      result hresult
  have hencodedTrace := globalFirstLaneEncodingHashQuery_validTrace table
    keyView.secretKey request.epoch request.message randomness state
      encodedHead hencoded
  have hencodedTrace' : CappedEncodingMonitor.validActions
      encodedHead.2.encodingActions =
        CappedEncodingMonitor.validActions
          (if state.cache
              (Concrete.CacheView.encodingInput keyView.secretKey.parameter
                request.epoch (request.message, randomness)) = none then
            [.sign request.epoch encodedHead.1.1]
          else []) := by
    simpa [firstLaneValidEncodingActions] using hencodedTrace
  rcases hcases with hreject | haccept
  · obtain ⟨hdecode, hresultEq⟩ := hreject
    subst result
    have hinvalidDigest :
        ¬TargetSum.ValidDigest (truncateHash encodedHead.1.1) := by
      intro ⟨encoding, hencoding⟩
      rw [hdecode] at hencoding
      contradiction
    dsimp only [firstLaneValidEncodingActions]
    change CappedEncodingMonitor.validActions
        encodedHead.2.encodingActions =
      CappedEncodingMonitor.validActions []
    rw [hencodedTrace']
    by_cases hcache : state.cache
        (Concrete.CacheView.encodingInput keyView.secretKey.parameter
          request.epoch (request.message, randomness)) = none
    · simp [hcache, CappedEncodingMonitor.validActions,
        CappedEncodingMonitor.ActionValid, hinvalidDigest]
    · simp [hcache]
  · obtain ⟨encoding, revealedHead, hdecode, hrevealed,
      hrevealedResult, hresultEq⟩ := haccept
    subst result
    have hrevealTrace :
        revealedHead.2.encodingActions = [] := by
      exact globalFirstLaneLiftRevealProbe_encodingActions_eq_nil table _ _
        hrevealed
    have hrandomness : revealedHead.1.1.randomness = randomness := by
      rw [hrevealedResult, globalSignatureRevealResult_randomness]
      rfl
    have hfinalCache : revealedHead.1.2.cache = encodedHead.1.2.cache := by
      rw [hrevealedResult, globalSignatureRevealResult_cache]
    have hencodedCache := globalFirstLaneEncodingHashQuery_cache_eq_some
      table keyView.secretKey request.epoch request.message randomness state
        encodedHead hencoded
    have hfinalLookup : revealedHead.1.2.cache
        (Concrete.CacheView.encodingInput keyView.secretKey.parameter
          request.epoch (request.message, randomness)) =
          some encodedHead.1.1 := by
      rw [hfinalCache]
      exact hencodedCache
    dsimp only [firstLaneValidEncodingActions]
    change CappedEncodingMonitor.validActions
        (encodedHead.2 ++ revealedHead.2).encodingActions =
      CappedEncodingMonitor.validActions
        (encodingActionTraceUpdate keyView.secretKey
          (.inr request : (OracleWorld + SigningSpec).Domain)
          (state.cache, []) (some revealedHead.1.1)
          (revealedHead.1.2.cache, []) [])
    rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append,
      hrevealTrace, List.append_nil, hencodedTrace']
    have hupdate := encodingActionTraceUpdate_sign_some keyView.secretKey
      request revealedHead.1.1 state.cache revealedHead.1.2.cache []
    dsimp only at hupdate
    rw [hrandomness] at hupdate
    by_cases hcache : state.cache
        (Concrete.CacheView.encodingInput keyView.secretKey.parameter
          request.epoch (request.message, randomness)) = none
    · simpa [hcache, hfinalLookup] using congrArg
        CappedEncodingMonitor.validActions hupdate.symm
    · simpa [hcache] using congrArg
        CappedEncodingMonitor.validActions hupdate.symm

theorem encodingActionTraceUpdate_sublist_of_observation_mem
    (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState finalState : QueryCache HashSpec × SigningCacheTrace)
    (output : (OracleWorld + SigningSpec).Range input)
    (initialTrace externalTrace : EncodingActionTrace)
    (hrepresented : ∀ observation,
      encodingObservation? secretKey input initialState output finalState =
          some observation →
        observation ∈ externalTrace) :
    List.Sublist
      (encodingActionTraceUpdate secretKey input initialState output finalState
        initialTrace)
      (initialTrace ++ externalTrace) := by
  unfold encodingActionTraceUpdate
  cases hobservation : encodingObservation? secretKey input initialState output
      finalState with
  | none => exact List.sublist_append_left initialTrace externalTrace
  | some observation =>
      exact (List.Sublist.refl initialTrace).append
        (List.singleton_sublist.mpr (hrepresented observation hobservation))

theorem globalFirstLaneHashQuery_observation_mem
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (hashInput : HashInput)
    (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneAttackerHashQueryFromHighRun
          (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey
            hashInput state)).run))
    (observation : EncodingMonitor.ObservedAction)
    (hobservation : encodingObservation? keyView.secretKey
      (.inl (.inr hashInput) : (OracleWorld + SigningSpec).Domain)
      (state.cache, []) result.1.1 (result.1.2.cache, []) = some observation) :
    observation ∈ result.2.encodingActions := by
  cases hepoch : encodingInputEpoch? keyView.secretKey.parameter hashInput with
  | none =>
      by_cases hfresh : state.cache hashInput = none
      <;> simp [encodingObservation?, hfresh, hepoch] at hobservation
  | some epoch =>
      by_cases hfresh : state.cache hashInput = none
      · rw [globalFirstLaneAttackerHashQueryFromHighRun_eq_some _ _ _ _ epoch
          hepoch] at hresult
        have htrace := globalFirstLaneAttackerHashQueryAtEpoch_trace table
          keyView.secretKey hashInput state epoch result hresult
        have haction : EncodingMonitor.ObservedAction.query epoch result.1.1 ∈
            result.2.encodingActions := by
          simp [htrace, hfresh]
        have hobservation' : EncodingMonitor.ObservedAction.query epoch
            result.1.1 = observation := by
          exact Option.some.inj (by simpa [encodingObservation?, hfresh, hepoch]
            using hobservation)
        simpa [← hobservation'] using haction
      · simp [encodingObservation?, hfresh] at hobservation

theorem globalFirstLaneSigningQuery_observation_mem
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView) (request : SignRequest)
    (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneSigningQuery keyView request state)).run))
    (observation : EncodingMonitor.ObservedAction)
    (hobservation : encodingObservation? keyView.secretKey
      (.inr request : (OracleWorld + SigningSpec).Domain) (state.cache, [])
      result.1.1 (result.1.2.cache, []) = some observation) :
    observation ∈ result.2.encodingActions := by
  cases houtput : result.1.1 with
  | none => simp [encodingObservation?, houtput] at hobservation
  | some signature =>
      let signedInput := Concrete.CacheView.encodingInput
        keyView.secretKey.parameter request.epoch
          (request.message, signature.randomness)
      by_cases hfresh : state.cache signedInput = none
      · cases hfinal : result.1.2.cache signedInput with
        | none =>
            simp [encodingObservation?, signedInput, hfresh, hfinal, houtput]
              at hobservation
        | some hashOutput =>
            have haction := globalFirstLaneSigningQuery_freshTarget_mem_trace
              table keyView request state
                (request.message, signature.randomness) hashOutput result
                  (by simpa [signedInput] using hfresh)
                  (by simpa [signedInput] using hfinal) hresult
            have hobservation' : EncodingMonitor.ObservedAction.sign
                request.epoch hashOutput = observation := by
              exact Option.some.inj (by simpa [encodingObservation?, signedInput,
                hfresh, hfinal, houtput] using hobservation)
            simpa [← hobservation'] using haction
      · simp [encodingObservation?, signedInput, hfresh, houtput]
          at hobservation

theorem globalFirstLaneUniformQuery_trace_sublist
    (keyView : ProgrammedGlobalChainKeygenView) (n : Nat)
    (state : GlobalCausalHashState) (initialTrace : EncodingActionTrace)
    (result : (Fin (n + 1) × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) :
    List.Sublist
      (encodingActionTraceUpdate keyView.secretKey
        (.inl (.inl n) : (OracleWorld + SigningSpec).Domain) (state.cache, [])
          result.1.1 (result.1.2.cache, []) initialTrace)
      (initialTrace ++ result.2.encodingActions) := by
  simp [encodingActionTraceUpdate, encodingObservation?]

theorem globalFirstLaneHashQuery_trace_sublist
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (hashInput : HashInput)
    (state : GlobalCausalHashState) (initialTrace : EncodingActionTrace)
    (result : (HashOutput × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneAttackerHashQueryFromHighRun
          (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey
            hashInput state)).run)) :
    List.Sublist
      (encodingActionTraceUpdate keyView.secretKey
        (.inl (.inr hashInput) : (OracleWorld + SigningSpec).Domain)
          (state.cache, []) result.1.1 (result.1.2.cache, []) initialTrace)
      (initialTrace ++ result.2.encodingActions) := by
  apply encodingActionTraceUpdate_sublist_of_observation_mem
  intro observation hobservation
  exact globalFirstLaneHashQuery_observation_mem table keyView edgeHigh
    hashInput state result hresult observation hobservation

theorem globalFirstLaneSigningQuery_trace_sublist
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView) (request : SignRequest)
    (state : GlobalCausalHashState) (initialTrace : EncodingActionTrace)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneSigningQuery keyView request state)).run)) :
    List.Sublist
      (encodingActionTraceUpdate keyView.secretKey
        (.inr request : (OracleWorld + SigningSpec).Domain) (state.cache, [])
          result.1.1 (result.1.2.cache, []) initialTrace)
      (initialTrace ++ result.2.encodingActions) := by
  apply encodingActionTraceUpdate_sublist_of_observation_mem
  intro observation hobservation
  exact globalFirstLaneSigningQuery_observation_mem table keyView request
    state result hresult observation hobservation

theorem globalExactTracedLift_trace_sublist
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (base : StateT GlobalCausalHashState (OracleComp GlobalFirstLaneWorld)
      ((OracleWorld + SigningSpec).Range input))
    (state : GlobalExactTracedState)
    (result : ((OracleWorld + SigningSpec).Range input ×
      GlobalExactTracedState) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalExactTracedLift keyView input base).run state)).run))
    (hbaseSub : ∀ baseResult,
      baseResult ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (base.run state.causalState)).run) →
      List.Sublist
        (encodingActionTraceUpdate keyView.secretKey input
          (state.causalState.cache, []) baseResult.1.1
            (baseResult.1.2.cache, []) state.encodingTrace)
        (state.encodingTrace ++ baseResult.2.encodingActions)) :
    List.Sublist result.1.2.encodingTrace
      (state.encodingTrace ++ result.2.encodingActions) := by
  unfold globalExactTracedLift at hresult
  rw [StateT.run_mk, simulateQ_map, WriterT.run_map', support_map] at hresult
  obtain ⟨baseResult, hbase, heq⟩ := hresult
  have htrace := congrArg (fun value => value.1.2.encodingTrace) heq
  have hactions := congrArg (fun value => value.2.encodingActions) heq
  dsimp only [Prod.map, id] at htrace hactions
  rw [← htrace, ← hactions]
  rw [globalExactTracedNextState_encodingTrace]
  exact hbaseSub baseResult hbase

abbrev GlobalFirstLaneOracleTraceSublist
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) : Prop :=
  ∀ (input : OracleWorld.Domain)
    (state : GlobalCausalHashState) (encodingTrace : EncodingActionTrace)
    (result : (OracleWorld.Range input × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex),
    result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneOracleExecution keyView edgeHigh input state)).run) →
    List.Sublist
      (encodingActionTraceUpdate keyView.secretKey (.inl input)
        (state.cache, []) result.1.1 (result.1.2.cache, []) encodingTrace)
      (encodingTrace ++ result.2.encodingActions)

theorem globalFirstLaneOracleTraceSublist_holds
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    GlobalFirstLaneOracleTraceSublist table keyView edgeHigh := by
  intro input state encodingTrace result hresult
  cases input with
  | inl n =>
      exact globalFirstLaneUniformQuery_trace_sublist keyView n state
        encodingTrace result
  | inr hashInput =>
      exact globalFirstLaneHashQuery_trace_sublist table keyView edgeHigh
        hashInput state encodingTrace result hresult

abbrev GlobalFirstLaneExactTracedOracleTraceSublist
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) : Prop :=
  ∀ (input : OracleWorld.Domain)
    (state : GlobalExactTracedState)
    (result : (OracleWorld.Range input × GlobalExactTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex),
    result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalFirstLaneExactTracedOracleImpl keyView edgeHigh input).run
          state)).run) →
    List.Sublist result.1.2.encodingTrace
      (state.encodingTrace ++ result.2.encodingActions)

theorem globalFirstLaneExactTracedOracleTraceSublist_holds
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    GlobalFirstLaneExactTracedOracleTraceSublist table keyView edgeHigh := by
  intro input state result hresult
  unfold globalFirstLaneExactTracedOracleImpl at hresult
  apply globalExactTracedLift_trace_sublist table keyView
    (.inl input)
    (StateT.mk fun causalState =>
      globalFirstLaneOracleExecution keyView edgeHigh input causalState)
    state result hresult
  exact globalFirstLaneOracleTraceSublist_holds table keyView edgeHigh
    input state.causalState state.encodingTrace

theorem globalFirstLaneExactTracedSigningImpl_trace_sublist
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView) (request : SignRequest)
    (state : GlobalExactTracedState)
    (result : (SigningSpec.Range request × GlobalExactTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalFirstLaneExactTracedSigningImpl keyView request).run state)
          ).run)) :
    List.Sublist result.1.2.encodingTrace
      (state.encodingTrace ++ result.2.encodingActions) := by
  unfold globalFirstLaneExactTracedSigningImpl at hresult
  apply globalExactTracedLift_trace_sublist table keyView
    (.inr request) (globalFirstLaneSigningImpl keyView request) state result
      hresult
  intro baseResult hbase
  exact globalFirstLaneSigningQuery_trace_sublist table keyView request
    state.causalState state.encodingTrace baseResult hbase

theorem globalFirstLaneExactTracedMappedAdversaryImpl_query_trace_sublist
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalExactTracedState)
    (result : ((OracleWorld + SigningSpec).Range input ×
      GlobalExactTracedState) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh input
          ).run state)).run)) :
    List.Sublist result.1.2.encodingTrace
      (state.encodingTrace ++ result.2.encodingActions) := by
  cases input with
  | inl worldInput =>
      exact globalFirstLaneExactTracedOracleTraceSublist_holds table keyView
        edgeHigh worldInput state result hresult
  | inr request =>
      exact globalFirstLaneExactTracedSigningImpl_trace_sublist table keyView
        request state result hresult

theorem simulateQ_eagerTrace_state_trace_sublist
    {spec : OracleSpec ι} {State : Type}
    (table : GlobalChainValueIndex → Digest)
    (impl : QueryImpl spec
      (StateT State (OracleComp GlobalFirstLaneWorld)))
    (stateTrace : State → EncodingActionTrace)
    (hstep : ∀ (input : spec.Domain) (state : State)
      (result : (spec.Range input × State) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex),
      result ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          ((impl input).run state)).run) →
      List.Sublist (stateTrace result.1.2)
        (stateTrace state ++ result.2.encodingActions))
    (computation : OracleComp spec α) (initialState : State)
    (result : (α × State) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ impl computation).run initialState)).run)) :
    List.Sublist (stateTrace result.1.2)
      (stateTrace initialState ++ result.2.encodingActions) := by
  apply simulateQ_eagerTrace_support_invariant table impl
    (fun initial trace final => List.Sublist (stateTrace final)
      (stateTrace initial ++ trace.encodingActions))
  · intro state
    simp [FirstLaneOracleSimulation.ActionTrace.encodingActions]
  · intro initial middle final headTrace tailTrace hhead htail
    rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append]
    simpa [List.append_assoc] using htail.trans
      (hhead.append (List.Sublist.refl tailTrace.encodingActions))
  · exact hstep
  · exact hresult

theorem globalFirstLaneExactTracedMappedAdversary_simulateQ_trace_sublist
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : GlobalExactTracedState)
    (result : (α × GlobalExactTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ
          (globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh)
            computation).run initialState)).run)) :
    List.Sublist result.1.2.encodingTrace
      (initialState.encodingTrace ++ result.2.encodingActions) := by
  apply simulateQ_eagerTrace_state_trace_sublist table
    (globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh)
    (fun state : GlobalExactTracedState => state.encodingTrace) _ computation
      initialState result hresult
  intro input state stepResult hstep
  exact globalFirstLaneExactTracedMappedAdversaryImpl_query_trace_sublist table
    keyView edgeHigh input state stepResult hstep

theorem globalFirstLaneLiftRevealProbe_mem_eagerTrace_support
    (table : GlobalChainValueIndex → Digest)
    (computation : OracleComp
      (RevealProbeOracleSimulation.World GlobalChainValueIndex) α)
    (result : α ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneLiftRevealProbe computation)).run)) :
    (result.1, result.2.chainActions) ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        computation).run) := by
  rw [← globalFirstLaneErase_liftRevealProbe computation,
    ← simulate_globalFirstLaneEagerTrace_chainProjection, support_map]
  exact ⟨result, hresult, rfl⟩

theorem globalFirstLaneHashQuery_cache_le
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (hashInput : HashInput)
    (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneAttackerHashQueryFromHighRun
          (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey
            hashInput state)).run)) :
    state.cache ≤ result.1.2.cache := by
  cases hepoch : encodingInputEpoch? keyView.secretKey.parameter hashInput with
  | some epoch =>
      rw [globalFirstLaneAttackerHashQueryFromHighRun_eq_some _ _ _ _ epoch
        hepoch] at hresult
      exact globalFirstLaneAttackerHashQueryAtEpoch_cache_le table
        keyView.secretKey hashInput state epoch result hresult
  | none =>
      rw [globalFirstLaneAttackerHashQueryFromHighRun_eq_none _ _ _ _ hepoch]
        at hresult
      have hprojected := globalFirstLaneLiftRevealProbe_mem_eagerTrace_support
        table ((globalCausalAttackerHashQueryFromHigh
          (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey
            hashInput).run state) result hresult
      exact
        simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_support_cache_le
          table (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey
            hashInput state (result.1, result.2.chainActions) hprojected

@[irreducible]
noncomputable def globalFirstLaneVerifierHashExecution
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (hashInput : HashInput)
    (state : GlobalCausalHashState) : OracleComp GlobalFirstLaneWorld
      (HashOutput × GlobalCausalHashState) :=
  globalFirstLaneAttackerHashQueryFromHighRun
    (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey hashInput
      state

theorem globalFirstLaneVerifierHashExecution_cache_le
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (hashInput : HashInput) (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneVerifierHashExecution keyView edgeHigh hashInput
          state)).run)) :
    state.cache ≤ result.1.2.cache := by
  unfold globalFirstLaneVerifierHashExecution at hresult
  exact globalFirstLaneHashQuery_cache_le table keyView edgeHigh hashInput state
    result hresult

theorem simulateQ_eagerTrace_state_cache_le
    {spec : OracleSpec ι} {State : Type}
    (table : GlobalChainValueIndex → Digest)
    (implRun : ∀ input : spec.Domain, State →
      OracleComp GlobalFirstLaneWorld (spec.Range input × State))
    (stateCache : State → QueryCache HashSpec)
    (hstep : ∀ (input : spec.Domain) (state : State)
      (result : (spec.Range input × State) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex),
      result ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (implRun input state)).run) →
      stateCache state ≤ stateCache result.1.2)
    (computation : OracleComp spec α) (initialState : State)
    (result : (α × State) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun input => StateT.mk (implRun input)) computation).run
          initialState)).run)) :
    stateCache initialState ≤ stateCache result.1.2 := by
  apply simulateQ_eagerTrace_support_invariant table
    (fun input => StateT.mk (implRun input))
    (fun initial _trace final => stateCache initial ≤ stateCache final)
  · intro state
    exact le_rfl
  · intro initial middle final headTrace tailTrace hhead htail
    exact hhead.trans htail
  · exact hstep
  · exact hresult

theorem globalFirstLaneVerifierHashExecution_simulateQ_cache_le
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp HashSpec α)
    (initialState : GlobalCausalHashState)
    (result : (α × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun hashInput => StateT.mk
          (globalFirstLaneVerifierHashExecution keyView edgeHigh hashInput))
            computation).run initialState)).run)) :
    initialState.cache ≤ result.1.2.cache := by
  exact simulateQ_eagerTrace_state_cache_le table
    (globalFirstLaneVerifierHashExecution keyView edgeHigh)
      (fun state : GlobalCausalHashState => state.cache)
      (globalFirstLaneVerifierHashExecution_cache_le table keyView edgeHigh)
      computation initialState result hresult

@[irreducible]
noncomputable def concreteVerificationAfterDigest
    (publicKey : PublicKey) (epoch : Epoch) (signature : Signature)
    (digest : Digest) : OracleComp HashSpec Bool :=
  match TargetSum.decodeDigest digest with
  | none => pure false
  | some encoding => do
      let endpoints ← Concrete.recoverEndpoints publicKey.parameter epoch
        encoding signature
      let leaf ← Concrete.leafHash publicKey.parameter epoch endpoints
      Concrete.verifyAfterLeaf publicKey epoch signature leaf

theorem concreteVerify_eq_encodingHash_bind_afterDigest
    (publicKey : PublicKey) (epoch : Epoch) (message : Message)
    (signature : Signature) :
    (Concrete.verify publicKey epoch message signature :
        OracleComp HashSpec Bool) = (do
      let digest ← Concrete.encodingHash publicKey.parameter epoch message
        signature.randomness
      concreteVerificationAfterDigest publicKey epoch signature digest) := by
  unfold Concrete.verify concreteVerificationAfterDigest
  rfl

theorem globalFirstLaneVerifier_eq_hashExecution
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (forgery : Forgery) :
    simulateQ (globalFirstLaneVerifierImpl keyView edgeHigh)
        (Concrete.scheme.verify keyView.publicKey forgery.epoch
          forgery.message forgery.signature) =
      simulateQ (fun hashInput => StateT.mk
        (globalFirstLaneVerifierHashExecution keyView edgeHigh hashInput))
        (Concrete.verify keyView.publicKey forgery.epoch forgery.message
          forgery.signature : OracleComp HashSpec Bool) := by
  change simulateQ (globalFirstLaneVerifierImpl keyView edgeHigh)
      (liftM (Concrete.verify keyView.publicKey forgery.epoch
        forgery.message forgery.signature : OracleComp HashSpec Bool)) = _
  rw [← OracleComp.liftComp_eq_liftM]
  trans simulateQ (globalFirstLaneHashImpl keyView edgeHigh)
    (Concrete.verify keyView.publicKey forgery.epoch forgery.message
      forgery.signature : OracleComp HashSpec Bool)
  · apply QueryImpl.simulateQ_liftComp_right_eq_of_apply
    intro hashInput
    exact globalFirstLaneVerifierImpl_hash keyView edgeHigh hashInput
  · congr 1
    funext hashInput
    unfold globalFirstLaneVerifierHashExecution
    rfl

theorem concreteEncodingHash_eq_query
    (parameter : PublicParameter) (epoch : Epoch) (message : Message)
    (randomness : Randomness) :
    (Concrete.encodingHash parameter epoch message randomness :
        OracleComp HashSpec Digest) = (do
      let output ← HasQuery.query (spec := HashSpec)
        (tweakableHashInput parameter (.encoding epoch)
          (Concrete.encodingPayload message randomness))
      pure (truncateHash output)) := by
  unfold Concrete.encodingHash Concrete.tweakableHash Concrete.oracleHash
  rfl

theorem simulateQ_eagerTrace_query_pure_support_decompose
    {spec : OracleSpec ι} {State β : Type}
    (table : GlobalChainValueIndex → Digest)
    (implRun : ∀ input : spec.Domain, State →
      OracleComp GlobalFirstLaneWorld (spec.Range input × State))
    (input : spec.Domain) (finish : spec.Range input → β)
    (initialState : State)
    (result : (β × State) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun queryInput => StateT.mk (implRun queryInput)) (do
          let output ← (OracleSpec.query input :
            OracleComp spec (spec.Range input))
          pure (finish output))).run initialState)).run)) :
    ∃ queryHead : (spec.Range input × State) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex,
      queryHead ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (implRun input initialState)).run) ∧
      result = ((finish queryHead.1.1, queryHead.1.2), queryHead.2) := by
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind,
    WriterT.run_bind', mem_support_bind_iff] at hresult
  obtain ⟨queryHead, hquery, hrest⟩ := hresult
  rw [support_map] at hrest
  obtain ⟨tail, htail, rfl⟩ := hrest
  simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure',
    support_pure, Set.mem_singleton_iff] at htail
  subst tail
  rw [simulateQ_spec_query] at hquery
  refine ⟨queryHead, hquery, ?_⟩
  simp only [Prod.map_apply, id_eq]
  rw [show (∅ : FirstLaneOracleSimulation.ActionTrace
    GlobalChainValueIndex) = [] by rfl, List.append_nil]

theorem globalFirstLaneEncodingHash_support_decompose
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (epoch : Epoch) (message : Message) (randomness : Randomness)
    (initialState : GlobalCausalHashState)
    (result : (Digest × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun hashInput => StateT.mk
          (globalFirstLaneVerifierHashExecution keyView edgeHigh hashInput))
            (Concrete.encodingHash keyView.publicKey.parameter epoch message
              randomness : OracleComp HashSpec Digest)).run initialState)
                ).run)) :
    ∃ queryHead : (HashOutput × GlobalCausalHashState) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex,
      queryHead ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (globalFirstLaneVerifierHashExecution keyView edgeHigh
            (tweakableHashInput keyView.publicKey.parameter (.encoding epoch)
              (Concrete.encodingPayload message randomness)) initialState)).run) ∧
      result = ((truncateHash queryHead.1.1, queryHead.1.2), queryHead.2) := by
  rw [concreteEncodingHash_eq_query] at hresult
  exact simulateQ_eagerTrace_query_pure_support_decompose table
    (globalFirstLaneVerifierHashExecution keyView edgeHigh)
      (tweakableHashInput keyView.publicKey.parameter (.encoding epoch)
        (Concrete.encodingPayload message randomness)) truncateHash
      initialState result hresult

theorem globalFirstLaneVerifier_support_decompose_raw
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (forgery : Forgery) (initialState : GlobalCausalHashState)
    (result : (Bool × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (globalFirstLaneVerifierImpl keyView edgeHigh)
          (Concrete.scheme.verify keyView.publicKey forgery.epoch
            forgery.message forgery.signature)).run initialState)).run)) :
    ∃ (queryHead : (HashOutput × GlobalCausalHashState) ×
          FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
      (tail : (Bool × GlobalCausalHashState) ×
          FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex),
      queryHead ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (globalFirstLaneVerifierHashExecution keyView edgeHigh
            (tweakableHashInput keyView.publicKey.parameter
              (.encoding forgery.epoch)
              (Concrete.encodingPayload forgery.message
                forgery.signature.randomness)) initialState)).run) ∧
      tail ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          ((simulateQ (fun hashInput => StateT.mk
            (globalFirstLaneVerifierHashExecution keyView edgeHigh hashInput))
              (concreteVerificationAfterDigest keyView.publicKey forgery.epoch
                forgery.signature (truncateHash queryHead.1.1))).run
                  queryHead.1.2)).run) ∧
      result = (tail.1, queryHead.2 ++ tail.2) := by
  rw [globalFirstLaneVerifier_eq_hashExecution keyView edgeHigh forgery]
    at hresult
  rw [concreteVerify_eq_encodingHash_bind_afterDigest] at hresult
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind,
    WriterT.run_bind', mem_support_bind_iff] at hresult
  obtain ⟨head, hhead, htail⟩ := hresult
  rw [support_map] at htail
  obtain ⟨tail, htail, rfl⟩ := htail
  obtain ⟨queryHead, hquery, rfl⟩ :=
    globalFirstLaneEncodingHash_support_decompose table keyView edgeHigh
      forgery.epoch forgery.message forgery.signature.randomness initialState
        head hhead
  refine ⟨queryHead, tail, hquery, ?_, ?_⟩
  · simpa using htail
  · cases tail
    rfl

theorem globalFirstLaneVerifier_support_decompose
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (forgery : Forgery) (initialState : GlobalCausalHashState)
    (hparameter : keyView.publicKey.parameter = keyView.secretKey.parameter)
    (result : (Bool × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (globalFirstLaneVerifierImpl keyView edgeHigh)
          (Concrete.scheme.verify keyView.publicKey forgery.epoch
            forgery.message forgery.signature)).run initialState)).run)) :
    ∃ (queryHead : (HashOutput × GlobalCausalHashState) ×
          FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
      (tail : (Bool × GlobalCausalHashState) ×
          FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex),
      queryHead ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (globalFirstLaneAttackerHashQueryAtEpoch keyView.secretKey
            (Concrete.CacheView.encodingInput keyView.secretKey.parameter
              forgery.epoch
                (forgery.message, forgery.signature.randomness))
            initialState forgery.epoch)).run) ∧
      tail ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          ((simulateQ (fun hashInput => StateT.mk
            (globalFirstLaneVerifierHashExecution keyView edgeHigh hashInput))
              (concreteVerificationAfterDigest keyView.publicKey forgery.epoch
                forgery.signature (truncateHash queryHead.1.1))).run
                  queryHead.1.2)).run) ∧
      result = (tail.1, queryHead.2 ++ tail.2) := by
  obtain ⟨queryHead, tail, hquery, htail, hresultEq⟩ :=
    globalFirstLaneVerifier_support_decompose_raw table keyView edgeHigh
      forgery initialState result hresult
  let targetInput := Concrete.CacheView.encodingInput
    keyView.secretKey.parameter forgery.epoch
      (forgery.message, forgery.signature.randomness)
  have hqueryInput :
      tweakableHashInput keyView.publicKey.parameter
          (.encoding forgery.epoch)
          (Concrete.encodingPayload forgery.message
            forgery.signature.randomness) = targetInput := by
    simp [targetInput, Concrete.CacheView.encodingInput, hparameter]
  rw [hqueryInput] at hquery
  unfold globalFirstLaneVerifierHashExecution at hquery
  have hepoch : encodingInputEpoch? keyView.secretKey.parameter targetInput =
      some forgery.epoch := by
    simp [targetInput]
  rw [globalFirstLaneAttackerHashQueryFromHighRun_eq_some _ _ _ _
    forgery.epoch hepoch] at hquery
  refine ⟨queryHead, tail, ?_, htail, hresultEq⟩
  · simpa [targetInput] using hquery

theorem globalFirstLaneVerifier_freshEncoding_mem_trace
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (forgery : Forgery) (initialState : GlobalCausalHashState)
    (hparameter : keyView.publicKey.parameter = keyView.secretKey.parameter)
    (result : (Bool × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (targetOutput : HashOutput)
    (hfresh : initialState.cache
      (Concrete.CacheView.encodingInput keyView.secretKey.parameter
        forgery.epoch (forgery.message, forgery.signature.randomness)) = none)
    (hfinal : result.1.2.cache
      (Concrete.CacheView.encodingInput keyView.secretKey.parameter
        forgery.epoch (forgery.message, forgery.signature.randomness)) =
          some targetOutput)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (globalFirstLaneVerifierImpl keyView edgeHigh)
          (Concrete.scheme.verify keyView.publicKey forgery.epoch
            forgery.message forgery.signature)).run initialState)).run)) :
    .query forgery.epoch targetOutput ∈ result.2.encodingActions := by
  obtain ⟨queryHead, tail, hquery, htail, rfl⟩ :=
    globalFirstLaneVerifier_support_decompose table keyView edgeHigh forgery
      initialState hparameter result hresult
  let targetInput := Concrete.CacheView.encodingInput
    keyView.secretKey.parameter forgery.epoch
      (forgery.message, forgery.signature.randomness)
  have hcached := globalFirstLaneAttackerHashQueryAtEpoch_cache_eq_some
    table keyView.secretKey targetInput initialState forgery.epoch queryHead
      hquery
  have hqueryTrace := globalFirstLaneAttackerHashQueryAtEpoch_trace table
    keyView.secretKey targetInput initialState forgery.epoch queryHead hquery
  have hfresh' : initialState.cache targetInput = none := by
    simpa [targetInput] using hfresh
  have haction : EncodingMonitor.ObservedAction.query forgery.epoch
      queryHead.1.1 ∈ queryHead.2.encodingActions := by
    rw [hqueryTrace, if_pos hfresh']
    simp
  have htailLe := globalFirstLaneVerifierHashExecution_simulateQ_cache_le
    table keyView edgeHigh
      (concreteVerificationAfterDigest keyView.publicKey forgery.epoch
        forgery.signature (truncateHash queryHead.1.1))
      queryHead.1.2 tail htail
  have hfinal' : tail.1.2.cache targetInput = some targetOutput := by
    simpa [targetInput] using hfinal
  have hqueryFinal : tail.1.2.cache targetInput =
      some queryHead.1.1 := htailLe hcached
  have houtput : queryHead.1.1 = targetOutput :=
    Option.some.inj (hqueryFinal.symm.trans hfinal')
  rw [houtput] at haction
  have hfull : EncodingMonitor.ObservedAction.query forgery.epoch
      targetOutput ∈
        queryHead.2.encodingActions ++ tail.2.encodingActions :=
    List.mem_append_left tail.2.encodingActions haction
  simpa [FirstLaneOracleSimulation.ActionTrace.encodingActions_append] using
    hfull

theorem globalFirstLaneExactTracedVerifierImpl_run_eq_map
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : OracleWorld.Domain)
    (state : GlobalExactTracedState) :
    (globalFirstLaneExactTracedVerifierImpl keyView edgeHigh input).run state =
      (fun result => (result.1, state.withCausalState result.2)) <$>
        (globalFirstLaneVerifierImpl keyView edgeHigh input).run
          state.causalState := by
  unfold globalFirstLaneExactTracedVerifierImpl
  rfl

theorem globalFirstLaneExactTracedVerifier_simulateQ_run_eq_map
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (state : GlobalExactTracedState) :
    (simulateQ (globalFirstLaneExactTracedVerifierImpl keyView edgeHigh)
        computation).run state =
      (fun result => (result.1, state.withCausalState result.2)) <$>
        (simulateQ (globalFirstLaneVerifierImpl keyView edgeHigh)
          computation).run state.causalState := by
  exact globalExactTracedCausalLens.simulateQ_run_eq
    (globalFirstLaneExactTracedVerifierImpl keyView edgeHigh)
    (globalFirstLaneVerifierImpl keyView edgeHigh)
    (globalFirstLaneExactTracedVerifierImpl_run_eq_map keyView edgeHigh)
    computation state

theorem globalFirstLaneExactTracedVerifier_eager_support_decompose
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (state : GlobalExactTracedState)
    (result : (α × GlobalExactTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ
          (globalFirstLaneExactTracedVerifierImpl keyView edgeHigh)
            computation).run state)).run)) :
    ∃ baseResult : (α × GlobalCausalHashState) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex,
      baseResult ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          ((simulateQ (globalFirstLaneVerifierImpl keyView edgeHigh)
            computation).run state.causalState)).run) ∧
      result = ((baseResult.1.1, state.withCausalState baseResult.1.2),
        baseResult.2) := by
  rw [globalFirstLaneExactTracedVerifier_simulateQ_run_eq_map] at hresult
  rw [simulateQ_map, WriterT.run_map', support_map] at hresult
  obtain ⟨baseResult, hbase, heq⟩ := hresult
  exact ⟨baseResult, hbase, heq.symm⟩

theorem globalFirstLaneExactTracedDetailedExecution_trace_sublist
    (table : GlobalChainValueIndex → Digest)
    (adversary : Adversary)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (state : GlobalExactTracedState)
    (hparameter : keyView.publicKey.parameter = keyView.secretKey.parameter)
    (result : ((Forgery × Bool) × GlobalExactTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalFirstLaneExactTracedDetailedExecution adversary keyView
          edgeHigh).run state)).run)) :
    List.Sublist result.1.2.encodingTrace
      (state.encodingTrace ++ result.2.encodingActions) := by
  unfold globalFirstLaneExactTracedDetailedExecution at hresult
  rw [StateT.run_mk, simulateQ_bind, WriterT.run_bind',
    mem_support_bind_iff] at hresult
  obtain ⟨handled, hadversary, hrestMapped⟩ := hresult
  rw [support_map] at hrestMapped
  obtain ⟨verificationResult, hverificationBlock, hresultEq⟩ := hrestMapped
  rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff]
    at hverificationBlock
  obtain ⟨verified, hverify, hfinalMapped⟩ := hverificationBlock
  simp only [simulateQ_pure, WriterT.run_pure', map_pure, support_pure,
    Set.mem_singleton_iff, Prod.map_apply, id_eq] at hfinalMapped
  cases hfinalMapped
  cases hresultEq
  obtain ⟨baseVerified, hbaseVerify, hverifiedEq⟩ :=
    globalFirstLaneExactTracedVerifier_eager_support_decompose table keyView
      edgeHigh
      (Concrete.scheme.verify keyView.publicKey handled.1.1.epoch
        handled.1.1.message handled.1.1.signature)
      handled.1.2 verified hverify
  subst verified
  have hadversarySub :=
    globalFirstLaneExactTracedMappedAdversary_simulateQ_trace_sublist table
      keyView edgeHigh (adversary.main keyView.publicKey) state handled
        hadversary
  simp only [Prod.map_apply, id_eq]
  rw [show (∅ : FirstLaneOracleSimulation.ActionTrace
    GlobalChainValueIndex) = [] by rfl, List.append_nil]
  change List.Sublist
    (appendVerificationEncodingObservation keyView.secretKey handled.1.1
      handled.1.2.causalState.cache baseVerified.1.2.cache
        handled.1.2.encodingTrace)
    (state.encodingTrace ++
      (handled.2 ++ baseVerified.2).encodingActions)
  rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append]
  let forgedInput := Concrete.CacheView.encodingInput
    keyView.secretKey.parameter handled.1.1.epoch
      (handled.1.1.message, handled.1.1.signature.randomness)
  by_cases hfresh : handled.1.2.causalState.cache forgedInput = none
  · cases houtput : baseVerified.1.2.cache forgedInput with
    | none =>
        have hsub := hadversarySub.trans
          (List.sublist_append_left
            (state.encodingTrace ++ handled.2.encodingActions)
            baseVerified.2.encodingActions)
        simpa [appendVerificationEncodingObservation, forgedInput, hfresh,
          houtput, List.append_assoc] using hsub
    | some output =>
        have haction := globalFirstLaneVerifier_freshEncoding_mem_trace table
          keyView edgeHigh handled.1.1 handled.1.2.causalState hparameter
            baseVerified output (by simpa [forgedInput] using hfresh)
              (by simpa [forgedInput] using houtput) hbaseVerify
        have hsub := hadversarySub.append
          (List.singleton_sublist.mpr haction)
        simpa [appendVerificationEncodingObservation, forgedInput, hfresh,
          houtput, List.append_assoc] using hsub
  · have hsub := hadversarySub.trans
      (List.sublist_append_left
        (state.encodingTrace ++ handled.2.encodingActions)
        baseVerified.2.encodingActions)
    simpa [appendVerificationEncodingObservation, forgedInput, hfresh,
      List.append_assoc] using hsub

theorem CoupledGlobalChainKeygenView.toProgrammedView_parameter_eq
    (parameter : PublicParameter) (view : CoupledGlobalChainKeygenView) :
    (view.toProgrammedView parameter).publicKey.parameter =
      (view.toProgrammedView parameter).secretKey.parameter := by
  rfl

set_option maxHeartbeats 2000000 in
theorem globalHighDirectKeygen_support_parameter_eq
    (keyResult : GlobalHighDirectKeyResult)
    (hresult : keyResult ∈ support globalHighDirectKeygen) :
    keyResult.1.publicKey.parameter = keyResult.1.secretKey.parameter := by
  unfold globalHighDirectKeygen at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨parameter, _hparameter, hafterParameter⟩ := hresult
  unfold globalHighDirectKeygenAfterParameter at hafterParameter
  rw [mem_support_bind_iff] at hafterParameter
  obtain ⟨material, _hmaterial, hafterMaterial⟩ := hafterParameter
  rw [mem_support_bind_iff] at hafterMaterial
  obtain ⟨edgeHigh, _hedgeHigh, hkeygen⟩ := hafterMaterial
  unfold globalHighDirectKeygenAfterMaterial at hkeygen
  rw [mem_support_bind_iff] at hkeygen
  obtain ⟨tree, _htree, hpure⟩ := hkeygen
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  let view : CoupledGlobalChainKeygenView := {
    secret := material.1
    table := globalChainTrajectoryMaterialTable material
    values := tree.1
    cache := tree.2
  }
  have hconstructed : (view.toProgrammedView parameter, edgeHigh) =
      keyResult := by
    simpa [view] using hpure.symm
  have hview : view.toProgrammedView parameter = keyResult.1 :=
    congrArg Prod.fst hconstructed
  exact Eq.mp (congrArg (fun candidate : ProgrammedGlobalChainKeygenView =>
    candidate.publicKey.parameter = candidate.secretKey.parameter) hview)
      (CoupledGlobalChainKeygenView.toProgrammedView_parameter_eq parameter view)

theorem globalFirstLaneExactTracedProgram_trace_sublist
    (table : GlobalChainValueIndex → Digest)
    (adversary : Adversary)
    (result : GlobalExactTracedResult ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneExactTracedProgram adversary)).run)) :
    List.Sublist result.1.2.2.encodingTrace result.2.encodingActions := by
  unfold globalFirstLaneExactTracedProgram at hresult
  rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hresult
  obtain ⟨keyHead, hkeyHead, hrest⟩ := hresult
  rw [FirstLaneOracleSimulation.simulate_eagerTrace_liftProbComp] at hkeyHead
  rw [support_map] at hkeyHead
  obtain ⟨keyResult, hkeyResult, hkeyHeadEq⟩ := hkeyHead
  subst keyHead
  simp only [List.nil_append] at hrest
  rw [support_map] at hrest
  obtain ⟨execution, hexecution, hresultEq⟩ := hrest
  rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hexecution
  obtain ⟨detail, hdetail, hfinal⟩ := hexecution
  simp only [simulateQ_pure, WriterT.run_pure', map_pure, support_pure,
    Set.mem_singleton_iff, Prod.map_apply, id_eq] at hfinal
  subst execution
  subst result
  simpa using globalFirstLaneExactTracedDetailedExecution_trace_sublist table
    adversary keyResult.1 keyResult.2
      (GlobalExactTracedState.initial
        (globalFilteredCausalKeygenState keyResult.1))
      (globalHighDirectKeygen_support_parameter_eq keyResult hkeyResult)
      detail hdetail

theorem globalFirstLaneSigningAttempt_none_validSignEpochs_eq_nil
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneSigningAttempt keyView request state)).run))
    (hnone : result.1.1 = none) :
    CappedEncodingMonitor.validObservedSignEpochs
      result.2.encodingActions = [] := by
  have hvalid := globalFirstLaneSigningAttempt_validTrace table keyView request
    state result hresult
  unfold firstLaneValidEncodingActions at hvalid
  unfold CappedEncodingMonitor.validObservedSignEpochs
  rw [hvalid]
  simp [encodingActionTraceUpdate, encodingObservation?, hnone,
    CappedEncodingMonitor.validActions, EncodingMonitor.observedSignEpochs]

theorem globalFirstLaneSigningAttempt_validSignEpochs_sublist_singleton
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneSigningAttempt keyView request state)).run)) :
    List.Sublist (CappedEncodingMonitor.validObservedSignEpochs
      result.2.encodingActions) [request.epoch] := by
  have hvalid := globalFirstLaneSigningAttempt_validTrace table keyView request
    state result hresult
  unfold firstLaneValidEncodingActions at hvalid
  unfold CappedEncodingMonitor.validObservedSignEpochs
  rw [hvalid]
  cases houtput : result.1.1 with
  | none =>
      simp [encodingActionTraceUpdate, encodingObservation?,
        CappedEncodingMonitor.validActions,
        EncodingMonitor.observedSignEpochs]
  | some signature =>
      let input := Concrete.CacheView.encodingInput keyView.secretKey.parameter
        request.epoch (request.message, signature.randomness)
      by_cases hfresh : state.cache input = none
      · cases hfinal : result.1.2.cache input with
        | none =>
            simp [encodingActionTraceUpdate, encodingObservation?,
              input, hfresh, hfinal, CappedEncodingMonitor.validActions,
              EncodingMonitor.observedSignEpochs]
        | some output =>
            by_cases hvalidOutput : CappedEncodingMonitor.ActionValid
              (.sign request.epoch output)
            · simp [encodingActionTraceUpdate, encodingObservation?,
                input, hfresh, hfinal, CappedEncodingMonitor.validActions,
                EncodingMonitor.observedSignEpochs, hvalidOutput]
            · simp [encodingActionTraceUpdate, encodingObservation?,
                input, hfresh, hfinal, CappedEncodingMonitor.validActions,
                EncodingMonitor.observedSignEpochs, hvalidOutput]
      · simp [encodingActionTraceUpdate, encodingObservation?,
          input, hfresh, CappedEncodingMonitor.validActions,
          EncodingMonitor.observedSignEpochs]

theorem globalFirstLaneSignBoundedAttempts_validSignEpochs_sublist_singleton
    (attempts : Nat) (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneSignBoundedAttempts attempts keyView request state)
        ).run)) :
    List.Sublist (CappedEncodingMonitor.validObservedSignEpochs
      result.2.encodingActions) [request.epoch] := by
  induction attempts generalizing state result with
  | zero =>
      simp [globalFirstLaneSignBoundedAttempts] at hresult
      subst result
      simp [CappedEncodingMonitor.validObservedSignEpochs,
        FirstLaneOracleSimulation.ActionTrace.encodingActions,
        CappedEncodingMonitor.validActions,
        EncodingMonitor.observedSignEpochs]
  | succ attempts ih =>
      rw [globalFirstLaneSignBoundedAttempts, simulateQ_bind,
        WriterT.run_bind', mem_support_bind_iff] at hresult
      obtain ⟨attemptHead, hattempt, hcontinuation⟩ := hresult
      rw [support_map] at hcontinuation
      obtain ⟨tailResult, htail, hresultEq⟩ := hcontinuation
      have htraceEq : attemptHead.2 ++ tailResult.2 = result.2 := by
        simpa using congrArg Prod.snd hresultEq
      cases hoption : attemptHead.1.1 with
      | none =>
          have hattemptNil :=
            globalFirstLaneSigningAttempt_none_validSignEpochs_eq_nil table
              keyView request state attemptHead hattempt hoption
          have htailSub := ih attemptHead.1.2 tailResult (by
            simpa [hoption] using htail)
          rw [← htraceEq,
            FirstLaneOracleSimulation.ActionTrace.encodingActions_append,
            CappedEncodingMonitor.validObservedSignEpochs_append,
            hattemptNil]
          simpa using htailSub
      | some signature =>
          simp only [hoption] at htail
          subst tailResult
          have hattemptSub :=
            globalFirstLaneSigningAttempt_validSignEpochs_sublist_singleton table
              keyView request state attemptHead hattempt
          rw [← htraceEq,
            FirstLaneOracleSimulation.ActionTrace.encodingActions_append,
            CappedEncodingMonitor.validObservedSignEpochs_append]
          simpa [CappedEncodingMonitor.validObservedSignEpochs,
            FirstLaneOracleSimulation.ActionTrace.encodingActions,
            CappedEncodingMonitor.validActions,
            EncodingMonitor.observedSignEpochs] using hattemptSub

theorem globalFirstLaneSigningQuery_validSignEpochs_sublist_singleton
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneSigningQuery keyView request state)).run)) :
    List.Sublist (CappedEncodingMonitor.validObservedSignEpochs
      result.2.encodingActions) [request.epoch] := by
  exact globalFirstLaneSignBoundedAttempts_validSignEpochs_sublist_singleton
    signingAttemptLimit table keyView request state result hresult

theorem globalFirstLaneUniformImpl_run
    (n : Nat) (state : GlobalCausalHashState) :
    (globalFirstLaneUniformImpl n).run state = (do
      let output ← FirstLaneOracleSimulation.uniformQuery n
      pure (output, state)) := by
  rfl

theorem globalFirstLaneUniformImpl_validSignEpochs_eq_nil
    (table : GlobalChainValueIndex → Digest) (n : Nat)
    (state : GlobalCausalHashState)
    (result : (Fin (n + 1) × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalFirstLaneUniformImpl n).run state)).run)) :
    CappedEncodingMonitor.validObservedSignEpochs
      result.2.encodingActions = [] := by
  rw [globalFirstLaneUniformImpl_run] at hresult
  rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hresult
  obtain ⟨head, hhead, htail⟩ := hresult
  simp [FirstLaneOracleSimulation.uniformQuery,
    FirstLaneOracleSimulation.eagerTraceImpl,
    FirstLaneOracleSimulation.eagerImpl,
    FirstLaneOracleSimulation.traceFragment,
    QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hhead
  obtain ⟨output, _houtput, rfl⟩ := hhead
  simp only [simulateQ_pure, WriterT.run_pure', map_pure, support_pure,
    Set.mem_singleton_iff, Prod.map_apply, id_eq] at htail
  subst result
  simp [CappedEncodingMonitor.validObservedSignEpochs,
    FirstLaneOracleSimulation.ActionTrace.encodingActions,
    CappedEncodingMonitor.validActions,
    EncodingMonitor.observedSignEpochs]

theorem globalFirstLaneHashRun_validSignEpochs_eq_nil
    (table : GlobalChainValueIndex → Digest)
    (high : GlobalChainValueIndex → Digest) (secretKey : SecretKey)
    (input : HashInput) (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneAttackerHashQueryFromHighRun high secretKey input state)
        ).run)) :
    CappedEncodingMonitor.validObservedSignEpochs
      result.2.encodingActions = [] := by
  cases hepoch : encodingInputEpoch? secretKey.parameter input with
  | none =>
      rw [globalFirstLaneAttackerHashQueryFromHighRun_eq_none high secretKey
        input state hepoch] at hresult
      have htrace := globalFirstLaneLiftRevealProbe_encodingActions_eq_nil table
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run state)
          result hresult
      rw [htrace]
      simp [CappedEncodingMonitor.validObservedSignEpochs,
        CappedEncodingMonitor.validActions,
        EncodingMonitor.observedSignEpochs]
  | some epoch =>
      rw [globalFirstLaneAttackerHashQueryFromHighRun_eq_some high secretKey
        input state epoch hepoch] at hresult
      have htrace := globalFirstLaneAttackerHashQueryAtEpoch_trace table
        secretKey input state epoch result hresult
      rw [htrace]
      by_cases hfresh : state.cache input = none
      · by_cases hvalid : CappedEncodingMonitor.ActionValid
            (.query epoch result.1.1)
        · simp [hfresh, CappedEncodingMonitor.validObservedSignEpochs,
            CappedEncodingMonitor.validActions,
            EncodingMonitor.observedSignEpochs, hvalid]
        · simp [hfresh, CappedEncodingMonitor.validObservedSignEpochs,
            CappedEncodingMonitor.validActions,
            EncodingMonitor.observedSignEpochs, hvalid]
      · simp [hfresh, CappedEncodingMonitor.validObservedSignEpochs,
          CappedEncodingMonitor.validActions,
          EncodingMonitor.observedSignEpochs]

theorem globalExactTracedLift_eager_support_decompose
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (base : StateT GlobalCausalHashState (OracleComp GlobalFirstLaneWorld)
      ((OracleWorld + SigningSpec).Range input))
    (state : GlobalExactTracedState)
    (result : ((OracleWorld + SigningSpec).Range input ×
      GlobalExactTracedState) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalExactTracedLift keyView input base).run state)).run)) :
    ∃ baseResult : ((OracleWorld + SigningSpec).Range input ×
        GlobalCausalHashState) ×
          FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex,
      baseResult ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (base.run state.causalState)).run) ∧
      result = ((baseResult.1.1,
        globalExactTracedNextState keyView input state baseResult.1.1
          baseResult.1.2), baseResult.2) := by
  unfold globalExactTracedLift at hresult
  rw [StateT.run_mk, simulateQ_map, WriterT.run_map', support_map] at hresult
  obtain ⟨baseResult, hbase, heq⟩ := hresult
  exact ⟨baseResult, hbase, heq.symm⟩

theorem globalFirstLaneExactTracedMappedAdversaryImpl_hash_eq_run
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (input : HashInput) :
    globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh
        (.inl (.inr input)) =
      globalExactTracedLift keyView (.inl (.inr input))
        (StateT.mk (globalFirstLaneAttackerHashQueryFromHighRun
          (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey
            input)) := by
  rfl

theorem globalExactTracedHash_validSignEpochs_eq_nil
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : HashInput)
    (base : StateT GlobalCausalHashState (OracleComp GlobalFirstLaneWorld)
      HashOutput)
    (state : GlobalExactTracedState)
    (result : (HashOutput × GlobalExactTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalExactTracedLift keyView (.inl (.inr input)) base).run
          state)).run))
    (hnil : ∀ baseResult,
      baseResult ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (base.run state.causalState)).run) →
      CappedEncodingMonitor.validObservedSignEpochs
        baseResult.2.encodingActions = []) :
    CappedEncodingMonitor.validObservedSignEpochs
      result.2.encodingActions = [] := by
  obtain ⟨baseResult, hbase, hresultEq⟩ :=
    globalExactTracedLift_eager_support_decompose table keyView
      (.inl (.inr input)) base state result hresult
  have htraceEq := congrArg (fun candidate =>
    CappedEncodingMonitor.validObservedSignEpochs
      candidate.2.encodingActions) hresultEq
  exact htraceEq.trans (hnil baseResult hbase)

theorem globalExactTracedHash_validSignEpochs_step
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : HashInput)
    (base : StateT GlobalCausalHashState (OracleComp GlobalFirstLaneWorld)
      HashOutput)
    (state : GlobalExactTracedState)
    (result : (HashOutput × GlobalExactTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalExactTracedLift keyView (.inl (.inr input)) base).run
          state)).run))
    (hnil : ∀ baseResult,
      baseResult ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (base.run state.causalState)).run) →
      CappedEncodingMonitor.validObservedSignEpochs
        baseResult.2.encodingActions = []) :
    List.Sublist
      ((state.attackerTrace.toSigningLog.map
          fun entry => entry.1.epoch) ++
        CappedEncodingMonitor.validObservedSignEpochs
          result.2.encodingActions)
      (result.1.2.attackerTrace.toSigningLog.map
        fun entry => entry.1.epoch) := by
  have htrace :=
    globalExactTracedHash_validSignEpochs_eq_nil table keyView
      input base state result hresult hnil
  obtain ⟨_baseResult, _hbase, hresultEq⟩ :=
    globalExactTracedLift_eager_support_decompose table keyView
      (.inl (.inr input)) base state result hresult
  have hstateEq : result.1.2.attackerTrace =
      state.attackerTrace ++ [AttackerAction.hash input] := by
    have hstateEq' := congrArg (fun candidate =>
      candidate.1.2.attackerTrace) hresultEq
    simpa [globalExactTracedNextState, attackerActionFragment] using hstateEq'
  have hstate : result.1.2.attackerTrace.toSigningLog.map
      (fun entry => entry.1.epoch) =
      state.attackerTrace.toSigningLog.map (fun entry => entry.1.epoch) := by
    rw [hstateEq, AttackerActionTrace.toSigningLog_append, List.map_append]
    simp [AttackerActionTrace.toSigningLog, AttackerAction.signingEntry?]
  rw [htrace, List.append_nil, hstate]

theorem globalExactTracedLift_oracle_validSignEpochs_step
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (worldInput : OracleWorld.Domain)
    (base : StateT GlobalCausalHashState (OracleComp GlobalFirstLaneWorld)
      (OracleWorld.Range worldInput))
    (initialState : GlobalExactTracedState)
    (result : (OracleWorld.Range worldInput ×
      GlobalExactTracedState) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalExactTracedLift keyView (.inl worldInput) base).run
          initialState)).run))
    (hnil : ∀ baseResult,
      baseResult ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (base.run initialState.causalState)).run) →
      CappedEncodingMonitor.validObservedSignEpochs
        baseResult.2.encodingActions = []) :
    List.Sublist
      ((initialState.attackerTrace.toSigningLog.map
          fun entry => entry.1.epoch) ++
        CappedEncodingMonitor.validObservedSignEpochs
          result.2.encodingActions)
      (result.1.2.attackerTrace.toSigningLog.map
        fun entry => entry.1.epoch) := by
  obtain ⟨baseResult, hbase, hresultEq⟩ :=
    globalExactTracedLift_eager_support_decompose table keyView
      (.inl worldInput) base initialState result hresult
  have houtputEq : result.1.1 = baseResult.1.1 := by
    simpa using congrArg (fun candidate => candidate.1.1) hresultEq
  have hstate : result.1.2.attackerTrace =
      initialState.attackerTrace ++
        attackerActionFragment (.inl worldInput) result.1.1 := by
    have hstateEq := congrArg (fun candidate =>
      candidate.1.2.attackerTrace) hresultEq
    simpa [globalExactTracedNextState, houtputEq] using hstateEq
  have htrace : CappedEncodingMonitor.validObservedSignEpochs
      result.2.encodingActions = [] := by
    have htraceEq := congrArg (fun candidate =>
      CappedEncodingMonitor.validObservedSignEpochs
        candidate.2.encodingActions) hresultEq
    rw [htraceEq]
    exact hnil baseResult hbase
  rw [htrace, List.append_nil, hstate,
    AttackerActionTrace.toSigningLog_append, List.map_append]
  simp [attackerActionFragment, AttackerActionTrace.toSigningLog,
    AttackerAction.signingEntry?]

theorem globalExactTracedLift_signing_validSignEpochs_step
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest)
    (base : StateT GlobalCausalHashState (OracleComp GlobalFirstLaneWorld)
      (SigningSpec.Range request))
    (initialState : GlobalExactTracedState)
    (result : (SigningSpec.Range request × GlobalExactTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalExactTracedLift keyView (.inr request) base).run
          initialState)).run))
    (hsub : ∀ baseResult,
      baseResult ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (base.run initialState.causalState)).run) →
      List.Sublist (CappedEncodingMonitor.validObservedSignEpochs
        baseResult.2.encodingActions) [request.epoch]) :
    List.Sublist
      ((initialState.attackerTrace.toSigningLog.map
          fun entry => entry.1.epoch) ++
        CappedEncodingMonitor.validObservedSignEpochs
          result.2.encodingActions)
      (result.1.2.attackerTrace.toSigningLog.map
        fun entry => entry.1.epoch) := by
  obtain ⟨baseResult, hbase, hresultEq⟩ :=
    globalExactTracedLift_eager_support_decompose table keyView
      (.inr request) base initialState result hresult
  have houtputEq : result.1.1 = baseResult.1.1 := by
    simpa using congrArg (fun candidate => candidate.1.1) hresultEq
  have hstate : result.1.2.attackerTrace =
      initialState.attackerTrace ++
        attackerActionFragment (.inr request) result.1.1 := by
    have hstateEq := congrArg (fun candidate =>
      candidate.1.2.attackerTrace) hresultEq
    simpa [globalExactTracedNextState, houtputEq] using hstateEq
  have htraceSub : List.Sublist
      (CappedEncodingMonitor.validObservedSignEpochs
        result.2.encodingActions) [request.epoch] := by
    have htraceEq := congrArg (fun candidate =>
      CappedEncodingMonitor.validObservedSignEpochs
        candidate.2.encodingActions) hresultEq
    rw [htraceEq]
    exact hsub baseResult hbase
  have happended := (List.Sublist.refl
    (initialState.attackerTrace.toSigningLog.map
      fun entry => entry.1.epoch)).append htraceSub
  simpa [hstate, AttackerActionTrace.toSigningLog_append,
    attackerActionFragment, AttackerActionTrace.toSigningLog,
    AttackerAction.signingEntry?] using happended

theorem globalFirstLaneExactTracedMappedAdversaryImpl_uniform_validSignEpochs_step
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (n : Nat)
    (initialState : GlobalExactTracedState)
    (result : ((OracleWorld + SigningSpec).Range (.inl (.inl n)) ×
      GlobalExactTracedState) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh
          (.inl (.inl n))).run initialState)).run)) :
    List.Sublist
      ((initialState.attackerTrace.toSigningLog.map
          fun entry => entry.1.epoch) ++
        CappedEncodingMonitor.validObservedSignEpochs
          result.2.encodingActions)
      (result.1.2.attackerTrace.toSigningLog.map
        fun entry => entry.1.epoch) := by
  unfold globalFirstLaneExactTracedMappedAdversaryImpl
    globalFirstLaneExactTracedOracleImpl at hresult
  apply globalExactTracedLift_oracle_validSignEpochs_step table
    keyView (.inl n)
    (StateT.mk fun causalState =>
      globalFirstLaneOracleExecution keyView edgeHigh (.inl n) causalState)
    initialState result hresult
  intro baseResult hbase
  exact globalFirstLaneUniformImpl_validSignEpochs_eq_nil table n
    initialState.causalState baseResult hbase

theorem globalFirstLaneExactTracedMappedAdversaryImpl_signing_validSignEpochs_step
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (request : SignRequest)
    (initialState : GlobalExactTracedState)
    (result : ((OracleWorld + SigningSpec).Range (.inr request) ×
      GlobalExactTracedState) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh
          (.inr request)).run initialState)).run)) :
    List.Sublist
      ((initialState.attackerTrace.toSigningLog.map
          fun entry => entry.1.epoch) ++
        CappedEncodingMonitor.validObservedSignEpochs
          result.2.encodingActions)
      (result.1.2.attackerTrace.toSigningLog.map
        fun entry => entry.1.epoch) := by
  unfold globalFirstLaneExactTracedMappedAdversaryImpl
    globalFirstLaneExactTracedSigningImpl at hresult
  apply globalExactTracedLift_signing_validSignEpochs_step table
    keyView request (globalFirstLaneSigningImpl keyView request)
      initialState result hresult
  intro baseResult hbase
  exact globalFirstLaneSigningQuery_validSignEpochs_sublist_singleton table
    keyView request initialState.causalState baseResult hbase

theorem globalFirstLaneExactTracedMappedAdversary_validSignEpochs_sublist_of_hashRun
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (hashRun : HashInput → GlobalCausalHashState →
      OracleComp GlobalFirstLaneWorld (HashOutput × GlobalCausalHashState))
    (hhashEq : ∀ input,
      globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh
          (.inl (.inr input)) =
        globalExactTracedLift keyView (.inl (.inr input))
          (StateT.mk (hashRun input)))
    (hhashNil : ∀ input state result,
      result ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (hashRun input state)).run) →
      CappedEncodingMonitor.validObservedSignEpochs
        result.2.encodingActions = [])
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : GlobalExactTracedState)
    (result : (α × GlobalExactTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ
          (globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh)
            computation).run initialState)).run)) :
    List.Sublist
      ((initialState.attackerTrace.toSigningLog.map
          fun entry => entry.1.epoch) ++
        CappedEncodingMonitor.validObservedSignEpochs
          result.2.encodingActions)
      (result.1.2.attackerTrace.toSigningLog.map
        fun entry => entry.1.epoch) := by
  apply simulateQ_eagerTrace_support_invariant table
    (globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh)
    (fun initial trace final => List.Sublist
      ((initial.attackerTrace.toSigningLog.map fun entry => entry.1.epoch) ++
        CappedEncodingMonitor.validObservedSignEpochs trace.encodingActions)
      (final.attackerTrace.toSigningLog.map fun entry => entry.1.epoch))
  · intro state
    simp [CappedEncodingMonitor.validObservedSignEpochs,
      FirstLaneOracleSimulation.ActionTrace.encodingActions,
      CappedEncodingMonitor.validActions, EncodingMonitor.observedSignEpochs]
  · intro initial middle final headTrace tailTrace hhead htail
    rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append,
      CappedEncodingMonitor.validObservedSignEpochs_append]
    simpa [List.append_assoc] using
      (hhead.append (List.Sublist.refl
        (CappedEncodingMonitor.validObservedSignEpochs
          tailTrace.encodingActions))).trans htail
  · intro input state stepResult hstep
    cases input with
    | inl worldInput =>
        cases worldInput with
        | inl n =>
            exact
              globalFirstLaneExactTracedMappedAdversaryImpl_uniform_validSignEpochs_step
                table keyView edgeHigh n state stepResult hstep
        | inr hashInput =>
            rw [hhashEq] at hstep
            apply globalExactTracedHash_validSignEpochs_step table keyView
              hashInput (StateT.mk (hashRun hashInput)) state stepResult hstep
            intro baseResult hbase
            exact hhashNil hashInput state.causalState baseResult hbase
    | inr request =>
        exact
          globalFirstLaneExactTracedMappedAdversaryImpl_signing_validSignEpochs_step
            table keyView edgeHigh request state stepResult hstep
  · exact hresult

theorem globalFirstLaneExactTracedMappedAdversary_validSignEpochs_sublist
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : GlobalExactTracedState)
    (result : (α × GlobalExactTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ
          (globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh)
            computation).run initialState)).run)) :
    List.Sublist
      ((initialState.attackerTrace.toSigningLog.map
          fun entry => entry.1.epoch) ++
        CappedEncodingMonitor.validObservedSignEpochs
          result.2.encodingActions)
      (result.1.2.attackerTrace.toSigningLog.map
        fun entry => entry.1.epoch) := by
  exact
    globalFirstLaneExactTracedMappedAdversary_validSignEpochs_sublist_of_hashRun
      table keyView edgeHigh
        (globalFirstLaneAttackerHashQueryFromHighRun
          (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey)
        (globalFirstLaneExactTracedMappedAdversaryImpl_hash_eq_run keyView
          edgeHigh)
        (globalFirstLaneHashRun_validSignEpochs_eq_nil table
          (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey)
        computation initialState result hresult

theorem globalFirstLaneVerifierImpl_hash_eq_run
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (input : HashInput) :
    globalFirstLaneVerifierImpl keyView edgeHigh (.inr input) =
      StateT.mk (globalFirstLaneAttackerHashQueryFromHighRun
        (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey input) := by
  rfl

theorem globalFirstLaneVerifier_validSignEpochs_eq_nil_of_hashRun
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (hashRun : HashInput → GlobalCausalHashState →
      OracleComp GlobalFirstLaneWorld (HashOutput × GlobalCausalHashState))
    (hhashEq : ∀ input,
      globalFirstLaneVerifierImpl keyView edgeHigh (.inr input) =
        StateT.mk (hashRun input))
    (hhashNil : ∀ input state result,
      result ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (hashRun input state)).run) →
      CappedEncodingMonitor.validObservedSignEpochs
        result.2.encodingActions = [])
    (computation : OracleComp OracleWorld α)
    (state : GlobalCausalHashState)
    (result : (α × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (globalFirstLaneVerifierImpl keyView edgeHigh)
          computation).run state)).run)) :
    CappedEncodingMonitor.validObservedSignEpochs
      result.2.encodingActions = [] := by
  apply simulateQ_eagerTrace_support_invariant table
    (globalFirstLaneVerifierImpl keyView edgeHigh)
    (fun _initial trace _final =>
      CappedEncodingMonitor.validObservedSignEpochs
        trace.encodingActions = [])
  · intro state
    simp [CappedEncodingMonitor.validObservedSignEpochs,
      FirstLaneOracleSimulation.ActionTrace.encodingActions,
      CappedEncodingMonitor.validActions, EncodingMonitor.observedSignEpochs]
  · intro initial middle final headTrace tailTrace hhead htail
    simp [FirstLaneOracleSimulation.ActionTrace.encodingActions_append,
      CappedEncodingMonitor.validObservedSignEpochs_append, hhead, htail]
  · intro input state stepResult hstep
    cases input with
    | inl n =>
        unfold globalFirstLaneVerifierImpl globalFirstLaneOracleImpl
          globalFirstLaneOracleExecution at hstep
        exact globalFirstLaneUniformImpl_validSignEpochs_eq_nil table n state
          stepResult hstep
    | inr input =>
        rw [hhashEq] at hstep
        exact hhashNil input state stepResult hstep
  · exact hresult

theorem globalFirstLaneVerifier_validSignEpochs_eq_nil
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (state : GlobalCausalHashState)
    (result : (α × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (globalFirstLaneVerifierImpl keyView edgeHigh)
          computation).run state)).run)) :
    CappedEncodingMonitor.validObservedSignEpochs
      result.2.encodingActions = [] := by
  exact globalFirstLaneVerifier_validSignEpochs_eq_nil_of_hashRun table
    keyView edgeHigh
      (globalFirstLaneAttackerHashQueryFromHighRun
        (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey)
      (globalFirstLaneVerifierImpl_hash_eq_run keyView edgeHigh)
      (globalFirstLaneHashRun_validSignEpochs_eq_nil table
        (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey)
      computation state result hresult

theorem globalFirstLaneExactTracedVerifier_validSignEpochs_eq_nil
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (state : GlobalExactTracedState)
    (result : (α × GlobalExactTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ
          (globalFirstLaneExactTracedVerifierImpl keyView edgeHigh)
            computation).run state)).run)) :
    CappedEncodingMonitor.validObservedSignEpochs
      result.2.encodingActions = [] := by
  obtain ⟨baseResult, hbase, hresultEq⟩ :=
    globalFirstLaneExactTracedVerifier_eager_support_decompose table keyView
      edgeHigh computation state result hresult
  have htraceEq := congrArg (fun candidate =>
    CappedEncodingMonitor.validObservedSignEpochs
      candidate.2.encodingActions) hresultEq
  exact htraceEq.trans
    (globalFirstLaneVerifier_validSignEpochs_eq_nil table keyView edgeHigh
      computation state.causalState baseResult hbase)

theorem globalFirstLaneExactTracedDetailedExecution_validSignEpochs_sublist
    (table : GlobalChainValueIndex → Digest)
    (adversary : Adversary)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (state : GlobalExactTracedState)
    (result : ((Forgery × Bool) × GlobalExactTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalFirstLaneExactTracedDetailedExecution adversary keyView
          edgeHigh).run state)).run)) :
    List.Sublist
      ((state.attackerTrace.toSigningLog.map
          fun entry => entry.1.epoch) ++
        CappedEncodingMonitor.validObservedSignEpochs
          result.2.encodingActions)
      (result.1.2.attackerTrace.toSigningLog.map
        fun entry => entry.1.epoch) := by
  unfold globalFirstLaneExactTracedDetailedExecution at hresult
  rw [StateT.run_mk, simulateQ_bind, WriterT.run_bind',
    mem_support_bind_iff] at hresult
  obtain ⟨handled, hadversary, hrestMapped⟩ := hresult
  rw [support_map] at hrestMapped
  obtain ⟨verificationResult, hverificationBlock, hresultEq⟩ := hrestMapped
  rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff]
    at hverificationBlock
  obtain ⟨verified, hverify, hfinalMapped⟩ := hverificationBlock
  simp only [simulateQ_pure, WriterT.run_pure', map_pure, support_pure,
    Set.mem_singleton_iff, Prod.map_apply, id_eq] at hfinalMapped
  cases hfinalMapped
  cases hresultEq
  have hadversarySub :=
    globalFirstLaneExactTracedMappedAdversary_validSignEpochs_sublist table
      keyView edgeHigh (adversary.main keyView.publicKey) state handled
        hadversary
  have hverifierNil :=
    globalFirstLaneExactTracedVerifier_validSignEpochs_eq_nil table keyView
      edgeHigh
      (Concrete.scheme.verify keyView.publicKey handled.1.1.epoch
        handled.1.1.message handled.1.1.signature)
      handled.1.2 verified hverify
  obtain ⟨_baseVerified, _hbaseVerify, hverifiedEq⟩ :=
    globalFirstLaneExactTracedVerifier_eager_support_decompose table keyView
      edgeHigh
      (Concrete.scheme.verify keyView.publicKey handled.1.1.epoch
        handled.1.1.message handled.1.1.signature)
      handled.1.2 verified hverify
  have hstate : verified.1.2.attackerTrace =
      handled.1.2.attackerTrace := by
    have hstateEq := congrArg (fun candidate =>
      candidate.1.2.attackerTrace) hverifiedEq
    simpa using hstateEq
  simpa [FirstLaneOracleSimulation.ActionTrace.encodingActions_append,
    CappedEncodingMonitor.validObservedSignEpochs_append, hverifierNil,
    hstate, List.append_nil] using hadversarySub

theorem globalFirstLaneExactTracedProgram_validSignEpochs_sublist
    (table : GlobalChainValueIndex → Digest)
    (adversary : Adversary)
    (result : GlobalExactTracedResult ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneExactTracedProgram adversary)).run)) :
    List.Sublist
      (CappedEncodingMonitor.validObservedSignEpochs
        result.2.encodingActions)
      (result.1.2.2.attackerTrace.toSigningLog.map
        fun entry => entry.1.epoch) := by
  unfold globalFirstLaneExactTracedProgram at hresult
  rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hresult
  obtain ⟨keyHead, hkeyHead, hrest⟩ := hresult
  rw [FirstLaneOracleSimulation.simulate_eagerTrace_liftProbComp] at hkeyHead
  rw [support_map] at hkeyHead
  obtain ⟨keyResult, _hkeyResult, hkeyHeadEq⟩ := hkeyHead
  subst keyHead
  simp only [List.nil_append] at hrest
  rw [support_map] at hrest
  obtain ⟨execution, hexecution, hresultEq⟩ := hrest
  rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hexecution
  obtain ⟨detail, hdetail, hfinal⟩ := hexecution
  simp only [simulateQ_pure, WriterT.run_pure', map_pure, support_pure,
    Set.mem_singleton_iff, Prod.map_apply, id_eq] at hfinal
  subst execution
  subst result
  simpa [AttackerActionTrace.toSigningLog] using
    globalFirstLaneExactTracedDetailedExecution_validSignEpochs_sublist table
      adversary keyResult.1 keyResult.2
        (GlobalExactTracedState.initial
          (globalFilteredCausalKeygenState keyResult.1)) detail hdetail

end XmssSecurity.CappedChain
