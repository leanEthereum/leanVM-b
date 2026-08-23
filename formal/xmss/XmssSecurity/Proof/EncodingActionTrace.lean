import XmssSecurity.Proof.AdaptiveEpochCollision
import XmssSecurity.Proof.EncodingTargetMap
import XmssSecurity.Proof.SigningCacheTrace

open OracleComp OracleSpec

namespace XmssSecurity

set_option maxRecDepth 100000

abbrev EncodingActionTrace := List EncodingMonitor.ObservedAction

def SigningCacheTrace.epochs (trace : SigningCacheTrace) : List Epoch :=
  trace.map fun entry => entry.request.epoch

@[simp]
theorem SigningCacheTrace.epochs_append
    (left right : SigningCacheTrace) :
    (left ++ right).epochs = left.epochs ++ right.epochs := by
  simp [SigningCacheTrace.epochs]

def FreshSigningActionsRepresented
    (secretKey : SecretKey) (signingTrace : SigningCacheTrace)
    (actions : EncodingActionTrace) : Prop :=
  ∀ entry ∈ signingTrace, ∀ signature, entry.signature = some signature →
    entry.initialCache
        (Concrete.CacheView.encodingInput secretKey.parameter entry.request.epoch
          (entry.request.message, signature.randomness)) = none →
    ∃ output before after,
      entry.finalCache
          (Concrete.CacheView.encodingInput secretKey.parameter entry.request.epoch
            (entry.request.message, signature.randomness)) = some output ∧
      actions = before ++ [.sign entry.request.epoch output] ++ after

def UnsignedEncodingEntriesRepresented
    (parameter : PublicParameter)
    (baseCache currentCache : QueryCache HashSpec)
    (signingTrace : SigningCacheTrace) (actions : EncodingActionTrace) : Prop :=
  ∀ epoch, epoch ∉ signingTrace.epochs → ∀ input output,
    encodingInputEpoch? parameter input = some epoch →
    baseCache input = none → currentCache input = some output →
    ∃ before after,
      actions = before ++ [.query epoch output] ++ after

def PostSigningQueriesRepresented
    (secretKey : SecretKey) (signingTrace : SigningCacheTrace)
    (currentCache : QueryCache HashSpec) (actions : EncodingActionTrace) : Prop :=
  signingTrace.epochs.Nodup →
    ∀ entry ∈ signingTrace, ∀ signature signedOutput targetInput targetOutput,
      entry.signature = some signature →
      entry.initialCache
          (Concrete.CacheView.encodingInput secretKey.parameter entry.request.epoch
            (entry.request.message, signature.randomness)) = none →
      entry.finalCache
          (Concrete.CacheView.encodingInput secretKey.parameter entry.request.epoch
            (entry.request.message, signature.randomness)) = some signedOutput →
      encodingInputEpoch? secretKey.parameter targetInput = some entry.request.epoch →
      entry.finalCache targetInput = none → currentCache targetInput = some targetOutput →
      ∃ before middle after,
        actions = before ++ [.sign entry.request.epoch signedOutput] ++ middle ++
          [.query entry.request.epoch targetOutput] ++ after

theorem UnsignedEncodingEntriesRepresented.refl
    (parameter : PublicParameter) (cache : QueryCache HashSpec) :
    UnsignedEncodingEntriesRepresented parameter cache cache [] [] := by
  intro epoch _ input output _ hfresh hcached
  rw [hfresh] at hcached
  cases hcached

theorem FreshSigningActionsRepresented.append_actions
    {secretKey : SecretKey} {signingTrace : SigningCacheTrace}
    {actions : EncodingActionTrace}
    (hrepresented : FreshSigningActionsRepresented secretKey signingTrace actions)
    (suffix : EncodingActionTrace) :
    FreshSigningActionsRepresented secretKey signingTrace (actions ++ suffix) := by
  intro entry hentry signature hsignature hfresh
  obtain ⟨output, before, after, houtput, hactions⟩ :=
    hrepresented entry hentry signature hsignature hfresh
  refine ⟨output, before, after ++ suffix, houtput, ?_⟩
  rw [hactions]
  simp [List.append_assoc]

noncomputable def encodingObservation?
    (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : QueryCache HashSpec × SigningCacheTrace)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalState : QueryCache HashSpec × SigningCacheTrace) :
    Option EncodingMonitor.ObservedAction := by
  classical
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput => exact none
      | inr hashInput =>
          exact if initialState.1 hashInput = none then
            match encodingInputEpoch? secretKey.parameter hashInput with
            | none => none
            | some epoch => some (.query epoch output)
          else
            none
  | inr request =>
      exact match output with
      | none => none
      | some signature =>
          let input := Concrete.CacheView.encodingInput secretKey.parameter request.epoch
            (request.message, signature.randomness)
          if initialState.1 input = none then
            match finalState.1 input with
            | none => none
            | some hashOutput => some (.sign request.epoch hashOutput)
          else
            none

noncomputable def encodingActionTraceUpdate
    (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : QueryCache HashSpec × SigningCacheTrace)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalState : QueryCache HashSpec × SigningCacheTrace)
    (trace : EncodingActionTrace) : EncodingActionTrace :=
  match encodingObservation? secretKey input initialState output finalState with
  | none => trace
  | some observation => trace ++ [observation]

noncomputable def encodingTracedLiftOf
    {m : Type → Type} [Monad m]
    (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (baseState : σ → τ)
    (encodingTrace : σ → EncodingActionTrace)
    (set : σ → τ → EncodingActionTrace → σ)
    (cache : τ → QueryCache HashSpec)
    (base : StateT τ m ((OracleWorld + SigningSpec).Range input)) :
    StateT σ m
      ((OracleWorld + SigningSpec).Range input) :=
  StateT.mk fun initial =>
    (fun result => (result.1, set initial result.2
      (encodingActionTraceUpdate secretKey input
        (cache (baseState initial), []) result.1 (cache result.2, [])
          (encodingTrace initial)))) <$>
      base.run (baseState initial)

noncomputable def encodingTracedLift
    {m : Type → Type} [Monad m]
    (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (cache : σ → QueryCache HashSpec)
    (base : StateT σ m ((OracleWorld + SigningSpec).Range input)) :
    StateT (σ × EncodingActionTrace) m
      ((OracleWorld + SigningSpec).Range input) :=
  encodingTracedLiftOf secretKey input Prod.fst Prod.snd
    (fun _ next trace => (next, trace)) cache base

@[simp]
theorem encodingTracedLift_run
    {m : Type → Type} [Monad m]
    (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (cache : σ → QueryCache HashSpec)
    (base : StateT σ m ((OracleWorld + SigningSpec).Range input))
    (initial : σ × EncodingActionTrace) :
    (encodingTracedLift secretKey input cache base).run initial =
      (fun result => (result.1, (result.2,
        encodingActionTraceUpdate secretKey input
          (cache initial.1, []) result.1 (cache result.2, []) initial.2))) <$>
        base.run initial.1 := by
  rfl

theorem encodingActionTraceUpdate_eq_or_append
    (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : QueryCache HashSpec × SigningCacheTrace)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalState : QueryCache HashSpec × SigningCacheTrace)
    (trace : EncodingActionTrace) :
    encodingActionTraceUpdate secretKey input initialState output finalState trace = trace ∨
      ∃ observation,
        encodingActionTraceUpdate secretKey input initialState output finalState trace =
          trace ++ [observation] := by
  unfold encodingActionTraceUpdate
  split
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

theorem encodingActionTraceUpdate_signEpochs_sublist
    (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : QueryCache HashSpec × SigningCacheTrace)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalState : QueryCache HashSpec × SigningCacheTrace)
    (trace : EncodingActionTrace)
    (hfinalTrace : finalState.2 = signingCacheTraceUpdate input initialState.1 output
      finalState.1 initialState.2)
    (hsublist : List.Sublist (EncodingMonitor.observedSignEpochs trace)
      initialState.2.epochs) :
    List.Sublist (EncodingMonitor.observedSignEpochs
        (encodingActionTraceUpdate secretKey input initialState output finalState trace))
      finalState.2.epochs := by
  classical
  cases input with
  | inl worldInput =>
      rw [hfinalTrace]
      cases worldInput with
      | inl uniformInput =>
          simpa [encodingActionTraceUpdate, encodingObservation?,
            signingCacheTraceUpdate, SigningCacheTrace.epochs] using hsublist
      | inr hashInput =>
          by_cases hfresh : initialState.1 hashInput = none
          · cases hepoch : encodingInputEpoch? secretKey.parameter hashInput with
            | none =>
                simpa [encodingActionTraceUpdate, encodingObservation?, hfresh, hepoch,
                  signingCacheTraceUpdate, SigningCacheTrace.epochs] using hsublist
            | some epoch =>
                simpa [encodingActionTraceUpdate, encodingObservation?, hfresh, hepoch,
                  signingCacheTraceUpdate, SigningCacheTrace.epochs,
                  EncodingMonitor.observedSignEpochs] using hsublist
          · simpa [encodingActionTraceUpdate, encodingObservation?, hfresh,
              signingCacheTraceUpdate, SigningCacheTrace.epochs] using hsublist
  | inr request =>
      rw [hfinalTrace]
      cases output with
      | none =>
          have hbase := hsublist.trans
            (List.sublist_append_left initialState.2.epochs [request.epoch])
          simpa [encodingActionTraceUpdate, encodingObservation?,
            signingCacheTraceUpdate, SigningCacheTrace.epochs] using hbase
      | some signature =>
          let signedInput := Concrete.CacheView.encodingInput secretKey.parameter
            request.epoch (request.message, signature.randomness)
          by_cases hfresh : initialState.1 signedInput = none
          · cases houtput : finalState.1 signedInput with
            | none =>
                have hbase := hsublist.trans
                  (List.sublist_append_left initialState.2.epochs [request.epoch])
                simpa [encodingActionTraceUpdate, encodingObservation?, signedInput,
                  hfresh, houtput, signingCacheTraceUpdate,
                  SigningCacheTrace.epochs] using hbase
            | some hashOutput =>
                have happend : List.Sublist
                    (EncodingMonitor.observedSignEpochs trace ++ [request.epoch])
                      (initialState.2.epochs ++ [request.epoch]) :=
                  hsublist.append (List.Sublist.refl [request.epoch])
                simpa [encodingActionTraceUpdate, encodingObservation?, signedInput,
                  hfresh, houtput, signingCacheTraceUpdate, SigningCacheTrace.epochs,
                  EncodingMonitor.observedSignEpochs] using happend
          · have hbase := hsublist.trans
                (List.sublist_append_left initialState.2.epochs [request.epoch])
            simpa [encodingActionTraceUpdate, encodingObservation?, signedInput,
              hfresh, signingCacheTraceUpdate, SigningCacheTrace.epochs] using hbase

def appendVerificationEncodingObservation
    (secretKey : SecretKey) (forgery : Forgery)
    (initialCache finalCache : QueryCache HashSpec)
    (trace : EncodingActionTrace) : EncodingActionTrace :=
  let input := Concrete.CacheView.encodingInput secretKey.parameter forgery.epoch
    (forgery.message, forgery.signature.randomness)
  if initialCache input = none then
    match finalCache input with
    | none => trace
    | some output => trace ++ [.query forgery.epoch output]
  else
    trace

end XmssSecurity
