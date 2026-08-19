import XmssSecurity.Proof.CappedGlobalFirstLaneErasure
import XmssSecurity.Proof.CappedEncodingActionTrace
import XmssSecurity.Proof.CappedGlobalChainHighPublicHit

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

def hashOutputOfDigest (digest : Digest) : HashOutput :=
  digest.zeroExtend hashOutputBits

@[simp]
theorem truncateHash_hashOutputOfDigest (digest : Digest) :
    truncateHash (hashOutputOfDigest digest) = digest := by
  apply BitVec.eq_of_getLsbD_eq
  intro index
  by_cases hi : index < digestBits
  · have hwide : index < digestBits + digestBits :=
      lt_of_lt_of_le hi (Nat.le_add_right digestBits digestBits)
    simp [hashOutputOfDigest, truncateHash, splitHashOutput, hwide,
      BitVec.getLsbD, hi]
  · simp [hashOutputOfDigest, truncateHash, splitHashOutput,
      BitVec.getLsbD, hi]

def normalizedEncodingAction : EncodingMonitor.ObservedAction →
    EncodingMonitor.ObservedAction
  | .query epoch output =>
      .query epoch (hashOutputOfDigest (truncateHash output))
  | .sign epoch output =>
      .sign epoch (hashOutputOfDigest (truncateHash output))

def normalizedEncodingTrace (trace : EncodingActionTrace) :
    EncodingActionTrace :=
  trace.map normalizedEncodingAction

theorem cappedEncodingApplyObserved_normalizedEncodingAction
    (state : EncodingMonitor.State)
    (action : EncodingMonitor.ObservedAction) :
    CappedEncodingMonitor.State.applyObserved state
        (normalizedEncodingAction action) =
      CappedEncodingMonitor.State.applyObserved state action := by
  cases action with
  | query epoch output =>
      simp only [normalizedEncodingAction,
        CappedEncodingMonitor.State.applyObserved,
        truncateHash_hashOutputOfDigest]
  | sign epoch output =>
      simp only [normalizedEncodingAction,
        CappedEncodingMonitor.State.applyObserved,
        truncateHash_hashOutputOfDigest]

theorem cappedEncodingRunObserved_normalizedEncodingTrace
    (state : EncodingMonitor.State) (trace : EncodingActionTrace) :
    CappedEncodingMonitor.runObserved state (normalizedEncodingTrace trace) =
      CappedEncodingMonitor.runObserved state trace := by
  induction trace generalizing state with
  | nil => rfl
  | cons action trace ih =>
      rw [normalizedEncodingTrace, List.map_cons]
      simp only [CappedEncodingMonitor.runObserved]
      rw [cappedEncodingApplyObserved_normalizedEncodingAction]
      cases happly : CappedEncodingMonitor.State.applyObserved state action with
      | none => rfl
      | some result =>
          rcases result with ⟨nextState, hit⟩
          simp only
          change (hit || CappedEncodingMonitor.runObserved nextState
              (normalizedEncodingTrace trace)) = _
          rw [ih]

def reconstructedHashEncodingActionFrom
    (epoch : Option Epoch) (digest : Digest) :
    Option EncodingMonitor.ObservedAction :=
  epoch.map fun epoch => .query epoch (hashOutputOfDigest digest)

noncomputable def reconstructedHashEncodingAction?
    (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (input : HashInput) : Option EncodingMonitor.ObservedAction :=
  reconstructedHashEncodingActionFrom
    (encodingInputEpoch? parameter input)
    (Concrete.CacheView.digestAt cache input)

noncomputable def reconstructedSignEncodingAction?
    (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (request : SignRequest) (signature : Signature) :
    Option EncodingMonitor.ObservedAction :=
  let input := Concrete.CacheView.encodingInput parameter request.epoch
    (request.message, signature.randomness)
  some (.sign request.epoch
    (hashOutputOfDigest (Concrete.CacheView.digestAt cache input)))

noncomputable def reconstructedAttackerEncodingAction?
    (parameter : PublicParameter) (cache : QueryCache HashSpec) :
    AttackerAction → Option EncodingMonitor.ObservedAction
  | .hash input => reconstructedHashEncodingAction? parameter cache input
  | .sign _request none => none
  | .sign request (some signature) =>
      reconstructedSignEncodingAction? parameter cache request signature

noncomputable def reconstructedAttackerEncodingTrace
    (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (trace : AttackerActionTrace) : EncodingActionTrace :=
  trace.filterMap (reconstructedAttackerEncodingAction? parameter cache)

def EncodingActionReconstructedBy
    (parameter : PublicParameter) (cache : QueryCache HashSpec) :
    EncodingMonitor.ObservedAction → AttackerAction → Prop
  | .query epoch output, .hash input =>
      encodingInputEpoch? parameter input = some epoch ∧
        ∃ cached, cache input = some cached ∧
          truncateHash output = truncateHash cached
  | .sign epoch output, .sign request (some signature) =>
      epoch = request.epoch ∧
        ∃ cached,
          cache (Concrete.CacheView.encodingInput parameter request.epoch
            (request.message, signature.randomness)) = some cached ∧
          truncateHash output = truncateHash cached
  | _, _ => False

def EncodingTraceReconstructedBy
    (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (encodingTrace : EncodingActionTrace)
    (attackerTrace : AttackerActionTrace) : Prop :=
  List.SublistForall₂ (EncodingActionReconstructedBy parameter cache)
    encodingTrace attackerTrace

theorem EncodingActionReconstructedBy.mono
    {parameter : PublicParameter} {left right : QueryCache HashSpec}
    (hle : left ≤ right) {encodingAction : EncodingMonitor.ObservedAction}
    {attackerAction : AttackerAction}
    (hrel : EncodingActionReconstructedBy parameter left encodingAction
      attackerAction) :
    EncodingActionReconstructedBy parameter right encodingAction
      attackerAction := by
  cases encodingAction with
  | query epoch output =>
      cases attackerAction with
      | hash input =>
          obtain ⟨hepoch, cached, hcached, hdigest⟩ := hrel
          exact ⟨hepoch, cached, hle hcached, hdigest⟩
      | sign request signature => cases hrel
  | sign epoch output =>
      cases attackerAction with
      | hash input => cases hrel
      | sign request signature =>
          cases signature with
          | none => cases hrel
          | some signature =>
              obtain ⟨hepoch, cached, hcached, hdigest⟩ := hrel
              exact ⟨hepoch, cached, hle hcached, hdigest⟩

theorem EncodingTraceReconstructedBy.mono
    {parameter : PublicParameter} {left right : QueryCache HashSpec}
    (hle : left ≤ right) {encodingTrace : EncodingActionTrace}
    {attackerTrace : AttackerActionTrace}
    (hrel : EncodingTraceReconstructedBy parameter left encodingTrace
      attackerTrace) :
    EncodingTraceReconstructedBy parameter right encodingTrace
      attackerTrace := by
  induction hrel with
  | nil => exact List.SublistForall₂.nil
  | cons hhead htail ih =>
      exact List.SublistForall₂.cons (hhead.mono hle) ih
  | cons_right htail ih =>
      exact List.SublistForall₂.cons_right ih

theorem EncodingTraceReconstructedBy.append_right
    {parameter : PublicParameter} {cache : QueryCache HashSpec}
    {encodingTrace : EncodingActionTrace}
    {attackerTrace : AttackerActionTrace}
    (hrel : EncodingTraceReconstructedBy parameter cache encodingTrace
      attackerTrace) (suffix : AttackerActionTrace) :
    EncodingTraceReconstructedBy parameter cache encodingTrace
      (attackerTrace ++ suffix) := by
  rw [EncodingTraceReconstructedBy, List.sublistForall₂_iff] at hrel ⊢
  obtain ⟨witness, hfor, hsub⟩ := hrel
  exact ⟨witness, hfor,
    hsub.trans (List.sublist_append_left attackerTrace suffix)⟩

theorem EncodingTraceReconstructedBy.snoc
    {parameter : PublicParameter} {cache : QueryCache HashSpec}
    {encodingTrace : EncodingActionTrace}
    {attackerTrace : AttackerActionTrace}
    (hrel : EncodingTraceReconstructedBy parameter cache encodingTrace
      attackerTrace)
    {encodingAction : EncodingMonitor.ObservedAction}
    {attackerAction : AttackerAction}
    (haction : EncodingActionReconstructedBy parameter cache encodingAction
      attackerAction) :
    EncodingTraceReconstructedBy parameter cache
      (encodingTrace ++ [encodingAction])
      (attackerTrace ++ [attackerAction]) := by
  rw [EncodingTraceReconstructedBy, List.sublistForall₂_iff] at hrel ⊢
  obtain ⟨witness, hfor, hsub⟩ := hrel
  refine ⟨witness ++ [attackerAction],
    List.rel_append hfor (List.Forall₂.cons haction List.Forall₂.nil), ?_⟩
  exact hsub.append (List.Sublist.refl [attackerAction])

theorem EncodingActionReconstructedBy.reconstructed_eq
    {parameter : PublicParameter} {cache : QueryCache HashSpec}
    {encodingAction : EncodingMonitor.ObservedAction}
    {attackerAction : AttackerAction}
    (hrel : EncodingActionReconstructedBy parameter cache encodingAction
      attackerAction) :
    reconstructedAttackerEncodingAction? parameter cache attackerAction =
      some (normalizedEncodingAction encodingAction) := by
  cases encodingAction with
  | query epoch output =>
      cases attackerAction with
      | hash input =>
          obtain ⟨hepoch, cached, hcached, hdigest⟩ := hrel
          have hview : Concrete.CacheView.digestAt cache input =
              truncateHash cached :=
            Concrete.CacheView.digestAt_eq_of_cache_eq_some hcached
          simp only [reconstructedAttackerEncodingAction?,
            reconstructedHashEncodingAction?, hepoch,
            reconstructedHashEncodingActionFrom, Option.map_some,
            normalizedEncodingAction, Option.some.injEq]
          rw [hview, hdigest]
      | sign request signature => cases hrel
  | sign epoch output =>
      cases attackerAction with
      | hash input => cases hrel
      | sign request signature =>
          cases signature with
          | none => cases hrel
          | some signature =>
              obtain ⟨hepoch, cached, hcached, hdigest⟩ := hrel
              subst epoch
              have hview : Concrete.CacheView.digestAt cache
                    (Concrete.CacheView.encodingInput parameter request.epoch
                      (request.message, signature.randomness)) =
                  truncateHash cached :=
                Concrete.CacheView.digestAt_eq_of_cache_eq_some hcached
              simp only [reconstructedAttackerEncodingAction?,
                reconstructedSignEncodingAction?, normalizedEncodingAction,
                Option.some.injEq]
              rw [hview, hdigest]

theorem EncodingTraceReconstructedBy.normalized_sublist
    {parameter : PublicParameter} {cache : QueryCache HashSpec}
    {encodingTrace : EncodingActionTrace}
    {attackerTrace : AttackerActionTrace}
    (hrel : EncodingTraceReconstructedBy parameter cache encodingTrace
      attackerTrace) :
    (normalizedEncodingTrace encodingTrace).Sublist
      (reconstructedAttackerEncodingTrace parameter cache attackerTrace) := by
  induction hrel with
  | nil => exact List.nil_sublist _
  | @cons encodingAction attackerAction encodingTrace attackerTrace
      hhead htail ih =>
      unfold normalizedEncodingTrace reconstructedAttackerEncodingTrace
      simp only [List.map_cons, List.filterMap_cons, hhead.reconstructed_eq]
      exact ih.cons_cons _
  | @cons_right attackerAction encodingTrace attackerTrace htail ih =>
      unfold reconstructedAttackerEncodingTrace
      simp only [List.filterMap_cons]
      cases reconstructedAttackerEncodingAction? parameter cache attackerAction with
      | none => exact ih
      | some action => exact ih.cons action

theorem encodingObservation?_reconstructedBy
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState finalState : QueryCache HashSpec × SigningCacheTrace)
    (output : (OracleWorld + SigningSpec).Range input)
    (observation : EncodingMonitor.ObservedAction)
    (hbase : (output, finalState) ∈ support
      ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey input).run
        initialState))
    (hobs : encodingObservation? secretKey input initialState output finalState =
      some observation) :
    ∃ attackerAction,
      attackerActionFragment input output = [attackerAction] ∧
      EncodingActionReconstructedBy secretKey.parameter finalState.1
        observation attackerAction := by
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput =>
          simp [encodingObservation?] at hobs
      | inr hashInput =>
          cases hfresh : initialState.1 hashInput with
          | some cached =>
              simp [encodingObservation?, hfresh] at hobs
          | none =>
              cases hepoch : encodingInputEpoch? secretKey.parameter hashInput with
              | none =>
                  simp [encodingObservation?, hfresh, hepoch] at hobs
              | some epoch =>
                  have hraw :=
                    cappedCacheTracedMappedAdversaryImpl_query_base_support
                      publicKey secretKey (.inl (.inr hashInput)) initialState
                        (output, finalState) hbase
                  change (output, finalState.1) ∈ support
                    ((randomOracle (spec := HashSpec) hashInput).run
                      initialState.1) at hraw
                  rw [QueryImpl.withCaching_run_none _ hfresh, support_map] at hraw
                  obtain ⟨sampled, _hsampled, heq⟩ := hraw
                  have houtput : sampled = output := congrArg Prod.fst heq
                  have hcacheEq : initialState.1.cacheQuery hashInput sampled =
                      finalState.1 := congrArg Prod.snd heq
                  subst output
                  simp [encodingObservation?, hfresh, hepoch] at hobs
                  subst observation
                  refine ⟨.hash hashInput, rfl, hepoch, sampled, ?_, rfl⟩
                  rw [← hcacheEq]
                  exact QueryCache.cacheQuery_self initialState.1 hashInput sampled
  | inr request =>
      cases output with
      | none => simp [encodingObservation?] at hobs
      | some signature =>
          let signedInput := Concrete.CacheView.encodingInput
            secretKey.parameter request.epoch
              (request.message, signature.randomness)
          cases hfresh : initialState.1 signedInput with
          | some cached =>
              simp [encodingObservation?, signedInput, hfresh] at hobs
          | none =>
              cases hcached : finalState.1 signedInput with
              | none =>
                  simp [encodingObservation?, signedInput, hfresh, hcached] at hobs
              | some cached =>
                  simp [encodingObservation?, signedInput, hfresh, hcached] at hobs
                  subst observation
                  refine ⟨.sign request (some signature), rfl, rfl, cached, ?_, rfl⟩
                  exact hcached

theorem cappedEncodingTracedMappedAdversaryImpl_query_reconstructedBy
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace)
    (attackerTrace : AttackerActionTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hrel : EncodingTraceReconstructedBy secretKey.parameter
      initialState.1.1 initialState.2 attackerTrace)
    (hmem : result ∈ support
      ((cappedEncodingTracedMappedAdversaryImpl publicKey secretKey input).run
        initialState)) :
    EncodingTraceReconstructedBy secretKey.parameter result.2.1.1
      result.2.2 (attackerTrace ++ attackerActionFragment input result.1) := by
  rw [cappedEncodingTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, finalState⟩, hbase, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  have hbaseSupport :=
    cappedCacheTracedMappedAdversaryImpl_query_base_support publicKey secretKey
      input initialState.1 (output, finalState) hbase
  have hle := cappedUnloggedMappedAdversaryImpl_cache_le publicKey secretKey
    input initialState.1.1 (output, finalState.1) hbaseSupport
  have hrel' := hrel.mono hle
  cases hobs : encodingObservation? secretKey input initialState.1 output
      finalState with
  | none =>
      have htrace : encodingActionTraceUpdate secretKey input initialState.1
          output finalState initialState.2 = initialState.2 := by
        simp [encodingActionTraceUpdate, hobs]
      rw [htrace]
      exact hrel'.append_right (attackerActionFragment input output)
  | some observation =>
      have htrace : encodingActionTraceUpdate secretKey input initialState.1
          output finalState initialState.2 =
            initialState.2 ++ [observation] := by
        simp [encodingActionTraceUpdate, hobs]
      obtain ⟨attackerAction, hfragment, haction⟩ :=
        encodingObservation?_reconstructedBy publicKey secretKey input
          initialState.1 finalState output observation hbase hobs
      rw [htrace, hfragment]
      exact hrel'.snoc haction

noncomputable def reconstructedForgeryEncodingTrace
    (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (forgery : Forgery) : EncodingActionTrace :=
  let input := Concrete.CacheView.encodingInput parameter forgery.epoch
    (forgery.message, forgery.signature.randomness)
  [.query forgery.epoch
    (hashOutputOfDigest (Concrete.CacheView.digestAt cache input))]

noncomputable def reconstructedEncodingTrace
    (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (trace : AttackerActionTrace) (forgery : Forgery) :
    EncodingActionTrace :=
  reconstructedAttackerEncodingTrace parameter cache trace ++
    reconstructedForgeryEncodingTrace parameter cache forgery

theorem normalized_appendVerificationEncodingObservation_sublist_reconstructed
    (secretKey : SecretKey) (forgery : Forgery)
    (initialCache finalCache : QueryCache HashSpec)
    (encodingTrace : EncodingActionTrace)
    (attackerTrace : AttackerActionTrace)
    (hrel : EncodingTraceReconstructedBy secretKey.parameter initialCache
      encodingTrace attackerTrace)
    (hle : initialCache ≤ finalCache) :
    (normalizedEncodingTrace
      (appendVerificationEncodingObservation secretKey forgery initialCache
        finalCache encodingTrace)).Sublist
      (reconstructedEncodingTrace secretKey.parameter finalCache attackerTrace
        forgery) := by
  have hsub := (hrel.mono hle).normalized_sublist
  let input := Concrete.CacheView.encodingInput secretKey.parameter forgery.epoch
    (forgery.message, forgery.signature.randomness)
  unfold appendVerificationEncodingObservation
  change (normalizedEncodingTrace
      (if initialCache input = none then
        match finalCache input with
        | none => encodingTrace
        | some output =>
            encodingTrace ++ [.query forgery.epoch output]
      else encodingTrace)).Sublist _
  cases hinitial : initialCache input with
  | some output =>
      rw [if_neg (Option.some_ne_none output)]
      unfold reconstructedEncodingTrace reconstructedForgeryEncodingTrace
      exact hsub.trans (List.sublist_append_left _ _)
  | none =>
      rw [if_pos rfl]
      cases hfinal : finalCache input with
      | none =>
          unfold reconstructedEncodingTrace reconstructedForgeryEncodingTrace
          exact hsub.trans (List.sublist_append_left _ _)
      | some output =>
          have hview : Concrete.CacheView.digestAt finalCache input =
              truncateHash output :=
            Concrete.CacheView.digestAt_eq_of_cache_eq_some hfinal
          unfold reconstructedEncodingTrace reconstructedForgeryEncodingTrace
          rw [normalizedEncodingTrace, List.map_append, List.map_singleton,
            normalizedEncodingAction]
          dsimp only
          rw [hview]
          exact hsub.append (List.Sublist.refl _)

noncomputable def sourceGlobalReconstructedEncodingTrace
    (result : SourceGlobalTracedProgramResult) : EncodingActionTrace :=
  reconstructedEncodingTrace result.1.secretKey.parameter result.2.2.1
    result.2.2.2 result.2.1.1

noncomputable def globalHighReconstructedEncodingTrace
    (result : GlobalHighMonitoredProgramResult) : EncodingActionTrace :=
  reconstructedEncodingTrace result.1.1.1.secretKey.parameter
    result.2.2.1.causal.cache result.2.2.2 result.2.1.1

@[simp]
theorem reconstructedAttackerEncodingTrace_nil
    (parameter : PublicParameter) (cache : QueryCache HashSpec) :
    reconstructedAttackerEncodingTrace parameter cache [] = [] := rfl

@[simp]
theorem reconstructedAttackerEncodingTrace_append
    (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (left right : AttackerActionTrace) :
    reconstructedAttackerEncodingTrace parameter cache (left ++ right) =
      reconstructedAttackerEncodingTrace parameter cache left ++
        reconstructedAttackerEncodingTrace parameter cache right := by
  simp [reconstructedAttackerEncodingTrace]

theorem observedSignEpochs_sublist_of_sublist
    {left right : EncodingActionTrace} (hsub : left.Sublist right) :
    (EncodingMonitor.observedSignEpochs left).Sublist
      (EncodingMonitor.observedSignEpochs right) := by
  induction hsub with
  | slnil => exact List.Sublist.refl _
  | cons action hsub ih =>
      cases action with
      | query epoch output => exact ih
      | sign epoch output => exact ih.cons epoch
  | cons_cons action hsub ih =>
      cases action with
      | query epoch output => exact ih
      | sign epoch output => exact ih.cons_cons epoch

theorem validObservedSignEpochs_sublist
    (trace : EncodingActionTrace) :
    (CappedEncodingMonitor.validObservedSignEpochs trace).Sublist
      (EncodingMonitor.observedSignEpochs trace) := by
  exact observedSignEpochs_sublist_of_sublist
    (CappedEncodingMonitor.validActions_sublist trace)

theorem reconstructedAttackerEncodingTrace_signEpochs_sublist
    (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (trace : AttackerActionTrace) :
    (EncodingMonitor.observedSignEpochs
      (reconstructedAttackerEncodingTrace parameter cache trace)).Sublist
      (trace.toSigningLog.map fun entry => entry.1.epoch) := by
  induction trace with
  | nil => exact List.Sublist.refl []
  | cons action trace ih =>
      cases action with
      | hash input =>
          cases haction : reconstructedHashEncodingAction? parameter cache input with
          | none =>
              simpa [reconstructedAttackerEncodingTrace,
                reconstructedAttackerEncodingAction?, haction,
                AttackerActionTrace.toSigningLog,
                AttackerAction.signingEntry?,
                EncodingMonitor.observedSignEpochs] using ih
          | some observed =>
              have hquery : ∃ epoch output,
                  observed = EncodingMonitor.ObservedAction.query epoch output := by
                unfold reconstructedHashEncodingAction? at haction
                unfold reconstructedHashEncodingActionFrom at haction
                cases hepoch : encodingInputEpoch? parameter input with
                | none => simp [hepoch] at haction
                | some epoch =>
                    simp [hepoch] at haction
                    exact ⟨epoch, hashOutputOfDigest
                      (Concrete.CacheView.digestAt cache input), haction.symm⟩
              obtain ⟨epoch, output, rfl⟩ := hquery
              simpa [reconstructedAttackerEncodingTrace,
                reconstructedAttackerEncodingAction?, haction,
                AttackerActionTrace.toSigningLog,
                AttackerAction.signingEntry?,
                EncodingMonitor.observedSignEpochs] using ih
      | sign request signature =>
          cases signature with
          | none =>
              simpa [reconstructedAttackerEncodingTrace,
                reconstructedAttackerEncodingAction?,
                AttackerActionTrace.toSigningLog,
                AttackerAction.signingEntry?,
                EncodingMonitor.observedSignEpochs] using ih.cons request.epoch
          | some signature =>
              simpa [reconstructedAttackerEncodingTrace,
                reconstructedAttackerEncodingAction?,
                reconstructedSignEncodingAction?,
                AttackerActionTrace.toSigningLog,
                AttackerAction.signingEntry?,
                EncodingMonitor.observedSignEpochs] using
                  ih.cons_cons request.epoch

theorem reconstructedEncodingTrace_validSignEpochs_nodup
    (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (trace : AttackerActionTrace) (forgery : Forgery)
    (hnodup : (trace.toSigningLog.map fun entry => entry.1.epoch).Nodup) :
    (CappedEncodingMonitor.validObservedSignEpochs
      (reconstructedEncodingTrace parameter cache trace forgery)).Nodup := by
  apply List.Nodup.sublist ?_ hnodup
  apply (validObservedSignEpochs_sublist
    (reconstructedEncodingTrace parameter cache trace forgery)).trans
  unfold reconstructedEncodingTrace reconstructedForgeryEncodingTrace
  rw [EncodingMonitor.observedSignEpochs_append]
  simpa [EncodingMonitor.observedSignEpochs] using
    reconstructedAttackerEncodingTrace_signEpochs_sublist parameter cache trace

theorem reconstructedAttackerEncodingAction?_hash_eq_of_cachesAgreeOn
    (parameter : PublicParameter) (left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (GlobalSigningComparableHashInput parameter) left right)
    (input : HashInput) :
    reconstructedHashEncodingAction? parameter left input =
      reconstructedHashEncodingAction? parameter right input := by
  cases hepoch : encodingInputEpoch? parameter input with
  | none =>
      unfold reconstructedHashEncodingAction?
      rw [hepoch]
      rfl
  | some epoch =>
      obtain ⟨payload, hpayload⟩ :=
        exists_encodingInput_of_encodingInputEpoch?_eq_some
          parameter input epoch hepoch
      subst input
      have hcache :
          left (Concrete.CacheView.encodingInput parameter epoch payload) =
            right (Concrete.CacheView.encodingInput parameter epoch payload) :=
        hagrees _ ⟨epoch, payload.1, payload.2, rfl⟩
      have hdigest :
          Concrete.CacheView.digestAt left
              (Concrete.CacheView.encodingInput parameter epoch payload) =
            Concrete.CacheView.digestAt right
              (Concrete.CacheView.encodingInput parameter epoch payload) := by
        unfold Concrete.CacheView.digestAt
        rw [hcache]
      unfold reconstructedHashEncodingAction?
      rw [hepoch]
      rw [hdigest]

theorem reconstructedSignEncodingAction?_eq_of_cachesAgreeOn
    (parameter : PublicParameter) (left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (GlobalSigningComparableHashInput parameter) left right)
    (request : SignRequest) (signature : Signature) :
    reconstructedSignEncodingAction? parameter left request signature =
      reconstructedSignEncodingAction? parameter right request signature := by
  let input := Concrete.CacheView.encodingInput parameter request.epoch
    (request.message, signature.randomness)
  have hcache : left input = right input :=
    hagrees input ⟨request.epoch, request.message,
      signature.randomness, rfl⟩
  have hdigest : Concrete.CacheView.digestAt left input =
      Concrete.CacheView.digestAt right input := by
    unfold Concrete.CacheView.digestAt
    rw [hcache]
  unfold reconstructedSignEncodingAction?
  dsimp only
  rw [hdigest]

theorem reconstructedAttackerEncodingAction?_eq_of_cachesAgreeOn
    (parameter : PublicParameter) (left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (GlobalSigningComparableHashInput parameter) left right)
    (action : AttackerAction) :
    reconstructedAttackerEncodingAction? parameter left action =
      reconstructedAttackerEncodingAction? parameter right action := by
  cases action with
  | hash input =>
      exact reconstructedAttackerEncodingAction?_hash_eq_of_cachesAgreeOn
        parameter left right hagrees input
  | sign request signature =>
      cases signature with
      | none => rfl
      | some signature =>
          exact reconstructedSignEncodingAction?_eq_of_cachesAgreeOn
            parameter left right hagrees request signature

theorem reconstructedAttackerEncodingTrace_eq_of_cachesAgreeOn
    (parameter : PublicParameter) (left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (GlobalSigningComparableHashInput parameter) left right)
    (trace : AttackerActionTrace) :
    reconstructedAttackerEncodingTrace parameter left trace =
      reconstructedAttackerEncodingTrace parameter right trace := by
  unfold reconstructedAttackerEncodingTrace
  apply List.filterMap_congr
  intro action _haction
  exact reconstructedAttackerEncodingAction?_eq_of_cachesAgreeOn
    parameter left right hagrees action

theorem reconstructedForgeryEncodingTrace_eq_of_cachesAgreeOn
    (parameter : PublicParameter) (left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (GlobalSigningComparableHashInput parameter) left right)
    (forgery : Forgery) :
    reconstructedForgeryEncodingTrace parameter left forgery =
      reconstructedForgeryEncodingTrace parameter right forgery := by
  let input := Concrete.CacheView.encodingInput parameter forgery.epoch
    (forgery.message, forgery.signature.randomness)
  have hcache : left input = right input :=
    hagrees input ⟨forgery.epoch, forgery.message,
      forgery.signature.randomness, rfl⟩
  have hdigest : Concrete.CacheView.digestAt left input =
      Concrete.CacheView.digestAt right input := by
    unfold Concrete.CacheView.digestAt
    rw [hcache]
  unfold reconstructedForgeryEncodingTrace
  dsimp only
  rw [hdigest]

theorem reconstructedEncodingTrace_eq_of_cachesAgreeOn
    (parameter : PublicParameter) (left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (GlobalSigningComparableHashInput parameter) left right)
    (trace : AttackerActionTrace) (forgery : Forgery) :
    reconstructedEncodingTrace parameter left trace forgery =
      reconstructedEncodingTrace parameter right trace forgery := by
  unfold reconstructedEncodingTrace
  rw [reconstructedAttackerEncodingTrace_eq_of_cachesAgreeOn
      parameter left right hagrees trace,
    reconstructedForgeryEncodingTrace_eq_of_cachesAgreeOn
      parameter left right hagrees forgery]

theorem sourceGlobalReconstructedEncodingTrace_eq_globalHigh_of_good
    (adversary : Adversary Concrete.scheme)
    (left : SourceGlobalTracedProgramResult)
    (right : GlobalHighMonitoredProgramResult)
    (hleftSupport : left ∈ support (sourceGlobalTracedProgram adversary))
    (hrightSupport : right ∈ support (globalHighMonitoredProgram adversary))
    (hkey : ProgrammedGlobalChainKeygenBaseHighStableRelation left.1 right.1)
    (hgood : left.2.1 = right.2.1 ∧
      GlobalMonitoredTracedStateRelation left.1 right.1.1 left.2.2
        right.2.2) :
    sourceGlobalReconstructedEncodingTrace left =
      globalHighReconstructedEncodingTrace right := by
  have hleftKeySupport :=
    sourceGlobalTracedProgram_support_keyView adversary left hleftSupport
  have hrightKeySupport :=
    (globalHighMonitoredProgram_support_info adversary right hrightSupport).1
  have hparameter : left.1.secretKey.parameter =
      right.1.1.1.secretKey.parameter :=
    (programmedGlobal_secretKey_parameter_eq left.1 right.1 hkey
      hleftKeySupport hrightKeySupport).symm
  obtain ⟨_monitor, _hmonitor, _hagrees, _hrevealed, hcausal,
    _hretained⟩ := hgood.2.1
  have hcache : HashCachesAgreeOn
      (GlobalSigningComparableHashInput left.1.secretKey.parameter)
      left.2.2.1 right.2.2.1.causal.cache := hcausal.1
  have htrace : left.2.2.2 = right.2.2.2 := hgood.2.2
  have hforgery : left.2.1.1 = right.2.1.1 :=
    congrArg Prod.fst hgood.1
  unfold sourceGlobalReconstructedEncodingTrace
    globalHighReconstructedEncodingTrace
  rw [← hparameter, ← htrace, ← hforgery]
  exact reconstructedEncodingTrace_eq_of_cachesAgreeOn
    left.1.secretKey.parameter left.2.2.1 right.2.2.1.causal.cache
      hcache left.2.2.2 left.2.1.1

def appendAttackerActionTrace
    (input : (OracleWorld + SigningSpec).Domain)
    (_initialState : (QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace)
    (output : (OracleWorld + SigningSpec).Range input)
    (_finalState : (QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace)
    (trace : AttackerActionTrace) : AttackerActionTrace :=
  trace ++ attackerActionFragment input output

noncomputable def cappedBothTracedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT ((((QueryCache HashSpec × SigningCacheTrace) ×
        EncodingActionTrace) × AttackerActionTrace)) ProbComp) :=
  QueryImpl.extendState
    (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey)
      appendAttackerActionTrace

theorem cappedBothTracedMappedAdversaryImpl_projection
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace)
    (initialTrace : AttackerActionTrace) :
    Prod.map id Prod.fst <$>
        (simulateQ (cappedBothTracedMappedAdversaryImpl publicKey secretKey)
          computation).run (initialState, initialTrace) =
      (simulateQ (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey)
        computation).run initialState := by
  exact OracleComp.extendState_run_proj_eq
    (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey)
    appendAttackerActionTrace computation initialState initialTrace

theorem cappedUnloggedMappedAdversaryImpl_eq_sourceDirectMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    cappedUnloggedMappedAdversaryImpl publicKey secretKey =
      sourceDirectMappedAdversaryImpl publicKey secretKey := by
  funext input
  cases input with
  | inl worldInput => rfl
  | inr request => rfl

theorem cappedEncodingTracedMappedAdversaryImpl_actionProjection
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace) :
    Prod.map id (fun state => state.1.1) <$>
        (simulateQ (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey)
          computation).run initialState =
      (simulateQ (sourceDirectMappedAdversaryImpl publicKey secretKey)
        computation).run initialState.1.1 := by
  calc
    _ = Prod.map id Prod.fst <$>
        (simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
          computation).run initialState.1 := by
      rw [← cappedEncodingTracedMappedAdversaryImpl_projection publicKey
        secretKey computation initialState.1 initialState.2]
      simp only [Functor.map_map]
      rfl
    _ = (simulateQ (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
          computation).run initialState.1.1 :=
      cappedCacheTracedMappedAdversaryImpl_cache_projection publicKey secretKey
        computation initialState.1.1 initialState.1.2
    _ = _ := by
      rw [cappedUnloggedMappedAdversaryImpl_eq_sourceDirectMappedAdversaryImpl]

theorem cappedBothTracedMappedAdversaryImpl_eq_actionTracedStateImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    cappedBothTracedMappedAdversaryImpl publicKey secretKey =
      actionTracedStateImpl
        (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey)
        attackerActionFragment := by
  funext input
  unfold cappedBothTracedMappedAdversaryImpl appendAttackerActionTrace
    QueryImpl.extendState actionTracedStateImpl
  rfl

theorem cappedBothTracedMappedAdversaryImpl_query_reconstructedBy
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : ((QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace) × AttackerActionTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      (((QueryCache HashSpec × SigningCacheTrace) ×
        EncodingActionTrace) × AttackerActionTrace))
    (hrel : EncodingTraceReconstructedBy secretKey.parameter
      initialState.1.1.1 initialState.1.2 initialState.2)
    (hmem : result ∈ support
      ((cappedBothTracedMappedAdversaryImpl publicKey secretKey input).run
        initialState)) :
    EncodingTraceReconstructedBy secretKey.parameter result.2.1.1.1
      result.2.1.2 result.2.2 := by
  rw [cappedBothTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, finalState⟩, hbase, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact cappedEncodingTracedMappedAdversaryImpl_query_reconstructedBy
    publicKey secretKey input initialState.1 initialState.2
      (output, finalState) hrel hbase

theorem cappedBothTracedMappedAdversaryImpl_query_logs_eq
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : ((QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace) × AttackerActionTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      (((QueryCache HashSpec × SigningCacheTrace) ×
        EncodingActionTrace) × AttackerActionTrace))
    (hlogs : initialState.1.1.2.toSigningLog =
      initialState.2.toSigningLog)
    (hmem : result ∈ support
      ((cappedBothTracedMappedAdversaryImpl publicKey secretKey input).run
        initialState)) :
    result.2.1.1.2.toSigningLog = result.2.2.toSigningLog := by
  rw [cappedBothTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, encodingState⟩, hencoding, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  rw [cappedEncodingTracedMappedAdversaryImpl,
    QueryImpl.extendState_apply, mem_support_bind_iff] at hencoding
  obtain ⟨⟨cacheOutput, finalState⟩, hbase, hencodingPure⟩ := hencoding
  simp only [support_pure, Set.mem_singleton_iff] at hencodingPure
  have houtput : output = cacheOutput := congrArg Prod.fst hencodingPure
  have hstate : encodingState =
      (finalState,
        encodingActionTraceUpdate secretKey input initialState.1.1 cacheOutput
          finalState initialState.1.2) :=
    congrArg Prod.snd hencodingPure
  subst output
  subst encodingState
  have htraceEq :=
    cappedCacheTracedMappedAdversaryImpl_query_signingTrace_eq
      publicKey secretKey input initialState.1.1 (cacheOutput, finalState) hbase
  have htraceEq' : finalState.2 = signingCacheTraceUpdate input
      initialState.1.1.1 cacheOutput finalState.1 initialState.1.1.2 := by
    simpa using htraceEq
  change finalState.2.toSigningLog =
    (initialState.2 ++ attackerActionFragment input cacheOutput).toSigningLog
  rw [htraceEq', signingCacheTraceUpdate_toSigningLog,
    signingLogUpdate, AttackerActionTrace.toSigningLog_append,
    attackerActionFragment_toSigningLog, hlogs]

theorem cappedBothTracedMappedAdversaryImpl_reconstructedBy
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : ((QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace) × AttackerActionTrace)
    (result : α × (((QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace) × AttackerActionTrace))
    (hrel : EncodingTraceReconstructedBy secretKey.parameter
      initialState.1.1.1 initialState.1.2 initialState.2)
    (hmem : result ∈ support
      ((simulateQ (cappedBothTracedMappedAdversaryImpl publicKey secretKey)
        computation).run initialState)) :
    EncodingTraceReconstructedBy secretKey.parameter result.2.1.1.1
      result.2.1.2 result.2.2 := by
  exact OracleComp.simulateQ_run_preservesInv
    (cappedBothTracedMappedAdversaryImpl publicKey secretKey)
    (fun state => EncodingTraceReconstructedBy secretKey.parameter
      state.1.1.1 state.1.2 state.2)
    (by
      intro input state hstate result hresult
      exact cappedBothTracedMappedAdversaryImpl_query_reconstructedBy
        publicKey secretKey input state result hstate hresult)
    computation initialState hrel result hmem

theorem cappedBothTracedMappedAdversaryImpl_logs_eq
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : ((QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace) × AttackerActionTrace)
    (result : α × (((QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace) × AttackerActionTrace))
    (hlogs : initialState.1.1.2.toSigningLog =
      initialState.2.toSigningLog)
    (hmem : result ∈ support
      ((simulateQ (cappedBothTracedMappedAdversaryImpl publicKey secretKey)
        computation).run initialState)) :
    result.2.1.1.2.toSigningLog = result.2.2.toSigningLog := by
  exact OracleComp.simulateQ_run_preservesInv
    (cappedBothTracedMappedAdversaryImpl publicKey secretKey)
    (fun state => state.1.1.2.toSigningLog = state.2.toSigningLog)
    (by
      intro input state hstate result hresult
      exact cappedBothTracedMappedAdversaryImpl_query_logs_eq
        publicKey secretKey input state result hstate hresult)
    computation initialState hlogs result hmem

theorem cappedBothTracedMappedAdversaryImpl_actionProjection
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace)
    (initialTrace : AttackerActionTrace) :
    Prod.map id (fun state => (state.1.1.1, state.2)) <$>
        (simulateQ (cappedBothTracedMappedAdversaryImpl publicKey secretKey)
          computation).run (initialState, initialTrace) =
      (simulateQ (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialState.1.1, initialTrace) := by
  rw [cappedBothTracedMappedAdversaryImpl_eq_actionTracedStateImpl]
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (actionTracedStateImpl
      (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey)
      attackerActionFragment)
    (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
    (fun state => (state.1.1.1, state.2))
  intro input state
  have hbase := cappedEncodingTracedMappedAdversaryImpl_actionProjection
    publicKey secretKey
      (liftM (OracleSpec.query input) :
        OracleComp (OracleWorld + SigningSpec) _) state.1
  have hbase' :
      Prod.map id (fun state => state.1.1) <$>
          (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey input).run
            state.1 =
        (sourceDirectMappedAdversaryImpl publicKey secretKey input).run
          state.1.1.1 := by
    simpa [simulateQ_query] using hbase
  unfold sourceDirectTracedMappedAdversaryImpl
  unfold actionTracedStateImpl
  simp only [StateT.run_mk, map_bind]
  rw [← hbase']
  simp only [bind_map_left, Functor.map_map, map_pure]
  rfl

abbrev CappedBothTraceExecution :=
  GameOutcome × (((QueryCache HashSpec × SigningCacheTrace) ×
    EncodingActionTrace) × AttackerActionTrace)

abbrev CappedEncodingTraceExecution :=
  GameOutcome × ((QueryCache HashSpec × SigningCacheTrace) ×
    EncodingActionTrace)

noncomputable def sourceDirectTracedDetailedExecutionFrom
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    ProbComp ((Forgery × Bool) × SourceTracedState) := do
  let handled ← (simulateQ
    (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
      (adversary.main publicKey)).run (initialCache, [])
  let verified ← (simulateQ sourceDirectTracedVerifierImpl
    (Concrete.scheme.verify publicKey handled.1.epoch
      handled.1.message handled.1.signature)).run handled.2
  pure ((handled.1, verified.1), verified.2)

def sourceDirectExecutionResultFrom
    (publicKey : PublicKey) (secretKey : SecretKey)
    (execution : (Forgery × Bool) × SourceTracedState) :
    (GameOutcome × QueryCache HashSpec) × AttackerActionTrace :=
  ((actionTraceOutcome publicKey secretKey
    (execution.1, execution.2.2), execution.2.1), execution.2.2)

theorem sourceDirectTracedDetailedExecutionFrom_eq_actionTraced
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    sourceDirectExecutionResultFrom publicKey secretKey <$>
        sourceDirectTracedDetailedExecutionFrom adversary publicKey secretKey
          initialCache =
      detailedGameAfterKeygenWithActionTrace adversary publicKey secretKey
        initialCache := by
  unfold sourceDirectTracedDetailedExecutionFrom
    detailedGameAfterKeygenWithActionTrace
    sourceActionTracedDetailedGameAfterKeygen
  rw [sourceDirectTracedMappedAdversaryImpl_run_eq]
  simp only [List.nil_append, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    simulateQ_bind, StateT.run_bind]
  apply bind_congr
  intro handled
  simp only [Function.comp_apply, pure_bind]
  rw [sourceDirectTracedVerifierImpl_run_eq]
  simp [sourceDirectExecutionResultFrom, map_eq_bind_pure_comp]

noncomputable def cappedDetailedGameAfterKeygenWithBothTraces
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    ProbComp CappedBothTraceExecution := do
  let result ←
    (simulateQ (cappedBothTracedMappedAdversaryImpl publicKey secretKey)
      (adversary.main publicKey)).run ((((initialCache, []), []), []))
  let forgery := result.1
  let state := result.2
  let verified ← (simulateQ xmssRomImpl
    (Concrete.scheme.verify publicKey forgery.epoch forgery.message
      forgery.signature)).run state.1.1.1
  let finalEncodingTrace := appendVerificationEncodingObservation secretKey
    forgery state.1.1.1 verified.2 state.1.2
  pure (⟨publicKey, secretKey, forgery, state.1.1.2.toSigningLog,
      verified.1⟩,
    (((verified.2, state.1.1.2), finalEncodingTrace), state.2))

noncomputable def cappedDetailedGameWithBothTraces
    (adversary : Adversary Concrete.scheme) :
    ProbComp CappedBothTraceExecution := do
  let keyResult ← (simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅
  cappedDetailedGameAfterKeygenWithBothTraces adversary keyResult.1.1
    keyResult.1.2 keyResult.2

theorem cappedDetailedGameAfterKeygenWithBothTraces_normalized_sublist
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec)
    (result : CappedBothTraceExecution)
    (hresult : result ∈ support
      (cappedDetailedGameAfterKeygenWithBothTraces adversary publicKey
        secretKey initialCache)) :
    (normalizedEncodingTrace result.2.1.2).Sublist
      (reconstructedEncodingTrace secretKey.parameter result.2.1.1.1
        result.2.2 result.1.forgery) := by
  unfold cappedDetailedGameAfterKeygenWithBothTraces at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨⟨forgery, adversaryState⟩, hadversary, hverifyRest⟩ := hresult
  rw [mem_support_bind_iff] at hverifyRest
  obtain ⟨⟨verified, finalCache⟩, hverify, hfinal⟩ := hverifyRest
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  have hreconstructed :=
    cappedBothTracedMappedAdversaryImpl_reconstructedBy publicKey secretKey
      (adversary.main publicKey) ((((initialCache, []), []), []))
      (forgery, adversaryState)
      List.SublistForall₂.nil hadversary
  have hle : adversaryState.1.1.1 ≤ finalCache :=
    xmssRom_cache_le
      (Concrete.scheme.verify publicKey forgery.epoch forgery.message
        forgery.signature) adversaryState.1.1.1
      (verified, finalCache) hverify
  exact normalized_appendVerificationEncodingObservation_sublist_reconstructed
    secretKey forgery adversaryState.1.1.1 finalCache adversaryState.1.2
      adversaryState.2 hreconstructed hle

theorem cappedDetailedGameAfterKeygenWithBothTraces_logs_eq
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec)
    (result : CappedBothTraceExecution)
    (hresult : result ∈ support
      (cappedDetailedGameAfterKeygenWithBothTraces adversary publicKey
        secretKey initialCache)) :
    result.1.signingLog = result.2.2.toSigningLog := by
  unfold cappedDetailedGameAfterKeygenWithBothTraces at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨⟨forgery, adversaryState⟩, hadversary, hverifyRest⟩ := hresult
  rw [mem_support_bind_iff] at hverifyRest
  obtain ⟨⟨verified, finalCache⟩, _hverify, hfinal⟩ := hverifyRest
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  exact cappedBothTracedMappedAdversaryImpl_logs_eq publicKey secretKey
    (adversary.main publicKey) ((((initialCache, []), []), []))
      (forgery, adversaryState) rfl hadversary

theorem cappedDetailedGameAfterKeygenWithBothTraces_outcome_eq_actionTraceOutcome
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec)
    (result : CappedBothTraceExecution)
    (hresult : result ∈ support
      (cappedDetailedGameAfterKeygenWithBothTraces adversary publicKey
        secretKey initialCache)) :
    result.1 = actionTraceOutcome publicKey secretKey
      ((result.1.forgery, result.1.verified), result.2.2) := by
  have hlogs := cappedDetailedGameAfterKeygenWithBothTraces_logs_eq
    adversary publicKey secretKey initialCache result hresult
  unfold cappedDetailedGameAfterKeygenWithBothTraces at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨⟨forgery, adversaryState⟩, hadversary, hverifyRest⟩ := hresult
  rw [mem_support_bind_iff] at hverifyRest
  obtain ⟨⟨verified, finalCache⟩, hverify, hfinal⟩ := hverifyRest
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  simp only [actionTraceOutcome]
  have hlogs' : adversaryState.1.1.2.toSigningLog =
      adversaryState.2.toSigningLog := by
    simpa using hlogs
  rw [hlogs']

theorem cappedDetailedGameAfterKeygenWithBothTraces_encodingHit_implies_reconstructedHit
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec)
    (result : CappedBothTraceExecution)
    (hresult : result ∈ support
      (cappedDetailedGameAfterKeygenWithBothTraces adversary publicKey
        secretKey initialCache))
    (hwinning : WinningOutcomeBadEventOccurs result.2.1.1.1 result.1
      .encoding)
    (hhit : CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
      result.2.1.2 = true) :
    CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
      (reconstructedEncodingTrace secretKey.parameter result.2.1.1.1
        result.2.2 result.1.forgery) = true := by
  have hsub := cappedDetailedGameAfterKeygenWithBothTraces_normalized_sublist
    adversary publicKey secretKey initialCache result hresult
  have hnormalized : CappedEncodingMonitor.runObserved
      EncodingMonitor.State.empty
      (normalizedEncodingTrace result.2.1.2) = true := by
    rw [cappedEncodingRunObserved_normalizedEncodingTrace]
    exact hhit
  have hlogs := cappedDetailedGameAfterKeygenWithBothTraces_logs_eq
    adversary publicKey secretKey initialCache result hresult
  have hlogNodup :
      (result.2.2.toSigningLog.map fun entry => entry.1.epoch).Nodup := by
    have hvalid := hwinning.signingTranscript_valid
    rw [hlogs] at hvalid
    exact hvalid
  have hnodup := reconstructedEncodingTrace_validSignEpochs_nodup
    secretKey.parameter result.2.1.1.1 result.2.2 result.1.forgery
      hlogNodup
  exact CappedEncodingMonitor.runObserved_empty_eq_true_mono_sublist
    hsub hnodup hnormalized

theorem cappedDetailedGameAfterKeygenWithBothTraces_encodingProjection
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    (fun result : CappedBothTraceExecution => (result.1, result.2.1)) <$>
        cappedDetailedGameAfterKeygenWithBothTraces adversary publicKey
          secretKey initialCache =
      cappedDetailedGameAfterKeygenWithEncodingTrace adversary publicKey
        secretKey initialCache := by
  let finish : Forgery ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) →
      ProbComp CappedEncodingTraceExecution := fun result => do
    let verified ← (simulateQ xmssRomImpl
      (Concrete.scheme.verify publicKey result.1.epoch result.1.message
        result.1.signature)).run result.2.1.1
    let finalEncodingTrace := appendVerificationEncodingObservation secretKey
      result.1 result.2.1.1 verified.2 result.2.2
    pure (⟨publicKey, secretKey, result.1, result.2.1.2.toSigningLog,
      verified.1⟩, ((verified.2, result.2.1.2), finalEncodingTrace))
  have hprojection := cappedBothTracedMappedAdversaryImpl_projection
    publicKey secretKey (adversary.main publicKey) (((initialCache, []), [])) []
  have hbound := congrArg (fun computation => computation >>= finish) hprojection
  simpa [cappedDetailedGameAfterKeygenWithBothTraces,
    cappedDetailedGameAfterKeygenWithEncodingTrace, finish, map_bind,
    bind_map_left, bind_assoc, Prod.map] using hbound

theorem cappedDetailedGameAfterKeygenWithBothTraces_actionProjection
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    (fun result : CappedBothTraceExecution =>
        ((actionTraceOutcome publicKey secretKey
            ((result.1.forgery, result.1.verified), result.2.2),
          result.2.1.1.1), result.2.2)) <$>
        cappedDetailedGameAfterKeygenWithBothTraces adversary publicKey
          secretKey initialCache =
      detailedGameAfterKeygenWithActionTrace adversary publicKey secretKey
        initialCache := by
  let finish : Forgery × SourceTracedState →
      ProbComp ((GameOutcome × QueryCache HashSpec) ×
        AttackerActionTrace) := fun handled => do
    let verified ← (simulateQ sourceDirectTracedVerifierImpl
      (Concrete.scheme.verify publicKey handled.1.epoch handled.1.message
        handled.1.signature)).run handled.2
    pure (sourceDirectExecutionResultFrom publicKey secretKey
      ((handled.1, verified.1), verified.2))
  have hprojection := cappedBothTracedMappedAdversaryImpl_actionProjection
    publicKey secretKey (adversary.main publicKey) (((initialCache, []), [])) []
  have hbound := congrArg (fun computation => computation >>= finish) hprojection
  rw [← sourceDirectTracedDetailedExecutionFrom_eq_actionTraced adversary
    publicKey secretKey initialCache]
  simpa [cappedDetailedGameAfterKeygenWithBothTraces,
    sourceDirectTracedDetailedExecutionFrom, finish, map_bind,
    bind_map_left, bind_assoc, sourceDirectTracedVerifierImpl_run_eq,
    sourceDirectExecutionResultFrom, Prod.map] using hbound


theorem cappedDetailedGameWithBothTraces_encodingProjection
    (adversary : Adversary Concrete.scheme) :
    (fun result : CappedBothTraceExecution => (result.1, result.2.1)) <$>
        cappedDetailedGameWithBothTraces adversary =
      cappedDetailedGameWithEncodingTrace adversary := by
  unfold cappedDetailedGameWithBothTraces
    cappedDetailedGameWithEncodingTrace
  rw [map_bind]
  apply bind_congr
  intro keyResult
  exact cappedDetailedGameAfterKeygenWithBothTraces_encodingProjection
    adversary keyResult.1.1 keyResult.1.2 keyResult.2

abbrev CappedBothTraceGameResult :=
  ((PublicKey × SecretKey) × QueryCache HashSpec) ×
    CappedBothTraceExecution

abbrev CappedActionTraceGameResult :=
  ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
    (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace)

def cappedBothEncodingProjection
    (result : CappedBothTraceGameResult) : CappedEncodingTraceExecution :=
  (result.2.1, result.2.2.1)

def cappedBothActionProjection
    (result : CappedBothTraceGameResult) : CappedActionTraceGameResult :=
  ((result.1,
    (actionTraceOutcome result.1.1.1 result.1.1.2
      ((result.2.1.forgery, result.2.1.verified), result.2.2.2),
      result.2.2.1.1.1)), result.2.2.2)

noncomputable def cappedDetailedGameWithKeygenCacheAndBothTraces
    (adversary : Adversary Concrete.scheme) :
    ProbComp CappedBothTraceGameResult := do
  let keyResult ← (simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅
  let execution ← cappedDetailedGameAfterKeygenWithBothTraces adversary
    keyResult.1.1 keyResult.1.2 keyResult.2
  pure (keyResult, execution)

theorem cappedDetailedGameWithKeygenCacheAndBothTraces_support_execution
    (adversary : Adversary Concrete.scheme)
    (result : CappedBothTraceGameResult)
    (hresult : result ∈ support
      (cappedDetailedGameWithKeygenCacheAndBothTraces adversary)) :
    result.2 ∈ support
      (cappedDetailedGameAfterKeygenWithBothTraces adversary result.1.1.1
        result.1.1.2 result.1.2) := by
  unfold cappedDetailedGameWithKeygenCacheAndBothTraces at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨keyResult, _hkeyResult, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨execution, hexecution, hfinal⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  exact hexecution

theorem cappedDetailedGameWithKeygenCacheAndBothTraces_outcome_eq
    (adversary : Adversary Concrete.scheme)
    (result : CappedBothTraceGameResult)
    (hresult : result ∈ support
      (cappedDetailedGameWithKeygenCacheAndBothTraces adversary)) :
    result.2.1 = (cappedBothActionProjection result).1.2.1 := by
  exact cappedDetailedGameAfterKeygenWithBothTraces_outcome_eq_actionTraceOutcome
    adversary result.1.1.1 result.1.1.2 result.1.2 result.2
      (cappedDetailedGameWithKeygenCacheAndBothTraces_support_execution
        adversary result hresult)

theorem cappedDetailedGameWithKeygenCacheAndBothTraces_normalized_sublist
    (adversary : Adversary Concrete.scheme)
    (result : CappedBothTraceGameResult)
    (hresult : result ∈ support
      (cappedDetailedGameWithKeygenCacheAndBothTraces adversary)) :
    (normalizedEncodingTrace result.2.2.1.2).Sublist
      (reconstructedEncodingTrace result.1.1.2.parameter result.2.2.1.1.1
        result.2.2.2 result.2.1.forgery) := by
  unfold cappedDetailedGameWithKeygenCacheAndBothTraces at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨keyResult, _hkeyResult, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨execution, hexecution, hfinal⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  exact cappedDetailedGameAfterKeygenWithBothTraces_normalized_sublist
    adversary keyResult.1.1 keyResult.1.2 keyResult.2 execution hexecution

theorem cappedDetailedGameWithKeygenCacheAndBothTraces_encodingProjection
    (adversary : Adversary Concrete.scheme) :
    (fun result : CappedBothTraceGameResult =>
        (result.2.1, result.2.2.1)) <$>
        cappedDetailedGameWithKeygenCacheAndBothTraces adversary =
      cappedDetailedGameWithEncodingTrace adversary := by
  unfold cappedDetailedGameWithKeygenCacheAndBothTraces
    cappedDetailedGameWithEncodingTrace
  simp only [map_bind]
  apply bind_congr
  intro keyResult
  rw [← cappedDetailedGameAfterKeygenWithBothTraces_encodingProjection
    adversary keyResult.1.1 keyResult.1.2 keyResult.2]
  simp [Functor.map_map]

theorem cappedDetailedGameWithKeygenCacheAndBothTraces_encodingProjection_eq
    (adversary : Adversary Concrete.scheme) :
    cappedBothEncodingProjection <$>
        cappedDetailedGameWithKeygenCacheAndBothTraces adversary =
      cappedDetailedGameWithEncodingTrace adversary :=
  cappedDetailedGameWithKeygenCacheAndBothTraces_encodingProjection adversary

theorem cappedDetailedGameWithKeygenCacheAndBothTraces_actionProjection
    (adversary : Adversary Concrete.scheme) :
    (fun result : CappedBothTraceGameResult =>
        ((result.1,
          (actionTraceOutcome result.1.1.1 result.1.1.2
            ((result.2.1.forgery, result.2.1.verified), result.2.2.2),
            result.2.2.1.1.1)), result.2.2.2)) <$>
        cappedDetailedGameWithKeygenCacheAndBothTraces adversary =
      detailedGameWithKeygenCacheAndActionTrace adversary := by
  unfold cappedDetailedGameWithKeygenCacheAndBothTraces
    detailedGameWithKeygenCacheAndActionTrace
  simp only [map_bind]
  apply bind_congr
  intro keyResult
  rw [← cappedDetailedGameAfterKeygenWithBothTraces_actionProjection
    adversary keyResult.1.1 keyResult.1.2 keyResult.2]
  simp [Functor.map_map]

theorem cappedDetailedGameWithKeygenCacheAndBothTraces_actionProjection_eq
    (adversary : Adversary Concrete.scheme) :
    cappedBothActionProjection <$>
        cappedDetailedGameWithKeygenCacheAndBothTraces adversary =
      detailedGameWithKeygenCacheAndActionTrace adversary :=
  cappedDetailedGameWithKeygenCacheAndBothTraces_actionProjection adversary

def ActionReconstructedFirstLaneEvent
    (result : CappedActionTraceGameResult) : Prop :=
  (WinningOutcomeBadEventOccurs result.1.2.2 result.1.2.1 .encoding ∧
      CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
        (reconstructedEncodingTrace result.1.2.1.secretKey.parameter
          result.1.2.2 result.2 result.1.2.1.forgery) = true) ∨
    GlobalWinningChainValueRevealed result.1.2.2 result.1.2.1

theorem cappedBoth_firstLane_implies_actionReconstructedFirstLane
    (adversary : Adversary Concrete.scheme)
    (result : CappedBothTraceGameResult)
    (hresult : result ∈ support
      (cappedDetailedGameWithKeygenCacheAndBothTraces adversary))
    (hfirst :
      (WinningOutcomeBadEventOccurs
          (cappedBothEncodingProjection result).2.1.1
          (cappedBothEncodingProjection result).1 .encoding ∧
        CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
          (cappedBothEncodingProjection result).2.2 = true) ∨
      GlobalWinningChainValueRevealed
        (cappedBothEncodingProjection result).2.1.1
        (cappedBothEncodingProjection result).1) :
    ActionReconstructedFirstLaneEvent (cappedBothActionProjection result) := by
  have hexecution :=
    cappedDetailedGameWithKeygenCacheAndBothTraces_support_execution
      adversary result hresult
  have houtcome := cappedDetailedGameWithKeygenCacheAndBothTraces_outcome_eq
    adversary result hresult
  have houtcome' : result.2.1 =
      actionTraceOutcome result.1.1.1 result.1.1.2
        ((result.2.1.forgery, result.2.1.verified), result.2.2.2) := by
    simpa [cappedBothActionProjection] using houtcome
  unfold cappedBothEncodingProjection at hfirst
  change
    (WinningOutcomeBadEventOccurs result.2.2.1.1.1
          (actionTraceOutcome result.1.1.1 result.1.1.2
            ((result.2.1.forgery, result.2.1.verified), result.2.2.2))
          .encoding ∧
        CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
          (reconstructedEncodingTrace result.1.1.2.parameter
            result.2.2.1.1.1 result.2.2.2 result.2.1.forgery) = true) ∨
      GlobalWinningChainValueRevealed result.2.2.1.1.1
        (actionTraceOutcome result.1.1.1 result.1.1.2
          ((result.2.1.forgery, result.2.1.verified), result.2.2.2))
  rcases hfirst with hencoding | hchain
  · apply Or.inl
    constructor
    · rw [← houtcome']
      exact hencoding.1
    · have hhit :=
        cappedDetailedGameAfterKeygenWithBothTraces_encodingHit_implies_reconstructedHit
          adversary result.1.1.1 result.1.1.2 result.1.2 result.2
            hexecution hencoding.1 hencoding.2
      exact hhit
  · apply Or.inr
    rw [← houtcome']
    exact hchain


end XmssSecurity.CappedChain
