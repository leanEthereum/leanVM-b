import XmssSecurity.AdaptiveEpochCollision
import XmssSecurity.EncodingTargetMap
import XmssSecurity.SigningCacheTrace

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

def FreshSigningCollisionsRepresented
    (secretKey : SecretKey) (signingTrace : SigningCacheTrace)
    (actions : EncodingActionTrace) : Prop :=
  signingTrace.epochs.Nodup →
    ∀ entry ∈ signingTrace, entry.FreshSigningEncodingCollision secretKey →
      ∃ signedOutput oldOutput before middle after,
          truncateHash signedOutput = truncateHash oldOutput ∧
          actions = before ++ [.query entry.request.epoch oldOutput] ++ middle ++
            [.sign entry.request.epoch signedOutput] ++ after

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

theorem FreshSigningCollisionsRepresented.append_actions
    {secretKey : SecretKey}
    {signingTrace : SigningCacheTrace} {actions : EncodingActionTrace}
    (hrepresented : FreshSigningCollisionsRepresented secretKey signingTrace actions)
    (suffix : EncodingActionTrace) :
    FreshSigningCollisionsRepresented secretKey signingTrace (actions ++ suffix) := by
  intro hnodup entry hentry hcollision
  obtain ⟨signedOutput, oldOutput, before, middle, after, hdigest, hactions⟩ :=
    hrepresented hnodup entry hentry hcollision
  refine ⟨signedOutput, oldOutput, before, middle, after ++ suffix, hdigest, ?_⟩
  rw [hactions]
  simp [List.append_assoc]

theorem PostSigningQueriesRepresented.append_actions
    {secretKey : SecretKey} {signingTrace : SigningCacheTrace}
    {currentCache : QueryCache HashSpec} {actions : EncodingActionTrace}
    (hrepresented : PostSigningQueriesRepresented secretKey signingTrace currentCache
      actions) (suffix : EncodingActionTrace) :
    PostSigningQueriesRepresented secretKey signingTrace currentCache
      (actions ++ suffix) := by
  intro hnodup entry hentry signature signedOutput targetInput targetOutput
    hsignature hfresh hsigned hencoding hentryFresh hcurrent
  obtain ⟨before, middle, after, hactions⟩ := hrepresented hnodup entry hentry
    signature signedOutput targetInput targetOutput hsignature hfresh hsigned hencoding
    hentryFresh hcurrent
  refine ⟨before, middle, after ++ suffix, ?_⟩
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

noncomputable def encodingTracedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)
        ProbComp) :=
  QueryImpl.extendState (cacheTracedMappedAdversaryImpl publicKey secretKey)
    (encodingActionTraceUpdate secretKey)

theorem cacheTracedMappedAdversaryImpl_query_signingTrace_eq
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : QueryCache HashSpec × SigningCacheTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      (QueryCache HashSpec × SigningCacheTrace))
    (hmem : result ∈ support
      ((cacheTracedMappedAdversaryImpl publicKey secretKey input).run initialState)) :
    result.2.2 = signingCacheTraceUpdate input initialState.1 result.1
      result.2.1 initialState.2 := by
  rw [cacheTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, finalCache⟩, _hbase, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  rfl

theorem cacheTracedMappedAdversaryImpl_query_base_support
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : QueryCache HashSpec × SigningCacheTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      (QueryCache HashSpec × SigningCacheTrace))
    (hmem : result ∈ support
      ((cacheTracedMappedAdversaryImpl publicKey secretKey input).run initialState)) :
    (result.1, result.2.1) ∈ support
      ((unloggedMappedAdversaryImpl publicKey secretKey input).run initialState.1) := by
  rw [cacheTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, finalCache⟩, hbase, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact hbase

theorem unloggedMappedAdversaryImpl_directHash_fresh_cache_eq
    (publicKey : PublicKey) (secretKey : SecretKey)
    (queriedInput targetInput : HashInput)
    (initialCache finalCache : QueryCache HashSpec)
    (output targetOutput : HashOutput)
    (hmem : (output, finalCache) ∈ support
      ((unloggedMappedAdversaryImpl publicKey secretKey
        (.inl (.inr queriedInput))).run initialCache))
    (hfresh : initialCache targetInput = none)
    (hfinal : finalCache targetInput = some targetOutput) :
    queriedInput = targetInput ∧ output = targetOutput := by
  change (output, finalCache) ∈ support
    ((randomOracle (spec := HashSpec) queriedInput).run initialCache) at hmem
  cases hqueried : initialCache queriedInput with
  | none =>
      rw [QueryImpl.withCaching_run_none _ hqueried, support_map] at hmem
      obtain ⟨sampled, _hsampled, heq⟩ := hmem
      cases heq
      by_cases hinput : queriedInput = targetInput
      · subst targetInput
        have hself := QueryCache.cacheQuery_self initialCache queriedInput output
        rw [hfinal] at hself
        exact ⟨rfl, Option.some.inj hself.symm⟩
      · have hnone : (initialCache.cacheQuery queriedInput output) targetInput = none := by
          rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hinput)]
          exact hfresh
        rw [hfinal] at hnone
        contradiction
  | some cached =>
      rw [QueryImpl.withCaching_run_some _ hqueried, support_pure,
        Set.mem_singleton_iff] at hmem
      cases hmem
      rw [hfresh] at hfinal
      contradiction

theorem unloggedMappedAdversaryImpl_uniform_cache_eq
    (publicKey : PublicKey) (secretKey : SecretKey)
    (uniformInput : unifSpec.Domain)
    (initialCache : QueryCache HashSpec)
    (result : unifSpec.Range uniformInput × QueryCache HashSpec)
    (hmem : result ∈ support
      ((unloggedMappedAdversaryImpl publicKey secretKey
        (.inl (.inl uniformInput))).run initialCache)) :
    result.2 = initialCache := by
  have hrun :
      (unifFwdImpl HashSpec uniformInput).run initialCache =
        (fun sample => (sample, initialCache)) <$>
          (liftM (unifSpec.query uniformInput) : ProbComp _) := by
    simpa [simulateQ_query] using
      (unifFwdImpl.simulateQ_run
        (hashSpec := HashSpec)
        (liftM (unifSpec.query uniformInput) : ProbComp _) initialCache)
  change result ∈ support ((unifFwdImpl HashSpec uniformInput).run initialCache) at hmem
  rw [hrun, support_map] at hmem
  obtain ⟨sample, _hsample, heq⟩ := hmem
  exact (congrArg Prod.snd heq).symm

theorem encodingTracedMappedAdversaryImpl_query_signEpochs_sublist
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hsublist : List.Sublist
      (EncodingMonitor.observedSignEpochs initialState.2) initialState.1.2.epochs)
    (hmem : result ∈ support
      ((encodingTracedMappedAdversaryImpl publicKey secretKey input).run initialState)) :
    List.Sublist (EncodingMonitor.observedSignEpochs result.2.2)
      result.2.1.2.epochs := by
  rw [encodingTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, finalState⟩, hbase, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact encodingActionTraceUpdate_signEpochs_sublist secretKey input initialState.1
    output finalState initialState.2
    (cacheTracedMappedAdversaryImpl_query_signingTrace_eq publicKey secretKey input
      initialState.1 (output, finalState) hbase) hsublist

theorem encodingTracedMappedAdversaryImpl_query_freshSigningActionsRepresented
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hrepresented : FreshSigningActionsRepresented secretKey initialState.1.2
      initialState.2)
    (hmem : result ∈ support
      ((encodingTracedMappedAdversaryImpl publicKey secretKey input).run initialState)) :
    FreshSigningActionsRepresented secretKey result.2.1.2 result.2.2 := by
  rw [encodingTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, finalState⟩, hbase, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  have htraceEq := cacheTracedMappedAdversaryImpl_query_signingTrace_eq
    publicKey secretKey input initialState.1 (output, finalState) hbase
  obtain ⟨suffix, hsuffix⟩ : ∃ suffix : EncodingActionTrace,
      encodingActionTraceUpdate secretKey input initialState.1 output finalState
          initialState.2 = initialState.2 ++ suffix := by
    rcases encodingActionTraceUpdate_eq_or_append secretKey input initialState.1
      output finalState initialState.2 with hsame | ⟨observation, happend⟩
    · exact ⟨[], by simpa using hsame⟩
    · exact ⟨[observation], happend⟩
  cases input with
  | inl worldInput =>
      rw [signingCacheTraceUpdate] at htraceEq
      rw [htraceEq, hsuffix]
      exact hrepresented.append_actions suffix
  | inr request =>
      rw [signingCacheTraceUpdate] at htraceEq
      rw [htraceEq]
      intro entry hentry signature hsignature hfresh
      rw [List.mem_append] at hentry
      rcases hentry with hentry | hentry
      · rw [hsuffix]
        exact hrepresented.append_actions suffix entry hentry signature hsignature hfresh
      · simp only [List.mem_singleton] at hentry
        subst entry
        cases output with
        | none => simp at hsignature
        | some returnedSignature =>
            simp only [Option.some.injEq] at hsignature
            subst returnedSignature
            change initialState.1.1
              (Concrete.CacheView.encodingInput secretKey.parameter request.epoch
                (request.message, signature.randomness)) = none at hfresh
            have hsignSupport : (some signature, finalState.1) ∈ support
                ((simulateQ xmssRomImpl
                  (Concrete.sign publicKey secretKey request.epoch request.message)).run
                    initialState.1.1) := by
              have hraw := cacheTracedMappedAdversaryImpl_query_base_support
                publicKey secretKey (.inr request) initialState.1
                (some signature, finalState) hbase
              change (some signature, finalState.1) ∈ support
                ((simulateQ xmssRomImpl
                  (Concrete.sign publicKey secretKey request.epoch request.message)).run
                    initialState.1.1) at hraw
              exact hraw
            obtain ⟨hashOutput, houtput⟩ :=
              Concrete.sign_success_encodingInput_cached publicKey secretKey request
                initialState.1.1 finalState.1 signature hsignSupport
            refine ⟨hashOutput, initialState.2, [], houtput, ?_⟩
            simp [encodingActionTraceUpdate, encodingObservation?, hfresh, houtput]

theorem encodingTracedMappedAdversaryImpl_query_unsignedEncodingEntriesRepresented
    (publicKey : PublicKey) (secretKey : SecretKey)
    (baseCache : QueryCache HashSpec)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hrepresented : UnsignedEncodingEntriesRepresented secretKey.parameter baseCache
      initialState.1.1 initialState.1.2 initialState.2)
    (hmem : result ∈ support
      ((encodingTracedMappedAdversaryImpl publicKey secretKey input).run initialState)) :
    UnsignedEncodingEntriesRepresented secretKey.parameter baseCache
      result.2.1.1 result.2.1.2 result.2.2 := by
  rw [encodingTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, finalState⟩, hbase, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  change UnsignedEncodingEntriesRepresented secretKey.parameter baseCache finalState.1
    finalState.2
      (encodingActionTraceUpdate secretKey input initialState.1 output finalState
        initialState.2)
  have htraceEq := cacheTracedMappedAdversaryImpl_query_signingTrace_eq
    publicKey secretKey input initialState.1 (output, finalState) hbase
  have hbaseSupport := cacheTracedMappedAdversaryImpl_query_base_support
    publicKey secretKey input initialState.1 (output, finalState) hbase
  have hcacheLe := unloggedMappedAdversaryImpl_cache_le publicKey secretKey input
    initialState.1.1 (output, finalState.1) hbaseSupport
  change initialState.1.1 ≤ finalState.1 at hcacheLe
  obtain ⟨suffix, hsuffix⟩ : ∃ suffix : EncodingActionTrace,
      encodingActionTraceUpdate secretKey input initialState.1 output finalState
          initialState.2 = initialState.2 ++ suffix := by
    rcases encodingActionTraceUpdate_eq_or_append secretKey input initialState.1
      output finalState initialState.2 with hsame | ⟨observation, happend⟩
    · exact ⟨[], by simpa using hsame⟩
    · exact ⟨[observation], happend⟩
  cases input with
  | inl worldInput =>
      rw [signingCacheTraceUpdate] at htraceEq
      cases worldInput with
      | inl uniformInput =>
          have hcacheEq := unloggedMappedAdversaryImpl_uniform_cache_eq publicKey
            secretKey uniformInput initialState.1.1 (output, finalState.1) hbaseSupport
          change finalState.1 = initialState.1.1 at hcacheEq
          rw [htraceEq, hcacheEq]
          simpa [encodingActionTraceUpdate, encodingObservation?] using hrepresented
      | inr queriedInput =>
          rw [htraceEq]
          intro epoch hunsigned targetInput targetOutput hencoding hbaseFresh hfinal
          cases hinitial : initialState.1.1 targetInput with
          | some oldOutput =>
              have hfinalOld := hcacheLe hinitial
              have houtputEq : oldOutput = targetOutput := by
                rw [hfinal] at hfinalOld
                exact Option.some.inj hfinalOld.symm
              subst oldOutput
              obtain ⟨before, after, hactions⟩ := hrepresented epoch hunsigned
                targetInput targetOutput hencoding hbaseFresh hinitial
              refine ⟨before, after ++ suffix, ?_⟩
              rw [hsuffix, hactions]
              simp [List.append_assoc]
          | none =>
              obtain ⟨hinput, houtput⟩ :=
                unloggedMappedAdversaryImpl_directHash_fresh_cache_eq publicKey
                  secretKey queriedInput targetInput initialState.1.1 finalState.1
                  output targetOutput hbaseSupport hinitial hfinal
              subst queriedInput
              subst output
              refine ⟨initialState.2, [], ?_⟩
              simp [encodingActionTraceUpdate, encodingObservation?, hinitial,
                hencoding]
  | inr request =>
      rw [signingCacheTraceUpdate] at htraceEq
      rw [htraceEq]
      intro epoch hunsigned targetInput targetOutput hencoding hbaseFresh hfinal
      have hunsignedInitial : epoch ∉ initialState.1.2.epochs := by
        intro hmem
        exact hunsigned (by simp [hmem])
      have hotherEpoch : request.epoch ≠ epoch := by
        intro heq
        subst epoch
        exact hunsigned (by simp [SigningCacheTrace.epochs])
      cases hinitial : initialState.1.1 targetInput with
      | some oldOutput =>
          have hfinalOld := hcacheLe hinitial
          have houtputEq : oldOutput = targetOutput := by
            rw [hfinal] at hfinalOld
            exact Option.some.inj hfinalOld.symm
          subst oldOutput
          obtain ⟨before, after, hactions⟩ := hrepresented epoch hunsignedInitial
            targetInput targetOutput hencoding hbaseFresh hinitial
          refine ⟨before, after ++ suffix, ?_⟩
          rw [hsuffix, hactions]
          simp [List.append_assoc]
      | none =>
          have hsignSupport : (output, finalState.1) ∈ support
              ((simulateQ xmssRomImpl
                (Concrete.sign publicKey secretKey request.epoch request.message)).run
                  initialState.1.1) := by
            change (output, finalState.1) ∈ support
              ((simulateQ xmssRomImpl
                (Concrete.sign publicKey secretKey request.epoch request.message)).run
                  initialState.1.1) at hbaseSupport
            exact hbaseSupport
          obtain ⟨targetPair, htargetPair⟩ :=
            exists_encodingInput_of_encodingInputEpoch?_eq_some secretKey.parameter
              targetInput epoch hencoding
          have hnone := Concrete.sign_preserves_other_epoch_encodingInput publicKey
            secretKey request initialState.1.1 finalState.1 output hsignSupport epoch
            targetPair hotherEpoch (by rw [htargetPair]; exact hinitial)
          rw [htargetPair, hfinal] at hnone
          cases hnone

theorem encodingTracedMappedAdversaryImpl_query_freshSigningCollisionsRepresented
    (publicKey : PublicKey) (secretKey : SecretKey)
    (baseCache : QueryCache HashSpec)
    (hbaseEncodingFree : ∀ epoch input,
      baseCache (Concrete.CacheView.encodingInput secretKey.parameter epoch input) = none)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hunsigned : UnsignedEncodingEntriesRepresented secretKey.parameter baseCache
      initialState.1.1 initialState.1.2 initialState.2)
    (hrepresented : FreshSigningCollisionsRepresented secretKey initialState.1.2
      initialState.2)
    (hmem : result ∈ support
      ((encodingTracedMappedAdversaryImpl publicKey secretKey input).run initialState)) :
    FreshSigningCollisionsRepresented secretKey result.2.1.2 result.2.2 := by
  rw [encodingTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, finalState⟩, hbase, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  change FreshSigningCollisionsRepresented secretKey finalState.2
    (encodingActionTraceUpdate secretKey input initialState.1 output finalState
      initialState.2)
  have htraceEq := cacheTracedMappedAdversaryImpl_query_signingTrace_eq
    publicKey secretKey input initialState.1 (output, finalState) hbase
  obtain ⟨suffix, hsuffix⟩ : ∃ suffix : EncodingActionTrace,
      encodingActionTraceUpdate secretKey input initialState.1 output finalState
          initialState.2 = initialState.2 ++ suffix := by
    rcases encodingActionTraceUpdate_eq_or_append secretKey input initialState.1
      output finalState initialState.2 with hsame | ⟨observation, happend⟩
    · exact ⟨[], by simpa using hsame⟩
    · exact ⟨[observation], happend⟩
  cases input with
  | inl worldInput =>
      rw [signingCacheTraceUpdate] at htraceEq
      rw [htraceEq, hsuffix]
      exact hrepresented.append_actions suffix
  | inr request =>
      rw [signingCacheTraceUpdate] at htraceEq
      rw [htraceEq]
      intro hnodup entry hentry hcollision
      have hnodupInitial : initialState.1.2.epochs.Nodup := by
        exact (List.nodup_append.mp (by simpa using hnodup)).1
      rw [List.mem_append] at hentry
      rcases hentry with hentry | hentry
      · rw [hsuffix]
        exact hrepresented.append_actions suffix hnodupInitial entry hentry hcollision
      · simp only [List.mem_singleton] at hentry
        subst entry
        obtain ⟨signature, signedOutput, oldInput, oldOutput, hsignature,
          hfresh, hsigned, hold, _hne, hdigest⟩ := hcollision
        change initialState.1.1
          (Concrete.CacheView.encodingInput secretKey.parameter request.epoch
            (request.message, signature.randomness)) = none at hfresh
        change finalState.1
          (Concrete.CacheView.encodingInput secretKey.parameter request.epoch
            (request.message, signature.randomness)) = some signedOutput at hsigned
        change initialState.1.1
          (Concrete.CacheView.encodingInput secretKey.parameter request.epoch oldInput) =
            some oldOutput at hold
        cases output with
        | none => simp at hsignature
        | some returnedSignature =>
            simp only [Option.some.injEq] at hsignature
            subst returnedSignature
            have hrequestFresh : request.epoch ∉ initialState.1.2.epochs := by
              intro hmem
              have hcross := (List.nodup_append.mp (by simpa using hnodup)).2.2
              exact hcross request.epoch hmem request.epoch
                (by simp [SigningCacheTrace.epochs]) rfl
            obtain ⟨before, middle, hqueryActions⟩ := hunsigned request.epoch
              hrequestFresh
              (Concrete.CacheView.encodingInput secretKey.parameter request.epoch oldInput)
              oldOutput (by simp) (hbaseEncodingFree request.epoch oldInput) hold
            refine ⟨signedOutput, oldOutput, before, middle, [], hdigest, ?_⟩
            rw [show encodingActionTraceUpdate secretKey (.inr request) initialState.1
                (some signature) finalState initialState.2 =
                initialState.2 ++ [.sign request.epoch signedOutput] by
              simp [encodingActionTraceUpdate, encodingObservation?, hfresh, hsigned]]
            rw [hqueryActions]
            simp [List.append_assoc]

theorem encodingTracedMappedAdversaryImpl_query_postSigningQueriesRepresented
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hsignActions : FreshSigningActionsRepresented secretKey initialState.1.2
      initialState.2)
    (hrepresented : PostSigningQueriesRepresented secretKey initialState.1.2
      initialState.1.1 initialState.2)
    (hmem : result ∈ support
      ((encodingTracedMappedAdversaryImpl publicKey secretKey input).run initialState)) :
    PostSigningQueriesRepresented secretKey result.2.1.2 result.2.1.1
      result.2.2 := by
  rw [encodingTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, finalState⟩, hbase, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  change PostSigningQueriesRepresented secretKey finalState.2 finalState.1
    (encodingActionTraceUpdate secretKey input initialState.1 output finalState
      initialState.2)
  have htraceEq := cacheTracedMappedAdversaryImpl_query_signingTrace_eq
    publicKey secretKey input initialState.1 (output, finalState) hbase
  have hbaseSupport := cacheTracedMappedAdversaryImpl_query_base_support
    publicKey secretKey input initialState.1 (output, finalState) hbase
  have hcacheLe := unloggedMappedAdversaryImpl_cache_le publicKey secretKey input
    initialState.1.1 (output, finalState.1) hbaseSupport
  change initialState.1.1 ≤ finalState.1 at hcacheLe
  obtain ⟨suffix, hsuffix⟩ : ∃ suffix : EncodingActionTrace,
      encodingActionTraceUpdate secretKey input initialState.1 output finalState
          initialState.2 = initialState.2 ++ suffix := by
    rcases encodingActionTraceUpdate_eq_or_append secretKey input initialState.1
      output finalState initialState.2 with hsame | ⟨observation, happend⟩
    · exact ⟨[], by simpa using hsame⟩
    · exact ⟨[observation], happend⟩
  cases input with
  | inl worldInput =>
      rw [signingCacheTraceUpdate] at htraceEq
      cases worldInput with
      | inl uniformInput =>
          have hcacheEq := unloggedMappedAdversaryImpl_uniform_cache_eq publicKey
            secretKey uniformInput initialState.1.1 (output, finalState.1) hbaseSupport
          change finalState.1 = initialState.1.1 at hcacheEq
          rw [htraceEq, hcacheEq]
          simpa [encodingActionTraceUpdate, encodingObservation?] using hrepresented
      | inr queriedInput =>
          rw [htraceEq]
          intro hnodup entry hentry signature signedOutput targetInput targetOutput
            hsignature hfresh hsigned hencoding hentryFresh hfinal
          cases hinitial : initialState.1.1 targetInput with
          | some oldOutput =>
              have hfinalOld := hcacheLe hinitial
              have houtputEq : oldOutput = targetOutput := by
                rw [hfinal] at hfinalOld
                exact Option.some.inj hfinalOld.symm
              subst oldOutput
              obtain ⟨before, middle, after, hactions⟩ := hrepresented hnodup entry
                hentry signature signedOutput targetInput targetOutput hsignature hfresh
                hsigned hencoding hentryFresh hinitial
              refine ⟨before, middle, after ++ suffix, ?_⟩
              rw [hsuffix, hactions]
              simp [List.append_assoc]
          | none =>
              obtain ⟨hinput, houtput⟩ :=
                unloggedMappedAdversaryImpl_directHash_fresh_cache_eq publicKey
                  secretKey queriedInput targetInput initialState.1.1 finalState.1
                  output targetOutput hbaseSupport hinitial hfinal
              subst queriedInput
              subst output
              obtain ⟨actionSignedOutput, before, middle, hcached, hsignActionsEq⟩ :=
                hsignActions entry hentry signature hsignature hfresh
              have hsignedOutputEq : actionSignedOutput = signedOutput := by
                rw [hsigned] at hcached
                exact Option.some.inj hcached.symm
              subst actionSignedOutput
              refine ⟨before, middle, [], ?_⟩
              rw [show encodingActionTraceUpdate secretKey (.inl (.inr targetInput))
                  initialState.1 targetOutput finalState initialState.2 =
                  initialState.2 ++ [.query entry.request.epoch targetOutput] by
                simp [encodingActionTraceUpdate, encodingObservation?, hinitial,
                  hencoding]]
              rw [hsignActionsEq]
              simp [List.append_assoc]
  | inr request =>
      rw [signingCacheTraceUpdate] at htraceEq
      rw [htraceEq]
      intro hnodup entry hentry signature signedOutput targetInput targetOutput
        hsignature hfresh hsigned hencoding hentryFresh hfinal
      have hnodupInitial : initialState.1.2.epochs.Nodup :=
        (List.nodup_append.mp (by simpa using hnodup)).1
      rw [List.mem_append] at hentry
      rcases hentry with hentry | hentry
      · have hotherEpoch : request.epoch ≠ entry.request.epoch := by
          intro heq
          have hcross := (List.nodup_append.mp (by simpa using hnodup)).2.2
          exact hcross entry.request.epoch
            (by exact List.mem_map.mpr ⟨entry, hentry, rfl⟩) request.epoch
            (by simp [SigningCacheTrace.epochs]) heq.symm
        cases hinitial : initialState.1.1 targetInput with
        | some oldOutput =>
            have hfinalOld := hcacheLe hinitial
            have houtputEq : oldOutput = targetOutput := by
              rw [hfinal] at hfinalOld
              exact Option.some.inj hfinalOld.symm
            subst oldOutput
            obtain ⟨before, middle, after, hactions⟩ := hrepresented hnodupInitial
              entry hentry signature signedOutput targetInput targetOutput hsignature
              hfresh hsigned hencoding hentryFresh hinitial
            refine ⟨before, middle, after ++ suffix, ?_⟩
            rw [hsuffix, hactions]
            simp [List.append_assoc]
        | none =>
            have hsignSupport : (output, finalState.1) ∈ support
                ((simulateQ xmssRomImpl
                  (Concrete.sign publicKey secretKey request.epoch request.message)).run
                    initialState.1.1) := by
              change (output, finalState.1) ∈ support
                ((simulateQ xmssRomImpl
                  (Concrete.sign publicKey secretKey request.epoch request.message)).run
                    initialState.1.1) at hbaseSupport
              exact hbaseSupport
            obtain ⟨targetPair, htargetPair⟩ :=
              exists_encodingInput_of_encodingInputEpoch?_eq_some secretKey.parameter
                targetInput entry.request.epoch hencoding
            have hnone := Concrete.sign_preserves_other_epoch_encodingInput publicKey
              secretKey request initialState.1.1 finalState.1 output hsignSupport
              entry.request.epoch targetPair hotherEpoch
              (by rw [htargetPair]; exact hinitial)
            rw [htargetPair, hfinal] at hnone
            cases hnone
      · simp only [List.mem_singleton] at hentry
        subst entry
        change finalState.1 targetInput = none at hentryFresh
        rw [hfinal] at hentryFresh
        cases hentryFresh

theorem encodingTracedMappedAdversaryImpl_signEpochs_sublist
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)
    (result : α ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hsublist : List.Sublist
      (EncodingMonitor.observedSignEpochs initialState.2) initialState.1.2.epochs)
    (hmem : result ∈ support
      ((simulateQ (encodingTracedMappedAdversaryImpl publicKey secretKey)
        computation).run initialState)) :
    List.Sublist (EncodingMonitor.observedSignEpochs result.2.2)
      result.2.1.2.epochs := by
  induction computation using OracleComp.inductionOn generalizing initialState result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hmem
      subst result
      exact hsublist
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleState⟩, hquery, hrest⟩ := hmem
      have hquery' : (output, middleState) ∈ support
          ((encodingTracedMappedAdversaryImpl publicKey secretKey input).run
            initialState) := by
        simpa [simulateQ_query] using hquery
      exact ih output middleState result
        (encodingTracedMappedAdversaryImpl_query_signEpochs_sublist publicKey secretKey
          input initialState (output, middleState) hsublist hquery') hrest

theorem encodingTracedMappedAdversaryImpl_freshSigningActionsRepresented
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)
    (result : α ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hrepresented : FreshSigningActionsRepresented secretKey initialState.1.2
      initialState.2)
    (hmem : result ∈ support
      ((simulateQ (encodingTracedMappedAdversaryImpl publicKey secretKey)
        computation).run initialState)) :
    FreshSigningActionsRepresented secretKey result.2.1.2 result.2.2 := by
  induction computation using OracleComp.inductionOn generalizing initialState result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hmem
      subst result
      exact hrepresented
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleState⟩, hquery, hrest⟩ := hmem
      have hquery' : (output, middleState) ∈ support
          ((encodingTracedMappedAdversaryImpl publicKey secretKey input).run
            initialState) := by
        simpa [simulateQ_query] using hquery
      exact ih output middleState result
        (encodingTracedMappedAdversaryImpl_query_freshSigningActionsRepresented
          publicKey secretKey input initialState (output, middleState) hrepresented
          hquery') hrest

theorem encodingTracedMappedAdversaryImpl_unsignedEncodingEntriesRepresented
    (publicKey : PublicKey) (secretKey : SecretKey)
    (baseCache : QueryCache HashSpec)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)
    (result : α ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hrepresented : UnsignedEncodingEntriesRepresented secretKey.parameter baseCache
      initialState.1.1 initialState.1.2 initialState.2)
    (hmem : result ∈ support
      ((simulateQ (encodingTracedMappedAdversaryImpl publicKey secretKey)
        computation).run initialState)) :
    UnsignedEncodingEntriesRepresented secretKey.parameter baseCache result.2.1.1
      result.2.1.2 result.2.2 := by
  induction computation using OracleComp.inductionOn generalizing initialState result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hmem
      subst result
      exact hrepresented
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleState⟩, hquery, hrest⟩ := hmem
      have hquery' : (output, middleState) ∈ support
          ((encodingTracedMappedAdversaryImpl publicKey secretKey input).run
            initialState) := by
        simpa [simulateQ_query] using hquery
      exact ih output middleState result
        (encodingTracedMappedAdversaryImpl_query_unsignedEncodingEntriesRepresented
          publicKey secretKey baseCache input initialState (output, middleState)
          hrepresented hquery') hrest

theorem encodingTracedMappedAdversaryImpl_encodingCollisionInvariants
    (publicKey : PublicKey) (secretKey : SecretKey)
    (baseCache : QueryCache HashSpec)
    (hbaseEncodingFree : ∀ epoch input,
      baseCache (Concrete.CacheView.encodingInput secretKey.parameter epoch input) = none)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)
    (result : α ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hunsigned : UnsignedEncodingEntriesRepresented secretKey.parameter baseCache
      initialState.1.1 initialState.1.2 initialState.2)
    (hcollisions : FreshSigningCollisionsRepresented secretKey initialState.1.2
      initialState.2)
    (hmem : result ∈ support
      ((simulateQ (encodingTracedMappedAdversaryImpl publicKey secretKey)
        computation).run initialState)) :
    UnsignedEncodingEntriesRepresented secretKey.parameter baseCache result.2.1.1
        result.2.1.2 result.2.2 ∧
      FreshSigningCollisionsRepresented secretKey result.2.1.2 result.2.2 := by
  induction computation using OracleComp.inductionOn generalizing initialState result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hmem
      subst result
      exact ⟨hunsigned, hcollisions⟩
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleState⟩, hquery, hrest⟩ := hmem
      have hquery' : (output, middleState) ∈ support
          ((encodingTracedMappedAdversaryImpl publicKey secretKey input).run
            initialState) := by
        simpa [simulateQ_query] using hquery
      have hmiddleUnsigned :=
        encodingTracedMappedAdversaryImpl_query_unsignedEncodingEntriesRepresented
          publicKey secretKey baseCache input initialState (output, middleState)
          hunsigned hquery'
      have hmiddleCollisions :=
        encodingTracedMappedAdversaryImpl_query_freshSigningCollisionsRepresented
          publicKey secretKey baseCache hbaseEncodingFree input initialState
          (output, middleState) hunsigned hcollisions hquery'
      exact ih output middleState result hmiddleUnsigned hmiddleCollisions hrest

theorem encodingTracedMappedAdversaryImpl_postSigningInvariants
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)
    (result : α ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hsignActions : FreshSigningActionsRepresented secretKey initialState.1.2
      initialState.2)
    (hpostSigning : PostSigningQueriesRepresented secretKey initialState.1.2
      initialState.1.1 initialState.2)
    (hmem : result ∈ support
      ((simulateQ (encodingTracedMappedAdversaryImpl publicKey secretKey)
        computation).run initialState)) :
    FreshSigningActionsRepresented secretKey result.2.1.2 result.2.2 ∧
      PostSigningQueriesRepresented secretKey result.2.1.2 result.2.1.1
        result.2.2 := by
  induction computation using OracleComp.inductionOn generalizing initialState result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hmem
      subst result
      exact ⟨hsignActions, hpostSigning⟩
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleState⟩, hquery, hrest⟩ := hmem
      have hquery' : (output, middleState) ∈ support
          ((encodingTracedMappedAdversaryImpl publicKey secretKey input).run
            initialState) := by
        simpa [simulateQ_query] using hquery
      have hmiddleSignActions :=
        encodingTracedMappedAdversaryImpl_query_freshSigningActionsRepresented
          publicKey secretKey input initialState (output, middleState) hsignActions
          hquery'
      have hmiddlePostSigning :=
        encodingTracedMappedAdversaryImpl_query_postSigningQueriesRepresented
          publicKey secretKey input initialState (output, middleState) hsignActions
          hpostSigning hquery'
      exact ih output middleState result hmiddleSignActions hmiddlePostSigning hrest

theorem encodingTracedMappedAdversaryImpl_projection
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : QueryCache HashSpec × SigningCacheTrace)
    (initialTrace : EncodingActionTrace) :
    Prod.map id Prod.fst <$>
        (simulateQ (encodingTracedMappedAdversaryImpl publicKey secretKey)
          computation).run (initialState, initialTrace) =
      (simulateQ (cacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run initialState := by
  exact OracleComp.extendState_run_proj_eq
    (cacheTracedMappedAdversaryImpl publicKey secretKey)
    (encodingActionTraceUpdate secretKey) computation initialState initialTrace

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

noncomputable def detailedGameAfterKeygenWithEncodingTrace
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    ProbComp (GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) := do
  let (forgery, adversaryState, encodingTrace) ←
    (simulateQ (encodingTracedMappedAdversaryImpl publicKey secretKey)
      (adversary.main publicKey)).run ((initialCache, []), [])
  let (verified, finalCache) ←
    (simulateQ xmssRomImpl
      (Concrete.scheme.verify publicKey forgery.epoch forgery.message
        forgery.signature)).run adversaryState.1
  let finalEncodingTrace := appendVerificationEncodingObservation secretKey forgery
    adversaryState.1 finalCache encodingTrace
  pure (⟨publicKey, secretKey, forgery, adversaryState.2.toSigningLog, verified⟩,
    ((finalCache, adversaryState.2), finalEncodingTrace))

theorem detailedGameAfterKeygenWithEncodingTrace_projection
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    (fun result => (result.1, result.2.1)) <$>
        detailedGameAfterKeygenWithEncodingTrace adversary publicKey secretKey initialCache =
      detailedGameAfterKeygenWithSigningTrace adversary publicKey secretKey initialCache := by
  let finishEncoding : Forgery ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) →
      ProbComp (GameOutcome × (QueryCache HashSpec × SigningCacheTrace)) :=
    fun result => do
      let (verified, finalCache) ←
        (simulateQ xmssRomImpl
          (Concrete.scheme.verify publicKey result.1.epoch result.1.message
            result.1.signature)).run result.2.1.1
      pure (⟨publicKey, secretKey, result.1, result.2.1.2.toSigningLog, verified⟩,
        (finalCache, result.2.1.2))
  let finishSigning : Forgery × (QueryCache HashSpec × SigningCacheTrace) →
      ProbComp (GameOutcome × (QueryCache HashSpec × SigningCacheTrace)) :=
    fun result => do
      let (verified, finalCache) ←
        (simulateQ xmssRomImpl
          (Concrete.scheme.verify publicKey result.1.epoch result.1.message
            result.1.signature)).run result.2.1
      pure (⟨publicKey, secretKey, result.1, result.2.2.toSigningLog, verified⟩,
        (finalCache, result.2.2))
  have hbridge := congrArg (fun computation => computation >>= finishSigning)
    (encodingTracedMappedAdversaryImpl_projection publicKey secretKey
      (adversary.main publicKey) (initialCache, []) [])
  simpa [detailedGameAfterKeygenWithEncodingTrace,
    detailedGameAfterKeygenWithSigningTrace, finishEncoding, finishSigning,
    bind_map_left, map_bind, bind_assoc, Prod.map] using hbridge

noncomputable def detailedGameWithEncodingTrace
    (adversary : Adversary Concrete.scheme) :
    ProbComp (GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) := do
  let keyResult ← (simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅
  detailedGameAfterKeygenWithEncodingTrace adversary keyResult.1.1 keyResult.1.2
    keyResult.2

theorem detailedGameWithEncodingTrace_projection
    (adversary : Adversary Concrete.scheme) :
    (fun result => (result.1, result.2.1)) <$>
        detailedGameWithEncodingTrace adversary =
      detailedGameWithSigningTrace adversary := by
  unfold detailedGameWithEncodingTrace detailedGameWithSigningTrace
  simp only [map_bind]
  apply bind_congr
  intro keyResult
  exact detailedGameAfterKeygenWithEncodingTrace_projection adversary keyResult.1.1
    keyResult.1.2 keyResult.2

theorem detailedGameAfterKeygenWithEncodingTrace_signEpochs_sublist
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec)
    (result : GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hmem : result ∈ support
      (detailedGameAfterKeygenWithEncodingTrace adversary publicKey secretKey
        initialCache)) :
    List.Sublist (EncodingMonitor.observedSignEpochs result.2.2)
      result.2.1.2.epochs := by
  unfold detailedGameAfterKeygenWithEncodingTrace at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨forgery, adversaryState, encodingTrace⟩, hadversary, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨⟨verified, finalCache⟩, _hverify, hfinal⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  have hsublist := encodingTracedMappedAdversaryImpl_signEpochs_sublist
    publicKey secretKey (adversary.main publicKey) ((initialCache, []), [])
    (forgery, (adversaryState, encodingTrace))
    (List.Sublist.refl []) hadversary
  change List.Sublist (EncodingMonitor.observedSignEpochs
    (appendVerificationEncodingObservation secretKey forgery adversaryState.1
      finalCache encodingTrace)) adversaryState.2.epochs
  let forgedInput := Concrete.CacheView.encodingInput secretKey.parameter forgery.epoch
    (forgery.message, forgery.signature.randomness)
  by_cases hfresh : adversaryState.1 forgedInput = none
  · cases houtput : finalCache forgedInput with
    | none =>
        simpa [appendVerificationEncodingObservation, forgedInput, hfresh,
          houtput, EncodingMonitor.observedSignEpochs] using hsublist
    | some output =>
        simpa [appendVerificationEncodingObservation, forgedInput, hfresh,
          houtput, EncodingMonitor.observedSignEpochs] using hsublist
  · simpa [appendVerificationEncodingObservation, forgedInput, hfresh,
      EncodingMonitor.observedSignEpochs] using hsublist

theorem detailedGameAfterKeygenWithEncodingTrace_freshSigningActionsRepresented
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec)
    (result : GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hmem : result ∈ support
      (detailedGameAfterKeygenWithEncodingTrace adversary publicKey secretKey
        initialCache)) :
    FreshSigningActionsRepresented secretKey result.2.1.2 result.2.2 := by
  unfold detailedGameAfterKeygenWithEncodingTrace at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨forgery, adversaryState, encodingTrace⟩, hadversary, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨⟨verified, finalCache⟩, _hverify, hfinal⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  have hrepresented :=
    encodingTracedMappedAdversaryImpl_freshSigningActionsRepresented
      publicKey secretKey (adversary.main publicKey) ((initialCache, []), [])
      (forgery, (adversaryState, encodingTrace))
      (by simp [FreshSigningActionsRepresented]) hadversary
  change FreshSigningActionsRepresented secretKey adversaryState.2
    (appendVerificationEncodingObservation secretKey forgery adversaryState.1
      finalCache encodingTrace)
  let forgedInput := Concrete.CacheView.encodingInput secretKey.parameter forgery.epoch
    (forgery.message, forgery.signature.randomness)
  by_cases hfresh : adversaryState.1 forgedInput = none
  · cases houtput : finalCache forgedInput with
    | none =>
        simpa [appendVerificationEncodingObservation, forgedInput, hfresh,
          houtput] using hrepresented
    | some output =>
        simpa [appendVerificationEncodingObservation, forgedInput, hfresh, houtput]
          using hrepresented.append_actions
            [EncodingMonitor.ObservedAction.query forgery.epoch output]
  · simpa [appendVerificationEncodingObservation, forgedInput, hfresh] using hrepresented

theorem detailedGameAfterKeygenWithEncodingTrace_freshSigningCollisionsRepresented
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec)
    (hinitialEncodingFree : ∀ epoch input,
      initialCache
        (Concrete.CacheView.encodingInput secretKey.parameter epoch input) = none)
    (result : GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hmem : result ∈ support
      (detailedGameAfterKeygenWithEncodingTrace adversary publicKey secretKey
        initialCache)) :
    FreshSigningCollisionsRepresented secretKey result.2.1.2 result.2.2 := by
  unfold detailedGameAfterKeygenWithEncodingTrace at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨forgery, adversaryState, encodingTrace⟩, hadversary, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨⟨verified, finalCache⟩, _hverify, hfinal⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  have hinvariants := encodingTracedMappedAdversaryImpl_encodingCollisionInvariants
    publicKey secretKey initialCache hinitialEncodingFree (adversary.main publicKey)
    ((initialCache, []), []) (forgery, (adversaryState, encodingTrace))
    (UnsignedEncodingEntriesRepresented.refl secretKey.parameter initialCache)
    (by simp [FreshSigningCollisionsRepresented, SigningCacheTrace.epochs]) hadversary
  have hrepresented := hinvariants.2
  change FreshSigningCollisionsRepresented secretKey adversaryState.2
    (appendVerificationEncodingObservation secretKey forgery adversaryState.1
      finalCache encodingTrace)
  let forgedInput := Concrete.CacheView.encodingInput secretKey.parameter forgery.epoch
    (forgery.message, forgery.signature.randomness)
  by_cases hfresh : adversaryState.1 forgedInput = none
  · cases houtput : finalCache forgedInput with
    | none =>
        simpa [appendVerificationEncodingObservation, forgedInput, hfresh,
          houtput] using hrepresented
    | some output =>
        simpa [appendVerificationEncodingObservation, forgedInput, hfresh, houtput]
          using hrepresented.append_actions
            [EncodingMonitor.ObservedAction.query forgery.epoch output]
  · simpa [appendVerificationEncodingObservation, forgedInput, hfresh] using hrepresented

theorem detailedGameWithEncodingTrace_signEpochs_sublist
    (adversary : Adversary Concrete.scheme)
    (result : GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hmem : result ∈ support (detailedGameWithEncodingTrace adversary)) :
    List.Sublist (EncodingMonitor.observedSignEpochs result.2.2)
      result.2.1.2.epochs := by
  unfold detailedGameWithEncodingTrace at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨publicKey, secretKey⟩, keyCache⟩, _hkeygen, hrest⟩ := hmem
  exact detailedGameAfterKeygenWithEncodingTrace_signEpochs_sublist adversary
    publicKey secretKey keyCache result hrest

theorem detailedGameWithEncodingTrace_freshSigningActionsRepresented
    (adversary : Adversary Concrete.scheme)
    (result : GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hmem : result ∈ support (detailedGameWithEncodingTrace adversary)) :
    FreshSigningActionsRepresented result.1.secretKey result.2.1.2 result.2.2 := by
  unfold detailedGameWithEncodingTrace at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨publicKey, secretKey⟩, keyCache⟩, _hkeygen, hrest⟩ := hmem
  have hrepresented :=
    detailedGameAfterKeygenWithEncodingTrace_freshSigningActionsRepresented adversary
      publicKey secretKey keyCache result hrest
  have hsecretKey :=
    (detailedGameAfterKeygenWithSigningTrace_invariants adversary publicKey secretKey
      keyCache (result.1, result.2.1) (by
        have hprojection : (result.1, result.2.1) ∈ support
            (detailedGameAfterKeygenWithSigningTrace adversary publicKey secretKey
              keyCache) := by
          rw [← detailedGameAfterKeygenWithEncodingTrace_projection, support_map]
          exact ⟨result, hrest, rfl⟩
        exact hprojection)).1
  rw [hsecretKey]
  exact hrepresented

theorem detailedGameWithEncodingTrace_freshSigningCollisionsRepresented
    (adversary : Adversary Concrete.scheme)
    (result : GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hmem : result ∈ support (detailedGameWithEncodingTrace adversary)) :
    FreshSigningCollisionsRepresented result.1.secretKey result.2.1.2 result.2.2 := by
  unfold detailedGameWithEncodingTrace at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨keyResult, hkeygen, hrest⟩ := hmem
  obtain ⟨⟨publicKey, secretKey⟩, keyCache⟩ := keyResult
  have hencodingFree : ∀ epoch input,
      keyCache (Concrete.CacheView.encodingInput secretKey.parameter epoch input) = none :=
    fun epoch input => Concrete.keygen_cache_none_encodingInput
      ((publicKey, secretKey), keyCache) hkeygen epoch input
  have hrepresented :=
    detailedGameAfterKeygenWithEncodingTrace_freshSigningCollisionsRepresented
      adversary publicKey secretKey keyCache hencodingFree result hrest
  have hprojection : (result.1, result.2.1) ∈ support
      (detailedGameAfterKeygenWithSigningTrace adversary publicKey secretKey keyCache) := by
    rw [← detailedGameAfterKeygenWithEncodingTrace_projection, support_map]
    exact ⟨result, hrest, rfl⟩
  have hsecretKey :=
    (detailedGameAfterKeygenWithSigningTrace_invariants adversary publicKey secretKey
      keyCache (result.1, result.2.1) hprojection).1
  rw [hsecretKey]
  exact hrepresented

theorem detailedGameWithEncodingTrace_signingEpochs_nodup_of_winning
    (adversary : Adversary Concrete.scheme)
    (result : GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hmem : result ∈ support (detailedGameWithEncodingTrace adversary))
    (hevent : WinningOutcomeBadEventOccurs result.2.1.1 result.1 .encoding) :
    result.2.1.2.epochs.Nodup := by
  have hprojected : (result.1, result.2.1) ∈
      support (detailedGameWithSigningTrace adversary) := by
    rw [← detailedGameWithEncodingTrace_projection, support_map]
    exact ⟨result, hmem, rfl⟩
  have hlog := (detailedGameWithSigningTrace_invariants adversary
    (result.1, result.2.1) hprojected).1
  have htraceNodup : result.2.1.2.epochs.Nodup := by
    have hvalid := hevent.signingTranscript_valid
    rw [← hlog] at hvalid
    unfold SigningTranscript.Valid at hvalid
    simpa [SigningCacheTrace.epochs, SigningCacheTrace.toSigningLog,
      List.map_map, Function.comp_def] using hvalid
  exact htraceNodup

theorem detailedGameWithEncodingTrace_signEpochs_nodup_of_winning
    (adversary : Adversary Concrete.scheme)
    (result : GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hmem : result ∈ support (detailedGameWithEncodingTrace adversary))
    (hevent : WinningOutcomeBadEventOccurs result.2.1.1 result.1 .encoding) :
    (EncodingMonitor.observedSignEpochs result.2.2).Nodup := by
  have htraceNodup :=
    detailedGameWithEncodingTrace_signingEpochs_nodup_of_winning adversary result
      hmem hevent
  exact htraceNodup.sublist
    (detailedGameWithEncodingTrace_signEpochs_sublist adversary result hmem)

theorem detailedGameWithEncodingTrace_freshSigningCollision_monitorHit
    (adversary : Adversary Concrete.scheme)
    (result : GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hmem : result ∈ support (detailedGameWithEncodingTrace adversary))
    (hevent : WinningOutcomeBadEventOccurs result.2.1.1 result.1 .encoding)
    (hcollision : ∃ entry ∈ result.2.1.2,
      entry.FreshSigningEncodingCollision result.1.secretKey) :
    EncodingMonitor.runObserved EncodingMonitor.State.empty result.2.2 = true := by
  obtain ⟨entry, hentry, hentryCollision⟩ := hcollision
  have htraceNodup :=
    detailedGameWithEncodingTrace_signingEpochs_nodup_of_winning adversary result
      hmem hevent
  have hactionNodup :=
    detailedGameWithEncodingTrace_signEpochs_nodup_of_winning adversary result
      hmem hevent
  have hrepresented :=
    detailedGameWithEncodingTrace_freshSigningCollisionsRepresented adversary result hmem
  obtain ⟨signedOutput, oldOutput, before, middle, after, hdigest, hactions⟩ :=
    hrepresented htraceNodup entry hentry hentryCollision
  rw [hactions]
  exact EncodingMonitor.runObserved_empty_eq_true_of_query_before_sign_of_nodup
    entry.request.epoch oldOutput signedOutput before middle after hdigest.symm
    (by simpa [hactions] using hactionNodup)

theorem detailedGameWithEncodingTrace_postSigningFreshForgedCollision_monitorHit
    (adversary : Adversary Concrete.scheme)
    (result : GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hmem : result ∈ support (detailedGameWithEncodingTrace adversary))
    (hevent : WinningOutcomeBadEventOccurs result.2.1.1 result.1 .encoding)
    (hcollision : ∃ entry ∈ result.2.1.2,
      entry.PostSigningFreshForgedEncodingCollision result.1.secretKey
        result.1.forgery result.2.1.1) :
    EncodingMonitor.runObserved EncodingMonitor.State.empty result.2.2 = true := by
  have htraceNodup :=
    detailedGameWithEncodingTrace_signingEpochs_nodup_of_winning adversary result
      hmem hevent
  have hactionNodup :=
    detailedGameWithEncodingTrace_signEpochs_nodup_of_winning adversary result
      hmem hevent
  unfold detailedGameWithEncodingTrace at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨publicKey, secretKey⟩, keyCache⟩, _hkeygen, hrest⟩ := hmem
  unfold detailedGameAfterKeygenWithEncodingTrace at hrest
  rw [mem_support_bind_iff] at hrest
  obtain ⟨⟨forgery, adversaryState, encodingTrace⟩, hadversary, hverifyRest⟩ := hrest
  rw [mem_support_bind_iff] at hverifyRest
  obtain ⟨⟨verified, finalCache⟩, hverify, hfinal⟩ := hverifyRest
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  have hinvariants := encodingTracedMappedAdversaryImpl_postSigningInvariants
    publicKey secretKey (adversary.main publicKey) ((keyCache, []), [])
    (forgery, (adversaryState, encodingTrace))
    (by simp [FreshSigningActionsRepresented])
    (by simp [PostSigningQueriesRepresented]) hadversary
  have hsignActions := hinvariants.1
  have hpostSigning := hinvariants.2
  obtain ⟨entry, hentry, hfreshForged, hentryForgedFresh,
    signature, hsignature, hsignedFresh⟩ := hcollision
  obtain ⟨collisionSignature, signedOutput, forgedOutput,
    hcollisionSignature, hepoch, _hforgedInitiallyFresh, hsigned,
    hforgedFinal, _hdistinct, hdigest⟩ := hfreshForged
  have hsignatureEq : collisionSignature = signature := by
    rw [hsignature] at hcollisionSignature
    exact (Option.some.inj hcollisionSignature).symm
  subst collisionSignature
  have hepoch' : entry.request.epoch = forgery.epoch := by
    simpa using hepoch
  let forgedInput := Concrete.CacheView.encodingInput secretKey.parameter forgery.epoch
    (forgery.message, forgery.signature.randomness)
  cases hadversaryForged : adversaryState.1 forgedInput with
  | some adversaryOutput =>
      have hcacheLe : adversaryState.1 ≤ finalCache :=
        xmssRom_cache_le _ adversaryState.1 (verified, finalCache) hverify
      have hadversaryOutputEq : adversaryOutput = forgedOutput := by
        have hcached := hcacheLe hadversaryForged
        change finalCache forgedInput = some forgedOutput at hforgedFinal
        rw [hforgedFinal] at hcached
        exact Option.some.inj hcached.symm
      subst adversaryOutput
      obtain ⟨before, middle, after, hactionsBase⟩ :=
        hpostSigning htraceNodup entry hentry signature signedOutput forgedInput
          forgedOutput hsignature hsignedFresh hsigned
          (by simp [forgedInput, hepoch']) hentryForgedFresh hadversaryForged
      have hactions :
          appendVerificationEncodingObservation secretKey forgery adversaryState.1
              finalCache encodingTrace =
            before ++ [.sign entry.request.epoch signedOutput] ++ middle ++
              [.query entry.request.epoch forgedOutput] ++ after := by
        simpa [appendVerificationEncodingObservation, forgedInput,
          hadversaryForged] using hactionsBase
      rw [hactions]
      exact EncodingMonitor.runObserved_empty_eq_true_of_sign_before_query_of_nodup
        entry.request.epoch signedOutput forgedOutput before middle after hdigest
        (by simpa [hactions] using hactionNodup)
  | none =>
      obtain ⟨actionOutput, before, middle, hactionOutput, hactionsBase⟩ :=
        hsignActions entry hentry signature hsignature hsignedFresh
      have hactionOutputEq : actionOutput = signedOutput := by
        rw [hsigned] at hactionOutput
        exact Option.some.inj hactionOutput.symm
      subst actionOutput
      have hactions :
          appendVerificationEncodingObservation secretKey forgery adversaryState.1
              finalCache encodingTrace =
            before ++ [.sign entry.request.epoch signedOutput] ++ middle ++
              [.query entry.request.epoch forgedOutput] ++ [] := by
        have hactionsBase' : encodingTrace =
            before ++ [.sign entry.request.epoch signedOutput] ++ middle := by
          simpa using hactionsBase
        change finalCache forgedInput = some forgedOutput at hforgedFinal
        rw [hactionsBase']
        simp [appendVerificationEncodingObservation, forgedInput,
          hadversaryForged, hforgedFinal, ← hepoch', List.append_assoc]
      rw [hactions]
      exact EncodingMonitor.runObserved_empty_eq_true_of_sign_before_query_of_nodup
        entry.request.epoch signedOutput forgedOutput before middle [] hdigest
        (by simpa [hactions] using hactionNodup)

end XmssSecurity
