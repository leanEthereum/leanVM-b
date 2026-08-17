import XmssSecurity.BoundedSignTrace
import XmssSecurity.CappedEncodingCollisionProbability
import XmssSecurity.PrecomputedSignQueryBound

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

set_option maxRecDepth 100000

theorem Concrete.signAttempt_none_validObservedSignEpochs_eq_nil
    (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (randomness : Randomness) (initialCache finalCache : QueryCache HashSpec)
    (trace : EncodingActionTrace)
    (hmem : ((none, finalCache), trace) ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((simulateQ (splitRandomOracle secretKey.parameter .sign)
          (Concrete.signAttempt secretKey epoch message randomness)).run
            initialCache)).run)) :
    CappedEncodingMonitor.validObservedSignEpochs trace = [] := by
  unfold Concrete.signAttempt Concrete.encodingHash Concrete.tweakableHash
    Concrete.oracleHash at hmem
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind,
    WriterT.run_bind', mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨output, queryCache⟩, queryTrace⟩, hquery, hrestMapped⟩ := hmem
  rw [support_map] at hrestMapped
  obtain ⟨restResult, hrest, heq⟩ := hrestMapped
  split at hrest
  · rename_i _ hdecode
    subst restResult
    have htraceEq : queryTrace = trace := by
      simpa using congrArg Prod.snd heq
    subst trace
    rw [simulateQ_bind, StateT.run_bind, simulateQ_bind,
      WriterT.run_bind', mem_support_bind_iff] at hquery
    obtain ⟨⟨⟨hashOutput, rawCache⟩, rawTrace⟩, hraw,
      htruncateMapped⟩ := hquery
    rw [support_map] at htruncateMapped
    obtain ⟨truncateResult, htruncate, htruncateEq⟩ := htruncateMapped
    simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure',
      support_pure, Set.mem_singleton_iff] at htruncate
    subst truncateResult
    have houtput : truncateHash hashOutput = output := by
      simpa using congrArg (fun value => value.1.1) htruncateEq
    have hcache : rawCache = queryCache := by
      simpa using congrArg (fun value => value.1.2) htruncateEq
    have htrace : rawTrace = queryTrace := by
      simpa using congrArg Prod.snd htruncateEq
    subst rawCache
    subst rawTrace
    let input := tweakableHashInput secretKey.parameter (.encoding epoch)
      (Concrete.encodingPayload message randomness)
    have hrawDirect : ((hashOutput, queryCache), queryTrace) ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((splitRandomOracle secretKey.parameter .sign input).run
          initialCache)).run) := by
      simpa [input, simulateQ_query] using hraw
    by_cases hfresh : initialCache
        input = none
    · have hqueryTrace := splitRandomOracle_sign_trace_fresh
        secretKey.parameter (message, randomness) epoch initialCache (by
          simpa [input, Concrete.CacheView.encodingInput] using hfresh)
          ((hashOutput, queryCache), queryTrace) (by
            simpa [input, Concrete.CacheView.encodingInput] using hrawDirect)
      change queryTrace = [.sign epoch hashOutput] at hqueryTrace
      rw [hqueryTrace]
      have hinvalid : ¬TargetSum.ValidDigest (truncateHash hashOutput) := by
        intro hvalid
        have hvalidOutput : TargetSum.ValidDigest output := by
          simpa [houtput] using hvalid
        obtain ⟨encoding, hencoding⟩ := hvalidOutput
        rw [hdecode] at hencoding
        simp at hencoding
      simp [CappedEncodingMonitor.validObservedSignEpochs,
        CappedEncodingMonitor.validActions,
        CappedEncodingMonitor.ActionValid, EncodingMonitor.observedSignEpochs,
        hinvalid]
    · cases hcached : initialCache input with
      | none => exact (hfresh hcached).elim
      | some cachedOutput =>
          unfold splitRandomOracle at hrawDirect
          rw [QueryImpl.withCaching_run_some _ hcached] at hrawDirect
          simp only [simulateQ_pure, WriterT.run_pure', support_pure,
            Set.mem_singleton_iff] at hrawDirect
          have htraceNil : queryTrace = [] := by
            simpa using congrArg Prod.snd hrawDirect
          rw [htraceNil]
          rfl
  · rw [simulateQ_map, StateT.run_map, simulateQ_map,
      WriterT.run_map', support_map] at hrest
    obtain ⟨baseResult, hsupport, hrestEq⟩ := hrest
    subst restResult
    rcases baseResult with ⟨⟨signature, cache⟩, tailTrace⟩
    simp at heq

theorem Concrete.signAttempt_traced_signEpochs_sublist_singleton
    (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec)
    (result : (Option Signature × QueryCache HashSpec) × EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((simulateQ (splitRandomOracle secretKey.parameter .sign)
          (Concrete.signAttempt secretKey epoch message randomness)).run cache)).run)) :
    List.Sublist (EncodingMonitor.observedSignEpochs result.2) [epoch] := by
  rw [List.sublist_singleton]
  let epochs := EncodingMonitor.observedSignEpochs result.2
  have hcount : epochs.count epoch ≤ 1 := by
    apply encodingSamplingTrace_sign_epoch_count_le epoch
      ((simulateQ (splitRandomOracle secretKey.parameter .sign)
        (Concrete.signAttempt secretKey epoch message randomness)).run cache) 1
    · simpa using splitRandomOracle_simulateQ_sign_epochSample_bound
        secretKey.parameter epoch
        (Concrete.signAttempt secretKey epoch message randomness) 1
        (by simpa using (Concrete.signAttempt_queryBound_encodingAddress
          secretKey epoch epoch message randomness)) cache
    · exact hmem
  have hall : ∀ candidate ∈ epochs, candidate = epoch := by
    intro candidate hcandidate
    by_contra hne
    have hzero := encodingSamplingTrace_sign_epoch_count_le candidate
      ((simulateQ (splitRandomOracle secretKey.parameter .sign)
        (Concrete.signAttempt secretKey epoch message randomness)).run cache) 0
      (splitRandomOracle_simulateQ_sign_epochSample_bound
        secretKey.parameter candidate
        (Concrete.signAttempt secretKey epoch message randomness) 0
        (by simpa [Ne.symm hne] using (Concrete.signAttempt_queryBound_encodingAddress
          secretKey epoch candidate message randomness)) cache)
      result hmem
    have hpositive : 0 < epochs.count candidate :=
      List.count_pos_iff.mpr hcandidate
    change epochs.count candidate ≤ 0 at hzero
    omega
  have hcountLength : epochs.count epoch = epochs.length :=
    List.count_eq_length.mpr fun candidate hcandidate =>
      (hall candidate hcandidate).symm
  have hlength : epochs.length ≤ 1 := by omega
  cases hepochs : epochs with
  | nil => exact Or.inl (by simpa [epochs] using hepochs)
  | cons head tail =>
      right
      have htail : tail = [] := by
        cases tail with
        | nil => rfl
        | cons second rest => simp [hepochs] at hlength
      subst tail
      have hhead : head = epoch := hall head (by simp [hepochs])
      simp [epochs, hepochs, hhead]

theorem Concrete.signAttempt_traced_validSignEpochs_sublist_singleton
    (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec)
    (result : (Option Signature × QueryCache HashSpec) × EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((simulateQ (splitRandomOracle secretKey.parameter .sign)
          (Concrete.signAttempt secretKey epoch message randomness)).run cache)).run)) :
    List.Sublist (CappedEncodingMonitor.validObservedSignEpochs result.2)
      [epoch] := by
  exact (EncodingMonitor.observedSignEpochs_sublist
    (CappedEncodingMonitor.validActions_sublist result.2)).trans
      (Concrete.signAttempt_traced_signEpochs_sublist_singleton secretKey epoch
        message randomness cache result hmem)

theorem Concrete.signBoundedAttempts_traced_validSignEpochs_sublist_singleton
    (attempts : Nat) (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (cache : QueryCache HashSpec)
    (result : (Option Signature × QueryCache HashSpec) × EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((simulateQ (splitXmssRomImpl secretKey.parameter .sign)
          (Concrete.signBoundedAttempts attempts secretKey epoch message)).run
            cache)).run)) :
    List.Sublist (CappedEncodingMonitor.validObservedSignEpochs result.2)
      [epoch] := by
  induction attempts generalizing cache result with
  | zero =>
      simp [Concrete.signBoundedAttempts] at hmem
      subst result
      simp [CappedEncodingMonitor.validObservedSignEpochs,
        CappedEncodingMonitor.validActions, EncodingMonitor.observedSignEpochs]
  | succ attempts ih =>
      rw [Concrete.signBoundedAttempts, simulateQ_bind, StateT.run_bind,
        simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hmem
      obtain ⟨⟨⟨randomness, randomnessCache⟩, randomnessTrace⟩, hrandomness,
        hrestMapped⟩ := hmem
      rw [support_map] at hrestMapped
      obtain ⟨restResult, hrest, hresultEq⟩ := hrestMapped
      simp only [splitXmssRomImpl,
        QueryImpl.simulateQ_add_liftM_left] at hrandomness
      have hrandomnessTrace : randomnessTrace = [] :=
        Concrete.signingRandomness_split_trace_eq_nil cache
          ((randomness, randomnessCache), randomnessTrace) hrandomness
      rw [simulateQ_bind, StateT.run_bind, simulateQ_bind,
        WriterT.run_bind', mem_support_bind_iff] at hrest
      obtain ⟨⟨⟨attemptResult, attemptCache⟩, attemptTrace⟩, hattempt,
        hcontinueMapped⟩ := hrest
      rw [support_map] at hcontinueMapped
      obtain ⟨tailResult, hcontinue, hrestEq⟩ := hcontinueMapped
      simp only [splitXmssRomImpl,
        QueryImpl.simulateQ_add_liftM_right] at hattempt
      have hrestTrace : attemptTrace ++ tailResult.2 = restResult.2 := by
        simpa using congrArg Prod.snd hrestEq
      have hresultTrace : randomnessTrace ++ restResult.2 = result.2 := by
        simpa using congrArg Prod.snd hresultEq
      have htraceEq : randomnessTrace ++ attemptTrace ++ tailResult.2 = result.2 := by
        calc
          _ = randomnessTrace ++ (attemptTrace ++ tailResult.2) :=
            List.append_assoc _ _ _
          _ = randomnessTrace ++ restResult.2 := by rw [hrestTrace]
          _ = result.2 := hresultTrace
      cases attemptResult with
      | none =>
          have hattemptNil :=
            Concrete.signAttempt_none_validObservedSignEpochs_eq_nil secretKey epoch
              message randomness randomnessCache attemptCache attemptTrace hattempt
          have htail := ih attemptCache tailResult hcontinue
          rw [← htraceEq, hrandomnessTrace,
            CappedEncodingMonitor.validObservedSignEpochs_append,
            CappedEncodingMonitor.validObservedSignEpochs_append, hattemptNil]
          simpa only [CappedEncodingMonitor.validObservedSignEpochs,
            CappedEncodingMonitor.validActions,
            EncodingMonitor.observedSignEpochs, List.nil_append] using htail
      | some signature =>
          simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure',
            support_pure, Set.mem_singleton_iff] at hcontinue
          subst tailResult
          have hattemptSub :=
            Concrete.signAttempt_traced_validSignEpochs_sublist_singleton
              secretKey epoch message randomness randomnessCache
                ((some signature, attemptCache), attemptTrace) hattempt
          rw [← htraceEq, hrandomnessTrace,
            CappedEncodingMonitor.validObservedSignEpochs_append,
            CappedEncodingMonitor.validObservedSignEpochs_append]
          simpa [CappedEncodingMonitor.validObservedSignEpochs,
            CappedEncodingMonitor.validActions,
            EncodingMonitor.observedSignEpochs, List.nil_append,
            List.append_nil] using hattemptSub

theorem Concrete.cappedSign_traced_validSignEpochs_sublist_singleton
    (publicKey : PublicKey) (secretKey : SecretKey)
    (epoch : Epoch) (message : Message) (cache : QueryCache HashSpec)
    (result : (Option Signature × QueryCache HashSpec) × EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((simulateQ (splitXmssRomImpl secretKey.parameter .sign)
          (Concrete.cappedSign publicKey secretKey epoch message)).run cache)).run)) :
    List.Sublist (CappedEncodingMonitor.validObservedSignEpochs result.2)
      [epoch] := by
  rw [Concrete.cappedSign_eq] at hmem
  exact Concrete.signBoundedAttempts_traced_validSignEpochs_sublist_singleton
    signingAttemptLimit secretKey epoch message cache result hmem

theorem Concrete.precomputedSignAttempt_none_validObservedSignEpochs_eq_nil
    (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (randomness : Randomness) (initialCache finalCache : QueryCache HashSpec)
    (trace : EncodingActionTrace)
    (hmem : ((none, finalCache), trace) ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((simulateQ (splitRandomOracle secretKey.parameter .sign)
          (Concrete.precomputedSignAttempt secretKey epoch message randomness)).run
            initialCache)).run)) :
    CappedEncodingMonitor.validObservedSignEpochs trace = [] := by
  unfold Concrete.precomputedSignAttempt Concrete.encodingHash Concrete.tweakableHash
    Concrete.oracleHash at hmem
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind,
    WriterT.run_bind', mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨output, queryCache⟩, queryTrace⟩, hquery, hrestMapped⟩ := hmem
  rw [support_map] at hrestMapped
  obtain ⟨restResult, hrest, heq⟩ := hrestMapped
  split at hrest
  · rename_i _ hdecode
    subst restResult
    have htraceEq : queryTrace = trace := by
      simpa using congrArg Prod.snd heq
    subst trace
    rw [simulateQ_bind, StateT.run_bind, simulateQ_bind,
      WriterT.run_bind', mem_support_bind_iff] at hquery
    obtain ⟨⟨⟨hashOutput, rawCache⟩, rawTrace⟩, hraw,
      htruncateMapped⟩ := hquery
    rw [support_map] at htruncateMapped
    obtain ⟨truncateResult, htruncate, htruncateEq⟩ := htruncateMapped
    simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure',
      support_pure, Set.mem_singleton_iff] at htruncate
    subst truncateResult
    have houtput : truncateHash hashOutput = output := by
      simpa using congrArg (fun value => value.1.1) htruncateEq
    have hcache : rawCache = queryCache := by
      simpa using congrArg (fun value => value.1.2) htruncateEq
    have htrace : rawTrace = queryTrace := by
      simpa using congrArg Prod.snd htruncateEq
    subst rawCache
    subst rawTrace
    let input := tweakableHashInput secretKey.parameter (.encoding epoch)
      (Concrete.encodingPayload message randomness)
    have hrawDirect : ((hashOutput, queryCache), queryTrace) ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((splitRandomOracle secretKey.parameter .sign input).run
          initialCache)).run) := by
      simpa [input, simulateQ_query] using hraw
    by_cases hfresh : initialCache input = none
    · have hqueryTrace := splitRandomOracle_sign_trace_fresh
        secretKey.parameter (message, randomness) epoch initialCache (by
          simpa [input, Concrete.CacheView.encodingInput] using hfresh)
          ((hashOutput, queryCache), queryTrace) (by
            simpa [input, Concrete.CacheView.encodingInput] using hrawDirect)
      change queryTrace = [.sign epoch hashOutput] at hqueryTrace
      rw [hqueryTrace]
      have hinvalid : ¬TargetSum.ValidDigest (truncateHash hashOutput) := by
        intro hvalid
        have hvalidOutput : TargetSum.ValidDigest output := by
          simpa [houtput] using hvalid
        obtain ⟨encoding, hencoding⟩ := hvalidOutput
        rw [hdecode] at hencoding
        simp at hencoding
      simp [CappedEncodingMonitor.validObservedSignEpochs,
        CappedEncodingMonitor.validActions,
        CappedEncodingMonitor.ActionValid, EncodingMonitor.observedSignEpochs,
        hinvalid]
    · cases hcached : initialCache input with
      | none => exact (hfresh hcached).elim
      | some cachedOutput =>
          unfold splitRandomOracle at hrawDirect
          rw [QueryImpl.withCaching_run_some _ hcached] at hrawDirect
          simp only [simulateQ_pure, WriterT.run_pure', support_pure,
            Set.mem_singleton_iff] at hrawDirect
          have htraceNil : queryTrace = [] := by
            simpa using congrArg Prod.snd hrawDirect
          rw [htraceNil]
          rfl
  · simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure',
      support_pure, Set.mem_singleton_iff] at hrest
    subst restResult
    simp at heq

theorem Concrete.precomputedSignAttempt_traced_signEpochs_sublist_singleton
    (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec)
    (result : (Option Signature × QueryCache HashSpec) × EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((simulateQ (splitRandomOracle secretKey.parameter .sign)
          (Concrete.precomputedSignAttempt secretKey epoch message randomness)).run
            cache)).run)) :
    List.Sublist (EncodingMonitor.observedSignEpochs result.2) [epoch] := by
  rw [List.sublist_singleton]
  let epochs := EncodingMonitor.observedSignEpochs result.2
  have hcount : epochs.count epoch ≤ 1 := by
    apply encodingSamplingTrace_sign_epoch_count_le epoch
      ((simulateQ (splitRandomOracle secretKey.parameter .sign)
        (Concrete.precomputedSignAttempt secretKey epoch message randomness)).run cache) 1
    · simpa using splitRandomOracle_simulateQ_sign_epochSample_bound
        secretKey.parameter epoch
        (Concrete.precomputedSignAttempt secretKey epoch message randomness) 1
        (by simpa using (Concrete.precomputedSignAttempt_queryBound_encodingAddress
          secretKey epoch epoch message randomness)) cache
    · exact hmem
  have hall : ∀ candidate ∈ epochs, candidate = epoch := by
    intro candidate hcandidate
    by_contra hne
    have hzero := encodingSamplingTrace_sign_epoch_count_le candidate
      ((simulateQ (splitRandomOracle secretKey.parameter .sign)
        (Concrete.precomputedSignAttempt secretKey epoch message randomness)).run cache) 0
      (splitRandomOracle_simulateQ_sign_epochSample_bound
        secretKey.parameter candidate
        (Concrete.precomputedSignAttempt secretKey epoch message randomness) 0
        (by simpa [Ne.symm hne] using
          (Concrete.precomputedSignAttempt_queryBound_encodingAddress
            secretKey epoch candidate message randomness)) cache)
      result hmem
    have hpositive : 0 < epochs.count candidate :=
      List.count_pos_iff.mpr hcandidate
    change epochs.count candidate ≤ 0 at hzero
    omega
  have hcountLength : epochs.count epoch = epochs.length :=
    List.count_eq_length.mpr fun candidate hcandidate =>
      (hall candidate hcandidate).symm
  have hlength : epochs.length ≤ 1 := by omega
  cases hepochs : epochs with
  | nil => exact Or.inl (by simpa [epochs] using hepochs)
  | cons head tail =>
      right
      have htail : tail = [] := by
        cases tail with
        | nil => rfl
        | cons second rest => simp [hepochs] at hlength
      subst tail
      have hhead : head = epoch := hall head (by simp [hepochs])
      simp [epochs, hepochs, hhead]

theorem Concrete.precomputedSignAttempt_traced_validSignEpochs_sublist_singleton
    (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec)
    (result : (Option Signature × QueryCache HashSpec) × EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((simulateQ (splitRandomOracle secretKey.parameter .sign)
          (Concrete.precomputedSignAttempt secretKey epoch message randomness)).run
            cache)).run)) :
    List.Sublist (CappedEncodingMonitor.validObservedSignEpochs result.2) [epoch] := by
  exact (EncodingMonitor.observedSignEpochs_sublist
    (CappedEncodingMonitor.validActions_sublist result.2)).trans
      (Concrete.precomputedSignAttempt_traced_signEpochs_sublist_singleton secretKey epoch
        message randomness cache result hmem)

theorem Concrete.precomputedSignBoundedAttempts_traced_validSignEpochs_sublist_singleton
    (attempts : Nat) (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (cache : QueryCache HashSpec)
    (result : (Option Signature × QueryCache HashSpec) × EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((simulateQ (splitXmssRomImpl secretKey.parameter .sign)
          (Concrete.precomputedSignBoundedAttempts attempts secretKey epoch message)).run
            cache)).run)) :
    List.Sublist (CappedEncodingMonitor.validObservedSignEpochs result.2) [epoch] := by
  induction attempts generalizing cache result with
  | zero =>
      simp [Concrete.precomputedSignBoundedAttempts] at hmem
      subst result
      simp [CappedEncodingMonitor.validObservedSignEpochs,
        CappedEncodingMonitor.validActions, EncodingMonitor.observedSignEpochs]
  | succ attempts ih =>
      rw [Concrete.precomputedSignBoundedAttempts, simulateQ_bind, StateT.run_bind,
        simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hmem
      obtain ⟨⟨⟨randomness, randomnessCache⟩, randomnessTrace⟩, hrandomness,
        hrestMapped⟩ := hmem
      rw [support_map] at hrestMapped
      obtain ⟨restResult, hrest, hresultEq⟩ := hrestMapped
      simp only [splitXmssRomImpl,
        QueryImpl.simulateQ_add_liftM_left] at hrandomness
      have hrandomnessTrace : randomnessTrace = [] :=
        Concrete.signingRandomness_split_trace_eq_nil cache
          ((randomness, randomnessCache), randomnessTrace) hrandomness
      rw [simulateQ_bind, StateT.run_bind, simulateQ_bind,
        WriterT.run_bind', mem_support_bind_iff] at hrest
      obtain ⟨⟨⟨attemptResult, attemptCache⟩, attemptTrace⟩, hattempt,
        hcontinueMapped⟩ := hrest
      rw [support_map] at hcontinueMapped
      obtain ⟨tailResult, hcontinue, hrestEq⟩ := hcontinueMapped
      simp only [splitXmssRomImpl,
        QueryImpl.simulateQ_add_liftM_right] at hattempt
      have hrestTrace : attemptTrace ++ tailResult.2 = restResult.2 := by
        simpa using congrArg Prod.snd hrestEq
      have hresultTrace : randomnessTrace ++ restResult.2 = result.2 := by
        simpa using congrArg Prod.snd hresultEq
      have htraceEq : randomnessTrace ++ attemptTrace ++ tailResult.2 = result.2 := by
        calc
          _ = randomnessTrace ++ (attemptTrace ++ tailResult.2) :=
            List.append_assoc _ _ _
          _ = randomnessTrace ++ restResult.2 := by rw [hrestTrace]
          _ = result.2 := hresultTrace
      cases attemptResult with
      | none =>
          have hattemptNil :=
            Concrete.precomputedSignAttempt_none_validObservedSignEpochs_eq_nil
              secretKey epoch message randomness randomnessCache attemptCache attemptTrace
                hattempt
          have htail := ih attemptCache tailResult hcontinue
          rw [← htraceEq, hrandomnessTrace,
            CappedEncodingMonitor.validObservedSignEpochs_append,
            CappedEncodingMonitor.validObservedSignEpochs_append, hattemptNil]
          simpa only [CappedEncodingMonitor.validObservedSignEpochs,
            CappedEncodingMonitor.validActions,
            EncodingMonitor.observedSignEpochs, List.nil_append] using htail
      | some signature =>
          simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure',
            support_pure, Set.mem_singleton_iff] at hcontinue
          subst tailResult
          have hattemptSub :=
            Concrete.precomputedSignAttempt_traced_validSignEpochs_sublist_singleton
              secretKey epoch message randomness randomnessCache
                ((some signature, attemptCache), attemptTrace) hattempt
          rw [← htraceEq, hrandomnessTrace,
            CappedEncodingMonitor.validObservedSignEpochs_append,
            CappedEncodingMonitor.validObservedSignEpochs_append]
          simpa [CappedEncodingMonitor.validObservedSignEpochs,
            CappedEncodingMonitor.validActions,
            EncodingMonitor.observedSignEpochs, List.nil_append,
            List.append_nil] using hattemptSub

theorem Concrete.precomputedCappedSign_traced_validSignEpochs_sublist_singleton
    (publicKey : PublicKey) (secretKey : SecretKey)
    (epoch : Epoch) (message : Message) (cache : QueryCache HashSpec)
    (result : (Option Signature × QueryCache HashSpec) × EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((simulateQ (splitXmssRomImpl secretKey.parameter .sign)
          (Concrete.precomputedCappedSign publicKey secretKey epoch message)).run cache)).run)) :
    List.Sublist (CappedEncodingMonitor.validObservedSignEpochs result.2) [epoch] := by
  rw [Concrete.precomputedCappedSign] at hmem
  exact Concrete.precomputedSignBoundedAttempts_traced_validSignEpochs_sublist_singleton
    signingAttemptLimit secretKey epoch message cache result hmem

theorem cappedSplitEncodingTracedMappedAdversaryImpl_query_trace_sublist
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState :
      (QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)
    (result : ((OracleWorld + SigningSpec).Range input ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
        EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((cappedSplitEncodingTracedMappedAdversaryImpl publicKey secretKey input).run
          initialState)).run)) :
    List.Sublist result.1.2.2 (initialState.2 ++ result.2) := by
  rw [cappedSplitEncodingTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨output, finalState⟩, externalTrace⟩, hbase, hfinal⟩ := hmem
  simp only [simulateQ_pure, WriterT.run_pure', map_pure, support_pure,
    Set.mem_singleton_iff, Prod.map_apply, id_eq] at hfinal
  subst result
  rw [cappedSplitCacheTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hbase
  obtain ⟨⟨⟨baseOutput, finalCache⟩, baseTrace⟩, hunlogged,
    hbaseFinal⟩ := hbase
  simp only [simulateQ_pure, WriterT.run_pure', map_pure, support_pure,
    Set.mem_singleton_iff, Prod.map_apply, id_eq] at hbaseFinal
  cases hbaseFinal
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput =>
          simp [encodingActionTraceUpdate, encodingObservation?]
      | inr hashInput =>
          by_cases hfresh : initialState.1.1 hashInput = none
          · cases hepoch : encodingInputEpoch? secretKey.parameter hashInput with
            | none =>
                simp [encodingActionTraceUpdate, encodingObservation?, hfresh,
                  hepoch]
            | some epoch =>
                change ((output, finalCache), baseTrace) ∈ support
                  ((simulateQ encodingSamplingTraceImpl
                    ((splitRandomOracle secretKey.parameter .query hashInput).run
                      initialState.1.1)).run) at hunlogged
                have htrace := splitRandomOracle_query_trace_fresh_of_epoch
                  secretKey.parameter hashInput epoch hepoch initialState.1.1
                    hfresh ((output, finalCache), baseTrace) hunlogged
                change baseTrace = [.query epoch output] at htrace
                have hsub := (List.Sublist.refl initialState.2).append
                  (List.singleton_sublist.mpr
                    (show EncodingMonitor.ObservedAction.query epoch output ∈
                      baseTrace by simp [htrace]))
                simpa [encodingActionTraceUpdate, encodingObservation?, hfresh,
                  hepoch] using hsub
          · simp [encodingActionTraceUpdate, encodingObservation?, hfresh]
  | inr request =>
      cases output with
      | none =>
          simp [encodingActionTraceUpdate, encodingObservation?]
      | some signature =>
          let signedInput := Concrete.CacheView.encodingInput secretKey.parameter
            request.epoch (request.message, signature.randomness)
          by_cases hfresh : initialState.1.1 signedInput = none
          · cases houtput : finalCache signedInput with
            | none =>
                simp [encodingActionTraceUpdate, encodingObservation?, signedInput,
                  hfresh, houtput]
            | some hashOutput =>
                change ((some signature, finalCache), baseTrace) ∈ support
                  ((simulateQ encodingSamplingTraceImpl
                    ((simulateQ (splitXmssRomImpl secretKey.parameter .sign)
                      (Concrete.scheme.sign publicKey secretKey request.epoch
                        request.message)).run initialState.1.1)).run) at hunlogged
                have haction := splitXmssRom_simulateQ_sign_fresh_trace
                  secretKey.parameter (request.message, signature.randomness)
                    request.epoch
                    (Concrete.scheme.sign publicKey secretKey request.epoch
                      request.message) initialState.1.1
                    ((some signature, finalCache), baseTrace) hashOutput hfresh
                    houtput hunlogged
                have hsub := (List.Sublist.refl initialState.2).append
                  (List.singleton_sublist.mpr haction)
                simpa [encodingActionTraceUpdate, encodingObservation?, signedInput,
                  hfresh, houtput] using hsub
          · simp [encodingActionTraceUpdate, encodingObservation?, signedInput,
              hfresh]

theorem cappedSplitEncodingTracedMappedAdversaryImpl_query_validSignEpochs_sublist
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState :
      (QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)
    (result : ((OracleWorld + SigningSpec).Range input ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
        EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((cappedSplitEncodingTracedMappedAdversaryImpl publicKey secretKey input).run
          initialState)).run)) :
    List.Sublist
      (initialState.1.2.epochs ++
        CappedEncodingMonitor.validObservedSignEpochs result.2)
      result.1.2.1.2.epochs := by
  rw [cappedSplitEncodingTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨output, finalState⟩, externalTrace⟩, hbase, hfinal⟩ := hmem
  simp only [simulateQ_pure, WriterT.run_pure', map_pure, support_pure,
    Set.mem_singleton_iff, Prod.map_apply, id_eq] at hfinal
  subst result
  rw [cappedSplitCacheTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hbase
  obtain ⟨⟨⟨baseOutput, finalCache⟩, baseTrace⟩, hunlogged,
    hbaseFinal⟩ := hbase
  simp only [simulateQ_pure, WriterT.run_pure', map_pure, support_pure,
    Set.mem_singleton_iff, Prod.map_apply, id_eq] at hbaseFinal
  cases hbaseFinal
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput =>
          have htrace := splitUniformOracle_traced_trace_eq_nil uniformInput
            initialState.1.1 ((output, finalCache), baseTrace) hunlogged
          change baseTrace = [] at htrace
          simp [htrace, signingCacheTraceUpdate,
            CappedEncodingMonitor.validObservedSignEpochs,
            CappedEncodingMonitor.validActions,
            EncodingMonitor.observedSignEpochs]
      | inr hashInput =>
          have htrace := splitRandomOracle_query_observedSignEpochs_eq_nil
            secretKey.parameter hashInput initialState.1.1
              ((output, finalCache), baseTrace) hunlogged
          have hvalidSub := EncodingMonitor.observedSignEpochs_sublist
            (CappedEncodingMonitor.validActions_sublist baseTrace)
          have hvalidNil :
              CappedEncodingMonitor.validObservedSignEpochs baseTrace = [] := by
            apply List.eq_nil_of_sublist_nil
            exact hvalidSub.trans (by simpa using htrace)
          simp [hvalidNil, signingCacheTraceUpdate]
  | inr request =>
      change ((output, finalCache), baseTrace) ∈ support
        ((simulateQ encodingSamplingTraceImpl
          ((simulateQ (splitXmssRomImpl secretKey.parameter .sign)
            (Concrete.scheme.sign publicKey secretKey request.epoch
              request.message)).run initialState.1.1)).run) at hunlogged
      have htrace := Concrete.precomputedCappedSign_traced_validSignEpochs_sublist_singleton
        publicKey secretKey request.epoch request.message initialState.1.1
          ((output, finalCache), baseTrace) hunlogged
      have happend := (List.Sublist.refl initialState.1.2.epochs).append htrace
      simpa [signingCacheTraceUpdate, SigningCacheTrace.epochs] using happend

theorem cappedSplitEncodingTracedMappedAdversary_simulateQ_trace_sublist
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState :
      (QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)
    (result : (α ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
        EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((simulateQ
          (cappedSplitEncodingTracedMappedAdversaryImpl publicKey secretKey)
            computation).run initialState)).run)) :
    List.Sublist result.1.2.2 (initialState.2 ++ result.2) := by
  induction computation using OracleComp.inductionOn generalizing
      initialState result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff] at hmem
      subst result
      change List.Sublist initialState.2 (initialState.2 ++ [])
      rw [List.append_nil]
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_bind,
        WriterT.run_bind', mem_support_bind_iff] at hmem
      obtain ⟨⟨⟨output, middleState⟩, firstTrace⟩, hfirst,
        hrestMapped⟩ := hmem
      rw [support_map] at hrestMapped
      obtain ⟨restResult, hrest, heq⟩ := hrestMapped
      rw [simulateQ_spec_query] at hfirst
      have hfirstSub :=
        cappedSplitEncodingTracedMappedAdversaryImpl_query_trace_sublist
          publicKey secretKey input initialState
            ((output, middleState), firstTrace) hfirst
      have hrestSub := ih output middleState restResult hrest
      have hcombined := hrestSub.trans
        (hfirstSub.append (List.Sublist.refl restResult.2))
      have hstateEq : restResult.1.2.2 = result.1.2.2 := by
        simpa using congrArg (fun value => value.1.2.2) heq
      have htraceEq : firstTrace ++ restResult.2 = result.2 := by
        simpa using congrArg Prod.snd heq
      rw [← hstateEq, ← htraceEq]
      simpa [List.append_assoc] using hcombined

theorem cappedSplitEncodingTracedMappedAdversary_simulateQ_validSignEpochs_sublist
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState :
      (QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)
    (result : (α ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
        EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((simulateQ
          (cappedSplitEncodingTracedMappedAdversaryImpl publicKey secretKey)
            computation).run initialState)).run)) :
    List.Sublist
      (initialState.1.2.epochs ++
        CappedEncodingMonitor.validObservedSignEpochs result.2)
      result.1.2.1.2.epochs := by
  induction computation using OracleComp.inductionOn generalizing
      initialState result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff] at hmem
      subst result
      simp [CappedEncodingMonitor.validObservedSignEpochs,
        CappedEncodingMonitor.validActions,
        EncodingMonitor.observedSignEpochs]
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_bind,
        WriterT.run_bind', mem_support_bind_iff] at hmem
      obtain ⟨⟨⟨output, middleState⟩, firstTrace⟩, hfirst,
        hrestMapped⟩ := hmem
      rw [support_map] at hrestMapped
      obtain ⟨restResult, hrest, heq⟩ := hrestMapped
      rw [simulateQ_spec_query] at hfirst
      have hfirstSub :=
        cappedSplitEncodingTracedMappedAdversaryImpl_query_validSignEpochs_sublist
          publicKey secretKey input initialState
            ((output, middleState), firstTrace) hfirst
      have hrestSub := ih output middleState restResult hrest
      have hcombined :=
        (hfirstSub.append (List.Sublist.refl
          (CappedEncodingMonitor.validObservedSignEpochs restResult.2))).trans
            hrestSub
      have hstateEq : restResult.1.2.1.2 = result.1.2.1.2 := by
        simpa using congrArg (fun value => value.1.2.1.2) heq
      have htraceEq : firstTrace ++ restResult.2 = result.2 := by
        simpa using congrArg Prod.snd heq
      rw [← hstateEq, ← htraceEq,
        CappedEncodingMonitor.validObservedSignEpochs_append]
      simpa [List.append_assoc] using hcombined

theorem cappedSplitDetailedGameAfterKeygenWithEncodingTrace_trace_sublist
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec)
    (result : (GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
        EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        (cappedSplitDetailedGameAfterKeygenWithEncodingTrace adversary publicKey
          secretKey initialCache)).run)) :
    List.Sublist result.1.2.2 result.2 := by
  unfold cappedSplitDetailedGameAfterKeygenWithEncodingTrace at hmem
  rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨forgery, adversaryState⟩, adversaryTrace⟩, hadversary,
    hrestMapped⟩ := hmem
  rw [support_map] at hrestMapped
  obtain ⟨verificationResult, hverificationBlock, hresultEq⟩ := hrestMapped
  rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff]
    at hverificationBlock
  obtain ⟨⟨⟨verified, finalCache⟩, verificationTrace⟩, hverify,
    hfinalMapped⟩ := hverificationBlock
  simp only [simulateQ_pure, WriterT.run_pure', map_pure, support_pure,
    Set.mem_singleton_iff, Prod.map_apply, id_eq] at hfinalMapped
  cases hfinalMapped
  cases hresultEq
  have hadversarySub :=
    cappedSplitEncodingTracedMappedAdversary_simulateQ_trace_sublist
      publicKey secretKey (adversary.main publicKey) ((initialCache, []), [])
        ((forgery, adversaryState), adversaryTrace) hadversary
  have hadversarySub' : List.Sublist adversaryState.2 adversaryTrace := by
    simpa using hadversarySub
  let forgedInput := Concrete.CacheView.encodingInput secretKey.parameter
    forgery.epoch (forgery.message, forgery.signature.randomness)
  by_cases hfresh : adversaryState.1.1 forgedInput = none
  · cases houtput : finalCache forgedInput with
    | none =>
        have hsub := hadversarySub'.trans
          (List.sublist_append_left adversaryTrace verificationTrace)
        simpa [appendVerificationEncodingObservation, forgedInput, hfresh,
          houtput] using hsub
    | some output =>
        have haction := splitXmssRom_simulateQ_query_fresh_trace
          secretKey.parameter
            (forgery.message, forgery.signature.randomness) forgery.epoch
            (Concrete.scheme.verify publicKey forgery.epoch forgery.message
              forgery.signature) adversaryState.1.1
            ((verified, finalCache), verificationTrace) output hfresh houtput
            hverify
        have hsub := hadversarySub'.append
          (List.singleton_sublist.mpr haction)
        simpa [appendVerificationEncodingObservation, forgedInput, hfresh,
          houtput] using hsub
  · have hsub := hadversarySub'.trans
        (List.sublist_append_left adversaryTrace verificationTrace)
    simpa [appendVerificationEncodingObservation, forgedInput, hfresh] using hsub

theorem cappedSplitDetailedGameAfterKeygenWithEncodingTrace_validSignEpochs_sublist
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec)
    (result : (GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
        EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        (cappedSplitDetailedGameAfterKeygenWithEncodingTrace adversary publicKey
          secretKey initialCache)).run)) :
    List.Sublist (CappedEncodingMonitor.validObservedSignEpochs result.2)
      result.1.2.1.2.epochs := by
  unfold cappedSplitDetailedGameAfterKeygenWithEncodingTrace at hmem
  rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨forgery, adversaryState⟩, adversaryTrace⟩, hadversary,
    hrestMapped⟩ := hmem
  rw [support_map] at hrestMapped
  obtain ⟨verificationResult, hverificationBlock, hresultEq⟩ := hrestMapped
  rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff]
    at hverificationBlock
  obtain ⟨⟨⟨verified, finalCache⟩, verificationTrace⟩, hverify,
    hfinalMapped⟩ := hverificationBlock
  simp only [simulateQ_pure, WriterT.run_pure', map_pure, support_pure,
    Set.mem_singleton_iff, Prod.map_apply, id_eq] at hfinalMapped
  cases hfinalMapped
  cases hresultEq
  have hadversarySub :=
    cappedSplitEncodingTracedMappedAdversary_simulateQ_validSignEpochs_sublist
      publicKey secretKey (adversary.main publicKey) ((initialCache, []), [])
        ((forgery, adversaryState), adversaryTrace) hadversary
  have hadversarySub' : List.Sublist
      (CappedEncodingMonitor.validObservedSignEpochs adversaryTrace)
      adversaryState.1.2.epochs := by
    simpa [SigningCacheTrace.epochs,
      CappedEncodingMonitor.validObservedSignEpochs,
      CappedEncodingMonitor.validActions,
      EncodingMonitor.observedSignEpochs] using hadversarySub
  have hverificationEpochs :=
    splitXmssRom_simulateQ_query_observedSignEpochs_eq_nil secretKey.parameter
      (Concrete.scheme.verify publicKey forgery.epoch forgery.message
        forgery.signature) adversaryState.1.1
          ((verified, finalCache), verificationTrace) hverify
  have hvalidVerification :
      CappedEncodingMonitor.validObservedSignEpochs verificationTrace = [] := by
    apply List.eq_nil_of_sublist_nil
    exact (EncodingMonitor.observedSignEpochs_sublist
      (CappedEncodingMonitor.validActions_sublist verificationTrace)).trans
        (by simpa using hverificationEpochs)
  simp only [Prod.map_apply, id_eq]
  change List.Sublist
    (CappedEncodingMonitor.validObservedSignEpochs
      (adversaryTrace ++ (verificationTrace ++ [])))
      adversaryState.1.2.epochs
  rw [List.append_nil,
    CappedEncodingMonitor.validObservedSignEpochs_append,
    hvalidVerification]
  simpa using hadversarySub'

theorem cappedSampledDetailedGameWithEncodingTrace_trace_sublist
    (adversary : Adversary Concrete.scheme)
    (result : (GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
        EncodingActionTrace)
    (hmem : result ∈ support
      (cappedSampledDetailedGameWithEncodingTrace adversary)) :
    List.Sublist result.1.2.2 result.2 := by
  unfold cappedSampledDetailedGameWithEncodingTrace at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨publicKey, secretKey⟩, keyCache⟩, _hkeygen, hrest⟩ := hmem
  exact cappedSplitDetailedGameAfterKeygenWithEncodingTrace_trace_sublist adversary
    publicKey secretKey keyCache result hrest

theorem cappedSampledDetailedGameWithEncodingTrace_validSignEpochs_sublist
    (adversary : Adversary Concrete.scheme)
    (result : (GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
        EncodingActionTrace)
    (hmem : result ∈ support
      (cappedSampledDetailedGameWithEncodingTrace adversary)) :
    List.Sublist (CappedEncodingMonitor.validObservedSignEpochs result.2)
      result.1.2.1.2.epochs := by
  unfold cappedSampledDetailedGameWithEncodingTrace at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨publicKey, secretKey⟩, keyCache⟩, _hkeygen, hrest⟩ := hmem
  exact
    cappedSplitDetailedGameAfterKeygenWithEncodingTrace_validSignEpochs_sublist
      adversary publicKey secretKey keyCache result hrest

theorem cappedDetailedGameWithEncodingTrace_signingLog_eq_trace
    (adversary : Adversary Concrete.scheme)
    (result : GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hmem : result ∈ support
      (cappedDetailedGameWithEncodingTrace adversary)) :
    result.1.signingLog = result.2.1.2.toSigningLog := by
  unfold cappedDetailedGameWithEncodingTrace at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨keyResult, _hkeygen, hrest⟩ := hmem
  unfold cappedDetailedGameAfterKeygenWithEncodingTrace at hrest
  rw [mem_support_bind_iff] at hrest
  obtain ⟨adversaryResult, _hadversary, hverification⟩ := hrest
  rw [mem_support_bind_iff] at hverification
  obtain ⟨verificationResult, _hverify, hfinal⟩ := hverification
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  rfl

theorem cappedSampledDetailedGameWithEncodingTrace_validSignEpochs_nodup_of_winning
    (adversary : Adversary Concrete.scheme)
    (result : (GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
        EncodingActionTrace)
    (hmem : result ∈ support
      (cappedSampledDetailedGameWithEncodingTrace adversary))
    (hevent : WinningOutcomeBadEventOccurs result.1.2.1.1 result.1.1 .encoding) :
    (CappedEncodingMonitor.validObservedSignEpochs result.2).Nodup := by
  have hsplit : result.1 ∈
      support (cappedSplitDetailedGameWithEncodingTrace adversary) := by
    rw [← cappedSampledDetailedGameWithEncodingTrace_projection, support_map]
    exact ⟨result, hmem, rfl⟩
  have hmanual : result.1 ∈
      support (cappedDetailedGameWithEncodingTrace adversary) := by
    rw [mem_support_iff, probOutput_def] at hsplit ⊢
    rw [cappedSplitDetailedGameWithEncodingTrace_evalDist_simulation] at hsplit
    exact hsplit
  have hlog := cappedDetailedGameWithEncodingTrace_signingLog_eq_trace
    adversary result.1 hmanual
  have htraceNodup : result.1.2.1.2.epochs.Nodup := by
    have hvalid := hevent.signingTranscript_valid
    rw [hlog] at hvalid
    unfold SigningTranscript.Valid at hvalid
    simpa [SigningCacheTrace.epochs, SigningCacheTrace.toSigningLog,
      List.map_map, Function.comp_def] using hvalid
  exact htraceNodup.sublist
    (cappedSampledDetailedGameWithEncodingTrace_validSignEpochs_sublist
      adversary result hmem)

theorem cappedSampledDetailedGameWithEncodingTrace_external_monitorHit_of_winning
    (adversary : Adversary Concrete.scheme)
    (result : (GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
        EncodingActionTrace)
    (hmem : result ∈ support
      (cappedSampledDetailedGameWithEncodingTrace adversary))
    (hevent : WinningOutcomeBadEventOccurs result.1.2.1.1 result.1.1 .encoding)
    (hhit : CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
      result.1.2.2 = true) :
    CappedEncodingMonitor.runObserved EncodingMonitor.State.empty result.2 = true := by
  exact CappedEncodingMonitor.runObserved_empty_eq_true_mono_sublist
    (cappedSampledDetailedGameWithEncodingTrace_trace_sublist
      adversary result hmem)
    (cappedSampledDetailedGameWithEncodingTrace_validSignEpochs_nodup_of_winning
      adversary result hmem hevent) hhit

theorem cappedWinning_encoding_monitorHit_probability_le_sampled_external
    (adversary : Adversary Concrete.scheme) :
    Pr[fun execution : GameOutcome ×
        ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
      WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
        CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
          execution.2.2 = true |
      cappedDetailedGameWithEncodingTrace adversary] ≤
    Pr[fun execution : (GameOutcome ×
        ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
          EncodingActionTrace =>
      CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
        execution.2 = true |
      cappedSampledDetailedGameWithEncodingTrace adversary] := by
  calc
    _ = Pr[fun execution : GameOutcome ×
          ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
        WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
          CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
            execution.2.2 = true |
        cappedSplitDetailedGameWithEncodingTrace adversary] := by
      rw [probEvent_def, probEvent_def,
        cappedSplitDetailedGameWithEncodingTrace_evalDist_simulation]
    _ = Pr[fun execution : (GameOutcome ×
          ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
            EncodingActionTrace =>
        WinningOutcomeBadEventOccurs execution.1.2.1.1 execution.1.1 .encoding ∧
          CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
            execution.1.2.2 = true |
        cappedSampledDetailedGameWithEncodingTrace adversary] := by
      rw [← cappedSampledDetailedGameWithEncodingTrace_projection, probEvent_map]
      rfl
    _ ≤ _ := by
      apply probEvent_mono
      intro execution hmem hevent
      exact cappedSampledDetailedGameWithEncodingTrace_external_monitorHit_of_winning
        adversary execution hmem hevent.1 hevent.2

theorem cappedWinning_encoding_monitorHit_probability_le
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    Pr[fun execution : GameOutcome ×
        ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
      WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
        CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
          execution.2.2 = true |
      cappedDetailedGameWithEncodingTrace adversary] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) :=
  (cappedWinning_encoding_monitorHit_probability_le_sampled_external adversary).trans
    (cappedSampledDetailedGame_externalCollision_probability_le q adversary hbound)

end XmssSecurity
