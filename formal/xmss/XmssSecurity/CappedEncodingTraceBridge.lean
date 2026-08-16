import XmssSecurity.BoundedSignTrace
import XmssSecurity.CappedEncodingCollisionProbability

open OracleComp OracleSpec

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

end XmssSecurity
