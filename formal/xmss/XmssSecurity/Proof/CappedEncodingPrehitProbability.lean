import XmssSecurity.Proof.CappedSigningCacheTrace
import XmssSecurity.Proof.BoundedSignProbability
import XmssSecurity.Proof.EncodingPrehit
import XmssSecurity.Proof.PrecomputedBoundedSignProbability

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

theorem cappedCacheTracedMappedAdversaryImpl_query_trace_update
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      (QueryCache HashSpec × SigningCacheTrace))
    (hresult : result ∈ support
      ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey input).run
        (initialCache, initialTrace))) :
    result.2.2 = signingCacheTraceUpdate input initialCache result.1
      result.2.1 initialTrace := by
  rw [cappedCacheTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hresult
  obtain ⟨baseResult, _hbase, hfinal⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  rfl

theorem cappedCacheTracedMappedAdversaryImpl_trace_eq_append
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : α × (QueryCache HashSpec × SigningCacheTrace))
    (hresult : result ∈ support
      ((simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, initialTrace))) :
    ∃ suffix, result.2.2 = initialTrace ++ suffix := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache initialTrace result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨[], by simp⟩
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hresult
      obtain ⟨⟨output, middleState⟩, hquery, hrest⟩ := hresult
      have hquery' : (output, middleState) ∈ support
          ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey input).run
            (initialCache, initialTrace)) := by
        simpa [simulateQ_query] using hquery
      have hmiddle := cappedCacheTracedMappedAdversaryImpl_query_trace_update
        publicKey secretKey input initialCache initialTrace (output, middleState) hquery'
      obtain ⟨later, hlater⟩ := ih output middleState.1 middleState.2 result hrest
      cases input with
      | inl worldInput =>
          refine ⟨later, ?_⟩
          rw [hlater, hmiddle]
          simp [signingCacheTraceUpdate]
      | inr request =>
          refine ⟨[SigningCacheEntry.mk request output initialCache middleState.1] ++
            later, ?_⟩
          rw [hlater, hmiddle]
          simp [signingCacheTraceUpdate, List.append_assoc]

theorem cappedCacheTracedMappedAdversaryImpl_cache_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : α × (QueryCache HashSpec × SigningCacheTrace))
    (hresult : result ∈ support
      ((simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, initialTrace))) :
    initialCache ≤ result.2.1 := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache initialTrace result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact le_rfl
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hresult
      obtain ⟨⟨output, middleState⟩, hquery, hrest⟩ := hresult
      have hquery' : (output, middleState) ∈ support
          ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey input).run
            (initialCache, initialTrace)) := by
        simpa [simulateQ_query] using hquery
      have hbase : (output, middleState.1) ∈ support
          ((cappedUnloggedMappedAdversaryImpl publicKey secretKey input).run initialCache) := by
        have hprojection := cappedCacheTracedMappedAdversaryImpl_cache_projection
          publicKey secretKey
          (liftM ((OracleWorld + SigningSpec).query input)) initialCache initialTrace
        simp only [simulateQ_spec_query] at hprojection
        rw [← hprojection, support_map]
        exact ⟨(output, middleState), hquery', rfl⟩
      exact (cappedUnloggedMappedAdversaryImpl_cache_le publicKey secretKey input
        initialCache (output, middleState.1) hbase).trans
          (ih output middleState.1 middleState.2 result hrest)

noncomputable def cappedCacheTracedSigningQuery
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) (initialCache : QueryCache HashSpec)
    (initialTrace : SigningCacheTrace) :
    ProbComp (Option Signature × (QueryCache HashSpec × SigningCacheTrace)) :=
  ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey (.inr request) :
    StateT (QueryCache HashSpec × SigningCacheTrace) ProbComp
      (Option Signature))).run (initialCache, initialTrace)

theorem cappedCacheTracedSigningQuery_encodingInputPrehit_probability_le_cachedCount
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) (initialCache : QueryCache HashSpec)
    (initialTrace : SigningCacheTrace) :
    Pr[fun result : Option Signature ×
        (QueryCache HashSpec × SigningCacheTrace) =>
      (SigningCacheEntry.mk request result.1 initialCache result.2.1)
        |>.EncodingInputPrehit secretKey |
      cappedCacheTracedSigningQuery publicKey secretKey request initialCache initialTrace] ≤
      (signingAttemptLimit : ℝ≥0∞) *
        cachedEncodingEntryCount initialCache secretKey.parameter request.epoch *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
  have hprojection :
      Prod.map id Prod.fst <$>
          cappedCacheTracedSigningQuery publicKey secretKey request initialCache initialTrace =
        (simulateQ xmssRomImpl
          (Concrete.precomputedCappedSign publicKey secretKey request.epoch
            request.message)).run initialCache := by
    unfold cappedCacheTracedSigningQuery cappedCacheTracedMappedAdversaryImpl
    rw [QueryImpl.extendState_apply]
    change Prod.map id Prod.fst <$>
        ((simulateQ xmssRomImpl
          (Concrete.precomputedCappedSign publicKey secretKey request.epoch
            request.message)).run initialCache >>= _) = _
    simp
  calc
    _ = Pr[fun result : Option Signature × QueryCache HashSpec =>
        (SigningCacheEntry.mk request result.1 initialCache result.2)
          |>.EncodingInputPrehit secretKey |
        Prod.map id Prod.fst <$>
          cappedCacheTracedSigningQuery publicKey secretKey request initialCache
            initialTrace] := by
      rw [probEvent_map]
      rfl
    _ = Pr[fun result : Option Signature × QueryCache HashSpec =>
        (SigningCacheEntry.mk request result.1 initialCache result.2)
          |>.EncodingInputPrehit secretKey |
        (simulateQ xmssRomImpl
          (Concrete.precomputedCappedSign publicKey secretKey request.epoch
            request.message)).run initialCache] := by rw [hprojection]
    _ ≤ _ := by
      simpa [SigningCacheEntry.EncodingInputPrehit] using
        Concrete.precomputedCappedSign_encodingInput_initialCache_hit_le_cachedCount
          publicKey secretKey request.epoch request.message initialCache

end XmssSecurity
