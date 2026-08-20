import XmssSecurity.Proof.CappedSigningCacheTrace
import XmssSecurity.Proof.BoundedSignProbability
import XmssSecurity.Proof.EncodingPrehit
import XmssSecurity.Proof.PrecomputedBoundedSignProbability
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

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
  exact OracleComp.simulateQ_run_preservesInv
    (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
    (fun state => ∃ suffix, state.2 = initialTrace ++ suffix)
    (by
      intro input state hstate queryResult hquery
      obtain ⟨suffix, hsuffix⟩ := hstate
      have hupdate := cappedCacheTracedMappedAdversaryImpl_query_trace_update
        publicKey secretKey input state.1 state.2 queryResult hquery
      cases input with
      | inl worldInput =>
          exact ⟨suffix, by simpa [signingCacheTraceUpdate, hsuffix] using hupdate⟩
      | inr request =>
          refine ⟨suffix ++ [SigningCacheEntry.mk request queryResult.1
            state.1 queryResult.2.1], ?_⟩
          simpa [signingCacheTraceUpdate, hsuffix, List.append_assoc] using hupdate)
    computation (initialCache, initialTrace) ⟨[], by simp⟩ result hresult

theorem cappedCacheTracedMappedAdversaryImpl_cache_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : α × (QueryCache HashSpec × SigningCacheTrace))
    (hresult : result ∈ support
      ((simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, initialTrace))) :
    initialCache ≤ result.2.1 := by
  exact OracleComp.simulateQ_run_preservesInv
    (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
    (fun state => initialCache ≤ state.1)
    (by
      intro input state hstate queryResult hquery
      exact hstate.trans
        (cappedCacheTracedMappedAdversaryImpl_query_cache_le
          publicKey secretKey input state queryResult hquery))
    computation (initialCache, initialTrace) le_rfl result hresult

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
        (simulateQ romImpl
          (Concrete.precomputedCappedSign secretKey request.epoch
            request.message)).run initialCache := by
    unfold cappedCacheTracedSigningQuery cappedCacheTracedMappedAdversaryImpl
    rw [QueryImpl.extendState_apply]
    change Prod.map id Prod.fst <$>
        ((simulateQ romImpl
          (Concrete.precomputedCappedSign secretKey request.epoch
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
        (simulateQ romImpl
          (Concrete.precomputedCappedSign secretKey request.epoch
            request.message)).run initialCache] := by rw [hprojection]
    _ ≤ _ := by
      simpa [SigningCacheEntry.EncodingInputPrehit] using
        Concrete.precomputedCappedSign_encodingInput_initialCache_hit_le_cachedCount
          secretKey request.epoch request.message initialCache

end XmssSecurity
