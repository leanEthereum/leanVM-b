import XmssSecurity.BoundedSignCache
import XmssSecurity.CappedSigningLogReplay
import XmssSecurity.SigningCacheTrace

open OracleComp OracleSpec

namespace XmssSecurity

def SigningCacheEntry.PreservesOtherValidEncodingInputs
    (secretKey : SecretKey) (entry : SigningCacheEntry) : Prop :=
  ∀ signature, entry.signature = some signature →
    ∀ targetEpoch targetInput encoding,
      TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash entry.finalCache secretKey.parameter
            targetEpoch targetInput) = some encoding →
      Concrete.CacheView.encodingInput secretKey.parameter entry.request.epoch
          (entry.request.message, signature.randomness) ≠
        Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput →
      entry.initialCache
          (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none →
      entry.finalCache
          (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none

def SigningCacheTrace.PreservesOtherValidEncodingInputs
    (secretKey : SecretKey) (trace : SigningCacheTrace) : Prop :=
  ∀ entry ∈ trace, entry.PreservesOtherValidEncodingInputs secretKey

noncomputable def cappedUnloggedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec) ProbComp) := by
  intro input
  cases input with
  | inl worldInput => exact xmssRomImpl worldInput
  | inr request =>
      exact simulateQ xmssRomImpl
        (Concrete.cappedScheme.sign publicKey secretKey request.epoch request.message)

noncomputable def cappedCacheTracedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec × SigningCacheTrace) ProbComp) :=
  QueryImpl.extendState (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
    signingCacheTraceUpdate

theorem cappedUnloggedMappedAdversaryImpl_cache_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (result : (OracleWorld + SigningSpec).Range input × QueryCache HashSpec)
    (hmem : result ∈ support
      ((cappedUnloggedMappedAdversaryImpl publicKey secretKey input).run initialCache)) :
    initialCache ≤ result.2 := by
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput =>
          have hrun :
              (unifFwdImpl HashSpec uniformInput).run initialCache =
                (fun sample => (sample, initialCache)) <$>
                  (liftM (unifSpec.query uniformInput) : ProbComp _) := by
            simpa [simulateQ_query] using
              (unifFwdImpl.simulateQ_run
                (hashSpec := HashSpec)
                (liftM (unifSpec.query uniformInput) : ProbComp _) initialCache)
          change result ∈ support
            ((unifFwdImpl HashSpec uniformInput).run initialCache) at hmem
          rw [hrun, support_map] at hmem
          obtain ⟨sample, _hsample, heq⟩ := hmem
          exact le_of_eq (congrArg Prod.snd heq)
      | inr hashInput =>
          change result ∈ support
            ((randomOracle (spec := HashSpec) hashInput).run initialCache) at hmem
          exact QueryImpl.withCaching_cache_le uniformSampleImpl hashInput initialCache
            result hmem
  | inr request =>
      exact xmssRom_cache_le
        (Concrete.cappedScheme.sign publicKey secretKey request.epoch request.message)
        initialCache result hmem

theorem cappedCacheTracedMappedAdversaryImpl_query_cachesLe
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      (QueryCache HashSpec × SigningCacheTrace))
    (htrace : initialTrace.CachesLe initialCache)
    (hmem : result ∈ support
      ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey input).run
        (initialCache, initialTrace))) :
    result.2.2.CachesLe result.2.1 := by
  rw [cappedCacheTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, finalCache⟩, hbase, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact signingCacheTraceUpdate_cachesLe input initialCache output finalCache
    initialTrace htrace
    (cappedUnloggedMappedAdversaryImpl_cache_le publicKey secretKey input initialCache
      (output, finalCache) hbase)

theorem cappedCacheTracedMappedAdversaryImpl_query_cacheOrder
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      (QueryCache HashSpec × SigningCacheTrace))
    (hchronological : initialTrace.Chronological)
    (hcaches : initialTrace.CachesLe initialCache)
    (hmem : result ∈ support
      ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey input).run
        (initialCache, initialTrace))) :
    result.2.2.Chronological ∧ result.2.2.CachesLe result.2.1 := by
  rw [cappedCacheTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, finalCache⟩, hbase, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  have hle := cappedUnloggedMappedAdversaryImpl_cache_le publicKey secretKey input
    initialCache (output, finalCache) hbase
  exact ⟨signingCacheTraceUpdate_chronological input initialCache output finalCache
      initialTrace hchronological hcaches,
    signingCacheTraceUpdate_cachesLe input initialCache output finalCache initialTrace
      hcaches hle⟩

theorem cappedCacheTracedMappedAdversaryImpl_query_successfulEncodingsCached
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      (QueryCache HashSpec × SigningCacheTrace))
    (htrace : initialTrace.SuccessfulEncodingsCached secretKey)
    (hmem : result ∈ support
      ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey input).run
        (initialCache, initialTrace))) :
    result.2.2.SuccessfulEncodingsCached secretKey := by
  rw [cappedCacheTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, finalCache⟩, hbase, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  cases input with
  | inl worldInput => simpa [signingCacheTraceUpdate] using htrace
  | inr request =>
      intro entry hentry
      rw [signingCacheTraceUpdate, List.mem_append] at hentry
      rcases hentry with hentry | hentry
      · exact htrace entry hentry
      · simp only [List.mem_singleton] at hentry
        subst entry
        intro signature hsignature
        change output = some signature at hsignature
        subst output
        exact Concrete.cappedSign_success_encodingInput_cached publicKey secretKey request
          initialCache finalCache signature hbase

theorem cappedCacheTracedMappedAdversaryImpl_query_preservesOtherValidEncodingInputs
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      (QueryCache HashSpec × SigningCacheTrace))
    (htrace : initialTrace.PreservesOtherValidEncodingInputs secretKey)
    (hmem : result ∈ support
      ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey input).run
        (initialCache, initialTrace))) :
    result.2.2.PreservesOtherValidEncodingInputs secretKey := by
  rw [cappedCacheTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, finalCache⟩, hbase, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  cases input with
  | inl worldInput => simpa [SigningCacheTrace.PreservesOtherValidEncodingInputs,
      signingCacheTraceUpdate] using htrace
  | inr request =>
      intro entry hentry
      rw [signingCacheTraceUpdate, List.mem_append] at hentry
      rcases hentry with hentry | hentry
      · exact htrace entry hentry
      · simp only [List.mem_singleton] at hentry
        subst entry
        intro signature hsignature targetEpoch targetInput encoding hdecode hother hnone
        change output = some signature at hsignature
        subst output
        by_cases hepoch : request.epoch = targetEpoch
        · exact Concrete.cappedSign_preserves_later_valid_other_encodingInput
            publicKey secretKey request.epoch targetEpoch request.message targetInput
            initialCache finalCache finalCache (some signature) hbase le_rfl encoding hdecode
            (by
              intro candidate hcand
              have heq : candidate = signature := Option.some.inj hcand.symm
              subst candidate
              exact hother)
            hnone
        · exact Concrete.cappedSign_preserves_other_epoch_encodingInput
            publicKey secretKey request.epoch targetEpoch request.message targetInput
            initialCache finalCache (some signature) hbase hepoch hnone

theorem cappedCacheTracedMappedAdversaryImpl_cachesLe
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : α × (QueryCache HashSpec × SigningCacheTrace))
    (htrace : initialTrace.CachesLe initialCache)
    (hmem : result ∈ support
      ((simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, initialTrace))) :
    result.2.2.CachesLe result.2.1 := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache initialTrace result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hmem
      subst result
      exact htrace
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleState⟩, hquery, hrest⟩ := hmem
      have hquery' : (output, middleState) ∈ support
          ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey input).run
            (initialCache, initialTrace)) := by
        simpa [simulateQ_query] using hquery
      exact ih output middleState.1 middleState.2 result
        (cappedCacheTracedMappedAdversaryImpl_query_cachesLe publicKey secretKey input
          initialCache initialTrace (output, middleState) htrace hquery') hrest

theorem cappedCacheTracedMappedAdversaryImpl_cacheOrder
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : α × (QueryCache HashSpec × SigningCacheTrace))
    (hchronological : initialTrace.Chronological)
    (hcaches : initialTrace.CachesLe initialCache)
    (hmem : result ∈ support
      ((simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, initialTrace))) :
    result.2.2.Chronological ∧ result.2.2.CachesLe result.2.1 := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache initialTrace result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hmem
      subst result
      exact ⟨hchronological, hcaches⟩
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleState⟩, hquery, hrest⟩ := hmem
      have hquery' : (output, middleState) ∈ support
          ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey input).run
            (initialCache, initialTrace)) := by
        simpa [simulateQ_query] using hquery
      obtain ⟨hmiddleChronological, hmiddleCaches⟩ :=
        cappedCacheTracedMappedAdversaryImpl_query_cacheOrder publicKey secretKey input
          initialCache initialTrace (output, middleState) hchronological hcaches hquery'
      exact ih output middleState.1 middleState.2 result hmiddleChronological
        hmiddleCaches hrest

theorem cappedCacheTracedMappedAdversaryImpl_successfulEncodingsCached
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : α × (QueryCache HashSpec × SigningCacheTrace))
    (htrace : initialTrace.SuccessfulEncodingsCached secretKey)
    (hmem : result ∈ support
      ((simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, initialTrace))) :
    result.2.2.SuccessfulEncodingsCached secretKey := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache initialTrace result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hmem
      subst result
      exact htrace
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleState⟩, hquery, hrest⟩ := hmem
      have hquery' : (output, middleState) ∈ support
          ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey input).run
            (initialCache, initialTrace)) := by
        simpa [simulateQ_query] using hquery
      exact ih output middleState.1 middleState.2 result
        (cappedCacheTracedMappedAdversaryImpl_query_successfulEncodingsCached
          publicKey secretKey input initialCache initialTrace (output, middleState)
          htrace hquery') hrest

theorem cappedCacheTracedMappedAdversaryImpl_preservesOtherValidEncodingInputs
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : α × (QueryCache HashSpec × SigningCacheTrace))
    (htrace : initialTrace.PreservesOtherValidEncodingInputs secretKey)
    (hmem : result ∈ support
      ((simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, initialTrace))) :
    result.2.2.PreservesOtherValidEncodingInputs secretKey := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache initialTrace result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hmem
      subst result
      exact htrace
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleState⟩, hquery, hrest⟩ := hmem
      have hquery' : (output, middleState) ∈ support
          ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey input).run
            (initialCache, initialTrace)) := by
        simpa [simulateQ_query] using hquery
      exact ih output middleState.1 middleState.2 result
        (cappedCacheTracedMappedAdversaryImpl_query_preservesOtherValidEncodingInputs
          publicKey secretKey input initialCache initialTrace (output, middleState)
          htrace hquery') hrest

end XmssSecurity
