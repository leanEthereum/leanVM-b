import XmssSecurity.EncodingOracleSimulation

open OracleComp OracleSpec

namespace XmssSecurity

set_option maxRecDepth 100000

theorem freshEncodingSampleImpl_query_support_trace_of_epoch
    (parameter : PublicParameter) (input : HashInput) (epoch : Epoch)
    (hepoch : encodingInputEpoch? parameter input = some epoch)
    (result : HashOutput × EncodingActionTrace)
    (hmem : result ∈ support
      (simulateQ encodingSamplingTraceImpl
        (freshEncodingSampleImpl parameter .query input)).run) :
    result.2 = [.query epoch result.1] := by
  unfold freshEncodingSampleImpl at hmem
  rw [encodingSampleAddress_eq_of_epoch parameter .query input epoch hepoch] at hmem
  exact encodingSampleQuery_query_support_trace epoch result hmem

theorem freshEncodingSampleImpl_sign_support_trace_of_epoch
    (parameter : PublicParameter) (input : HashInput) (epoch : Epoch)
    (hepoch : encodingInputEpoch? parameter input = some epoch)
    (result : HashOutput × EncodingActionTrace)
    (hmem : result ∈ support
      (simulateQ encodingSamplingTraceImpl
        (freshEncodingSampleImpl parameter .sign input)).run) :
    result.2 = [.sign epoch result.1] := by
  unfold freshEncodingSampleImpl at hmem
  rw [encodingSampleAddress_eq_of_epoch parameter .sign input epoch hepoch] at hmem
  exact encodingSampleQuery_sign_support_trace epoch result hmem

theorem freshEncodingSampleImpl_query_support_trace
    (parameter : PublicParameter) (inputPayload : Message × Randomness)
    (epoch : Epoch) (result : HashOutput × EncodingActionTrace)
    (hmem : result ∈ support
      (simulateQ encodingSamplingTraceImpl
        (freshEncodingSampleImpl parameter .query
          (Concrete.CacheView.encodingInput parameter epoch inputPayload))).run) :
    result.2 = [.query epoch result.1] := by
  exact freshEncodingSampleImpl_query_support_trace_of_epoch parameter
    (Concrete.CacheView.encodingInput parameter epoch inputPayload) epoch
      (encodingInputEpoch?_encodingInput parameter epoch inputPayload) result hmem

theorem freshEncodingSampleImpl_sign_support_trace
    (parameter : PublicParameter) (inputPayload : Message × Randomness)
    (epoch : Epoch) (result : HashOutput × EncodingActionTrace)
    (hmem : result ∈ support
      (simulateQ encodingSamplingTraceImpl
        (freshEncodingSampleImpl parameter .sign
          (Concrete.CacheView.encodingInput parameter epoch inputPayload))).run) :
    result.2 = [.sign epoch result.1] := by
  exact freshEncodingSampleImpl_sign_support_trace_of_epoch parameter
    (Concrete.CacheView.encodingInput parameter epoch inputPayload) epoch
      (encodingInputEpoch?_encodingInput parameter epoch inputPayload) result hmem

theorem splitRandomOracle_query_trace_fresh_of_epoch
    (parameter : PublicParameter) (input : HashInput) (epoch : Epoch)
    (hepoch : encodingInputEpoch? parameter input = some epoch)
    (cache : QueryCache HashSpec) (hcache : cache input = none)
    (result : (HashOutput × QueryCache HashSpec) × EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((splitRandomOracle parameter .query input).run cache)).run)) :
    result.2 = [.query epoch result.1.1] := by
  rw [splitRandomOracle, QueryImpl.withCaching_run_none _ hcache,
    simulateQ_map, WriterT.run_map', support_map] at hmem
  obtain ⟨sampleResult, hsample, heq⟩ := hmem
  have hsampleTrace := freshEncodingSampleImpl_query_support_trace_of_epoch
    parameter input epoch hepoch sampleResult hsample
  have hresultTrace : result.2 = sampleResult.2 := by
    simpa using (congrArg Prod.snd heq).symm
  have hresultOutput : result.1.1 = sampleResult.1 := by
    simpa using (congrArg (fun value => value.1.1) heq).symm
  rw [hresultTrace, hresultOutput]
  exact hsampleTrace

theorem splitRandomOracle_query_trace_fresh
    (parameter : PublicParameter) (inputPayload : Message × Randomness)
    (epoch : Epoch) (cache : QueryCache HashSpec)
    (hcache : cache
      (Concrete.CacheView.encodingInput parameter epoch inputPayload) = none)
    (result : (HashOutput × QueryCache HashSpec) × EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((splitRandomOracle parameter .query
          (Concrete.CacheView.encodingInput parameter epoch inputPayload)).run cache)).run)) :
    result.2 = [.query epoch result.1.1] := by
  exact splitRandomOracle_query_trace_fresh_of_epoch parameter
    (Concrete.CacheView.encodingInput parameter epoch inputPayload) epoch
    (encodingInputEpoch?_encodingInput parameter epoch inputPayload)
    cache hcache result hmem

theorem splitRandomOracle_sign_trace_fresh
    (parameter : PublicParameter) (inputPayload : Message × Randomness)
    (epoch : Epoch) (cache : QueryCache HashSpec)
    (hcache : cache
      (Concrete.CacheView.encodingInput parameter epoch inputPayload) = none)
    (result : (HashOutput × QueryCache HashSpec) × EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((splitRandomOracle parameter .sign
          (Concrete.CacheView.encodingInput parameter epoch inputPayload)).run cache)).run)) :
    result.2 = [.sign epoch result.1.1] := by
  let input := Concrete.CacheView.encodingInput parameter epoch inputPayload
  change cache input = none at hcache
  change result ∈ support
    ((simulateQ encodingSamplingTraceImpl
      ((splitRandomOracle parameter .sign input).run cache)).run) at hmem
  rw [splitRandomOracle, QueryImpl.withCaching_run_none _ hcache,
    simulateQ_map, WriterT.run_map', support_map] at hmem
  obtain ⟨sampleResult, hsample, heq⟩ := hmem
  have hsampleTrace := freshEncodingSampleImpl_sign_support_trace_of_epoch
    parameter input epoch
      (encodingInputEpoch?_encodingInput parameter epoch inputPayload)
        sampleResult hsample
  have hresultTrace : result.2 = sampleResult.2 := by
    simpa using (congrArg Prod.snd heq).symm
  have hresultOutput : result.1.1 = sampleResult.1 := by
    simpa using (congrArg (fun value => value.1.1) heq).symm
  rw [hresultTrace, hresultOutput]
  exact hsampleTrace

theorem splitRandomOracle_traced_cache_eq
    (parameter : PublicParameter) (kind : EncodingSampleKind)
    (input : HashInput) (cache : QueryCache HashSpec)
    (result : (HashOutput × QueryCache HashSpec) × EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((splitRandomOracle parameter kind input).run cache)).run)) :
    result.1.2 = match cache input with
      | none => cache.cacheQuery input result.1.1
      | some _ => cache := by
  have hprojected : result.1 ∈ support
      (simulateQ encodingSamplingWorldImpl
        ((splitRandomOracle parameter kind input).run cache)) := by
    rw [← encodingSamplingTrace_projection, support_map]
    exact ⟨result, hmem, rfl⟩
  change result.1 ∈ support
    (runSplitRandomOracle parameter kind input cache) at hprojected
  rw [splitRandomOracle_bridge] at hprojected
  unfold runRandomOracle at hprojected
  cases hcache : cache input with
  | none =>
      rw [randomOracle_run_none_eq_uniformHashOutput input cache hcache,
        support_map] at hprojected
      obtain ⟨output, _houtput, heq⟩ := hprojected
      have houtputEq : output = result.1.1 := congrArg Prod.fst heq
      have hcacheEq : cache.cacheQuery input output = result.1.2 :=
        congrArg Prod.snd heq
      rw [← houtputEq]
      exact hcacheEq.symm
  | some cached =>
      rw [randomOracle, QueryImpl.withCaching_run_some _ hcache,
        support_pure, Set.mem_singleton_iff] at hprojected
      exact congrArg Prod.snd hprojected

theorem splitRandomOracle_simulateQ_traced_cache_le
    (parameter : PublicParameter) (kind : EncodingSampleKind)
    (computation : OracleComp HashSpec α)
    (initialCache : QueryCache HashSpec)
    (result : (α × QueryCache HashSpec) × EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((simulateQ (splitRandomOracle parameter kind) computation).run
          initialCache)).run)) :
    initialCache ≤ result.1.2 := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff] at hmem
      subst result
      exact le_rfl
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_bind,
        WriterT.run_bind', mem_support_bind_iff] at hmem
      obtain ⟨⟨⟨output, middleCache⟩, firstTrace⟩, hfirst,
        hrestMapped⟩ := hmem
      rw [support_map] at hrestMapped
      obtain ⟨restResult, hrest, heq⟩ := hrestMapped
      have hfirstCache : initialCache ≤ middleCache := by
        rw [simulateQ_spec_query] at hfirst
        have hcacheEq := splitRandomOracle_traced_cache_eq parameter kind
          input initialCache ((output, middleCache), firstTrace) hfirst
        change middleCache = match initialCache input with
          | none => initialCache.cacheQuery input output
          | some _ => initialCache at hcacheEq
        cases hcache : initialCache input with
        | none =>
            rw [hcache] at hcacheEq
            rw [hcacheEq]
            exact QueryCache.le_cacheQuery initialCache hcache
        | some cached =>
            rw [hcache] at hcacheEq
            exact le_of_eq hcacheEq.symm
      have hrestCache : middleCache ≤ restResult.1.2 :=
        ih output middleCache restResult hrest
      have hfinalCache : restResult.1.2 = result.1.2 := by
        simpa using congrArg (fun value => value.1.2) heq
      rw [← hfinalCache]
      exact hfirstCache.trans hrestCache

theorem splitRandomOracle_simulateQ_query_fresh_trace
    (parameter : PublicParameter) (targetPayload : Message × Randomness)
    (epoch : Epoch) (computation : OracleComp HashSpec α)
    (initialCache : QueryCache HashSpec)
    (result : (α × QueryCache HashSpec) × EncodingActionTrace)
    (targetOutput : HashOutput)
    (hcache : initialCache
      (Concrete.CacheView.encodingInput parameter epoch targetPayload) = none)
    (hfinal : result.1.2
      (Concrete.CacheView.encodingInput parameter epoch targetPayload) =
        some targetOutput)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((simulateQ (splitRandomOracle parameter .query) computation).run
          initialCache)).run)) :
    .query epoch targetOutput ∈ result.2 := by
  let targetInput := Concrete.CacheView.encodingInput parameter epoch targetPayload
  change initialCache targetInput = none at hcache
  change result.1.2 targetInput = some targetOutput at hfinal
  induction computation using OracleComp.inductionOn generalizing
      initialCache result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff] at hmem
      subst result
      change initialCache targetInput = some targetOutput at hfinal
      rw [hcache] at hfinal
      contradiction
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_bind,
        WriterT.run_bind', mem_support_bind_iff] at hmem
      obtain ⟨⟨⟨output, middleCache⟩, firstTrace⟩, hfirst,
        hrestMapped⟩ := hmem
      rw [support_map] at hrestMapped
      obtain ⟨restResult, hrest, heq⟩ := hrestMapped
      have hfinalRest : restResult.1.2 targetInput = some targetOutput := by
        rw [← hfinal]
        simpa using congrArg (fun value => value.1.2 targetInput) heq
      have htraceEq : firstTrace ++ restResult.2 = result.2 := by
        simpa using congrArg Prod.snd heq
      rw [simulateQ_spec_query] at hfirst
      cases hmiddle : middleCache targetInput with
      | none =>
          have hfound := ih output middleCache restResult hrest hmiddle hfinalRest
          rw [← htraceEq]
          exact List.mem_append_right firstTrace hfound
      | some middleOutput =>
          have hstepCache := splitRandomOracle_traced_cache_eq parameter .query
            input initialCache ((output, middleCache), firstTrace) hfirst
          change middleCache = match initialCache input with
            | none => initialCache.cacheQuery input output
            | some _ => initialCache at hstepCache
          have hinput : input = targetInput := by
            by_contra hne
            cases hinputCache : initialCache input with
            | none =>
                rw [hinputCache] at hstepCache
                change middleCache = initialCache.cacheQuery input output at hstepCache
                have hne' : targetInput ≠ input := fun heq => hne heq.symm
                have htargetStill : middleCache targetInput = none := by
                  rw [hstepCache,
                    QueryCache.cacheQuery_of_ne initialCache output hne']
                  exact hcache
                rw [hmiddle] at htargetStill
                contradiction
            | some cached =>
                rw [hinputCache] at hstepCache
                have htargetStill : middleCache targetInput = none := by
                  rw [hstepCache]
                  exact hcache
                rw [hmiddle] at htargetStill
                contradiction
          subst input
          have hfirstTrace := splitRandomOracle_query_trace_fresh parameter
            targetPayload epoch initialCache hcache
              ((output, middleCache), firstTrace) hfirst
          change firstTrace = [.query epoch output] at hfirstTrace
          have hmiddleOutput : middleCache targetInput = some output := by
            rw [hcache] at hstepCache
            change middleCache = initialCache.cacheQuery targetInput output at hstepCache
            rw [hstepCache]
            exact QueryCache.cacheQuery_self initialCache targetInput output
          have hrestLe := splitRandomOracle_simulateQ_traced_cache_le
            parameter .query (next output) middleCache restResult hrest
          have houtput : output = targetOutput := by
            have hpreserved := hrestLe hmiddleOutput
            rw [hfinalRest] at hpreserved
            exact Option.some.inj hpreserved.symm
          rw [← htraceEq, hfirstTrace, houtput]
          simp

theorem splitRandomOracle_simulateQ_sign_fresh_trace
    (parameter : PublicParameter) (targetPayload : Message × Randomness)
    (epoch : Epoch) (computation : OracleComp HashSpec α)
    (initialCache : QueryCache HashSpec)
    (result : (α × QueryCache HashSpec) × EncodingActionTrace)
    (targetOutput : HashOutput)
    (hcache : initialCache
      (Concrete.CacheView.encodingInput parameter epoch targetPayload) = none)
    (hfinal : result.1.2
      (Concrete.CacheView.encodingInput parameter epoch targetPayload) =
        some targetOutput)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((simulateQ (splitRandomOracle parameter .sign) computation).run
          initialCache)).run)) :
    .sign epoch targetOutput ∈ result.2 := by
  let targetInput := Concrete.CacheView.encodingInput parameter epoch targetPayload
  change initialCache targetInput = none at hcache
  change result.1.2 targetInput = some targetOutput at hfinal
  induction computation using OracleComp.inductionOn generalizing
      initialCache result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff] at hmem
      subst result
      change initialCache targetInput = some targetOutput at hfinal
      rw [hcache] at hfinal
      contradiction
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_bind,
        WriterT.run_bind', mem_support_bind_iff] at hmem
      obtain ⟨⟨⟨output, middleCache⟩, firstTrace⟩, hfirst,
        hrestMapped⟩ := hmem
      rw [support_map] at hrestMapped
      obtain ⟨restResult, hrest, heq⟩ := hrestMapped
      have hfinalRest : restResult.1.2 targetInput = some targetOutput := by
        rw [← hfinal]
        simpa using congrArg (fun value => value.1.2 targetInput) heq
      have htraceEq : firstTrace ++ restResult.2 = result.2 := by
        simpa using congrArg Prod.snd heq
      rw [simulateQ_spec_query] at hfirst
      cases hmiddle : middleCache targetInput with
      | none =>
          have hfound := ih output middleCache restResult hrest hmiddle hfinalRest
          rw [← htraceEq]
          exact List.mem_append_right firstTrace hfound
      | some middleOutput =>
          have hstepCache := splitRandomOracle_traced_cache_eq parameter .sign
            input initialCache ((output, middleCache), firstTrace) hfirst
          change middleCache = match initialCache input with
            | none => initialCache.cacheQuery input output
            | some _ => initialCache at hstepCache
          have hinput : input = targetInput := by
            by_contra hne
            cases hinputCache : initialCache input with
            | none =>
                rw [hinputCache] at hstepCache
                change middleCache = initialCache.cacheQuery input output at hstepCache
                have hne' : targetInput ≠ input := fun heq => hne heq.symm
                have htargetStill : middleCache targetInput = none := by
                  rw [hstepCache,
                    QueryCache.cacheQuery_of_ne initialCache output hne']
                  exact hcache
                rw [hmiddle] at htargetStill
                contradiction
            | some cached =>
                rw [hinputCache] at hstepCache
                have htargetStill : middleCache targetInput = none := by
                  rw [hstepCache]
                  exact hcache
                rw [hmiddle] at htargetStill
                contradiction
          subst input
          have hfirstTrace := splitRandomOracle_sign_trace_fresh parameter
            targetPayload epoch initialCache hcache
              ((output, middleCache), firstTrace) hfirst
          change firstTrace = [.sign epoch output] at hfirstTrace
          have hmiddleOutput : middleCache targetInput = some output := by
            rw [hcache] at hstepCache
            change middleCache = initialCache.cacheQuery targetInput output at hstepCache
            rw [hstepCache]
            exact QueryCache.cacheQuery_self initialCache targetInput output
          have hrestLe := splitRandomOracle_simulateQ_traced_cache_le
            parameter .sign (next output) middleCache restResult hrest
          have houtput : output = targetOutput := by
            have hpreserved := hrestLe hmiddleOutput
            rw [hfinalRest] at hpreserved
            exact Option.some.inj hpreserved.symm
          rw [← htraceEq, hfirstTrace, houtput]
          simp

theorem splitUniformOracle_traced_cache_eq
    (input : unifSpec.Domain) (cache : QueryCache HashSpec)
    (result : (unifSpec.Range input × QueryCache HashSpec) ×
      EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((splitUniformOracle input).run cache)).run)) :
    result.1.2 = cache := by
  have hprojected : result.1 ∈ support
      (simulateQ encodingSamplingWorldImpl
        ((splitUniformOracle input).run cache)) := by
    rw [← encodingSamplingTrace_projection, support_map]
    exact ⟨result, hmem, rfl⟩
  rw [splitUniformOracle_bridge] at hprojected
  have hrun :
      (unifFwdImpl HashSpec input).run cache =
        (fun sample => (sample, cache)) <$>
          (liftM (unifSpec.query input) : ProbComp _) := by
    simpa [simulateQ_query] using
      (unifFwdImpl.simulateQ_run
        (hashSpec := HashSpec)
        (liftM (unifSpec.query input) : ProbComp _) cache)
  rw [hrun, support_map] at hprojected
  obtain ⟨sample, _hsample, heq⟩ := hprojected
  exact (congrArg Prod.snd heq).symm

theorem splitXmssRom_simulateQ_traced_cache_le
    (parameter : PublicParameter) (kind : EncodingSampleKind)
    (computation : OracleComp OracleWorld α)
    (initialCache : QueryCache HashSpec)
    (result : (α × QueryCache HashSpec) × EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((simulateQ (splitXmssRomImpl parameter kind) computation).run
          initialCache)).run)) :
    initialCache ≤ result.1.2 := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff] at hmem
      subst result
      exact le_rfl
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_bind,
        WriterT.run_bind', mem_support_bind_iff] at hmem
      obtain ⟨⟨⟨output, middleCache⟩, firstTrace⟩, hfirst,
        hrestMapped⟩ := hmem
      rw [support_map] at hrestMapped
      obtain ⟨restResult, hrest, heq⟩ := hrestMapped
      have hfirstCache : initialCache ≤ middleCache := by
        rw [simulateQ_spec_query] at hfirst
        cases input with
        | inl uniformInput =>
            have hprojected : (output, middleCache) ∈ support
                (simulateQ encodingSamplingWorldImpl
                  ((splitUniformOracle uniformInput).run initialCache)) := by
              rw [← encodingSamplingTrace_projection, support_map]
              exact ⟨((output, middleCache), firstTrace), hfirst, rfl⟩
            rw [splitUniformOracle_bridge] at hprojected
            have hrun :
                (unifFwdImpl HashSpec uniformInput).run initialCache =
                  (fun sample => (sample, initialCache)) <$>
                    (liftM (unifSpec.query uniformInput) : ProbComp _) := by
              simpa [simulateQ_query] using
                (unifFwdImpl.simulateQ_run
                  (hashSpec := HashSpec)
                  (liftM (unifSpec.query uniformInput) : ProbComp _) initialCache)
            rw [hrun, support_map] at hprojected
            obtain ⟨sample, _hsample, heq⟩ := hprojected
            exact le_of_eq (congrArg Prod.snd heq)
        | inr hashInput =>
            have hcacheEq := splitRandomOracle_traced_cache_eq parameter kind
              hashInput initialCache ((output, middleCache), firstTrace) hfirst
            change middleCache = match initialCache hashInput with
              | none => initialCache.cacheQuery hashInput output
              | some _ => initialCache at hcacheEq
            cases hcache : initialCache hashInput with
            | none =>
                rw [hcache] at hcacheEq
                rw [hcacheEq]
                exact QueryCache.le_cacheQuery initialCache hcache
            | some cached =>
                rw [hcache] at hcacheEq
                exact le_of_eq hcacheEq.symm
      have hrestCache : middleCache ≤ restResult.1.2 :=
        ih output middleCache restResult hrest
      have hfinalCache : restResult.1.2 = result.1.2 := by
        simpa using congrArg (fun value => value.1.2) heq
      rw [← hfinalCache]
      exact hfirstCache.trans hrestCache

theorem splitXmssRom_simulateQ_fresh_trace_of
    (parameter : PublicParameter) (kind : EncodingSampleKind)
    (action : Epoch → HashOutput → EncodingMonitor.ObservedAction)
    (targetPayload : Message × Randomness) (epoch : Epoch)
    (computation : OracleComp OracleWorld α)
    (initialCache : QueryCache HashSpec)
    (result : (α × QueryCache HashSpec) × EncodingActionTrace)
    (targetOutput : HashOutput)
    (hcache : initialCache
      (Concrete.CacheView.encodingInput parameter epoch targetPayload) = none)
    (hfinal : result.1.2
      (Concrete.CacheView.encodingInput parameter epoch targetPayload) =
        some targetOutput)
    (hsingle : ∀ cache,
      cache (Concrete.CacheView.encodingInput parameter epoch targetPayload) = none →
      ∀ singleResult : (HashOutput × QueryCache HashSpec) ×
          EncodingActionTrace,
        singleResult ∈ support
          ((simulateQ encodingSamplingTraceImpl
            ((splitRandomOracle parameter kind
              (Concrete.CacheView.encodingInput parameter epoch targetPayload)).run
                cache)).run) →
        singleResult.2 = [action epoch singleResult.1.1])
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((simulateQ (splitXmssRomImpl parameter kind) computation).run
          initialCache)).run)) :
    action epoch targetOutput ∈ result.2 := by
  let targetInput := Concrete.CacheView.encodingInput parameter epoch targetPayload
  change initialCache targetInput = none at hcache
  change result.1.2 targetInput = some targetOutput at hfinal
  change ∀ cache, cache targetInput = none →
    ∀ singleResult : (HashOutput × QueryCache HashSpec) × EncodingActionTrace,
      singleResult ∈ support
        ((simulateQ encodingSamplingTraceImpl
          ((splitRandomOracle parameter kind targetInput).run cache)).run) →
      singleResult.2 = [action epoch singleResult.1.1] at hsingle
  induction computation using OracleComp.inductionOn generalizing
      initialCache result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff] at hmem
      subst result
      change initialCache targetInput = some targetOutput at hfinal
      rw [hcache] at hfinal
      contradiction
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_bind,
        WriterT.run_bind', mem_support_bind_iff] at hmem
      obtain ⟨⟨⟨output, middleCache⟩, firstTrace⟩, hfirst,
        hrestMapped⟩ := hmem
      rw [support_map] at hrestMapped
      obtain ⟨restResult, hrest, heq⟩ := hrestMapped
      have hfinalRest : restResult.1.2 targetInput = some targetOutput := by
        rw [← hfinal]
        simpa using congrArg (fun value => value.1.2 targetInput) heq
      have htraceEq : firstTrace ++ restResult.2 = result.2 := by
        simpa using congrArg Prod.snd heq
      rw [simulateQ_spec_query] at hfirst
      cases input with
      | inl uniformInput =>
          have hcacheEq := splitUniformOracle_traced_cache_eq uniformInput
            initialCache ((output, middleCache), firstTrace) hfirst
          change middleCache = initialCache at hcacheEq
          have hmiddleFresh : middleCache targetInput = none := by
            rw [hcacheEq]
            exact hcache
          have hfound := ih output middleCache restResult hrest hmiddleFresh
            hfinalRest
          rw [← htraceEq]
          exact List.mem_append_right firstTrace hfound
      | inr hashInput =>
          cases hmiddle : middleCache targetInput with
          | none =>
              have hfound := ih output middleCache restResult hrest hmiddle
                hfinalRest
              rw [← htraceEq]
              exact List.mem_append_right firstTrace hfound
          | some middleOutput =>
              have hstepCache := splitRandomOracle_traced_cache_eq parameter kind
                hashInput initialCache ((output, middleCache), firstTrace) hfirst
              change middleCache = match initialCache hashInput with
                | none => initialCache.cacheQuery hashInput output
                | some _ => initialCache at hstepCache
              have hinput : hashInput = targetInput := by
                by_contra hne
                cases hinputCache : initialCache hashInput with
                | none =>
                    rw [hinputCache] at hstepCache
                    change middleCache = initialCache.cacheQuery hashInput output
                      at hstepCache
                    have hne' : targetInput ≠ hashInput :=
                      fun heq => hne heq.symm
                    have htargetStill : middleCache targetInput = none := by
                      rw [hstepCache,
                        QueryCache.cacheQuery_of_ne initialCache output hne']
                      exact hcache
                    rw [hmiddle] at htargetStill
                    contradiction
                | some cached =>
                    rw [hinputCache] at hstepCache
                    have htargetStill : middleCache targetInput = none := by
                      rw [hstepCache]
                      exact hcache
                    rw [hmiddle] at htargetStill
                    contradiction
              subst hashInput
              have hfirstTrace := hsingle initialCache hcache
                ((output, middleCache), firstTrace) hfirst
              change firstTrace = [action epoch output] at hfirstTrace
              have hmiddleOutput : middleCache targetInput = some output := by
                rw [hcache] at hstepCache
                change middleCache = initialCache.cacheQuery targetInput output
                  at hstepCache
                rw [hstepCache]
                exact QueryCache.cacheQuery_self initialCache targetInput output
              have hrestLe := splitXmssRom_simulateQ_traced_cache_le
                parameter kind (next output) middleCache restResult hrest
              have houtput : output = targetOutput := by
                have hpreserved := hrestLe hmiddleOutput
                rw [hfinalRest] at hpreserved
                exact Option.some.inj hpreserved.symm
              rw [← htraceEq, hfirstTrace, houtput]
              simp

theorem splitXmssRom_simulateQ_query_fresh_trace
    (parameter : PublicParameter) (targetPayload : Message × Randomness)
    (epoch : Epoch) (computation : OracleComp OracleWorld α)
    (initialCache : QueryCache HashSpec)
    (result : (α × QueryCache HashSpec) × EncodingActionTrace)
    (targetOutput : HashOutput)
    (hcache : initialCache
      (Concrete.CacheView.encodingInput parameter epoch targetPayload) = none)
    (hfinal : result.1.2
      (Concrete.CacheView.encodingInput parameter epoch targetPayload) =
        some targetOutput)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((simulateQ (splitXmssRomImpl parameter .query) computation).run
          initialCache)).run)) :
    .query epoch targetOutput ∈ result.2 := by
  apply splitXmssRom_simulateQ_fresh_trace_of parameter .query
    EncodingMonitor.ObservedAction.query targetPayload epoch computation
    initialCache result targetOutput hcache hfinal
  · intro cache hfresh singleResult hsingle
    exact splitRandomOracle_query_trace_fresh parameter targetPayload epoch
      cache hfresh singleResult hsingle
  · exact hmem

theorem splitXmssRom_simulateQ_sign_fresh_trace
    (parameter : PublicParameter) (targetPayload : Message × Randomness)
    (epoch : Epoch) (computation : OracleComp OracleWorld α)
    (initialCache : QueryCache HashSpec)
    (result : (α × QueryCache HashSpec) × EncodingActionTrace)
    (targetOutput : HashOutput)
    (hcache : initialCache
      (Concrete.CacheView.encodingInput parameter epoch targetPayload) = none)
    (hfinal : result.1.2
      (Concrete.CacheView.encodingInput parameter epoch targetPayload) =
        some targetOutput)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((simulateQ (splitXmssRomImpl parameter .sign) computation).run
          initialCache)).run)) :
    .sign epoch targetOutput ∈ result.2 := by
  apply splitXmssRom_simulateQ_fresh_trace_of parameter .sign
    EncodingMonitor.ObservedAction.sign targetPayload epoch computation
    initialCache result targetOutput hcache hfinal
  · intro cache hfresh singleResult hsingle
    exact splitRandomOracle_sign_trace_fresh parameter targetPayload epoch
      cache hfresh singleResult hsingle
  · exact hmem

theorem splitEncodingTracedMappedAdversaryImpl_query_trace_sublist
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState :
      (QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)
    (result : ((OracleWorld + SigningSpec).Range input ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
        EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((splitEncodingTracedMappedAdversaryImpl publicKey secretKey input).run
          initialState)).run)) :
    List.Sublist result.1.2.2 (initialState.2 ++ result.2) := by
  rw [splitEncodingTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨output, finalState⟩, externalTrace⟩, hbase, hfinal⟩ := hmem
  simp only [simulateQ_pure, WriterT.run_pure', map_pure, support_pure,
    Set.mem_singleton_iff, Prod.map_apply, id_eq] at hfinal
  subst result
  rw [splitCacheTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
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

theorem splitEncodingTracedMappedAdversary_simulateQ_trace_sublist
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
          (splitEncodingTracedMappedAdversaryImpl publicKey secretKey)
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
        splitEncodingTracedMappedAdversaryImpl_query_trace_sublist
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

theorem splitDetailedGameAfterKeygenWithEncodingTrace_trace_sublist
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec)
    (result : (GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
        EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        (splitDetailedGameAfterKeygenWithEncodingTrace adversary publicKey
          secretKey initialCache)).run)) :
    List.Sublist result.1.2.2 result.2 := by
  unfold splitDetailedGameAfterKeygenWithEncodingTrace at hmem
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
    splitEncodingTracedMappedAdversary_simulateQ_trace_sublist
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

theorem sampledDetailedGameWithEncodingTrace_trace_sublist
    (adversary : Adversary Concrete.scheme)
    (result : (GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
        EncodingActionTrace)
    (hmem : result ∈ support (sampledDetailedGameWithEncodingTrace adversary)) :
    List.Sublist result.1.2.2 result.2 := by
  unfold sampledDetailedGameWithEncodingTrace at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨publicKey, secretKey⟩, keyCache⟩, _hkeygen, hrest⟩ := hmem
  exact splitDetailedGameAfterKeygenWithEncodingTrace_trace_sublist adversary
    publicKey secretKey keyCache result hrest

end XmssSecurity
