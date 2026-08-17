import XmssSecurity.EncodingOracleSimulation
import XmssSecurity.EncodingAddressQueryBound
import VCVio.OracleComp.QueryTracking.SubSpec

open OracleComp OracleSpec

namespace XmssSecurity

set_option maxRecDepth 100000

theorem encodingSamplingTraceImpl_support_trace_any
    (input : EncodingSamplingWorld.Domain)
    (result : EncodingSamplingWorld.Range input × EncodingActionTrace)
    (hmem : result ∈ support (encodingSamplingTraceImpl input).run) :
    result.2 = encodingSamplingTraceFragment input result.1 := by
  have hrun :
      (encodingSamplingTraceImpl input).run =
        (fun output =>
          (output, encodingSamplingTraceFragment input output)) <$>
            encodingSamplingWorldImpl input := by
    unfold encodingSamplingTraceImpl
    rw [QueryImpl.withTraceAppend_apply, WriterT.run_bind']
    rw [WriterT.run_monadLift']
    simp [WriterT.run_tell]
  rw [hrun, support_map] at hmem
  obtain ⟨output, _houtput, heq⟩ := hmem
  subst result
  rfl

theorem encodingUniformQuery_support_trace_empty
    (index : unifSpec.Domain)
    (result : unifSpec.Range index × EncodingActionTrace)
    (hmem : result ∈ support
      (simulateQ encodingSamplingTraceImpl (encodingUniformQuery index)).run) :
    result.2 = [] := by
  unfold encodingUniformQuery at hmem
  rw [OracleComp.liftComp_query, simulateQ_map, WriterT.run_map', support_map]
    at hmem
  obtain ⟨outerResult, houter, hresultEq⟩ := hmem
  simp only [OracleQuery.input_query] at houter
  rw [simulateQ_liftM_query encodingSamplingTraceImpl
    (unifSpec.query index)] at houter
  simp only [QueryImpl.mapQuery, WriterT.run_map', support_map] at houter
  obtain ⟨handledResult, hhandled, houterEq⟩ := houter
  change handledResult ∈
    support (encodingSamplingTraceImpl (.inl index)).run at hhandled
  have htrace := encodingSamplingTraceImpl_support_trace_any
    (.inl index) handledResult hhandled
  have hresultTrace : result.2 = handledResult.2 := by
    calc
      result.2 = outerResult.2 := by
        simpa using (congrArg Prod.snd hresultEq).symm
      _ = handledResult.2 := by
        simpa using (congrArg Prod.snd houterEq).symm
  rw [hresultTrace, htrace]
  rfl

theorem encodingSamplingTrace_sign_epoch_count_le
    (epoch : Epoch) (computation : OracleComp EncodingSamplingWorld α)
    (fuel : Nat)
    (hbound : computation.IsQueryBoundP
      (IsEncodingSampleAt .sign epoch) fuel)
    (result : α × EncodingActionTrace)
    (hmem : result ∈ support
      (simulateQ encodingSamplingTraceImpl computation).run) :
    (EncodingMonitor.observedSignEpochs result.2).count epoch ≤ fuel := by
  induction computation using OracleComp.inductionOn generalizing fuel result with
  | pure value =>
      simp only [simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hmem
      subst result
      simp [EncodingMonitor.observedSignEpochs]
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hmem
      obtain ⟨⟨output, firstTrace⟩, hfirst, hrestMapped⟩ := hmem
      rw [support_map] at hrestMapped
      obtain ⟨restResult, hrest, heq⟩ := hrestMapped
      rw [simulateQ_spec_query] at hfirst
      have hfirstTrace := encodingSamplingTraceImpl_support_trace_any input
        (output, firstTrace) hfirst
      change firstTrace = encodingSamplingTraceFragment input output at hfirstTrace
      have hfirstCount :
          (EncodingMonitor.observedSignEpochs firstTrace).count epoch =
            if IsEncodingSampleAt .sign epoch input then 1 else 0 := by
        rw [hfirstTrace]
        cases input with
        | inl index =>
            simp [encodingSamplingTraceFragment,
              EncodingMonitor.observedSignEpochs]
        | inr address =>
            rcases address with ⟨kind, taggedEpoch, sampledInput⟩
            cases kind with
            | side =>
                cases taggedEpoch <;> simp [encodingSamplingTraceFragment,
                  EncodingMonitor.observedSignEpochs]
            | query =>
                cases taggedEpoch <;> simp [encodingSamplingTraceFragment,
                  EncodingMonitor.observedSignEpochs]
            | sign =>
                cases taggedEpoch with
                | none =>
                    simp [encodingSamplingTraceFragment,
                      EncodingMonitor.observedSignEpochs]
                | some taggedEpoch =>
                    by_cases heq : taggedEpoch = epoch
                    · subst taggedEpoch
                      simp [encodingSamplingTraceFragment,
                        EncodingMonitor.observedSignEpochs]
                    · simp [encodingSamplingTraceFragment,
                        EncodingMonitor.observedSignEpochs, heq]
      have hrestCount := ih output
        (if IsEncodingSampleAt .sign epoch input then fuel - 1 else fuel)
          (hbound.2 output) restResult hrest
      have htraceEq : firstTrace ++ restResult.2 = result.2 := by
        simpa using congrArg Prod.snd heq
      rw [← htraceEq, EncodingMonitor.observedSignEpochs_append,
        List.count_append, hfirstCount]
      by_cases htarget : IsEncodingSampleAt .sign epoch input
      · simp only [if_pos htarget] at hrestCount ⊢
        have hpositive : 0 < fuel := hbound.1.resolve_left (by simpa using htarget)
        omega
      · simpa only [if_neg htarget, zero_add] using hrestCount

theorem atHashAddress_encoding_of_encodingInputEpoch?_eq_some
    (parameter : PublicParameter) (input : HashInput) (epoch : Epoch)
    (hepoch : encodingInputEpoch? parameter input = some epoch) :
    AtHashAddress parameter (.encoding epoch) input := by
  obtain ⟨payload, hinput⟩ :=
    exists_encodingInput_of_encodingInputEpoch?_eq_some parameter input epoch hepoch
  rw [← hinput, Concrete.CacheView.encodingInput]
  exact (atHashAddress_tweakableHashInput_iff parameter
    (.encoding epoch) (.encoding epoch) _).2 rfl

theorem splitRandomOracle_sign_epochSample_bound_zero
    (parameter : PublicParameter) (input : HashInput) (epoch : Epoch)
    (cache : QueryCache HashSpec)
    (hnot : ¬ AtHashAddress parameter (.encoding epoch) input) :
    ((splitRandomOracle parameter .sign input).run cache).IsQueryBoundP
      (IsEncodingSampleAt .sign epoch) 0 := by
  unfold splitRandomOracle
  cases hcache : cache input with
  | some cached =>
      rw [QueryImpl.withCaching_run_some _ hcache]
      simp
  | none =>
      rw [QueryImpl.withCaching_run_none _ hcache,
        OracleComp.isQueryBoundP_map_iff]
      unfold freshEncodingSampleImpl encodingSampleAddress
      cases hepoch : encodingInputEpoch? parameter input with
      | none =>
          simp only [encodingSampleAddressFromEpoch]
          unfold encodingSampleQuery
          rw [OracleComp.liftComp_query]
          change (liftM (EncodingSamplingWorld.query
            (Sum.inr ⟨.side, none, input⟩)) : OracleComp EncodingSamplingWorld _)
              |>.IsQueryBoundP
                (IsEncodingSampleAt .sign epoch) 0
          rw [OracleComp.isQueryBoundP_query_iff]
          simp
      | some taggedEpoch =>
          have hne : taggedEpoch ≠ epoch := by
            intro heq
            subst taggedEpoch
            exact hnot
              (atHashAddress_encoding_of_encodingInputEpoch?_eq_some
                parameter input epoch hepoch)
          simp only [encodingSampleAddressFromEpoch]
          unfold encodingSampleQuery
          rw [OracleComp.liftComp_query]
          change (liftM (EncodingSamplingWorld.query
            (Sum.inr ⟨.sign, some taggedEpoch, input⟩)) :
              OracleComp EncodingSamplingWorld _)
                |>.IsQueryBoundP
                  (IsEncodingSampleAt .sign epoch) 0
          rw [OracleComp.isQueryBoundP_query_iff]
          simpa using hne

theorem splitRandomOracle_sign_epochSample_bound
    (parameter : PublicParameter) (input : HashInput) (epoch : Epoch)
    (cache : QueryCache HashSpec) :
    ((splitRandomOracle parameter .sign input).run cache).IsQueryBoundP
      (IsEncodingSampleAt .sign epoch) 1 := by
  exact (splitRandomOracle_encodingSample_bound parameter .sign input cache).of_imp
    (by
      intro sampleInput hsample
      cases sampleInput with
      | inl index => simp at hsample
      | inr address => simp)

theorem splitRandomOracle_query_sign_epochSample_bound_zero
    (parameter : PublicParameter) (input : HashInput) (epoch : Epoch)
    (cache : QueryCache HashSpec) :
    ((splitRandomOracle parameter .query input).run cache).IsQueryBoundP
      (IsEncodingSampleAt .sign epoch) 0 := by
  unfold splitRandomOracle
  cases hcache : cache input with
  | some cached =>
      rw [QueryImpl.withCaching_run_some _ hcache]
      simp
  | none =>
      rw [QueryImpl.withCaching_run_none _ hcache,
        OracleComp.isQueryBoundP_map_iff]
      unfold freshEncodingSampleImpl encodingSampleAddress
      cases hepoch : encodingInputEpoch? parameter input with
      | none =>
          simp only [encodingSampleAddressFromEpoch]
          unfold encodingSampleQuery
          rw [OracleComp.liftComp_query]
          change (liftM (EncodingSamplingWorld.query
            (Sum.inr ⟨.side, none, input⟩)) : OracleComp EncodingSamplingWorld _)
              |>.IsQueryBoundP
                (IsEncodingSampleAt .sign epoch) 0
          rw [OracleComp.isQueryBoundP_query_iff]
          simp
      | some taggedEpoch =>
          simp only [encodingSampleAddressFromEpoch]
          unfold encodingSampleQuery
          rw [OracleComp.liftComp_query]
          change (liftM (EncodingSamplingWorld.query
            (Sum.inr ⟨.query, some taggedEpoch, input⟩)) :
              OracleComp EncodingSamplingWorld _)
                |>.IsQueryBoundP
                  (IsEncodingSampleAt .sign epoch) 0
          rw [OracleComp.isQueryBoundP_query_iff]
          simp

theorem splitRandomOracle_simulateQ_sign_epochSample_bound
    (parameter : PublicParameter) (epoch : Epoch)
    (computation : OracleComp HashSpec α) (fuel : Nat)
    (hbound : computation.IsQueryBoundP
      (AtHashAddress parameter (.encoding epoch)) fuel)
    (cache : QueryCache HashSpec) :
    ((simulateQ (splitRandomOracle parameter .sign) computation).run cache)
      |>.IsQueryBoundP
        (IsEncodingSampleAt .sign epoch) fuel := by
  apply OracleComp.IsQueryBoundP.simulateQ_run_of_step hbound
  · intro input _ state
    exact splitRandomOracle_sign_epochSample_bound parameter input epoch state
  · intro input hnot state
    exact splitRandomOracle_sign_epochSample_bound_zero parameter input epoch state hnot

theorem splitXmssRom_sign_epochSample_bound
    (parameter : PublicParameter) (epoch : Epoch)
    (computation : OracleComp OracleWorld α) (fuel : Nat)
    (hbound : computation.IsQueryBoundP
      (IsEncodingHashQueryAt parameter epoch) fuel)
    (cache : QueryCache HashSpec) :
    ((simulateQ (splitXmssRomImpl parameter .sign) computation).run cache)
      |>.IsQueryBoundP
        (IsEncodingSampleAt .sign epoch) fuel := by
  apply OracleComp.IsQueryBoundP.simulateQ_run_add_inr_of_step
    (p := IsEncodingHashQueryAt parameter epoch)
    (q := IsEncodingSampleAt .sign epoch)
    (fun input => by simp [IsEncodingHashQueryAt]) hbound
  · intro input state
    exact (splitUniformOracle_encodingSample_bound input state).of_imp (by
      intro sampleInput hsample
      cases sampleInput <;> simp_all)
  · intro input _ state
    exact splitRandomOracle_sign_epochSample_bound parameter input epoch state
  · intro input hnot state
    exact splitRandomOracle_sign_epochSample_bound_zero parameter input epoch state
      (by simpa [IsEncodingHashQueryAt] using hnot)

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
  exact encodingSampleQuery_query_support_trace epoch input result hmem

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
  exact encodingSampleQuery_sign_support_trace epoch input result hmem

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

theorem splitUniformOracle_traced_trace_eq_nil
    (input : unifSpec.Domain) (cache : QueryCache HashSpec)
    (result : (unifSpec.Range input × QueryCache HashSpec) ×
      EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((splitUniformOracle input).run cache)).run)) :
    result.2 = [] := by
  unfold splitUniformOracle at hmem
  rw [QueryImpl.liftTarget_apply, StateT.run_monadLift, simulateQ_bind,
    WriterT.run_bind', mem_support_bind_iff] at hmem
  obtain ⟨⟨output, firstTrace⟩, hquery, hrestMapped⟩ := hmem
  rw [support_map] at hrestMapped
  obtain ⟨restResult, hrest, heq⟩ := hrestMapped
  simp only [simulateQ_pure, WriterT.run_pure', support_pure,
    Set.mem_singleton_iff] at hrest
  subst restResult
  have hfirstTrace := encodingUniformQuery_support_trace_empty input
    (output, firstTrace) hquery
  change firstTrace = [] at hfirstTrace
  have hresultTrace : firstTrace ++ [] = result.2 := by
    simpa using congrArg Prod.snd heq
  rw [← hresultTrace, hfirstTrace]
  simp

theorem splitRandomOracle_query_observedSignEpochs_eq_nil
    (parameter : PublicParameter) (input : HashInput)
    (cache : QueryCache HashSpec)
    (result : (HashOutput × QueryCache HashSpec) × EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((splitRandomOracle parameter .query input).run cache)).run)) :
    EncodingMonitor.observedSignEpochs result.2 = [] := by
  by_contra hne
  obtain ⟨epoch, hepoch⟩ := List.exists_mem_of_ne_nil
    (EncodingMonitor.observedSignEpochs result.2) hne
  have hpositive :
      0 < (EncodingMonitor.observedSignEpochs result.2).count epoch :=
    List.count_pos_iff.mpr hepoch
  have hzero := encodingSamplingTrace_sign_epoch_count_le epoch
    ((splitRandomOracle parameter .query input).run cache) 0
      (splitRandomOracle_query_sign_epochSample_bound_zero parameter input epoch cache)
      result hmem
  omega

theorem splitUniformOracle_simulateQ_trace_eq_nil
    {computation : ProbComp α} (cache : QueryCache HashSpec)
    (result : (α × QueryCache HashSpec) × EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((simulateQ splitUniformOracle computation).run cache)).run)) :
    result.2 = [] := by
  induction computation using OracleComp.inductionOn generalizing cache result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff] at hmem
      subst result
      rfl
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_bind,
        WriterT.run_bind', mem_support_bind_iff] at hmem
      obtain ⟨⟨⟨output, middleCache⟩, firstTrace⟩, hfirst,
        hrestMapped⟩ := hmem
      rw [support_map] at hrestMapped
      obtain ⟨restResult, hrest, heq⟩ := hrestMapped
      rw [simulateQ_spec_query] at hfirst
      have hfirstTrace := splitUniformOracle_traced_trace_eq_nil input cache
        ((output, middleCache), firstTrace) hfirst
      change firstTrace = [] at hfirstTrace
      have hrestTrace := ih output middleCache restResult hrest
      have htraceEq : firstTrace ++ restResult.2 = result.2 := by
        simpa using congrArg Prod.snd heq
      rw [← htraceEq, hfirstTrace, hrestTrace]
      simp

theorem splitXmssRom_simulateQ_query_observedSignEpochs_eq_nil
    (parameter : PublicParameter) (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec)
    (result : (α × QueryCache HashSpec) × EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((simulateQ (splitXmssRomImpl parameter .query) computation).run
          cache)).run)) :
    EncodingMonitor.observedSignEpochs result.2 = [] := by
  induction computation using OracleComp.inductionOn generalizing cache result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff] at hmem
      subst result
      rfl
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_bind,
        WriterT.run_bind', mem_support_bind_iff] at hmem
      obtain ⟨⟨⟨output, middleCache⟩, firstTrace⟩, hfirst,
        hrestMapped⟩ := hmem
      rw [support_map] at hrestMapped
      obtain ⟨restResult, hrest, heq⟩ := hrestMapped
      rw [simulateQ_spec_query] at hfirst
      have hfirstEpochs :
          EncodingMonitor.observedSignEpochs firstTrace = [] := by
        cases input with
        | inl uniformInput =>
            have htrace := splitUniformOracle_traced_trace_eq_nil uniformInput cache
              ((output, middleCache), firstTrace) hfirst
            change firstTrace = [] at htrace
            simp [htrace, EncodingMonitor.observedSignEpochs]
        | inr hashInput =>
            exact splitRandomOracle_query_observedSignEpochs_eq_nil parameter
              hashInput cache ((output, middleCache), firstTrace) hfirst
      have hrestEpochs := ih output middleCache restResult hrest
      have htraceEq : firstTrace ++ restResult.2 = result.2 := by
        simpa using congrArg Prod.snd heq
      rw [← htraceEq, EncodingMonitor.observedSignEpochs_append,
        hfirstEpochs, hrestEpochs]
      rfl

theorem splitUniformOracle_trace_eq_nil_of_exists
    (cache : QueryCache HashSpec)
    (result : (α × QueryCache HashSpec) × EncodingActionTrace)
    (hmem : ∃ computation : ProbComp α, result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((simulateQ splitUniformOracle computation).run cache)).run)) :
    result.2 = [] := by
  obtain ⟨computation, hresult⟩ := hmem
  exact splitUniformOracle_simulateQ_trace_eq_nil cache result hresult

theorem Concrete.signingRandomness_split_trace_eq_nil
    (cache : QueryCache HashSpec)
    (result : (Randomness × QueryCache HashSpec) × EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((simulateQ splitUniformOracle Concrete.signingRandomness).run cache)).run)) :
    result.2 = [] := by
  exact splitUniformOracle_simulateQ_trace_eq_nil
    (computation := Concrete.signingRandomness) cache result hmem

theorem Concrete.sign_traced_sign_epoch_count_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (epoch targetEpoch : Epoch) (message : Message)
    (cache : QueryCache HashSpec)
    (result : (Option Signature × QueryCache HashSpec) ×
      EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((simulateQ (splitXmssRomImpl secretKey.parameter .sign)
          (Concrete.singleAttemptScheme.sign publicKey secretKey epoch message)).run cache)).run)) :
    (EncodingMonitor.observedSignEpochs result.2).count targetEpoch ≤
      if epoch = targetEpoch then 1 else 0 := by
  change result ∈ support
    ((simulateQ encodingSamplingTraceImpl
      ((simulateQ (splitXmssRomImpl secretKey.parameter .sign)
        (Concrete.sign publicKey secretKey epoch message)).run cache)).run) at hmem
  rw [Concrete.sign_eq, simulateQ_bind, StateT.run_bind, simulateQ_bind,
    WriterT.run_bind', mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨randomness, middleCache⟩, firstTrace⟩, hfirst,
    hrestMapped⟩ := hmem
  rw [support_map] at hrestMapped
  obtain ⟨restResult, hrest, heq⟩ := hrestMapped
  simp only [splitXmssRomImpl,
    QueryImpl.simulateQ_add_liftM_left] at hfirst
  simp only [splitXmssRomImpl,
    QueryImpl.simulateQ_add_liftM_right] at hrest
  have hfirstTrace : firstTrace = [] := by
    have htrace := Concrete.signingRandomness_split_trace_eq_nil cache
      ((randomness, middleCache), firstTrace) hfirst
    exact htrace
  have hrestCount :
      (EncodingMonitor.observedSignEpochs restResult.2).count targetEpoch ≤
        if epoch = targetEpoch then 1 else 0 := by
    apply encodingSamplingTrace_sign_epoch_count_le targetEpoch
      ((simulateQ (splitRandomOracle secretKey.parameter .sign)
        (Concrete.signAttempt secretKey epoch message randomness)).run middleCache)
      (if epoch = targetEpoch then 1 else 0)
    · exact splitRandomOracle_simulateQ_sign_epochSample_bound
        secretKey.parameter targetEpoch
          (Concrete.signAttempt secretKey epoch message randomness)
          (if epoch = targetEpoch then 1 else 0)
          (Concrete.signAttempt_queryBound_encodingAddress secretKey epoch
            targetEpoch message randomness) middleCache
    · exact hrest
  have htraceEq : firstTrace ++ restResult.2 = result.2 := by
    simpa using congrArg Prod.snd heq
  rw [← htraceEq, hfirstTrace]
  simpa [EncodingMonitor.observedSignEpochs] using hrestCount

theorem Concrete.sign_traced_signEpochs_sublist_singleton
    (publicKey : PublicKey) (secretKey : SecretKey)
    (epoch : Epoch) (message : Message)
    (cache : QueryCache HashSpec)
    (result : (Option Signature × QueryCache HashSpec) ×
      EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((simulateQ (splitXmssRomImpl secretKey.parameter .sign)
          (Concrete.singleAttemptScheme.sign publicKey secretKey epoch message)).run cache)).run)) :
    List.Sublist (EncodingMonitor.observedSignEpochs result.2) [epoch] := by
  rw [List.sublist_singleton]
  let epochs := EncodingMonitor.observedSignEpochs result.2
  have hcount : epochs.count epoch ≤ 1 := by
    simpa [epochs] using Concrete.sign_traced_sign_epoch_count_le publicKey secretKey
      epoch epoch message cache result hmem
  have hall : ∀ candidate ∈ epochs, candidate = epoch := by
    intro candidate hcandidate
    by_contra hne
    have hzero := Concrete.sign_traced_sign_epoch_count_le publicKey secretKey
      epoch candidate message cache result hmem
    have hpositive : 0 < epochs.count candidate :=
      List.count_pos_iff.mpr hcandidate
    rw [if_neg (Ne.symm hne)] at hzero
    change epochs.count candidate ≤ 0 at hzero
    omega
  have hcountLength : epochs.count epoch = epochs.length :=
    List.count_eq_length.mpr fun candidate hcandidate =>
      (hall candidate hcandidate).symm
  have hlength : epochs.length ≤ 1 := by omega
  cases hepochs : epochs with
  | nil => exact Or.inl hepochs
  | cons first rest =>
      cases rest with
      | nil =>
          have hfirst : first = epoch := hall first (by simp [hepochs])
          subst first
          exact Or.inr hepochs
      | cons second tail =>
          simp [hepochs] at hlength

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
                      (Concrete.singleAttemptScheme.sign publicKey secretKey request.epoch
                        request.message)).run initialState.1.1)).run) at hunlogged
                have haction := splitXmssRom_simulateQ_sign_fresh_trace
                  secretKey.parameter (request.message, signature.randomness)
                    request.epoch
                    (Concrete.singleAttemptScheme.sign publicKey secretKey request.epoch
                      request.message) initialState.1.1
                    ((some signature, finalCache), baseTrace) hashOutput hfresh
                    houtput hunlogged
                have hsub := (List.Sublist.refl initialState.2).append
                  (List.singleton_sublist.mpr haction)
                simpa [encodingActionTraceUpdate, encodingObservation?, signedInput,
                  hfresh, houtput] using hsub
          · simp [encodingActionTraceUpdate, encodingObservation?, signedInput,
              hfresh]

theorem splitEncodingTracedMappedAdversaryImpl_query_externalSignEpochs_sublist
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
    List.Sublist
      (initialState.1.2.epochs ++
        EncodingMonitor.observedSignEpochs result.2)
      result.1.2.1.2.epochs := by
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
          have htrace := splitUniformOracle_traced_trace_eq_nil uniformInput
            initialState.1.1 ((output, finalCache), baseTrace) hunlogged
          change baseTrace = [] at htrace
          simp [htrace, signingCacheTraceUpdate,
            EncodingMonitor.observedSignEpochs]
      | inr hashInput =>
          have htrace := splitRandomOracle_query_observedSignEpochs_eq_nil
            secretKey.parameter hashInput initialState.1.1
              ((output, finalCache), baseTrace) hunlogged
          change EncodingMonitor.observedSignEpochs baseTrace = [] at htrace
          simp [htrace, signingCacheTraceUpdate]
  | inr request =>
      change ((output, finalCache), baseTrace) ∈ support
        ((simulateQ encodingSamplingTraceImpl
          ((simulateQ (splitXmssRomImpl secretKey.parameter .sign)
            (Concrete.singleAttemptScheme.sign publicKey secretKey request.epoch
              request.message)).run initialState.1.1)).run) at hunlogged
      have htrace := Concrete.sign_traced_signEpochs_sublist_singleton
        publicKey secretKey request.epoch request.message initialState.1.1
          ((output, finalCache), baseTrace) hunlogged
      have happend := (List.Sublist.refl initialState.1.2.epochs).append htrace
      simpa [signingCacheTraceUpdate, SigningCacheTrace.epochs] using happend

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

theorem splitEncodingTracedMappedAdversary_simulateQ_externalSignEpochs_sublist
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
    List.Sublist
      (initialState.1.2.epochs ++
        EncodingMonitor.observedSignEpochs result.2)
      result.1.2.1.2.epochs := by
  induction computation using OracleComp.inductionOn generalizing
      initialState result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff] at hmem
      subst result
      simp [EncodingMonitor.observedSignEpochs]
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_bind,
        WriterT.run_bind', mem_support_bind_iff] at hmem
      obtain ⟨⟨⟨output, middleState⟩, firstTrace⟩, hfirst,
        hrestMapped⟩ := hmem
      rw [support_map] at hrestMapped
      obtain ⟨restResult, hrest, heq⟩ := hrestMapped
      rw [simulateQ_spec_query] at hfirst
      have hfirstSub :=
        splitEncodingTracedMappedAdversaryImpl_query_externalSignEpochs_sublist
          publicKey secretKey input initialState
            ((output, middleState), firstTrace) hfirst
      have hrestSub := ih output middleState restResult hrest
      have hcombined :=
        (hfirstSub.append (List.Sublist.refl
          (EncodingMonitor.observedSignEpochs restResult.2))).trans hrestSub
      have hstateEq : restResult.1.2.1.2 = result.1.2.1.2 := by
        simpa using congrArg (fun value => value.1.2.1.2) heq
      have htraceEq : firstTrace ++ restResult.2 = result.2 := by
        simpa using congrArg Prod.snd heq
      rw [← hstateEq, ← htraceEq,
        EncodingMonitor.observedSignEpochs_append]
      simpa [List.append_assoc] using hcombined

theorem splitDetailedGameAfterKeygenWithEncodingTrace_trace_sublist
    (adversary : Adversary Concrete.singleAttemptScheme)
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
            (Concrete.singleAttemptScheme.verify publicKey forgery.epoch forgery.message
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

theorem splitDetailedGameAfterKeygenWithEncodingTrace_externalSignEpochs_sublist
    (adversary : Adversary Concrete.singleAttemptScheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec)
    (result : (GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
        EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        (splitDetailedGameAfterKeygenWithEncodingTrace adversary publicKey
          secretKey initialCache)).run)) :
    List.Sublist (EncodingMonitor.observedSignEpochs result.2)
      result.1.2.1.2.epochs := by
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
    splitEncodingTracedMappedAdversary_simulateQ_externalSignEpochs_sublist
      publicKey secretKey (adversary.main publicKey) ((initialCache, []), [])
        ((forgery, adversaryState), adversaryTrace) hadversary
  have hadversarySub' : List.Sublist
      (EncodingMonitor.observedSignEpochs adversaryTrace)
      adversaryState.1.2.epochs := by
    simpa [SigningCacheTrace.epochs] using hadversarySub
  have hverificationEpochs :=
    splitXmssRom_simulateQ_query_observedSignEpochs_eq_nil secretKey.parameter
      (Concrete.singleAttemptScheme.verify publicKey forgery.epoch forgery.message
        forgery.signature) adversaryState.1.1
          ((verified, finalCache), verificationTrace) hverify
  simp only [Prod.map_apply, id_eq]
  change List.Sublist
    (EncodingMonitor.observedSignEpochs
      (adversaryTrace ++ (verificationTrace ++ [])))
      adversaryState.1.2.epochs
  rw [List.append_nil, EncodingMonitor.observedSignEpochs_append,
    hverificationEpochs]
  simpa using hadversarySub'

theorem sampledDetailedGameWithEncodingTrace_trace_sublist
    (adversary : Adversary Concrete.singleAttemptScheme)
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

theorem sampledDetailedGameWithEncodingTrace_externalSignEpochs_sublist
    (adversary : Adversary Concrete.singleAttemptScheme)
    (result : (GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
        EncodingActionTrace)
    (hmem : result ∈ support (sampledDetailedGameWithEncodingTrace adversary)) :
    List.Sublist (EncodingMonitor.observedSignEpochs result.2)
      result.1.2.1.2.epochs := by
  unfold sampledDetailedGameWithEncodingTrace at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨publicKey, secretKey⟩, keyCache⟩, _hkeygen, hrest⟩ := hmem
  exact
    splitDetailedGameAfterKeygenWithEncodingTrace_externalSignEpochs_sublist
      adversary publicKey secretKey keyCache result hrest

theorem sampledDetailedGameWithEncodingTrace_externalSignEpochs_nodup_of_winning
    (adversary : Adversary Concrete.singleAttemptScheme)
    (result : (GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
        EncodingActionTrace)
    (hmem : result ∈ support (sampledDetailedGameWithEncodingTrace adversary))
    (hevent : WinningOutcomeBadEventOccurs result.1.2.1.1 result.1.1 .encoding) :
    (EncodingMonitor.observedSignEpochs result.2).Nodup := by
  have hsplit : result.1 ∈
      support (splitDetailedGameWithEncodingTrace adversary) := by
    rw [← sampledDetailedGameWithEncodingTrace_projection, support_map]
    exact ⟨result, hmem, rfl⟩
  have hmanual : result.1 ∈
      support (detailedGameWithEncodingTrace adversary) := by
    rw [mem_support_iff, probOutput_def] at hsplit ⊢
    rw [splitDetailedGameWithEncodingTrace_evalDist_simulation] at hsplit
    exact hsplit
  have hsigningNodup :=
    detailedGameWithEncodingTrace_signingEpochs_nodup_of_winning adversary
      result.1 hmanual hevent
  exact hsigningNodup.sublist
    (sampledDetailedGameWithEncodingTrace_externalSignEpochs_sublist adversary
      result hmem)

theorem sampledDetailedGameWithEncodingTrace_external_monitorHit_of_winning
    (adversary : Adversary Concrete.singleAttemptScheme)
    (result : (GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
        EncodingActionTrace)
    (hmem : result ∈ support (sampledDetailedGameWithEncodingTrace adversary))
    (hevent : WinningOutcomeBadEventOccurs result.1.2.1.1 result.1.1 .encoding)
    (hhit : EncodingMonitor.runObserved EncodingMonitor.State.empty
      result.1.2.2 = true) :
    EncodingMonitor.runObserved EncodingMonitor.State.empty result.2 = true := by
  exact EncodingMonitor.runObserved_empty_eq_true_mono_sublist
    (sampledDetailedGameWithEncodingTrace_trace_sublist adversary result hmem)
    (sampledDetailedGameWithEncodingTrace_externalSignEpochs_nodup_of_winning
      adversary result hmem hevent) hhit

end XmssSecurity
