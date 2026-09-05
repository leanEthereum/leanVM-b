import SphincsSecurity.Proof.EncodingPrehitSupport

namespace SphincsSecurity.Concrete.TightEncoding

open OracleComp OracleSpec

theorem prehitFree_fresh_transition_of_mem_support
    (secretKey : SecretKey) (event : QueryCache HashSpec → Prop)
    (computation : OracleComp OracleWorld α) (initialCache : QueryCache HashSpec)
    (value : α) (finalCache : QueryCache HashSpec)
    (hrun : ((value, finalCache), false) ∈ support
      (runEncodingPrehitMonitor secretKey computation initialCache false))
    (hbefore : ¬ event initialCache) (hafter : event finalCache) :
    ∃ (cache : QueryCache HashSpec) (input : HashInput) (answer : HashOutput),
      initialCache ≤ cache ∧ ¬ event cache ∧ cache input = none ∧
      event (cache.cacheQuery input answer) ∧ cache.cacheQuery input answer ≤ finalCache ∧
      ¬ EncodingMessagePrehit cache secretKey input answer := by
  classical
  induction computation using OracleComp.inductionOn generalizing initialCache with
  | pure output =>
      simp only [runEncodingPrehitMonitor_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, and_true] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      exact (hbefore hafter).elim
  | query_bind query next ih =>
      obtain ⟨⟨answer, middleCache⟩, hquery, hnohit, hrest⟩ :=
        (mem_support_runEncodingPrehitMonitor_query_bind_false_iff secretKey query next
          initialCache (value, finalCache)).mp hrun
      cases query with
      | inl uniformInput =>
          change (answer, middleCache) ∈ support ((unifFwdImpl HashSpec uniformInput).run initialCache) at hquery
          have hrunUniform := unifFwdImpl.simulateQ_run (hashSpec := HashSpec)
            (liftM (unifSpec.query uniformInput) : ProbComp _) initialCache
          simp only [simulateQ_spec_query] at hrunUniform
          rw [hrunUniform, support_map] at hquery
          obtain ⟨sample, _, heq⟩ := hquery
          obtain ⟨rfl, rfl⟩ := heq
          exact ih answer initialCache hrest hbefore
      | inr input =>
          change HashOutput at answer
          change (answer, middleCache) ∈ support ((randomOracle input).run initialCache) at hquery
          cases hcached : initialCache input with
          | some cachedAnswer =>
              rw [QueryImpl.withCaching_run_some uniformSampleImpl hcached,
                support_pure, Set.mem_singleton_iff] at hquery
              obtain ⟨rfl, rfl⟩ := hquery
              exact ih answer initialCache hrest hbefore
          | none =>
              rw [QueryImpl.withCaching_run_none uniformSampleImpl hcached, support_map] at hquery
              obtain ⟨freshAnswer, _, heq⟩ := hquery
              obtain ⟨rfl, rfl⟩ := heq
              by_cases hmiddle : event (initialCache.cacheQuery input answer)
              · refine ⟨initialCache, input, answer, le_rfl, hbefore, hcached, hmiddle, ?_, ?_⟩
                · exact cache_le_of_mem_runEncodingPrehitMonitor secretKey (next answer)
                    (initialCache.cacheQuery input answer) false ((value, finalCache), false) hrest
                · simpa [encodingPrehitQuery, hcached] using hnohit
              · obtain ⟨cache, laterInput, laterAnswer, hprefix, hlaterBefore, hfresh, hlaterAfter, hsuffix, hnohit⟩ :=
                  ih answer (initialCache.cacheQuery input answer) hrest hmiddle
                exact ⟨cache, laterInput, laterAnswer, (le_cacheQuery hcached).trans hprefix,
                  hlaterBefore, hfresh, hlaterAfter, hsuffix, hnohit⟩

theorem encodingMessage_ne_honestValue_of_prehitFree_continuation
    (secretKey : SecretKey) (position : EncodingPosition) (index : Index) (previous : HashInput)
    (htree : treeIndexAt index position.lay = position.tree)
    (hleaf : leafIndexAt index position.lay = position.leafIdx)
    (hat : AtEncodingPosition secretKey.parameter previous position)
    (computation : OracleComp OracleWorld α) (initialCache : QueryCache HashSpec)
    (value : α) (finalCache : QueryCache HashSpec)
    (hcached : initialCache previous ≠ none)
    (hbefore : ¬ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
      initialCache (layerMessagePosition index position.lay))
    (hafter : Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
      finalCache (layerMessagePosition index position.lay))
    (hrun : ((value, finalCache), false) ∈ support
      (runEncodingPrehitMonitor secretKey computation initialCache false)) :
    slotDigest 0 previous ≠ honestValue (fromCache finalCache)
      secretKey.parameter secretKey.otsSecret secretKey.ftsSecret (layerMessagePosition index position.lay) := by
  intro hmatch
  obtain ⟨cache, input, answer, hprefix, hunsettled, _hfresh, hsettled, hsuffix, hnohit⟩ :=
    prehitFree_fresh_transition_of_mem_support secretKey
      (fun cache => Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
        cache (layerMessagePosition index position.lay)) computation initialCache value finalCache hrun hbefore hafter
  apply hnohit
  refine ⟨position, index, previous, htree, hleaf, hunsettled, hsettled, hat, ?_, ?_⟩
  · obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hcached
    exact Option.ne_none_iff_exists'.mpr ⟨output, hprefix houtput⟩
  · exact hmatch.trans (honestValue_eq_of_settled (agreesWithFn_fromCache_of_le hsuffix) hsettled)

theorem encodingMessageSettledAt_of_prehitFree_matching_query
    (secretKey : SecretKey) (position : EncodingPosition) (index : Index) (input : HashInput)
    (htree : treeIndexAt index position.lay = position.tree)
    (hleaf : leafIndexAt index position.lay = position.leafIdx)
    (hat : AtEncodingPosition secretKey.parameter input position)
    (next : HashOutput → OracleComp OracleWorld α) (initialCache : QueryCache HashSpec)
    (value : α) (finalCache : QueryCache HashSpec)
    (hafter : Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
      finalCache (layerMessagePosition index position.lay))
    (hmatch : slotDigest 0 input = honestValue (fromCache finalCache)
      secretKey.parameter secretKey.otsSecret secretKey.ftsSecret (layerMessagePosition index position.lay))
    (hrun : ((value, finalCache), false) ∈ support
      (runEncodingPrehitMonitor secretKey (OracleWorld.query (.inr input) >>= next) initialCache false)) :
    EncodingMessageSettledAt initialCache secretKey position := by
  classical
  by_contra hbefore
  obtain ⟨⟨answer, middleCache⟩, hquery, _hnohit, hrest⟩ :=
    (mem_support_runEncodingPrehitMonitor_query_bind_false_iff secretKey (.inr input) next
      initialCache (value, finalCache)).mp hrun
  change HashOutput at answer
  change (answer, middleCache) ∈ support ((randomOracle input).run initialCache) at hquery
  have impossible (cache : QueryCache HashSpec) (output : HashOutput)
      (hcached : cache input ≠ none) (hunsettled : ¬ EncodingMessageSettledAt cache secretKey position)
      (hcontinuation : ((value, finalCache), false) ∈ support
        (runEncodingPrehitMonitor secretKey (next output) cache false)) : False := by
    apply encodingMessage_ne_honestValue_of_prehitFree_continuation secretKey position index input htree hleaf hat
      (next output) cache value finalCache hcached (fun hsettled => hunsettled ⟨index, htree, hleaf, hsettled⟩)
      hafter hcontinuation hmatch
  cases hcached : initialCache input with
  | some cachedAnswer =>
      rw [QueryImpl.withCaching_run_some uniformSampleImpl hcached,
        support_pure, Set.mem_singleton_iff] at hquery
      obtain ⟨rfl, rfl⟩ := hquery
      exact impossible initialCache answer (by rw [hcached]; simp) hbefore hrest
  | none =>
      rw [QueryImpl.withCaching_run_none uniformSampleImpl hcached, support_map] at hquery
      obtain ⟨freshAnswer, _, heq⟩ := hquery
      obtain ⟨rfl, rfl⟩ := heq
      exact impossible (initialCache.cacheQuery input answer) answer
        (by rw [QueryCache.cacheQuery_self]; simp)
        (fun hsettled => hbefore (hsettled.of_cacheQuery_of_atEncoding hcached hat)) hrest

end SphincsSecurity.Concrete.TightEncoding
