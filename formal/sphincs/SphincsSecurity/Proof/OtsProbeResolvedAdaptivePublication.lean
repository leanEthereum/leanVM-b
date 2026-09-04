import SphincsSecurity.Proof.OtsProbeResolvedAdaptiveSigner

/-!
# Signed-chain publication through canonical adaptive execution
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option maxRecDepth 100000 in
theorem revealedChainAllowed_runSynchronizedResolved_signingTraceComputation
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (targetCache : QueryCache HashSpec) (allowedLog : QueryLog SigningSpec)
    (completion : Coordinate → HashOutput) (fallback : QueryImpl HashSpec Id)
    (hlogRuns : ∀ (entry : (request : SignRequest) × SigningSpec.Range request)
      (signature : Signature), entry ∈ allowedLog → entry.2 = some signature →
        SuccessfulSignRun (tableAnswer parameter completion fallback) targetCache
          (⟨parameter, root,
            fun lay tree leafIdx chainIdx =>
              truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
            ftsSecret⟩ : SecretKey)
          entry.1 signature)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (result : ResolvedRunResult ((α × QueryLog SigningSpec) × SplitHashCache))
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hallowed : RevealedChainAllowed
      (CoveredChainCoordinate (tableAnswer parameter completion fallback) targetCache
        (⟨parameter, root,
          fun lay tree leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
          ftsSecret⟩ : SecretKey)
        allowedLog)
      context.state)
    (hsub : ∀ entry, entry ∈ result.value.1.2 → entry ∈ allowedLog)
    (hresult : some result ∈ support
      (runSynchronizedResolved
        (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
        (signingTraceComputation computation) context fuel table cache))
    (hcompletion : DeferredCompletion table result.context completion)
    (hfallback : CacheAgreesWithFnOffTable parameter completion
      (ordinaryQueryCache result.value.2) fallback) :
    RevealedChainAllowed
      (CoveredChainCoordinate (tableAnswer parameter completion fallback) targetCache
        (⟨parameter, root,
          fun lay tree leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
          ftsSecret⟩ : SecretKey)
        allowedLog)
      result.context.state := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache
      concreteCache result with
  | pure value =>
      have htrace : signingTraceComputation
          (pure value : OracleComp (OracleWorld + SigningSpec) α) = pure (value, []) := by
        simp [signingTraceComputation]
      rw [htrace, runSynchronizedResolved_pure _ (value, []) context fuel table cache
        hinvariant.2.2.2.1] at hresult
      simp only [mem_support_pure_iff, Option.some.injEq] at hresult
      subst result
      exact hallowed
  | query_bind input next ih =>
      rw [signingTraceComputation_query_bind, runSynchronizedResolved,
        OracleComp.construct_query_bind] at hresult
      simp only [dif_pos hinvariant.2.2.2.1, mem_support_bind_iff] at hresult
      obtain ⟨queryOption, hquery, hrest⟩ := hresult
      cases queryOption with
      | none => simp at hrest
      | some queryResult =>
          change some result ∈ support
            (runSynchronizedResolved
              (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
              ((fun tail =>
                (tail.1, signingLogFragment input queryResult.value.1 ++ tail.2)) <$>
                  signingTraceComputation (next queryResult.value.1))
              queryResult.context queryResult.remaining queryResult.table
                queryResult.value.2) at hrest
          rw [map_eq_bind_pure_comp, runSynchronizedResolved_bind,
            mem_support_bind_iff] at hrest
          obtain ⟨tailOption, htail, hfinish⟩ := hrest
          cases tailOption with
          | none => simp at hfinish
          | some tailResult =>
              have hqueryCore :=
                resolvedCore_of_mem_canonicalChronologicalAdversaryImpl parameter root table
                  ftsSecret input context fuel cache queryResult
                    hinvariant.2.1.valuesConsistent hinvariant.2.2.1 hquery
              change some tailResult ∈ support
                (runSynchronizedResolved
                  (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
                  (signingTraceComputation (next queryResult.value.1)) queryResult.context
                    queryResult.remaining queryResult.table queryResult.value.2) at htail
              rw [hqueryCore.1] at htail
              have htailCore :=
                resolvedCore_of_mem_runSynchronizedResolved_canonicalChronological parameter root
                  table ftsSecret (signingTraceComputation (next queryResult.value.1))
                    queryResult.context queryResult.remaining queryResult.value.2 tailResult
                      hqueryCore.2.1 hqueryCore.2.2 htail
              simp only at hfinish
              change some result ∈ support
                (runSynchronizedResolved
                  (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
                  (pure (tailResult.value.1.1,
                    signingLogFragment input queryResult.value.1 ++ tailResult.value.1.2))
                  tailResult.context tailResult.remaining tailResult.table
                    tailResult.value.2) at hfinish
              have htailCompletable :
                  DeferredCompletable tailResult.table tailResult.context := by
                by_contra hnotCompletable
                rw [runSynchronizedResolved_pure_of_not_completable _ _ tailResult.context
                  tailResult.remaining tailResult.table tailResult.value.2
                    hnotCompletable] at hfinish
                simp at hfinish
              rw [runSynchronizedResolved_pure _ _ tailResult.context tailResult.remaining
                tailResult.table tailResult.value.2 htailCompletable] at hfinish
              simp only [mem_support_pure_iff, Option.some.injEq] at hfinish
              subst result
              simp only at hsub hcompletion hfallback ⊢
              have hqueryCompletion : DeferredCompletion table queryResult.context completion :=
                hcompletion.of_mem_runSynchronizedResolved_canonicalChronological
                  (signingTraceComputation (next queryResult.value.1)) queryResult.context
                    queryResult.remaining queryResult.value.2 tailResult completion
                      hqueryCore.2.1 hqueryCore.2.2 htail
              have hqueryRel :=
                canonicalReachableResolvedImplCouples_chronologicalAdversaryImpl parameter root
                  table ftsSecret input context fuel cache concreteCache hinvariant hclosed
                    hpublished
              obtain ⟨queryRight, _hqueryRightSupport, hqueryRelation⟩ :=
                exists_right_of_relTriple_of_mem_support hqueryRel hquery
              rcases queryRight with ⟨_queryValue, queryConcreteCache⟩
              obtain ⟨_queryOutput, hqueryInvariant, hqueryClosed, hqueryPublished⟩ :=
                hqueryRelation.clean_of_completion hqueryCompletion
              have htailRel := relTriple_runSynchronizedResolved_reachable
                (canonicalReachableResolvedImplCouples_chronologicalAdversaryImpl parameter root
                  table ftsSecret)
                (signingTraceComputation (next queryResult.value.1)) queryResult.context
                  queryResult.remaining queryResult.value.2 queryConcreteCache hqueryInvariant
                    hqueryClosed hqueryPublished
              let secretKey : SecretKey :=
                ⟨parameter, root,
                  fun lay tree leafIdx chainIdx =>
                    truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
                  ftsSecret⟩
              have hqueryFallback : CacheAgreesWithFnOffTable parameter completion
                  (ordinaryQueryCache queryResult.value.2) fallback :=
                CacheAgreesWithFnOffTable.of_reachableRelTriple htailRel hqueryInvariant htail
                  hcompletion hfallback (fun value finalCache hright =>
                    FtsProbeSimulation.simulateQ_unloggedMappedAdversaryImpl_cache_le secretKey
                      (signingTraceComputation (next queryResult.value.1)) queryConcreteCache
                        finalCache value hright)
              have hqueryAllowed :=
                revealedChainAllowed_canonicalChronologicalAdversaryQuery parameter root table
                  ftsSecret targetCache allowedLog completion fallback hlogRuns input context
                    fuel cache concreteCache queryResult hinvariant hclosed hpublished hallowed
                      (fun entry hentry => hsub entry
                        (List.mem_append_left tailResult.value.1.2 hentry))
                      hquery hqueryCompletion hqueryFallback
              apply ih queryResult.value.1 queryResult.context queryResult.remaining
                queryResult.value.2 queryConcreteCache tailResult hqueryInvariant hqueryClosed
                  hqueryPublished hqueryAllowed
              · intro entry hentry
                exact hsub entry (List.mem_append_right _ hentry)
              · exact htail
              · exact hcompletion
              · exact hfallback

end SphincsSecurity.Concrete.OtsProbeSimulation
