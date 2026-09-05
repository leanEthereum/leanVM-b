import SphincsSecurity.Proof.OtsProbeNativeRootRecordLikelihood

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open _root_.OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem evalDist_nativeRootCompatibleTrace_ordinaryCache
    (parameter : PublicParameter) (root : Digest) (target : Position) (before after : HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache) (hcache : OrdinarySplitCacheEq leftCache rightCache) :
    evalDist (observeCompatibleNativeRootTrace parameter target before after <$>
      runNativeQueryTrace parameter root ftsSecret computation context fuel table leftCache) =
    evalDist (observeCompatibleNativeRootTrace parameter target before after <$>
      runNativeQueryTrace parameter root ftsSecret computation context fuel table rightCache) := by
  induction computation using OracleComp.inductionOn generalizing context fuel table leftCache rightCache with
  | pure value =>
      simp only [runNativeQueryTrace, OracleComp.construct_pure]
      split_ifs <;> simp [observeCompatibleNativeRootTrace, NativeRootTraceCompatible, normalizeNativeRootResult]
  | query_bind input next ih =>
      by_cases hcomplete : DeferredCompletable table context
      · rw [runNativeQueryTrace_query_bind, runNativeQueryTrace_query_bind, if_pos hcomplete, if_pos hcomplete]
        simp only [map_bind]
        apply evalDist_bind_eq_of_relTriple_next _ _ _ _ _
          (ordinaryCacheNativeCouples_chronologicalOuterQuery parameter root ftsSecret input
            leftCache rightCache hcache context fuel table)
        intro leftResult rightResult hrel
        cases leftResult with
        | none =>
            cases rightResult with
            | none => simp [observeCompatibleNativeRootTrace, NativeRootTraceCompatible]
            | some rightResult => contradiction
        | some leftResult =>
            cases rightResult with
            | none => contradiction
            | some rightResult =>
                rcases hrel with ⟨hcontext, hfuel, htable, hvalue, hnextCache⟩
                simp only
                rw [← hcontext, ← hfuel, ← htable, ← hvalue]
                have htail := ih leftResult.value.1 leftResult.context leftResult.remaining leftResult.table
                  leftResult.value.2 rightResult.value.2 hnextCache
                have hmapped := evalDist_map_eq_of_evalDist_eq htail
                  (prependCompatibleNativeRootGuess before after
                    (nativeRootSelectionGuess? parameter target ⟨input, context, fuel, table, leftCache⟩))
                simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
                  observeCompatibleNativeRootTrace_prepend, nativeRootSelectionGuess?, nativeRootSelectionCandidate?] using hmapped
      · rw [runNativeQueryTrace_of_not_completable parameter root ftsSecret _ context fuel table leftCache hcomplete,
          runNativeQueryTrace_of_not_completable parameter root ftsSecret _ context fuel table rightCache hcomplete]

theorem nativeRootSwapCacheRel_padded_of_no_guesses
    (parameter : PublicParameter) (target : Position) (before after : HashOutput) (cache : SplitHashCache)
    (hbefore : NoEncodingRootGuessCached parameter target (truncateHash before) cache)
    (hafter : NoEncodingRootGuessCached parameter target (truncateHash after) cache) :
    NativeRootSwapCacheRel parameter target before after
      (replaceHiddenRootCache target before cache) (replaceHiddenRootCache target after cache) := by
  refine ⟨replaceHiddenRootCache target before cache, ?_, ?_⟩
  · apply RootEncodingCacheRel.of_same_of_no_guesses
    · intro input hinput
      simpa [replaceHiddenRootCache] using hbefore input hinput
    · intro input hinput
      simpa [replaceHiddenRootCache] using hafter input hinput
  · have hrel := rootHiddenCacheRel_replace target before after (replaceHiddenRootCache target before cache)
      (by simp [replaceHiddenRootCache])
    simpa only [replaceHiddenRootCache, Function.update_idem] using hrel

theorem probOutput_nativeRootTraceRecord_sameCache_eq_of_compatible
    (parameter : PublicParameter) (root : Digest) (target : Position) (hroot : IsLayerRoot target)
    (before after : HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (left right : DeferredContext) (hcontext : NativeRootContextRel target before after left right)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hbeforeCache : NoEncodingRootGuessCached parameter target (truncateHash before) cache)
    (hafterCache : NoEncodingRootGuessCached parameter target (truncateHash after) cache)
    (record : ResolvedRunResult α × Finset Digest)
    (hbefore : truncateHash before ∉ record.2) (hafter : truncateHash after ∉ record.2) :
    Pr[= some record | observeCompatibleNativeRootTrace parameter target before before <$>
      runNativeQueryTrace parameter root ftsSecret computation left fuel table cache] =
    Pr[= some record | observeCompatibleNativeRootTrace parameter target after after <$>
      runNativeQueryTrace parameter root ftsSecret computation right fuel table cache] := by
  have hleft := congrArg (fun distribution => distribution (some record))
    (evalDist_nativeRootCompatibleTrace_ordinaryCache parameter root target before before ftsSecret computation left fuel table
      cache (replaceHiddenRootCache target before cache) (ordinarySplitCacheEq_replaceHiddenRootCache target before cache))
  have hright := congrArg (fun distribution => distribution (some record))
    (evalDist_nativeRootCompatibleTrace_ordinaryCache parameter root target after after ftsSecret computation right fuel table
      cache (replaceHiddenRootCache target after cache) (ordinarySplitCacheEq_replaceHiddenRootCache target after cache))
  exact hleft.trans ((probOutput_nativeRootTraceRecord_eq_of_compatible parameter root target hroot before after ftsSecret
    computation left right hcontext fuel table _ _
    (nativeRootSwapCacheRel_padded_of_no_guesses parameter target before after cache hbeforeCache hafterCache)
    record hbefore hafter).trans hright.symm)

end SphincsSecurity.Concrete.OtsProbeSimulation
