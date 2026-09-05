import SphincsSecurity.Proof.OtsProbeNativeRootCompatibleTrace

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open _root_.OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem nativeRootSelectionGuess_eq_of_rootRel
    (parameter : PublicParameter) (target : Position) (before after : HashOutput)
    (input : (OracleWorld + SigningSpec).Domain) (left right : DeferredContext)
    (hcontext : NativeRootContextRel target before after left right)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (leftCache rightCache : SplitHashCache) :
    nativeRootSelectionGuess? parameter target ⟨input, left, fuel, table, leftCache⟩ =
      nativeRootSelectionGuess? parameter target ⟨input, right, fuel, table, rightCache⟩ := by
  cases input with
  | inl query =>
      cases query with
      | inl n => rfl
      | inr input => simp only [nativeRootSelectionGuess?, nativeRootSelectionCandidate?, hcontext.candidate_eq parameter input]
  | inr message => rfl

theorem observeCompatibleNativeRootTrace_eq_of_rel
    {parameter : PublicParameter} {target : Position} {before after : HashOutput}
    {left right : Option (ResolvedRunResult (α × SplitHashCache))}
    (hrel : NativeRootSwapSameRel parameter target before after left right)
    (leftHistory rightHistory : List CanonicalQuerySelection)
    (hhistory : nativeRootCandidateHistory parameter target leftHistory = nativeRootCandidateHistory parameter target rightHistory) :
    observeCompatibleNativeRootTrace parameter target before after (left, leftHistory) =
      observeCompatibleNativeRootTrace parameter target before after (right, rightHistory) := by
  have hnormalize := hrel.normalize
  have hcompatible : NativeRootTraceCompatible parameter target before after (left, leftHistory) ↔
      NativeRootTraceCompatible parameter target before after (right, rightHistory) := by
    cases left with
    | none =>
        cases right with
        | none => rfl
        | some right => contradiction
    | some left =>
        cases right with
        | none => contradiction
        | some right => simp only [NativeRootTraceCompatible, hrel.1.revealed_eq, hhistory]
  simp only [observeCompatibleNativeRootTrace, hcompatible, hnormalize, hhistory]

theorem evalDist_nativeRootSwap_compatibleTrace
    (parameter : PublicParameter) (root : Digest) (target : Position) (hroot : IsLayerRoot target)
    (before after : HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (left right : DeferredContext) (hcontext : NativeRootContextRel target before after left right)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (leftCache rightCache : SplitHashCache)
    (hcache : NativeRootSwapCacheRel parameter target before after leftCache rightCache) :
    evalDist (observeCompatibleNativeRootTrace parameter target before after <$>
      runNativeQueryTrace parameter root ftsSecret computation left fuel table leftCache) =
    evalDist (observeCompatibleNativeRootTrace parameter target before after <$>
      runNativeQueryTrace parameter root ftsSecret computation right fuel table rightCache) := by
  induction computation using OracleComp.inductionOn generalizing left right fuel table leftCache rightCache with
  | pure value =>
      simp only [runNativeQueryTrace, OracleComp.construct_pure, hcontext.completable_iff]
      split_ifs with hcomplete
      · simp only [map_pure]
        congr 1
        have hrel : NativeRootSwapSameRel parameter target before after
            (some (⟨left, fuel, (value, leftCache), table⟩ : ResolvedRunResult (α × SplitHashCache)))
            (some (⟨right, fuel, (value, rightCache), table⟩ : ResolvedRunResult (α × SplitHashCache))) :=
          ⟨hcontext, rfl, rfl, rfl, hcache⟩
        exact congrArg pure (observeCompatibleNativeRootTrace_eq_of_rel hrel [] [] rfl)
      · simp [observeCompatibleNativeRootTrace, NativeRootTraceCompatible]
  | query_bind input next ih =>
      by_cases hcomplete : DeferredCompletable table left
      · have hrightComplete := (hcontext.completable_iff table).mpr hcomplete
        by_cases hsafe : NativeRootOuterSafe parameter target before after input left
        · rw [runNativeQueryTrace_query_bind, runNativeQueryTrace_query_bind, if_pos hcomplete, if_pos hrightComplete]
          simp only [map_bind]
          apply evalDist_bind_eq_of_relTriple_next _ _ _ _ _
            (relTriple_nativeRootSwap_outerQuery_of_safe parameter root target hroot before after ftsSecret input
              left right hcontext fuel table leftCache rightCache hcache hsafe)
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
                  rcases hrel with ⟨hnext, hfuel, htable, hvalue, hnextCache⟩
                  simp only
                  rw [← hfuel, ← htable, ← hvalue]
                  have htail := ih leftResult.value.1 leftResult.context rightResult.context hnext leftResult.remaining
                    leftResult.table leftResult.value.2 rightResult.value.2 hnextCache
                  have hguess := nativeRootSelectionGuess_eq_of_rootRel parameter target before after input left right hcontext
                    fuel table leftCache rightCache
                  have hmapped := evalDist_map_eq_of_evalDist_eq htail
                    (prependCompatibleNativeRootGuess before after
                      (nativeRootSelectionGuess? parameter target ⟨input, left, fuel, table, leftCache⟩))
                  simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
                    observeCompatibleNativeRootTrace_prepend, hguess] using hmapped
        · rw [evalDist_observeCompatibleNativeRootTrace_eq_none_of_unsafe parameter root target hroot before after ftsSecret
            input next left hcontext.replaceable fuel table leftCache hsafe]
          have hrightUnsafe : ¬NativeRootOuterSafe parameter target after before input right :=
            fun h => hsafe ((hcontext.outerSafe_swap_iff parameter input).mpr h)
          have hzero := evalDist_observeCompatibleNativeRootTrace_eq_none_of_unsafe parameter root target hroot after before ftsSecret
            input next right hcontext.symm.replaceable fuel table rightCache hrightUnsafe
          have hswap : (observeCompatibleNativeRootTrace parameter target after before (α := α)) =
              observeCompatibleNativeRootTrace parameter target before after :=
            funext (observeCompatibleNativeRootTrace_swap parameter target after before)
          rw [hswap] at hzero
          exact hzero.symm
      · have hrightNot : ¬DeferredCompletable table right := fun h => hcomplete ((hcontext.completable_iff table).mp h)
        rw [runNativeQueryTrace_of_not_completable parameter root ftsSecret _ left fuel table leftCache hcomplete,
          runNativeQueryTrace_of_not_completable parameter root ftsSecret _ right fuel table rightCache hrightNot]

end SphincsSecurity.Concrete.OtsProbeSimulation
