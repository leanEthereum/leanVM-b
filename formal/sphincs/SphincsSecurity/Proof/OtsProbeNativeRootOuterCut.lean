import SphincsSecurity.Proof.OtsProbeNativeOuterCut
import SphincsSecurity.Proof.OtsProbeNativeRootSwapStep

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem relTriple_nativeRootSwap_outerCut
    (parameter : PublicParameter) (root : Digest) (target : Position) (hroot : IsLayerRoot target)
    (before after : HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (left right : DeferredContext) (hcontext : NativeRootContextRel target before after left right)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (leftCache rightCache : SplitHashCache)
    (hcache : NativeRootSwapCacheRel parameter target before after leftCache rightCache) :
    RelTriple
      (runNativeOuterCut (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        (NativeRootOuterSafe parameter target before after) computation left fuel table leftCache)
      (runNativeOuterCut (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        (NativeRootOuterSafe parameter target before after) computation right fuel table rightCache)
      (NativeRootSwapSameRel parameter target before after) := by
  induction computation using OracleComp.inductionOn generalizing left right fuel table leftCache rightCache with
  | pure value => exact relTriple_pure_pure ⟨hcontext, rfl, rfl, rfl, hcache⟩
  | query_bind input next ih =>
      rw [runNativeOuterCut_query_bind, runNativeOuterCut_query_bind]
      by_cases hsafe : NativeRootOuterSafe parameter target before after input left
      · have hright := (hcontext.outerSafe_iff parameter input).mp hsafe
        rw [if_pos hsafe, if_pos hright]
        apply relTriple_bind (relTriple_nativeRootSwap_outerQuery_of_safe parameter root target hroot before after ftsSecret input
          left right hcontext fuel table leftCache rightCache hcache hsafe)
        intro leftResult rightResult hrel
        cases leftResult with
        | none =>
            cases rightResult with
            | none => exact relTriple_pure_pure trivial
            | some rightResult => contradiction
        | some leftResult =>
            cases rightResult with
            | none => contradiction
            | some rightResult =>
                rcases hrel with ⟨hnextContext, hfuel, htable, hvalue, hnextCache⟩
                simp only
                rw [← hfuel, ← htable, ← hvalue]
                exact ih leftResult.value.1 leftResult.context rightResult.context hnextContext leftResult.remaining
                  leftResult.table leftResult.value.2 rightResult.value.2 hnextCache
      · have hright : ¬NativeRootOuterSafe parameter target before after input right :=
          fun h => hsafe ((hcontext.outerSafe_iff parameter input).mpr h)
        rw [if_neg hsafe, if_neg hright]
        exact relTriple_pure_pure ⟨hcontext, rfl, rfl, rfl, hcache⟩

theorem evalDist_nativeRootSwap_outerCut_live_of_stored
    (parameter : PublicParameter) (root : Digest) (target : Position) (hroot : IsLayerRoot target)
    (before after : HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (h : NativePositionReplaceable target before after context)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    evalDist (normalizeLiveNativeRootResult target <$>
      runNativeOuterCut (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        (NativeRootOuterSafe parameter target before after) computation context fuel table cache) =
    evalDist (normalizeLiveNativeRootResult target <$>
      runNativeOuterCut (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        (NativeRootOuterSafe parameter target before after) computation (replaceNativePosition target after context) fuel table
        (fullSwapRootCache parameter target (truncateHash before) (truncateHash after) after cache)) := by
  have hpadding :
      evalDist (normalizeLiveNativeRootResult target <$>
        runNativeOuterCut (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
          (NativeRootOuterSafe parameter target before after) computation context fuel table cache) =
      evalDist (normalizeLiveNativeRootResult target <$>
        runNativeOuterCut (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
          (NativeRootOuterSafe parameter target before after) computation context fuel table
          (replaceHiddenRootCache target before cache)) := by
    apply evalDist_map_eq_of_relTriple
    apply relTriple_post_mono
      (relTriple_runNativeOuterCut_ordinaryCache _
        (ordinaryCacheNativeCouples_chronologicalOuterQuery parameter root ftsSecret) _ computation context fuel table
        cache (replaceHiddenRootCache target before cache) (ordinarySplitCacheEq_replaceHiddenRootCache target before cache))
    intro left right hrel
    exact hrel.normalizeLive target
  have hswap :
      evalDist (normalizeLiveNativeRootResult target <$>
        runNativeOuterCut (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
          (NativeRootOuterSafe parameter target before after) computation context fuel table
          (replaceHiddenRootCache target before cache)) =
      evalDist (normalizeLiveNativeRootResult target <$>
        runNativeOuterCut (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
          (NativeRootOuterSafe parameter target before after) computation (replaceNativePosition target after context) fuel table
          (fullSwapRootCache parameter target (truncateHash before) (truncateHash after) after
            (replaceHiddenRootCache target before cache))) := by
    apply evalDist_map_eq_of_relTriple
    apply relTriple_post_mono
      (relTriple_nativeRootSwap_outerCut parameter root target hroot before after ftsSecret computation context
        (replaceNativePosition target after context) ⟨h, rfl⟩ fuel table (replaceHiddenRootCache target before cache) _
        (nativeRootSwapCacheRel_fullSwap parameter target before after (replaceHiddenRootCache target before cache)
          (by simp [replaceHiddenRootCache])))
    intro left right hrel
    exact hrel.normalizeLive
  rw [fullSwapRootCache_replaceHiddenRootCache] at hswap
  exact hpadding.trans hswap

end SphincsSecurity.Concrete.OtsProbeSimulation
