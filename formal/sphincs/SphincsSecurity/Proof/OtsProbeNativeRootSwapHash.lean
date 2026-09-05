import SphincsSecurity.Proof.OtsProbeNativeRootHashPlan
import SphincsSecurity.Proof.OtsProbeNativeOrdinaryCacheHash

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

theorem relTriple_nativeRootSwap_probingHashQuery
    (parameter : PublicParameter) (target : Position) (before after : HashOutput) (input : HashInput)
    (left right : DeferredContext) (hcontext : NativeRootContextRel target before after left right)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (leftCache rightCache : SplitHashCache)
    (hcache : NativeRootSwapCacheRel parameter target before after leftCache rightCache)
    (havoid : RootInputAvoids parameter target (truncateHash before) (truncateHash after) input)
    (hprobe : ∀ candidate, (purePlanProbingHashQuery parameter input left.state).candidate? = some candidate →
      ¬IsPrivateValueExposure target before after (.probe candidate.coordinate candidate.candidate))
    (haction : NativeRootActionSafe parameter target input left right
      (purePlanProbingHashQuery parameter input left.state).action) :
    RelTriple
      (runResolvedFromTable left fuel table ((probingHashQuery parameter input).run leftCache))
      (runResolvedFromTable right fuel table ((probingHashQuery parameter input).run rightCache))
      (NativeRootSwapSameRel parameter target before after) := by
  obtain ⟨middleCache, hencoding, hhidden⟩ := hcache
  have hfirst := rootEncodingNativeCouples_probingHashQuery_avoids parameter target
    (truncateHash before) (truncateHash after) input havoid leftCache middleCache hencoding left fuel table
  have hsecond := relTriple_nativeRoot_probingHashQuery_of_safe parameter target before after input
    left right hcontext fuel table middleCache rightCache hhidden hprobe haction
  apply relTriple_post_mono (SphincsSecurity.relTriple_trans_exists hfirst hsecond)
  intro leftResult rightResult hrel
  obtain ⟨middleResult, hfirst, hsecond⟩ := hrel
  cases leftResult with
  | none =>
      cases middleResult with
      | some middleResult => contradiction
      | none =>
          cases rightResult with
          | none => trivial
          | some rightResult => contradiction
  | some leftResult =>
      cases middleResult with
      | none => contradiction
      | some middleResult =>
          cases rightResult with
          | none => contradiction
          | some rightResult =>
              rcases hfirst with ⟨hcontextEq, hfuel₁, htable₁, hvalue₁, hcache₁⟩
              rcases hsecond with ⟨hcontext₂, hfuel₂, htable₂, hvalue₂, hcache₂⟩
              refine ⟨?_, hfuel₁.trans hfuel₂, htable₁.trans htable₂, hvalue₁.trans hvalue₂,
                middleResult.value.2, hcache₁, hcache₂⟩
              rw [hcontextEq]
              exact hcontext₂
theorem evalDist_nativeRootSwap_hashQuery_live_of_stored
    (parameter : PublicParameter) (target : Position) (before after : HashOutput) (input : HashInput)
    (context : DeferredContext) (h : NativePositionReplaceable target before after context)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (havoid : RootInputAvoids parameter target (truncateHash before) (truncateHash after) input)
    (hprobe : ∀ candidate, (purePlanProbingHashQuery parameter input context.state).candidate? = some candidate →
      ¬IsPrivateValueExposure target before after (.probe candidate.coordinate candidate.candidate))
    (haction : NativeRootActionSafe parameter target input context (replaceNativePosition target after context)
      (purePlanProbingHashQuery parameter input context.state).action) :
    evalDist (normalizeLiveNativeRootResult target <$>
      runResolvedFromTable context fuel table ((probingHashQuery parameter input).run cache)) =
    evalDist (normalizeLiveNativeRootResult target <$>
      runResolvedFromTable (replaceNativePosition target after context) fuel table
        ((probingHashQuery parameter input).run
          (fullSwapRootCache parameter target (truncateHash before) (truncateHash after) after cache))) := by
  have hpadding :
      evalDist (normalizeLiveNativeRootResult target <$>
        runResolvedFromTable context fuel table ((probingHashQuery parameter input).run cache)) =
      evalDist (normalizeLiveNativeRootResult target <$>
        runResolvedFromTable context fuel table ((probingHashQuery parameter input).run
          (replaceHiddenRootCache target before cache))) := by
    apply evalDist_map_eq_of_relTriple
    apply relTriple_post_mono
      (ordinaryCacheNativeCouples_probingHashQuery parameter input cache (replaceHiddenRootCache target before cache)
        (ordinarySplitCacheEq_replaceHiddenRootCache target before cache) context fuel table)
    intro left right hrel
    exact hrel.normalizeLive target
  have hswap :
      evalDist (normalizeLiveNativeRootResult target <$>
        runResolvedFromTable context fuel table ((probingHashQuery parameter input).run
          (replaceHiddenRootCache target before cache))) =
      evalDist (normalizeLiveNativeRootResult target <$>
        runResolvedFromTable (replaceNativePosition target after context) fuel table
          ((probingHashQuery parameter input).run
            (fullSwapRootCache parameter target (truncateHash before) (truncateHash after) after
              (replaceHiddenRootCache target before cache)))) := by
    apply evalDist_map_eq_of_relTriple
    apply relTriple_post_mono
      (relTriple_nativeRootSwap_probingHashQuery parameter target before after input context
        (replaceNativePosition target after context) ⟨h, rfl⟩ fuel table (replaceHiddenRootCache target before cache) _
        (nativeRootSwapCacheRel_fullSwap parameter target before after (replaceHiddenRootCache target before cache)
          (by simp [replaceHiddenRootCache])) havoid hprobe haction)
    intro left right hrel
    exact hrel.normalizeLive
  rw [fullSwapRootCache_replaceHiddenRootCache] at hswap
  exact hpadding.trans hswap

end SphincsSecurity.Concrete.OtsProbeSimulation
