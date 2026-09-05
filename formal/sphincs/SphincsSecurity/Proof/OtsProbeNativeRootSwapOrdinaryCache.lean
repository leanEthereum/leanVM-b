import SphincsSecurity.Proof.OtsProbeNativeOrdinaryCacheSigner

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

theorem ordinarySplitCacheEq_replaceHiddenRootCache
    (target : Position) (output : HashOutput) (cache : SplitHashCache) :
    OrdinarySplitCacheEq cache (replaceHiddenRootCache target output cache) := by
  intro input
  simp [replaceHiddenRootCache]

theorem fullSwapRootCache_replaceHiddenRootCache
    (parameter : PublicParameter) (target : Position) (leftRoot rightRoot : Digest)
    (before after : HashOutput) (cache : SplitHashCache) :
    fullSwapRootCache parameter target leftRoot rightRoot after
      (replaceHiddenRootCache target before cache) =
        fullSwapRootCache parameter target leftRoot rightRoot after cache := by
  funext key
  cases key with
  | ordinary input =>
      simp [fullSwapRootCache, replaceHiddenRootCache, swapCanonicalRootEncodingCache]
  | hidden coordinate =>
      by_cases h : coordinate = .position target
      · simp [fullSwapRootCache, replaceHiddenRootCache, h]
      · simp [fullSwapRootCache, replaceHiddenRootCache, swapCanonicalRootEncodingCache, h]

theorem OrdinaryCacheNativeSameRel.normalizeLive
    {left right : Option (ResolvedRunResult (α × SplitHashCache))}
    (h : OrdinaryCacheNativeSameRel left right) (target : Position) :
    normalizeLiveNativeRootResult target left = normalizeLiveNativeRootResult target right := by
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some right => contradiction
  | some left =>
      cases right with
      | none => contradiction
      | some right =>
          rcases h with ⟨hcontext, hfuel, htable, hvalue, _⟩
          simp only [normalizeLiveNativeRootResult, normalizeNativeRootResult,
            Option.map_some, hcontext, hfuel, htable, hvalue]
          rw [hcontext, htable]

theorem evalDist_nativeRootSwap_chronologicalSign_live_of_stored
    (parameter : PublicParameter) (root : Digest) (target : Position) (hroot : IsLayerRoot target)
    (before after : HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (context : DeferredContext) (h : NativePositionReplaceable target before after context)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    evalDist (normalizeLiveNativeRootResult target <$>
      runResolvedFromTable context fuel table ((maskedPublishedChronologicalSign parameter root ftsSecret message).run cache)) =
    evalDist (normalizeLiveNativeRootResult target <$>
      runResolvedFromTable (replaceNativePosition target after context) fuel table
        ((maskedPublishedChronologicalSign parameter root ftsSecret message).run
          (fullSwapRootCache parameter target (truncateHash before) (truncateHash after) after cache))) := by
  have hpadding :
      evalDist (normalizeLiveNativeRootResult target <$>
        runResolvedFromTable context fuel table ((maskedPublishedChronologicalSign parameter root ftsSecret message).run cache)) =
      evalDist (normalizeLiveNativeRootResult target <$>
        runResolvedFromTable context fuel table ((maskedPublishedChronologicalSign parameter root ftsSecret message).run
          (replaceHiddenRootCache target before cache))) := by
    apply evalDist_map_eq_of_relTriple
    apply relTriple_post_mono
      (ordinaryCacheNativeCouples_chronologicalSign parameter root ftsSecret message
        cache (replaceHiddenRootCache target before cache)
        (ordinarySplitCacheEq_replaceHiddenRootCache target before cache) context fuel table)
    intro left right hrel
    exact hrel.normalizeLive target
  have hswap := evalDist_nativeRootSwap_chronologicalSign_live parameter root target hroot
    before after ftsSecret message context h fuel table (replaceHiddenRootCache target before cache)
    (by simp [replaceHiddenRootCache])
  rw [fullSwapRootCache_replaceHiddenRootCache] at hswap
  exact hpadding.trans hswap

end SphincsSecurity.Concrete.OtsProbeSimulation
