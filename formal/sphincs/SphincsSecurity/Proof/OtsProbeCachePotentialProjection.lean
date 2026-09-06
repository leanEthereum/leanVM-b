import SphincsSecurity.Proof.OtsProbeEncodingPotential
import SphincsSecurity.Proof.OtsProbePublicationCacheMap

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem resolvedCachePotentialBound_of_ordinary_projection
    (potential : QueryCache HashSpec → ENNReal)
    (computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcommutes : ∀ ordinary, CacheMapCommutes (fun cache => replaceOrdinaryCache cache ordinary) computation) :
    ResolvedCachePotentialBound (fun cache => potential (ordinaryQueryCache cache)) computation := by
  intro context fuel table cache
  have hself : replaceOrdinaryCache cache (ordinaryQueryCache cache) = cache := by
    funext key
    cases key <;> rfl
  have heq := hcommutes (ordinaryQueryCache cache) cache
  dsimp only at heq
  rw [hself] at heq
  calc
    _ = ∑' result, Pr[= result | runResolvedFromTable context fuel table (computation.run cache)] *
        (match result with | none => 0 | some _ => potential (ordinaryQueryCache cache)) := by
      conv_lhs => rw [heq, runResolvedFromTable_map, tsum_probOutput_map_mul]
      apply tsum_congr
      intro result
      cases result <;> simp [resolvedCachePotential, ordinaryQueryCache_replaceOrdinaryCache]
    _ ≤ ∑' result, Pr[= result | runResolvedFromTable context fuel table (computation.run cache)] *
        potential (ordinaryQueryCache cache) := by
      apply ENNReal.tsum_le_tsum
      intro result
      apply mul_le_mul' le_rfl
      cases result <;> simp
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left bot_le tsum_probOutput_le_one

theorem resolvedCachePotentialBound_ensureChainPrefix
    (potential : QueryCache HashSpec → ENNReal)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) (digit : Digit) :
    ResolvedCachePotentialBound (fun cache => potential (ordinaryQueryCache cache))
      (ensureChainPrefix lay tree leafIdx chainIdx digit) :=
  resolvedCachePotentialBound_of_ordinary_projection potential _
    (fun _ => cacheMapCommutes_ensureChainPrefix _ lay tree leafIdx chainIdx digit)

theorem resolvedCachePotentialBound_ensureTreePath
    (potential : QueryCache HashSpec → ENNReal) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    ResolvedCachePotentialBound (fun cache => potential (ordinaryQueryCache cache)) (ensureTreePath lay tree leafIdx) :=
  resolvedCachePotentialBound_of_ordinary_projection potential _ (fun _ => cacheMapCommutes_ensureTreePath _ lay tree leafIdx)

theorem resolvedCachePotentialBound_maskedTreeRoot
    (potential : QueryCache HashSpec → ENNReal) (lay : Layer) (tree : TreeIndex) :
    ResolvedCachePotentialBound (fun cache => potential (ordinaryQueryCache cache)) (maskedTreeRoot lay tree) :=
  resolvedCachePotentialBound_of_ordinary_projection potential _
    (fun ordinary => cacheMapCommutes_maskedTreeRoot _ (replaceOrdinaryCache_commutesWithHiddenUpdates ordinary) lay tree)

theorem resolvedCachePotentialBound_revealPrivateLayerValues
    (potential : QueryCache HashSpec → ENNReal) (index : Index) (lay : Layer) (encoding : ChainIndex → Digit) :
    ResolvedCachePotentialBound (fun cache => potential (ordinaryQueryCache cache)) (revealPrivateLayerValues index lay encoding) :=
  resolvedCachePotentialBound_of_ordinary_projection potential _
    (fun ordinary => cacheMapCommutes_revealPrivateLayerValues _ (replaceOrdinaryCache_commutesWithHiddenUpdates ordinary) index lay encoding)

end SphincsSecurity.Concrete.OtsProbeSimulation
