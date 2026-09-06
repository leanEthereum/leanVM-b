import SphincsSecurity.Proof.FtsProbeResolvedCachePreservation
import SphincsSecurity.Proof.JointProbeResolvedFinalization

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def projectJointResolvedCache (parameter : PublicParameter) (table : Coordinate → Digest)
    (result : AdaptiveRevealProbe.DetailedResult Coordinate (Option (ResolvedRunResult (α × JointSourceCache)))) :
    Option (ResolvedRunResult (α × OtsProbeSimulation.SplitHashCache)) :=
  (cleanJointResolved result).map (fun entry => { entry with value :=
    (entry.value.1, OtsProbeSimulation.replaceOrdinaryCache entry.value.2.1 (mergedCache parameter table entry.value.2.2)) })

theorem jointSourceNativeBlock_resolved
    (parameter : PublicParameter) (ftsTable : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (hcommutes : ∀ cache, OtsProbeSimulation.CacheMapCommutes (nativeCacheProjection parameter ftsTable cache) computation)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput)
    (cache : JointSourceCache) (hclean : AdaptiveRevealProbe.tableHits state ftsTable = false) :
    projectJointResolvedCache parameter ftsTable <$>
      AdaptiveRevealProbe.runDetailed ftsTable state ftsFuel
        (runJointResolved ((jointSourceNativeBlock computation).run cache) context fuel otsTable) =
      OtsProbeSimulation.runResolvedFromTable context fuel otsTable
        (computation.run (OtsProbeSimulation.replaceOrdinaryCache cache.1 (mergedCache parameter ftsTable cache.2))) := by
  conv_lhs => dsimp only [jointSourceNativeBlock, StateT.run]
  rw [runJointResolved_map, runJointResolved_native,
    ← nativeCacheProjection_prepare parameter ftsTable cache.2 cache.1,
    (hcommutes cache.2).resolved]
  simp only [map_eq_bind_pure_comp, AdaptiveRevealProbe.runDetailed_liftProbComp_bind, bind_assoc]
  apply bind_congr
  intro result
  cases result with
  | none => simp [AdaptiveRevealProbe.runDetailed, projectJointResolvedCache, cleanJointResolved, hclean]
  | some entry =>
      simp [AdaptiveRevealProbe.runDetailed, projectJointResolvedCache, cleanJointResolved, hclean, nativeCacheProjection]

theorem jointSourceFtsBlock_resolved
    (parameter : PublicParameter) (ftsTable : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (masked : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α)
    (ordinary : OracleComp HashSpec α)
    (h : NativeResolvedCoupled parameter ftsTable state ftsFuel masked ordinary)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput)
    (cache : JointSourceCache) :
    projectJointResolvedCache parameter ftsTable <$>
      AdaptiveRevealProbe.runDetailed ftsTable state ftsFuel
        (runJointResolved ((jointSourceFtsBlock masked).run cache) context fuel otsTable) =
      OtsProbeSimulation.runResolvedFromTable context fuel otsTable
        ((simulateQ OtsProbeSimulation.ordinaryHashImpl ordinary).run
          (OtsProbeSimulation.replaceOrdinaryCache cache.1 (mergedCache parameter ftsTable cache.2))) := by
  rw [← h context fuel otsTable _ cache.2 rfl]
  conv_lhs => dsimp only [jointSourceFtsBlock, StateT.run]
  rw [runJointResolved_map, runJointResolved_fts, Functor.map_map,
    AdaptiveRevealProbe.runDetailed_mapValue, Functor.map_map]
  congr 1
  funext result
  cases result with
  | stopped hit => rfl
  | done hit finalState value =>
      cases hit <;> simp [projectJointResolvedCache, cleanJointResolved,
        AdaptiveRevealProbe.DetailedResult.mapValue, projectDetailedCache, OtsProbeSimulation.ordinaryResolvedResult,
        OtsProbeSimulation.replaceOrdinaryCache_replace]

end SphincsSecurity.Concrete.FtsProbeSimulation
