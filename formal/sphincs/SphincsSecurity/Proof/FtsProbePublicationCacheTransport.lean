import SphincsSecurity.Proof.FtsProbeNativePublicationOrigin
import SphincsSecurity.Proof.OtsProbePublicationCacheTransport

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (HistoryResolvedPrefix PublishedSignatureBody completePublicationEntry replaceHistoryOrdinaryCache)

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000

noncomputable def projectNativePublicationWithCache (parameter : PublicParameter) (table : Coordinate → Digest) :
    AdaptiveRevealProbe.DetailedResult Coordinate (NativePublicationResult × SplitHashCache) → NativePublicationResult
  | .stopped _ => none
  | .done true _ _ => none
  | .done false _ (result, cache) => result.map (replaceHistoryOrdinaryCache (mergedCache parameter table cache))

theorem projectNativePublicationWithCache_revealSelected
    (parameter : PublicParameter) (table : Coordinate → Digest) (index : Index) (leaves : DigestTree → FtsLeaf)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) (cache : SplitHashCache)
    (entry : HistoryResolvedPrefix (Option PublishedSignatureBody × OtsProbeSimulation.SplitHashCache))
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state cache) (hcached : HiddenIndexCached index cache) :
    projectNativePublicationWithCache parameter table <$>
      AdaptiveRevealProbe.runDetailed table state fuel
        ((fun result => (some (completePublicationEntry result.1 entry), result.2)) <$>
          (revealSelectedFtsSecrets parameter index leaves).run cache) =
      pure (some (replaceHistoryOrdinaryCache (mergedCache parameter table cache)
        (completePublicationEntry (fun tree => table (index, tree, leaves (ftsIndexOf tree))) entry))) := by
  rw [AdaptiveRevealProbe.runDetailed_mapValue, Functor.map_map]
  have hcoupled := coupledAt_revealSelectedFtsSecrets parameter table index leaves state fuel cache hclean hsynced hcached
  unfold CoupledAt at hcoupled
  have hm := congrArg (fun computation =>
    (fun result => result.map fun selected =>
      replaceHistoryOrdinaryCache selected.2 (completePublicationEntry selected.1 entry)) <$> computation) hcoupled
  simp only [Functor.map_map, StateT.run_pure, map_pure, Option.map_some] at hm
  apply Eq.trans _ hm
  apply congrArg (fun f => f <$> AdaptiveRevealProbe.runDetailed table state fuel
    ((revealSelectedFtsSecrets parameter index leaves).run cache))
  funext result
  cases result with
  | stopped hit => rfl
  | done hit finalState value => cases hit <;> rfl

theorem projectNativePublicationWithCache_revealAfterNativeBody
    (parameter : PublicParameter) (table : Coordinate → Digest) (index : Index) (leaves : DigestTree → FtsLeaf)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) (cache : SplitHashCache)
    (bodyRun : ProbComp NativeBodyResult)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state cache) (hcached : HiddenIndexCached index cache) :
    projectNativePublicationWithCache parameter table <$>
      AdaptiveRevealProbe.runDetailed table state fuel ((revealAfterNativeBody parameter index leaves bodyRun).run cache) =
      Option.map (fun entry => replaceHistoryOrdinaryCache (mergedCache parameter table cache)
        (completePublicationEntry (fun tree => table (index, tree, leaves (ftsIndexOf tree))) entry)) <$> bodyRun := by
  unfold revealAfterNativeBody
  simp only [StateT.run_bind, StateT.run_liftM, bind_assoc, pure_bind]
  rw [AdaptiveRevealProbe.runDetailed_liftProbComp_bind, map_bind, map_eq_bind_pure_comp]
  apply bind_congr
  intro entry
  cases entry with
  | none => simp [AdaptiveRevealProbe.runDetailed, projectNativePublicationWithCache, hclean]
  | some entry =>
      cases hbody : entry.value.1 with
      | none =>
          simp [StateT.run_pure, AdaptiveRevealProbe.runDetailed, projectNativePublicationWithCache, hclean,
            completePublicationEntry, hbody, replaceHistoryOrdinaryCache]
      | some body =>
          simpa only [hbody, StateT.run_map, StateT.run_bind, StateT.run_pure, bind_pure_comp, Function.comp_def, Option.map_some] using
            projectNativePublicationWithCache_revealSelected parameter table index leaves state fuel cache entry hclean hsynced hcached

theorem maskedNativePublication_projection_withCache
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) (layers : Layer → Option OtsProbeSimulation.ChronologicalLayerPart)
    (context : OtsProbeSimulation.DeferredContext) (otsFuel : Nat) (history : List OtsProbeSimulation.Probe)
    (otsCache : OtsProbeSimulation.SplitHashCache) (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat) (ftsCache : SplitHashCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache) (hcached : HiddenIndexCached index ftsCache) :
    projectNativePublicationWithCache parameter table <$>
      AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((maskedNativePublication parameter randomness index leaves ftsPath layers context otsFuel history otsCache).run ftsCache) =
      OtsProbeSimulation.runResolvedHistoryPrefix
        (OtsProbeSimulation.eraseProbeQueries
          ((OtsProbeSimulation.publishChronologicalSignature (fun index tree leaf => table (index, tree, leaf))
            randomness index leaves ftsPath layers).run
              (OtsProbeSimulation.replaceOrdinaryCache otsCache (mergedCache parameter table ftsCache))))
        context otsFuel history := by
  rw [OtsProbeSimulation.runHistory_publishChronologicalSignature_eq_body,
    (OtsProbeSimulation.ordinaryCacheIndependent_publishSignatureBody randomness index ftsPath layers).historyPrefix]
  rw [Functor.map_map]
  simpa only [maskedNativePublication, Option.map_map, Function.comp_def,
    OtsProbeSimulation.completePublicationEntry_replaceHistoryOrdinaryCache] using
    projectNativePublicationWithCache_revealAfterNativeBody parameter table index leaves state ftsFuel ftsCache
      (OtsProbeSimulation.runResolvedHistoryPrefix
        (OtsProbeSimulation.eraseProbeQueries ((OtsProbeSimulation.publishSignatureBody randomness index ftsPath layers).run otsCache))
        context otsFuel history) hclean hsynced hcached

end SphincsSecurity.Concrete.FtsProbeSimulation
