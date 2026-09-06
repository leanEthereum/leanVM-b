import SphincsSecurity.Proof.OtsProbePublicationCacheMap
import SphincsSecurity.Proof.JointProbeResolvedBlockSupport

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex PublishedSignatureBody)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] revealSelectedFtsSecrets

theorem jointResolved_publication_selected
    (parameter : PublicParameter) (table : Coordinate → Digest) (index : Index) (leaves : DigestTree → FtsLeaf)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat) (ftsCache : SplitHashCache)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput)
    (nativeCache : OtsProbeSimulation.SplitHashCache) (body : PublishedSignatureBody)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache) (hcached : HiddenIndexCached index ftsCache) :
    projectJointResolvedCache parameter table <$>
      AdaptiveRevealProbe.runDetailed table state ftsFuel
        (runJointResolved ((fun result => (some (body.complete result.1), nativeCache, result.2)) <$>
          jointFtsSource ((revealSelectedFtsSecrets parameter index leaves).run ftsCache)) context fuel otsTable) =
      pure (some (⟨context, fuel,
        (some (body.complete (fun tree => table (index, tree, leaves (ftsIndexOf tree)))),
          OtsProbeSimulation.replaceOrdinaryCache nativeCache (mergedCache parameter table ftsCache)), otsTable⟩ :
            ResolvedRunResult (Option Signature × OtsProbeSimulation.SplitHashCache))) := by
  have h := coupledAt_revealSelectedFtsSecrets parameter table index leaves state ftsFuel ftsCache hclean hsynced hcached
  have hm := congrArg (fun computation =>
    (fun result => result.map (fun selected => (⟨context, fuel,
      (some (body.complete selected.1), OtsProbeSimulation.replaceOrdinaryCache nativeCache selected.2), otsTable⟩ :
        ResolvedRunResult (Option Signature × OtsProbeSimulation.SplitHashCache)))) <$> computation) h
  simp only [Functor.map_map, StateT.run_pure, map_pure, Option.map_some] at hm
  rw [runJointResolved_map, runJointResolved_fts, Functor.map_map, AdaptiveRevealProbe.runDetailed_mapValue, Functor.map_map]
  apply Eq.trans _ hm
  apply congrArg (fun f => f <$> AdaptiveRevealProbe.runDetailed table state ftsFuel
    ((revealSelectedFtsSecrets parameter index leaves).run ftsCache))
  funext result
  cases result with
  | stopped hit => rfl
  | done hit finalState value => cases hit <;> rfl

theorem jointSourcePublication_resolved
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) (layers : Layer → Option OtsProbeSimulation.ChronologicalLayerPart)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state cache.2) (hcached : HiddenIndexCached index cache.2) :
    projectJointResolvedCache parameter table <$>
      AdaptiveRevealProbe.runDetailed table state ftsFuel
        (runJointResolved ((jointSourcePublication parameter randomness index leaves ftsPath layers).run cache) context fuel otsTable) =
      OtsProbeSimulation.runResolvedFromTable context fuel otsTable
        ((OtsProbeSimulation.publishChronologicalSignature (fun index tree leaf => table (index, tree, leaf))
          randomness index leaves ftsPath layers).run
          (OtsProbeSimulation.replaceOrdinaryCache cache.1 (mergedCache parameter table cache.2))) := by
  have hbody := OtsProbeSimulation.cacheMapCommutes_publishSignatureBody
    (fun nativeCache => OtsProbeSimulation.replaceOrdinaryCache nativeCache (mergedCache parameter table cache.2))
    (OtsProbeSimulation.replaceOrdinaryCache_commutesWithHiddenUpdates _) randomness index ftsPath layers
  rw [OtsProbeSimulation.publishChronologicalSignature_eq_body, StateT.run_map,
    OtsProbeSimulation.runResolvedFromTable_map, hbody.resolved, Functor.map_map]
  conv_lhs => dsimp only [jointSourcePublication, StateT.run]
  rw [runJointResolved_bind, runJointResolved_native, AdaptiveRevealProbe.runDetailed_liftProbComp_bind, map_bind,
    map_eq_bind_pure_comp]
  apply bind_congr
  intro result
  cases result with
  | none => simp [AdaptiveRevealProbe.runDetailed, projectJointResolvedCache, cleanJointResolved, hclean]
  | some entry =>
      cases hselected : entry.value.1 with
      | none => simp [hselected, runJointResolved_pure, AdaptiveRevealProbe.runDetailed, projectJointResolvedCache,
          cleanJointResolved, hclean]
      | some body =>
          simpa only [hselected, Option.map_some, Function.comp_def, StateT.run] using
            jointResolved_publication_selected parameter table index leaves state ftsFuel cache.2 entry.context entry.remaining
              entry.table entry.value.2 body hclean hsynced hcached

theorem jointResolvedCoupledAt_publication
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) (layers : Layer → Option OtsProbeSimulation.ChronologicalLayerPart)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state cache.2) (hcached : HiddenIndexCached index cache.2) :
    JointResolvedCoupledAt parameter table state ftsFuel (jointSourcePublication parameter randomness index leaves ftsPath layers)
      (OtsProbeSimulation.publishChronologicalSignature (fun index tree leaf => table (index, tree, leaf))
        randomness index leaves ftsPath layers) context fuel otsTable cache :=
  jointResolvedCoupledAt_of_project_eq parameter table state ftsFuel _ _ context fuel otsTable cache
    (jointSourcePublication_resolved parameter table randomness index leaves ftsPath layers state ftsFuel
      context fuel otsTable cache hclean hsynced hcached)

end SphincsSecurity.Concrete.FtsProbeSimulation
