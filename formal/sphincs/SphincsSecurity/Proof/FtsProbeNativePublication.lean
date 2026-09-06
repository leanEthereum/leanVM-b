import SphincsSecurity.Proof.OtsProbePublicationBody
import SphincsSecurity.Proof.AdaptiveRevealProbeLift

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (HistoryResolvedPrefix PublishedSignatureBody completePublicationEntry)

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000

abbrev NativeBodyResult := Option (HistoryResolvedPrefix (Option PublishedSignatureBody × OtsProbeSimulation.SplitHashCache))
abbrev NativePublicationResult := Option (HistoryResolvedPrefix (Option Signature × OtsProbeSimulation.SplitHashCache))

noncomputable def revealAfterNativeBody (parameter : PublicParameter) (index : Index) (leaves : DigestTree → FtsLeaf)
    (bodyRun : ProbComp NativeBodyResult) :
    StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) NativePublicationResult := do
  let entry ← liftM (AdaptiveRevealProbe.liftProbComp (Coordinate := Coordinate) bodyRun)
  match entry with
  | none => pure none
  | some entry =>
      match entry.value.1 with
      | none => pure (some ⟨entry.context, entry.remaining, (none, entry.value.2), entry.history⟩)
      | some _ => do
          let selected ← revealSelectedFtsSecrets parameter index leaves
          pure (some (completePublicationEntry selected entry))

def projectNativePublication : AdaptiveRevealProbe.DetailedResult Coordinate (NativePublicationResult × SplitHashCache) → NativePublicationResult
  | .stopped _ => none
  | .done true _ _ => none
  | .done false _ (result, _) => result

theorem projectNativePublication_revealSelected
    (parameter : PublicParameter) (table : Coordinate → Digest) (index : Index) (leaves : DigestTree → FtsLeaf)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) (cache : SplitHashCache)
    (entry : HistoryResolvedPrefix (Option PublishedSignatureBody × OtsProbeSimulation.SplitHashCache))
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state cache) (hcached : HiddenIndexCached index cache) :
    projectNativePublication <$>
      AdaptiveRevealProbe.runDetailed table state fuel
        ((fun result => (some (completePublicationEntry result.1 entry), result.2)) <$>
          (revealSelectedFtsSecrets parameter index leaves).run cache) =
      pure (some (completePublicationEntry (fun tree => table (index, tree, leaves (ftsIndexOf tree))) entry)) := by
  rw [AdaptiveRevealProbe.runDetailed_mapValue, Functor.map_map]
  have hcoupled := coupledAt_revealSelectedFtsSecrets parameter table index leaves state fuel cache hclean hsynced hcached
  unfold CoupledAt at hcoupled
  have hm := congrArg (fun computation =>
    (fun result => result.map fun selected => completePublicationEntry selected.1 entry) <$> computation) hcoupled
  simp only [Functor.map_map, StateT.run_pure, map_pure, Option.map_some] at hm
  apply Eq.trans _ hm
  apply congrArg (fun f => f <$> AdaptiveRevealProbe.runDetailed table state fuel
    ((revealSelectedFtsSecrets parameter index leaves).run cache))
  funext result
  cases result with
  | stopped hit => rfl
  | done hit finalState value => cases hit <;> rfl

theorem projectNativePublication_revealAfterNativeBody
    (parameter : PublicParameter) (table : Coordinate → Digest) (index : Index) (leaves : DigestTree → FtsLeaf)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) (cache : SplitHashCache)
    (bodyRun : ProbComp NativeBodyResult)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state cache) (hcached : HiddenIndexCached index cache) :
    projectNativePublication <$>
      AdaptiveRevealProbe.runDetailed table state fuel ((revealAfterNativeBody parameter index leaves bodyRun).run cache) =
      Option.map (completePublicationEntry (fun tree => table (index, tree, leaves (ftsIndexOf tree)))) <$> bodyRun := by
  unfold revealAfterNativeBody
  simp only [StateT.run_bind, StateT.run_liftM, bind_assoc, pure_bind]
  rw [AdaptiveRevealProbe.runDetailed_liftProbComp_bind, map_bind, map_eq_bind_pure_comp]
  apply bind_congr
  intro entry
  cases entry with
  | none => simp [AdaptiveRevealProbe.runDetailed, projectNativePublication, hclean]
  | some entry =>
      cases hbody : entry.value.1 with
      | none =>
          simp [StateT.run_pure, AdaptiveRevealProbe.runDetailed, projectNativePublication, hclean,
            completePublicationEntry, hbody]
      | some body =>
          simpa only [hbody, StateT.run_map, StateT.run_bind, StateT.run_pure, bind_pure_comp, Function.comp_def, Option.map_some] using
            projectNativePublication_revealSelected parameter table index leaves state fuel cache entry hclean hsynced hcached

noncomputable def maskedNativePublication
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) (layers : Layer → Option OtsProbeSimulation.ChronologicalLayerPart)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) :
    StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) NativePublicationResult :=
  revealAfterNativeBody parameter index leaves
    (OtsProbeSimulation.runResolvedHistoryPrefix
      (OtsProbeSimulation.eraseProbeQueries ((OtsProbeSimulation.publishSignatureBody randomness index ftsPath layers).run cache))
      context fuel history)

theorem maskedNativePublication_projection
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) (layers : Layer → Option OtsProbeSimulation.ChronologicalLayerPart)
    (context : OtsProbeSimulation.DeferredContext) (otsFuel : Nat) (history : List OtsProbeSimulation.Probe)
    (otsCache : OtsProbeSimulation.SplitHashCache) (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat) (ftsCache : SplitHashCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache) (hcached : HiddenIndexCached index ftsCache) :
    projectNativePublication <$>
      AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((maskedNativePublication parameter randomness index leaves ftsPath layers context otsFuel history otsCache).run ftsCache) =
      OtsProbeSimulation.runResolvedHistoryPrefix
        (OtsProbeSimulation.eraseProbeQueries
          ((OtsProbeSimulation.publishChronologicalSignature (fun index tree leaf => table (index, tree, leaf))
            randomness index leaves ftsPath layers).run otsCache)) context otsFuel history := by
  rw [OtsProbeSimulation.runHistory_publishChronologicalSignature_eq_body]
  exact projectNativePublication_revealAfterNativeBody parameter table index leaves state ftsFuel ftsCache _ hclean hsynced hcached

end SphincsSecurity.Concrete.FtsProbeSimulation
