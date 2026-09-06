import SphincsSecurity.Proof.FtsProbeEncodingCacheSigner
import SphincsSecurity.Proof.JointProbeRawBlockSupport
import SphincsSecurity.Proof.JointProbeEncodingPotential
import SphincsSecurity.Proof.OtsProbeResolvedCacheSupport

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def JointEncodingCacheMonotone (source : JointSource α) : Prop :=
  ∀ table state ftsFuel context fuel otsTable cache finalState remaining entry,
    AdaptiveRevealProbe.RawResult.done finalState remaining (some entry) ∈ support
      (AdaptiveRevealProbe.runRaw table state ftsFuel (runJointResolved (source.run cache) context fuel otsTable)) →
    EncodingCacheExtends (ordinaryQueryCache cache.2) (ordinaryQueryCache entry.value.2.2)

theorem JointEncodingCacheMonotone.pure (value : α) : JointEncodingCacheMonotone (pure value) := by
  intro table state ftsFuel context fuel otsTable cache finalState remaining entry hresult
  simp only [StateT.run_pure, runJointResolved_pure, AdaptiveRevealProbe.runRaw, construct_pure,
    mem_support_pure_iff, AdaptiveRevealProbe.RawResult.done.injEq, Option.some.injEq] at hresult
  obtain ⟨_, _, heq⟩ := hresult
  subst entry
  exact .refl _

theorem JointEncodingCacheMonotone.bind {left : JointSource α} {next : α → JointSource β}
    (hleft : JointEncodingCacheMonotone left) (hnext : ∀ value, JointEncodingCacheMonotone (next value)) :
    JointEncodingCacheMonotone (left >>= next) := by
  intro table state ftsFuel context fuel otsTable cache finalState remaining entry hresult
  rw [StateT.run_bind, runJointResolved_bind, AdaptiveRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨middle, hmiddle, hrest⟩ := hresult
  cases middle with
  | stopped hit => simp at hrest
  | done middleState middleFuel middle =>
      cases middle with
      | none => simp [AdaptiveRevealProbe.runRaw] at hrest
      | some middle =>
          exact (hleft table state ftsFuel context fuel otsTable cache middleState middleFuel middle hmiddle).trans
            (hnext middle.value.1 table middleState middleFuel middle.context middle.remaining middle.table middle.value.2
              finalState remaining entry hrest)

theorem jointEncodingCacheMonotone_nativeBlock
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (hmonotone : OtsProbeSimulation.OrdinaryCacheMonotoneSupport computation) :
    JointEncodingCacheMonotone (jointSourceNativeBlock computation) := by
  intro table state ftsFuel context fuel otsTable cache finalState remaining entry hresult
  obtain ⟨native, hnative, _, _, rfl⟩ := mem_support_jointSourceNativeBlock_raw_done table state finalState ftsFuel remaining
    computation context fuel otsTable cache entry hresult
  have h := hmonotone.resolved context fuel otsTable (prepareNativeCache cache.2 cache.1) native hnative
  rw [prepareNativeCache, OtsProbeSimulation.ordinaryQueryCache_replaceOrdinaryCache] at h
  exact EncodingCacheExtends.of_le h

theorem jointEncodingCacheMonotone_ftsBlock
    (computation : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α)
    (hmonotone : EncodingCacheMonotoneSupport computation) :
    JointEncodingCacheMonotone (jointSourceFtsBlock computation) := by
  intro table state ftsFuel context fuel otsTable cache finalState remaining entry hresult
  obtain ⟨value, finalCache, rfl, hvalue⟩ := mem_support_jointSourceFtsBlock_raw_done table state finalState ftsFuel remaining
    computation context fuel otsTable cache entry hresult
  exact hmonotone.raw table state finalState ftsFuel remaining cache.2 (value, finalCache) hvalue

theorem jointEncodingCacheMonotone_unmergedNativeBlock
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α) :
    JointEncodingCacheMonotone (jointSourceUnmergedNativeBlock computation) := by
  intro table state ftsFuel context fuel otsTable cache finalState remaining entry hresult
  simp only [jointSourceUnmergedNativeBlock, StateT.run] at hresult
  rw [runJointResolved_map, runJointResolved_native, AdaptiveRevealProbe.runRaw_mapValue,
    AdaptiveRevealProbe.runRaw_liftProbComp, Functor.map_map, support_map] at hresult
  obtain ⟨nativeOption, _, heq⟩ := hresult
  cases nativeOption with
  | none => simp [AdaptiveRevealProbe.RawResult.mapValue] at heq
  | some native =>
      simp only [AdaptiveRevealProbe.RawResult.mapValue, Option.map_some,
        AdaptiveRevealProbe.RawResult.done.injEq, Option.some.injEq] at heq
      obtain ⟨_, _, heq⟩ := heq
      subst entry
      exact .refl _

attribute [local irreducible] JointEncodingCacheMonotone

theorem JointEncodingCacheMonotone.map {source : JointSource α}
    (hsource : JointEncodingCacheMonotone source) (f : α → β) : JointEncodingCacheMonotone (f <$> source) := by
  rw [map_eq_bind_pure_comp]
  exact hsource.bind fun _ => JointEncodingCacheMonotone.pure _

theorem jointEncodingCacheMonotone_publication
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) (layers : Layer → Option OtsProbeSimulation.ChronologicalLayerPart) :
    JointEncodingCacheMonotone (jointSourcePublication parameter randomness index leaves ftsPath layers) := by
  rw [jointSourcePublication_eq_unmerged]
  apply (jointEncodingCacheMonotone_unmergedNativeBlock _).bind
  intro body
  cases body with
  | none => exact JointEncodingCacheMonotone.pure _
  | some body =>
      exact (jointEncodingCacheMonotone_ftsBlock _ (encodingCacheMonotoneSupport_revealSelectedFtsSecrets parameter index leaves)).map _

end SphincsSecurity.Concrete.FtsProbeSimulation
