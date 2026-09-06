import SphincsSecurity.Proof.FtsProbeHashStepInvariants
import SphincsSecurity.Proof.FtsProbeNativePublicationInvariants

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def maskedJointBottomAndPublication
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (upper : Fin (numLayers - 1) → Option OtsProbeSimulation.ChronologicalLayerPart) (root : Digest) :
    NativeFtsStep (Option Signature) :=
  bindNativeSteps (liftNativeBlock (OtsProbeSimulation.maskedChronologicalLayerAfterMessage parameter index bottomLayer root))
    fun bottom => maskedNativePublication parameter randomness index leaves ftsPath (Fin.snoc upper bottom)

theorem coupled_maskedJointBottomAndPublication
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (upper : Fin (numLayers - 1) → Option OtsProbeSimulation.ChronologicalLayerPart) (root : Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache) (hcached : HiddenIndexCached index ftsCache) :
    NativeStepCoupledAt parameter table state ftsFuel
      (maskedJointBottomAndPublication parameter randomness index leaves ftsPath upper root)
      (do
        let bottom ← OtsProbeSimulation.maskedChronologicalLayerAfterMessage parameter index bottomLayer root
        OtsProbeSimulation.publishChronologicalSignature (fun index tree leaf => table (index, tree, leaf))
          randomness index leaves ftsPath (Fin.snoc upper bottom)) context fuel history cache ftsCache := by
  unfold maskedJointBottomAndPublication
  apply nativeStepCoupledAt_bind parameter table state ftsFuel _ _ _ _ context fuel history cache ftsCache hclean
    (liftNativeBlock_probeFree _ context fuel history cache)
  · exact projectNativeStepCache_liftNativeBlock parameter table state ftsFuel ftsCache _
      (cacheMapCommutes_native_maskedChronologicalLayerAfterMessage parameter table ftsCache index bottomLayer root)
      context fuel history cache hclean
  · intro finalState entry finalCache hresult
    obtain ⟨hstate, hsynced', hhidden⟩ := invariants_liftNativeBlock parameter table state finalState ftsFuel _
      (fun cache => cacheMapCommutes_native_maskedChronologicalLayerAfterMessage parameter table cache index bottomLayer root)
      context fuel history cache ftsCache finalCache (some entry) hsynced hresult
    have hcached' : HiddenIndexCached index finalCache := by
      intro tree leaf
      simpa only [hhidden] using hcached tree leaf
    unfold NativeStepCoupledAt
    have hproject : projectNativeStepCache (α := Option Signature) parameter table =
        projectNativePublicationWithCache parameter table := by
      funext result
      cases result with
      | stopped hit => rfl
      | done hit finalState value => cases hit <;> rfl
    rw [hproject]
    exact maskedNativePublication_projection_withCache parameter table randomness index leaves ftsPath (Fin.snoc upper entry.value.1)
      entry.context entry.remaining entry.history entry.value.2 finalState ftsFuel finalCache
      (by simpa [hstate] using hclean) hsynced' hcached'

theorem maskedJointBottomAndPublication_probeFree
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (upper : Fin (numLayers - 1) → Option OtsProbeSimulation.ChronologicalLayerPart) (root : Digest)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) :
    ProbeFree (maskedJointBottomAndPublication parameter randomness index leaves ftsPath upper root context fuel history cache) := by
  apply bindNativeSteps_probeFree
  · exact liftNativeBlock_probeFree _ context fuel history cache
  · intro bottom context fuel history cache
    exact revealAfterNativeBody_probeFree parameter index leaves _

end SphincsSecurity.Concrete.FtsProbeSimulation
