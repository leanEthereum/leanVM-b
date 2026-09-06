import SphincsSecurity.Proof.FtsProbeNativeDigestLoop

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] maskedFtsKey maskedFtsOpen signDigestLoop
  OtsProbeSimulation.maskedUpperChronologicalLayers OtsProbeSimulation.maskedChronologicalLayerAfterMessage

theorem maskedJointKeyAndPublication_probeFree
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (upper : Fin (numLayers - 1) → Option OtsProbeSimulation.ChronologicalLayerPart)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) :
    ProbeFree (maskedJointKeyAndPublication parameter randomness index leaves ftsPath upper context fuel history cache) := by
  apply bindNativeSteps_probeFree
  · exact liftFtsBlock_probeFree _ context fuel history cache (maskedFtsKey_probeFree parameter index)
  · exact maskedJointBottomAndPublication_probeFree parameter randomness index leaves ftsPath upper

theorem maskedJointLayersAndPublication_probeFree
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) :
    ProbeFree (maskedJointLayersAndPublication parameter randomness index leaves ftsPath context fuel history cache) := by
  apply bindNativeSteps_probeFree
  · exact liftNativeBlock_probeFree _ context fuel history cache
  · exact maskedJointKeyAndPublication_probeFree parameter randomness index leaves ftsPath

theorem maskedJointSignAfterDigest_probeFree
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) :
    ProbeFree (maskedJointSignAfterDigest parameter randomness index leaves context fuel history cache) := by
  apply bindNativeSteps_probeFree
  · exact liftFtsBlock_probeFree _ context fuel history cache (maskedFtsOpen_probeFree parameter index leaves)
  · exact maskedJointLayersAndPublication_probeFree parameter randomness index leaves

theorem maskedJointSign_probeFree
    (parameter : PublicParameter) (root : Digest) (message : Message)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) :
    ProbeFree (maskedJointSign parameter root message context fuel history cache) := by
  apply bindNativeSteps_probeFree
  · exact liftNativeBlock_probeFree _ context fuel history cache
  · intro selected context fuel history cache
    cases selected with
    | none => exact liftNativeBlock_probeFree _ context fuel history cache
    | some selected => exact maskedJointSignAfterDigest_probeFree parameter selected.1 selected.2.1 selected.2.2 context fuel history cache

end SphincsSecurity.Concrete.FtsProbeSimulation
