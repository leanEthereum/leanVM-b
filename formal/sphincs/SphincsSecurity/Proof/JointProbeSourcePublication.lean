import SphincsSecurity.Proof.JointProbeSourceBlocks
import SphincsSecurity.Proof.FtsProbeNativeDigestLoop

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (HistoryResolvedPrefix)

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def jointSourcePublication
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) (layers : Layer → Option OtsProbeSimulation.ChronologicalLayerPart) :
    JointSource (Option Signature) := fun cache => do
  let (body, nativeCache) ← jointNativeSource
    ((OtsProbeSimulation.publishSignatureBody randomness index ftsPath layers).run cache.1)
  match body with
  | none => pure (none, nativeCache, cache.2)
  | some body =>
      (fun result => (some (body.complete result.1), nativeCache, result.2)) <$>
        jointFtsSource ((revealSelectedFtsSecrets parameter index leaves).run cache.2)

theorem jointSourcePublication_implements
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) (layers : Layer → Option OtsProbeSimulation.ChronologicalLayerPart) :
    JointSourceImplements (jointSourcePublication parameter randomness index leaves ftsPath layers)
      (maskedNativePublication parameter randomness index leaves ftsPath layers) := by
  intro context fuel history cache
  conv_lhs => dsimp only [jointSourcePublication, StateT.run]
  rw [runJointErasedHistory_bind, runJointErasedHistory_native]
  simp only [maskedNativePublication, revealAfterNativeBody, StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind, map_bind]
  apply bind_congr
  intro result
  cases result with
  | none => rfl
  | some entry =>
      cases hbody : entry.value.1 with
      | none => simp [hbody, runJointErasedHistory_pure, packJointStepResult]
      | some body =>
          simp only [hbody]
          rw [runJointErasedHistory_map, runJointErasedHistory_fts]
          simp [packJointStepResult, OtsProbeSimulation.completePublicationEntry, hbody, Functor.map_map]
          rfl

end SphincsSecurity.Concrete.FtsProbeSimulation
