import SphincsSecurity.Proof.JointProbeSourcePublication
import SphincsSecurity.Proof.FtsProbeJointExecution

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

noncomputable def jointSourceBottomAndPublication
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (upper : Fin (numLayers - 1) → Option OtsProbeSimulation.ChronologicalLayerPart) (root : Digest) :
    JointSource (Option Signature) := do
  let bottom ← jointSourceNativeBlock (OtsProbeSimulation.maskedChronologicalLayerAfterMessage parameter index bottomLayer root)
  jointSourcePublication parameter randomness index leaves ftsPath (Fin.snoc upper bottom)

theorem jointSourceBottomAndPublication_implements
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (upper : Fin (numLayers - 1) → Option OtsProbeSimulation.ChronologicalLayerPart) (root : Digest) :
    JointSourceImplements (jointSourceBottomAndPublication parameter randomness index leaves ftsPath upper root)
      (maskedJointBottomAndPublication parameter randomness index leaves ftsPath upper root) := by
  exact JointSourceImplements.bind (runJointErasedHistory_nativeBlock _)
    (fun bottom => jointSourcePublication_implements parameter randomness index leaves ftsPath (Fin.snoc upper bottom))

noncomputable def jointSourceKeyAndPublication
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (upper : Fin (numLayers - 1) → Option OtsProbeSimulation.ChronologicalLayerPart) : JointSource (Option Signature) := do
  let root ← jointSourceFtsBlock (maskedFtsKey parameter index)
  jointSourceBottomAndPublication parameter randomness index leaves ftsPath upper root

theorem jointSourceKeyAndPublication_implements
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (upper : Fin (numLayers - 1) → Option OtsProbeSimulation.ChronologicalLayerPart) :
    JointSourceImplements (jointSourceKeyAndPublication parameter randomness index leaves ftsPath upper)
      (maskedJointKeyAndPublication parameter randomness index leaves ftsPath upper) := by
  exact JointSourceImplements.bind (runJointErasedHistory_ftsBlock _)
    (jointSourceBottomAndPublication_implements parameter randomness index leaves ftsPath upper)

noncomputable def jointSourceLayersAndPublication
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) : JointSource (Option Signature) := do
  let upper ← jointSourceNativeBlock (OtsProbeSimulation.maskedUpperChronologicalLayers parameter index)
  jointSourceKeyAndPublication parameter randomness index leaves ftsPath upper

theorem jointSourceLayersAndPublication_implements
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) :
    JointSourceImplements (jointSourceLayersAndPublication parameter randomness index leaves ftsPath)
      (maskedJointLayersAndPublication parameter randomness index leaves ftsPath) := by
  exact JointSourceImplements.bind (runJointErasedHistory_nativeBlock _)
    (jointSourceKeyAndPublication_implements parameter randomness index leaves ftsPath)

noncomputable def jointSourceSignAfterDigest
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    JointSource (Option Signature) := do
  let ftsPath ← jointSourceFtsBlock (maskedFtsOpen parameter index leaves)
  jointSourceLayersAndPublication parameter randomness index leaves ftsPath

theorem jointSourceSignAfterDigest_implements
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    JointSourceImplements (jointSourceSignAfterDigest parameter randomness index leaves)
      (maskedJointSignAfterDigest parameter randomness index leaves) := by
  exact JointSourceImplements.bind (runJointErasedHistory_ftsBlock _)
    (jointSourceLayersAndPublication_implements parameter randomness index leaves)

noncomputable def jointSourceSign (parameter : PublicParameter) (root : Digest) (message : Message) :
    JointSource (Option Signature) := do
  let selected ← jointSourceNativeBlock (simulateQ OtsProbeSimulation.ordinaryRomImpl
    (signDigestLoop digestAttemptLimit (jointDigestKey parameter root) message))
  match selected with
  | none => jointSourceNativeBlock (pure none)
  | some (randomness, index, leaves) => jointSourceSignAfterDigest parameter randomness index leaves

theorem jointSourceSign_implements (parameter : PublicParameter) (root : Digest) (message : Message) :
    JointSourceImplements (jointSourceSign parameter root message) (maskedJointSign parameter root message) := by
  apply JointSourceImplements.bind (runJointErasedHistory_nativeBlock _)
  intro selected
  cases selected with
  | none => exact runJointErasedHistory_nativeBlock _
  | some selected => exact jointSourceSignAfterDigest_implements parameter selected.1 selected.2.1 selected.2.2

noncomputable def jointSourceOuterQuery (parameter : PublicParameter) (root : Digest) :
    (input : (OracleWorld + SigningSpec).Domain) → JointSource ((OracleWorld + SigningSpec).Range input)
  | .inl (.inl n) => jointSourceNativeBlock (OtsProbeSimulation.splitUniformImpl n)
  | .inl (.inr input) => jointSourceHashQuery parameter input
  | .inr message => jointSourceSign parameter root message

theorem jointSourceOuterQuery_implements (parameter : PublicParameter) (root : Digest)
    (input : (OracleWorld + SigningSpec).Domain) :
    JointSourceImplements (jointSourceOuterQuery parameter root input) (jointOuterQuery parameter root input) := by
  cases input with
  | inl input =>
      cases input with
      | inl n => exact runJointErasedHistory_nativeBlock _
      | inr input => exact runJointErasedHistory_hashQuery parameter input
  | inr message => exact jointSourceSign_implements parameter root message

noncomputable def jointSourceComputation (parameter : PublicParameter) (root : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : JointSource α :=
  OracleComp.construct (fun value => jointSourceNativeBlock (pure value))
    (fun input _ next => jointSourceOuterQuery parameter root input >>= next) computation

theorem jointSourceComputation_implements (parameter : PublicParameter) (root : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    JointSourceImplements (jointSourceComputation parameter root computation) (maskedJointComputation parameter root computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact runJointErasedHistory_nativeBlock _
  | query_bind input next ih =>
      rw [jointSourceComputation, construct_query_bind, maskedJointComputation_query_bind]
      exact (jointSourceOuterQuery_implements parameter root input).bind ih

end SphincsSecurity.Concrete.FtsProbeSimulation
