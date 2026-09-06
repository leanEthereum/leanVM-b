import SphincsSecurity.Proof.JointProbeCachePotential

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] JointCachePotentialBound
set_option backward.isDefEq.respectTransparency false

theorem jointSourcePublication_eq_unmerged
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) (layers : Layer → Option OtsProbeSimulation.ChronologicalLayerPart) :
    jointSourcePublication parameter randomness index leaves ftsPath layers = (do
      let body ← jointSourceUnmergedNativeBlock (OtsProbeSimulation.publishSignatureBody randomness index ftsPath layers)
      match body with
      | none => pure none
      | some body => (fun values => some (body.complete values)) <$>
          jointSourceFtsBlock (revealSelectedFtsSecrets parameter index leaves)) := by
  funext cache
  change (jointSourcePublication parameter randomness index leaves ftsPath layers).run cache =
    (do
      let body ← jointSourceUnmergedNativeBlock (OtsProbeSimulation.publishSignatureBody randomness index ftsPath layers)
      match body with
      | none => pure none
      | some body => (fun values => some (body.complete values)) <$>
          jointSourceFtsBlock (revealSelectedFtsSecrets parameter index leaves)).run cache
  rw [StateT.run_bind]
  simp only [jointSourcePublication, jointSourceUnmergedNativeBlock, StateT.run, bind_map_left]
  apply bind_congr
  rintro ⟨body, nativeCache⟩
  cases body with
  | none => rfl
  | some body =>
      change _ = ((fun values => some (body.complete values)) <$>
        jointSourceFtsBlock (revealSelectedFtsSecrets parameter index leaves)).run (nativeCache, cache.2)
      rw [StateT.run_map]
      simp only [jointSourceFtsBlock, StateT.run, Functor.map_map]

theorem jointCachePotentialBound_publication_encoding
    (encodingParameter parameter : PublicParameter) (position : EncodingPosition) (message : Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) (layers : Layer → Option OtsProbeSimulation.ChronologicalLayerPart) :
    JointCachePotentialBound (encodingExhaustionPotential (encodingRetryInputs encodingParameter position message))
      (jointSourcePublication parameter randomness index leaves ftsPath layers) := by
  rw [jointSourcePublication_eq_unmerged]
  apply (jointCachePotentialBound_unmergedNativeBlock _ _).bind
  intro body
  cases body with
  | none =>
      exact JointCachePotentialBound.pure _ _
  | some body =>
      exact (jointCachePotentialBound_ftsBlock _ _
          (rawCachePotentialBound_revealSelectedFtsSecrets_encoding encodingParameter parameter position message index leaves)).map _

theorem jointCachePotentialBound_bottomAndPublication_encoding
    (encodingParameter parameter : PublicParameter) (position : EncodingPosition) (message : Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (upper : Fin (numLayers - 1) → Option OtsProbeSimulation.ChronologicalLayerPart) (root : Digest) :
    JointCachePotentialBound (encodingExhaustionPotential (encodingRetryInputs encodingParameter position message))
      (jointSourceBottomAndPublication parameter randomness index leaves ftsPath upper root) := by
  unfold jointSourceBottomAndPublication
  exact (jointCachePotentialBound_nativeBlock _ _
    (OtsProbeSimulation.resolvedCachePotentialBound_chronologicalLayer_encoding _ parameter index bottomLayer root)).bind
    fun bottom => jointCachePotentialBound_publication_encoding encodingParameter parameter position message
      randomness index leaves ftsPath (Fin.snoc upper bottom)

theorem jointCachePotentialBound_keyAndPublication_encoding
    (encodingParameter parameter : PublicParameter) (position : EncodingPosition) (message : Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (upper : Fin (numLayers - 1) → Option OtsProbeSimulation.ChronologicalLayerPart) :
    JointCachePotentialBound (encodingExhaustionPotential (encodingRetryInputs encodingParameter position message))
      (jointSourceKeyAndPublication parameter randomness index leaves ftsPath upper) := by
  unfold jointSourceKeyAndPublication
  exact (jointCachePotentialBound_ftsBlock _ _ (rawCachePotentialBound_maskedFtsKey_encoding _ parameter index)).bind
    (jointCachePotentialBound_bottomAndPublication_encoding encodingParameter parameter position message randomness index leaves ftsPath upper)

theorem jointCachePotentialBound_layersAndPublication_encoding
    (encodingParameter parameter : PublicParameter) (position : EncodingPosition) (message : Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) :
    JointCachePotentialBound (encodingExhaustionPotential (encodingRetryInputs encodingParameter position message))
      (jointSourceLayersAndPublication parameter randomness index leaves ftsPath) := by
  unfold jointSourceLayersAndPublication
  exact (jointCachePotentialBound_nativeBlock _ _
    (OtsProbeSimulation.resolvedCachePotentialBound_upperLayers_encoding _ parameter index)).bind
    (jointCachePotentialBound_keyAndPublication_encoding encodingParameter parameter position message randomness index leaves ftsPath)

theorem jointCachePotentialBound_signAfterDigest_encoding
    (encodingParameter parameter : PublicParameter) (position : EncodingPosition) (message : Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    JointCachePotentialBound (encodingExhaustionPotential (encodingRetryInputs encodingParameter position message))
      (jointSourceSignAfterDigest parameter randomness index leaves) := by
  unfold jointSourceSignAfterDigest
  exact (jointCachePotentialBound_ftsBlock _ _ (rawCachePotentialBound_maskedFtsOpen_encoding _ parameter index leaves)).bind
    (jointCachePotentialBound_layersAndPublication_encoding encodingParameter parameter position message randomness index leaves)

theorem jointCachePotentialBound_sign_encoding
    (encodingParameter parameter : PublicParameter) (position : EncodingPosition) (message : Digest)
    (root : Digest) (signedMessage : Message) :
    JointCachePotentialBound (encodingExhaustionPotential (encodingRetryInputs encodingParameter position message))
      (jointSourceSign parameter root signedMessage) := by
  unfold jointSourceSign
  apply (jointCachePotentialBound_nativeBlock _ _ (OtsProbeSimulation.resolvedCachePotentialBound_ordinaryRom_encoding _ _)).bind
  intro selected
  cases selected with
  | none =>
      exact jointCachePotentialBound_nativeBlock _ _ (OtsProbeSimulation.ResolvedCachePotentialBound.pure _ _)
  | some selected =>
      exact jointCachePotentialBound_signAfterDigest_encoding encodingParameter parameter position message
          selected.1 selected.2.1 selected.2.2

theorem jointCachePotentialBound_hash_encoding
    (encodingParameter parameter : PublicParameter) (position : EncodingPosition) (message : Digest) (input : HashInput) :
    JointCachePotentialBound (encodingExhaustionPotential (encodingRetryInputs encodingParameter position message))
      (jointSourceHashQuery parameter input) := by
  unfold jointSourceHashQuery
  cases decodeProbe? parameter input with
  | none =>
      exact jointCachePotentialBound_nativeBlock _ _
          (OtsProbeSimulation.resolvedCachePotentialBound_probingHashQuery_encoding encodingParameter parameter position message input)
  | some probe =>
      exact jointCachePotentialBound_ftsBlock _ _ (rawCachePotentialBound_probingHashQuery_encoding _ parameter input)

theorem jointCachePotentialBound_outerQuery_encoding
    (encodingParameter parameter : PublicParameter) (position : EncodingPosition) (message : Digest)
    (root : Digest) (input : (OracleWorld + SigningSpec).Domain) :
    JointCachePotentialBound (encodingExhaustionPotential (encodingRetryInputs encodingParameter position message))
      (jointSourceOuterQuery parameter root input) := by
  cases input with
  | inl input =>
      cases input with
      | inl n =>
          exact jointCachePotentialBound_nativeBlock _ _ (OtsProbeSimulation.resolvedCachePotentialBound_lift _ _)
      | inr input =>
          exact jointCachePotentialBound_hash_encoding encodingParameter parameter position message input
  | inr message =>
      exact jointCachePotentialBound_sign_encoding encodingParameter parameter position _ root message

theorem jointCachePotentialBound_computation_encoding
    (encodingParameter parameter : PublicParameter) (position : EncodingPosition) (message : Digest) (root : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    JointCachePotentialBound (encodingExhaustionPotential (encodingRetryInputs encodingParameter position message))
      (jointSourceComputation parameter root computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      exact jointCachePotentialBound_nativeBlock _ _ (OtsProbeSimulation.ResolvedCachePotentialBound.pure _ _)
  | query_bind input next ih =>
      change JointCachePotentialBound _ (jointSourceOuterQuery parameter root input >>= fun value => jointSourceComputation parameter root (next value))
      exact (jointCachePotentialBound_outerQuery_encoding encodingParameter parameter position message root input).bind ih

theorem jointCachePotentialBound_retained_encoding
    (encodingParameter : PublicParameter) (position : EncodingPosition) (message : Digest)
    (adversary : Adversary) (parameter : PublicParameter) (q : Nat) :
    JointCachePotentialBound (encodingExhaustionPotential (encodingRetryInputs encodingParameter position message))
      (jointSourceRetained adversary parameter q) := by
  unfold jointSourceRetained
  exact (jointCachePotentialBound_nativeBlock _ _ (OtsProbeSimulation.resolvedCachePotentialBound_publishedTreeRoot_encoding _)).bind
    fun root => jointCachePotentialBound_computation_encoding encodingParameter parameter position message root _

end SphincsSecurity.Concrete.FtsProbeSimulation
