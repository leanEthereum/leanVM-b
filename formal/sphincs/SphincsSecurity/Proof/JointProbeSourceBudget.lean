import SphincsSecurity.Proof.JointProbeSourceSigner
import SphincsSecurity.Proof.OtsProbeNativePublicationCache

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

theorem maskedChronologicalLayerAfterMessage_probeFree
    (parameter : PublicParameter) (index : Index) (lay : Layer) (message : Digest) :
    ProbeFree (maskedChronologicalLayerAfterMessage parameter index lay message) := by
  have hots : ProbeFree (maskedOtsLayerAfterMessage parameter index lay message) := by
    unfold maskedOtsLayerAfterMessage
    apply (maskedOtsSign_probeFree parameter lay (treeIndexAt index lay) (leafIndexAt index lay) message).bind
    intro selected
    cases selected with
    | none => exact ProbeFree.pure _
    | some selected =>
        exact (ensureTreePath_probeFree lay (treeIndexAt index lay) (leafIndexAt index lay)).bind
          (fun _ => ProbeFree.pure _)
  unfold maskedChronologicalLayerAfterMessage
  apply hots.bind
  intro selected
  cases selected with
  | none => exact ProbeFree.pure _
  | some selected => exact (revealPrivateLayerValues_probeFree index lay selected.2).bind (fun _ => ProbeFree.pure _)

theorem maskedUpperChronologicalLayers_probeFree (parameter : PublicParameter) (index : Index) :
    ProbeFree (maskedUpperChronologicalLayers parameter index) := by
  apply sequenceFin_probeFree
  intro lay
  unfold maskedUpperChronologicalLayer
  exact (maskedTreeRoot_probeFree _ _).bind (maskedChronologicalLayerAfterMessage_probeFree parameter index _)

end SphincsSecurity.Concrete.OtsProbeSimulation

namespace SphincsSecurity.Concrete.FtsProbeSimulation

attribute [local irreducible] maskedFtsKey maskedFtsOpen signDigestLoop
  OtsProbeSimulation.maskedUpperChronologicalLayers OtsProbeSimulation.maskedChronologicalLayerAfterMessage

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def JointSourceProbeBound (source : JointSource α) (q : Nat) : Prop :=
  ∀ cache, (source.run cache).IsQueryBoundP JointProbeIsProbe q

theorem JointSourceProbeBound.bind {left : JointSource α} {next : α → JointSource β} {q r : Nat}
    (hleft : JointSourceProbeBound left q) (hnext : ∀ value, JointSourceProbeBound (next value) r) :
    JointSourceProbeBound (left >>= next) (q + r) := by
  intro cache
  rw [StateT.run_bind]
  exact OracleComp.isQueryBoundP_bind (hleft cache) (fun result _ => hnext result.1 result.2)

theorem jointSourcePublication_probeFree
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) (layers : Layer → Option OtsProbeSimulation.ChronologicalLayerPart) :
    JointSourceProbeBound (jointSourcePublication parameter randomness index leaves ftsPath layers) 0 := by
  intro cache
  change (jointNativeSource ((OtsProbeSimulation.publishSignatureBody randomness index ftsPath layers).run cache.1) >>= _).IsQueryBoundP _ 0
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (jointNativeSource_probeBound _ 0 (OtsProbeSimulation.publishSignatureBody_probeFree randomness index ftsPath layers cache.1))
  rintro ⟨body, nativeCache⟩ _
  cases body with
  | none => simp
  | some body =>
      rw [isQueryBoundP_map_iff]
      exact jointFtsSource_probeBound _ 0 (revealSelectedFtsSecrets_probeFree parameter index leaves cache.2)

theorem jointSourceBottomAndPublication_probeFree
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (upper : Fin (numLayers - 1) → Option OtsProbeSimulation.ChronologicalLayerPart) (root : Digest) :
    JointSourceProbeBound (jointSourceBottomAndPublication parameter randomness index leaves ftsPath upper root) 0 := by
  exact JointSourceProbeBound.bind (q := 0) (r := 0) (jointSourceNativeBlock_probeBound _ 0
    (OtsProbeSimulation.maskedChronologicalLayerAfterMessage_probeFree parameter index bottomLayer root))
    (fun bottom => jointSourcePublication_probeFree parameter randomness index leaves ftsPath (Fin.snoc upper bottom))

theorem jointSourceKeyAndPublication_probeFree
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (upper : Fin (numLayers - 1) → Option OtsProbeSimulation.ChronologicalLayerPart) :
    JointSourceProbeBound (jointSourceKeyAndPublication parameter randomness index leaves ftsPath upper) 0 := by
  exact JointSourceProbeBound.bind (q := 0) (r := 0) (jointSourceFtsBlock_probeBound _ 0 (maskedFtsKey_probeFree parameter index))
    (jointSourceBottomAndPublication_probeFree parameter randomness index leaves ftsPath upper)

theorem jointSourceLayersAndPublication_probeFree
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) :
    JointSourceProbeBound (jointSourceLayersAndPublication parameter randomness index leaves ftsPath) 0 := by
  exact JointSourceProbeBound.bind (q := 0) (r := 0) (jointSourceNativeBlock_probeBound _ 0
    (OtsProbeSimulation.maskedUpperChronologicalLayers_probeFree parameter index))
    (jointSourceKeyAndPublication_probeFree parameter randomness index leaves ftsPath)

theorem jointSourceSignAfterDigest_probeFree
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    JointSourceProbeBound (jointSourceSignAfterDigest parameter randomness index leaves) 0 := by
  exact JointSourceProbeBound.bind (q := 0) (r := 0) (jointSourceFtsBlock_probeBound _ 0 (maskedFtsOpen_probeFree parameter index leaves))
    (jointSourceLayersAndPublication_probeFree parameter randomness index leaves)

theorem jointSourceSign_probeFree (parameter : PublicParameter) (root : Digest) (message : Message) :
    JointSourceProbeBound (jointSourceSign parameter root message) 0 := by
  apply JointSourceProbeBound.bind (q := 0) (r := 0) (jointSourceNativeBlock_probeBound _ 0 (OtsProbeSimulation.simulateQ_ordinaryRomImpl_probeFree _))
  intro selected
  cases selected with
  | none => exact jointSourceNativeBlock_probeBound _ 0 (OtsProbeSimulation.ProbeFree.pure _)
  | some selected => exact jointSourceSignAfterDigest_probeFree parameter selected.1 selected.2.1 selected.2.2

theorem jointSourceOuterQuery_probeBound (parameter : PublicParameter) (root : Digest)
    (input : (OracleWorld + SigningSpec).Domain) :
    JointSourceProbeBound (jointSourceOuterQuery parameter root input) (if OtsProbeSimulation.IsOuterHash input then 1 else 0) := by
  cases input with
  | inl input =>
      cases input with
      | inl n => exact jointSourceNativeBlock_probeBound _ 0 (OtsProbeSimulation.splitUniformImpl_probeFree n)
      | inr input => exact jointSourceHashQuery_probeBound parameter input
  | inr message => exact jointSourceSign_probeFree parameter root message

theorem jointSourceComputation_probeBound (parameter : PublicParameter) (root : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (hbound : computation.IsQueryBoundP OtsProbeSimulation.IsOuterHash q) :
    JointSourceProbeBound (jointSourceComputation parameter root computation) q := by
  induction computation using OracleComp.inductionOn generalizing q with
  | pure value =>
      intro cache
      exact (jointSourceNativeBlock_probeBound _ 0 (OtsProbeSimulation.ProbeFree.pure value) cache).mono (Nat.zero_le q)
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      intro cache
      have hstep := JointSourceProbeBound.bind (jointSourceOuterQuery_probeBound parameter root input)
        (fun output => ih output _ (hbound.2 output)) cache
      have hcost : (if OtsProbeSimulation.IsOuterHash input then 1 else 0) +
          (if OtsProbeSimulation.IsOuterHash input then q - 1 else q) ≤ q := by
        by_cases hhash : OtsProbeSimulation.IsOuterHash input
        · have hpos := hbound.1.resolve_left (not_not.mpr hhash)
          simp only [if_pos hhash]
          omega
        · simp [hhash]
      exact hstep.mono hcost

end SphincsSecurity.Concrete.FtsProbeSimulation
