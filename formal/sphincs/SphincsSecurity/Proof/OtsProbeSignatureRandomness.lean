import SphincsSecurity.Proof.OtsProbeNativePublicationCache

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ftsOpen maskedChronologicalSignLayers

theorem publishSignatureBody_randomness_of_mem
    (randomness : Randomness) (index : Index) (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (layers : Layer → Option ChronologicalLayerPart) (cache finalCache : SplitHashCache) (body : PublishedSignatureBody)
    (hresult : (some body, finalCache) ∈ support ((publishSignatureBody randomness index ftsPath layers).run cache)) :
    body.randomness = randomness := by
  unfold publishSignatureBody at hresult
  cases hparts : traverseOption layers with
  | none => simp [hparts] at hresult
  | some parts =>
      simp only [hparts, StateT.run_bind, mem_support_bind_iff] at hresult
      obtain ⟨published, _, hresult⟩ := hresult
      simp only [StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq] at hresult
      rw [hresult.1]

theorem publishChronologicalSignature_randomness_of_mem
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) (layers : Layer → Option ChronologicalLayerPart)
    (cache finalCache : SplitHashCache) (signature : Signature)
    (hresult : (some signature, finalCache) ∈ support
      ((publishChronologicalSignature ftsSecret randomness index leaves ftsPath layers).run cache)) :
    signature.randomness = randomness := by
  rw [publishChronologicalSignature_eq_body, StateT.run_map, support_map] at hresult
  obtain ⟨result, hresult, heq⟩ := hresult
  rcases result with ⟨body, bodyCache⟩
  cases body with
  | none => simp at heq
  | some body =>
      simp only [Option.map_some, Prod.mk.injEq, Option.some.injEq] at heq
      rw [← heq.1]
      exact publishSignatureBody_randomness_of_mem randomness index ftsPath layers cache bodyCache body hresult

theorem maskedPublishedChronologicalSignAfterDigest_randomness_of_mem
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (cache finalCache : SplitHashCache) (signature : Signature)
    (hresult : (some signature, finalCache) ∈ support
      ((maskedPublishedChronologicalSignAfterDigest parameter ftsSecret randomness index leaves).run cache)) :
    signature.randomness = randomness := by
  unfold maskedPublishedChronologicalSignAfterDigest at hresult
  rw [StateT.run_bind, mem_support_bind_iff] at hresult
  obtain ⟨path, _, hresult⟩ := hresult
  rw [StateT.run_bind, mem_support_bind_iff] at hresult
  obtain ⟨layers, _, hresult⟩ := hresult
  exact publishChronologicalSignature_randomness_of_mem ftsSecret randomness index leaves path.1 layers.1 layers.2 finalCache signature hresult

end SphincsSecurity.Concrete.OtsProbeSimulation
