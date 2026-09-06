import SphincsSecurity.Proof.EncodingExhaustionBound

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 512

abbrev EncodingRetryFamily := PublicParameter × EncodingPosition × Digest

theorem encodingRetryFamily_card : Fintype.card EncodingRetryFamily = 3 * 2 ^ 294 := by
  have hposition : Fintype.card EncodingPosition = Fintype.card (Layer × TreeIndex × LeafIndex) :=
    Fintype.card_congr
      { toFun := fun position => (position.lay, position.tree, position.leafIdx)
        invFun := fun fields => ⟨fields.1, fields.2.1, fields.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  change Fintype.card (PublicParameter × EncodingPosition × Digest) = _
  rw [Fintype.card_prod, Fintype.card_prod, hposition]
  norm_num [publicParameterBits, digestBits, numLayers, totalHeight, maxLayerHeight]

noncomputable def encodingExhaustionTotalPotential (cache : QueryCache HashSpec) : ENNReal :=
  ∑ family : EncodingRetryFamily,
    encodingExhaustionPotential (encodingRetryInputs family.1 family.2.1 family.2.2) cache

theorem encodingExhaustionTotalPotential_empty_le_inv216 :
    encodingExhaustionTotalPotential ∅ ≤ ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  simp only [encodingExhaustionTotalPotential, encodingExhaustionPotential_empty_cache,
    encodingRetryInputs_card, Finset.sum_const, Finset.card_univ, encodingRetryFamily_card, nsmul_eq_mul]
  simpa only [encodingInvalidProbability, probEvent_uniform_encoding_invalid] using
    encoding_exhaustion_global_bound_le_inv216

private theorem le_sum_univ {ι : Type} [Fintype ι] (f : ι → ENNReal) (i : ι) : f i ≤ ∑ j, f j :=
  Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ i)

theorem one_le_encodingExhaustionTotalPotential_of_exhausted
    {cache : QueryCache HashSpec} (hexhausted : AnyEncodingInputsExhausted cache) :
    1 ≤ encodingExhaustionTotalPotential cache := by
  obtain ⟨parameter, position, message, hexhausted⟩ := hexhausted
  have hterm := encodingExhaustionPotential_eq_one_of_exhausted _ cache hexhausted
  rw [← hterm]
  unfold encodingExhaustionTotalPotential
  exact le_sum_univ
    (fun family : EncodingRetryFamily =>
      encodingExhaustionPotential (encodingRetryInputs family.1 family.2.1 family.2.2) cache)
    (parameter, position, message)

end SphincsSecurity.Concrete
