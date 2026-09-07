import SphincsSecurity.Proof.EncodingCollisionSettlement
import SphincsSecurity.Proof.EncodingMessageReserve

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition
set_option backward.isDefEq.respectTransparency false

noncomputable def encodingCollisionRefund (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (key : SecretKey) (position : EncodingPosition) : Nat :=
  (encodingCachedAt key.parameter cache position).ncard -
    (encodingCollisionMessageTargets key.parameter cache hfinite position).card

theorem encodingCollisionTargets_add_refund_eq (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (key : SecretKey) (position : EncodingPosition) :
    (encodingCollisionMessageTargets key.parameter cache hfinite position).card +
      encodingCollisionRefund cache hfinite key position = (encodingCachedAt key.parameter cache position).ncard :=
  Nat.add_sub_of_le (encodingCollisionMessageTargets_card_le_cached key.parameter cache hfinite position)

theorem encodingMessageReserve_add_collisionTargets_refund_le_of_new_message
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {key : SecretKey} {input : HashInput} {answer : HashOutput}
    {position : EncodingPosition}
    (hfresh : cache input = none) (hnotAt : ∀ candidate : EncodingPosition, ¬ AtEncodingPosition key.parameter input candidate)
    (hbefore : ¬ EncodingMessageSettledAt cache key position)
    (hafter : EncodingMessageSettledAt (cache.cacheQuery input answer) key position) :
    encodingMessageReserve (cache.cacheQuery input answer) key +
      (encodingCollisionMessageTargets key.parameter cache hfinite position).card +
      encodingCollisionRefund cache hfinite key position ≤ encodingMessageReserve cache key := by
  have hselected : encodingMessageReserveAt (cache.cacheQuery input answer) key position +
      (encodingCollisionMessageTargets key.parameter cache hfinite position).card +
      encodingCollisionRefund cache hfinite key position = encodingMessageReserveAt cache key position := by
    rw [encodingMessageReserveAt, if_pos hafter, Nat.zero_add,
      encodingMessageReserveAt, if_neg hbefore, encodingCollisionTargets_add_refund_eq]
  rw [encodingMessageReserve, encodingMessageReserve,
    Fintype.sum_eq_add_sum_subtype_ne _ position, Fintype.sum_eq_add_sum_subtype_ne _ position]
  have hother : (∑ candidate : {candidate : EncodingPosition // candidate ≠ position},
      encodingMessageReserveAt (cache.cacheQuery input answer) key candidate) ≤
      ∑ candidate : {candidate : EncodingPosition // candidate ≠ position}, encodingMessageReserveAt cache key candidate := by
    apply Finset.sum_le_sum
    intro candidate _
    exact encodingMessageReserveAt_cacheQuery_le_of_not_atPosition hfresh (hnotAt candidate)
  omega

theorem uniform_encodingSelectionContribution_add_refund_le_messageCredit
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {key : SecretKey} {input : HashInput}
    {position : EncodingPosition} {index : Index}
    (hfresh : cache input = none)
    (htree : treeIndexAt index position.lay = position.tree)
    (hleaf : leafIndexAt index position.lay = position.leafIdx)
    (hunsettled : ¬ Settled key.parameter key.otsSecret key.ftsSecret cache (layerMessagePosition index position.lay))
    (hat : AtPosition key.parameter input (layerMessagePosition index position.lay)) :
    (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      encodingSelectionContribution (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) key position) +
      (encodingCollisionRefund cache hfinite key position : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ ≤
      encodingSelectionContribution cache hfinite key position +
        ((encodingCachedAt key.parameter cache position).ncard : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ := by
  apply (add_le_add (uniform_encodingSelectionContribution_cacheQuery_add_collisionMessageTargets_sum_le
    hfinite hfresh htree hleaf hunsettled hat) le_rfl).trans_eq
  rw [add_assoc, ← add_mul, ← Nat.cast_add, encodingCollisionTargets_add_refund_eq]

end SphincsSecurity.Concrete
