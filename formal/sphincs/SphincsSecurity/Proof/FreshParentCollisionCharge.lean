import SphincsSecurity.Proof.JointParentReserveConservation
import SphincsSecurity.Proof.SigningCollisionCoverageCharge

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem twice_freshFtsParentReserveCharge_le_collisionCharge
    (key : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) :
    2 * freshFtsParentReserveCharge key cache input ≤ collisionSigningStructuralCharge key cache input := by
  unfold freshFtsParentReserveCharge freshParentReserveCharge
  by_cases hfresh : cache input = none
  · rw [if_pos hfresh]
    by_cases hp : ∃ position, AtPosition key.parameter input position ∧ ¬ OtsProbeSimulation.IsOtsPosition position ∧
        ¬ ∀ child ∈ position.children, Settled key.parameter key.otsSecret key.ftsSecret cache child
    · have hparent : ftsParentQueryCharge key cache input = 1 := by
        simp only [ftsParentQueryCharge, parentReserveCharge, if_pos hp, Nat.cast_one]
      obtain ⟨position, hat, he, hchildren⟩ := hp
      have hencoding : ¬ ∃ encoding : EncodingPosition, AtEncodingPosition key.parameter input encoding := by
        rintro ⟨encoding, henc⟩
        exact henc.not_atPosition position hat
      have hsettling : ¬ ∃ queried : Position, AtPosition key.parameter input queried ∧
          ¬ Settled key.parameter key.otsSecret key.ftsSecret cache queried ∧
          ∀ answer, Settled key.parameter key.otsSecret key.ftsSecret (cache.cacheQuery input answer) queried := by
        rintro ⟨queried, hq, hb, ha⟩
        have heq := atPosition_unique key.parameter hq hat
        subst queried
        exact hchildren (eq_cachedInput_and_children_of_settled_cacheQuery key.parameter key.otsSecret key.ftsSecret hfresh hat hb (ha 0)).2
      have hbase : collisionParentStoppedEncodingBaseCharge key cache input = 1 := by
        simp only [collisionParentStoppedEncodingBaseCharge, if_pos hfresh, if_neg hencoding, if_neg hsettling,
          if_pos (show ∃ queried, AtPosition key.parameter input queried from ⟨position, hat⟩)]
      change 2 * ftsParentQueryCharge key cache input ≤ _
      rw [collisionSigningStructuralCharge, collisionParentStoppedEncodingQueryCharge, hbase, hparent]
      calc
        _ = (1 : ENNReal) + 1 := by norm_num
        _ ≤ _ := add_le_add le_self_add le_rfl
    · simp only [parentReserveCharge, if_neg hp, Nat.cast_zero, mul_zero, zero_le]
  · simp only [if_neg hfresh, mul_zero, zero_le]

end SphincsSecurity.Concrete
