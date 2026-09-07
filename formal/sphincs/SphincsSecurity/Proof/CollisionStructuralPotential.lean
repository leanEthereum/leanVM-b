import SphincsSecurity.Proof.CollisionAnswerEncodingStoppedBound
import SphincsSecurity.Proof.OriginalStructuralPotential

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition instFintypeEncodingPosition
set_option backward.isDefEq.respectTransparency false

noncomputable def collisionSigningStructuralCharge (key : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  collisionParentStoppedEncodingQueryCharge key cache input + ftsParentQueryCharge key cache input

noncomputable def collisionStructuralRecordPotential (key : SecretKey) (cache : QueryCache HashSpec) (saved : Option ExceptionRecord) : ENNReal :=
  collisionAnswerEncodingMonitorPotential key cache saved.isSome + ftsParentSelectionPotential key cache saved

theorem expected_collisionStructuralRecordPotential_le_preCharge
    (key : SecretKey) (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (saved : Option ExceptionRecord) :
    (∑' result, Pr[= result | runFirstException (CleanParentSettlement key.parameter key.otsSecret key.ftsSecret) computation cache saved] *
      collisionStructuralRecordPotential key result.1.2 result.2) ≤
      collisionStructuralRecordPotential key cache saved +
        expectedPreExceptionCharge (CleanParentSettlement key.parameter key.otsSecret key.ftsSecret) (collisionSigningStructuralCharge key)
          computation cache saved.isSome * (Fintype.card Digest : ENNReal)⁻¹ := by
  have ha := expected_collisionAnswerEncodingMonitorPotential_le_preExceptionCharge key computation cache hfinite saved.isSome
  rw [← runFirstException_flag_projection, tsum_probOutput_map_mul] at ha
  have hp := expected_ftsParentSelectionPotential_le_preCharge key computation cache hfinite saved
  simp only [collisionStructuralRecordPotential, mul_add, ENNReal.tsum_add]
  apply (add_le_add ha hp).trans_eq
  rw [show collisionSigningStructuralCharge key = (fun cache input => collisionParentStoppedEncodingQueryCharge key cache input +
    ftsParentQueryCharge key cache input) from rfl, expectedPreExceptionCharge_add, add_mul]
  ac_rfl

theorem collisionStructuralRecordPotential_none_ge_bad
    (key : SecretKey) (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (hbad : Bad key.parameter key.otsSecret key.ftsSecret cache ∨ EncodingBad cache key) :
    1 ≤ collisionStructuralRecordPotential key cache none := by
  simp only [collisionStructuralRecordPotential, collisionAnswerEncodingMonitorPotential, Option.isSome_none, Bool.false_eq_true, if_false,
    collisionAnswerEncodingAdaptivePotential_eq hfinite, collisionAnswerEncodingTotalPotential_eq_one_of_bad_or_encodingBad hfinite hbad]
  exact le_self_add

end SphincsSecurity.Concrete
