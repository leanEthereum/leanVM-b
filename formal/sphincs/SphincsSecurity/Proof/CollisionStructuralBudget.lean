import SphincsSecurity.Proof.CollisionStructuralRootPotential
import SphincsSecurity.Proof.SettledEncodingReserve
import SphincsSecurity.Proof.PreExceptionChargeMonotonicity

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition instFintypeEncodingPosition
set_option backward.isDefEq.respectTransparency false

noncomputable def collisionSigningBaseCharge (key : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  collisionParentStoppedEncodingBaseCharge key cache input + ftsParentQueryCharge key cache input

theorem collisionSigningBaseCharge_le_structural (key : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) :
    collisionSigningBaseCharge key cache input ≤ signingStructuralCharge key cache input := by
  unfold collisionSigningBaseCharge signingStructuralCharge
  apply add_le_add ?_ le_rfl
  unfold collisionParentStoppedEncodingBaseCharge parentStoppedEncodingQueryCharge
  by_cases hfresh : cache input = none
  · rw [if_pos hfresh, if_pos hfresh]
    by_cases he : ∃ position : EncodingPosition, AtEncodingPosition key.parameter input position
    · rw [if_pos he, dif_pos he, Nat.cast_add, Nat.cast_one]
      exact le_add_left le_rfl
    · rw [if_neg he, dif_neg he]
  · rw [if_neg hfresh, if_neg hfresh]

namespace FtsProbeSimulation

theorem collisionSigningBaseCharge_add_encoding_le
    (key : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) :
    collisionSigningBaseCharge key cache input + encodingHashCharge key.parameter cache input ≤
      nonMessageHashCharge key.parameter cache input +
        if NonMessageNonSecretHashInput key.parameter input then 1 else 0 := by
  by_cases he : ∃ position : EncodingPosition, AtEncodingPosition key.parameter input position
  · obtain ⟨position, hat⟩ := he
    have hm : ¬ MessageHashInput key.parameter input := fun h => h.not_atEncoding position hat
    have hn : NonMessageNonSecretHashInput key.parameter input := ⟨NonSecretHashInput.of_atEncoding hat, hm⟩
    have hp : ftsParentQueryCharge key cache input = 0 :=
      (add_eq_zero.mp (ots_ftsLeaf_parent_queryCharge_eq_zero_of_atEncoding key cache input hat)).2
    simpa only [collisionSigningBaseCharge, hp, add_zero, encodingHashCharge,
      if_pos (show ∃ position, AtEncodingPosition key.parameter input position from ⟨position, hat⟩),
      nonMessageHashCharge, if_neg hm, if_pos hn] using
      add_le_add (collisionParentStoppedEncodingBaseCharge_le_one key cache input) (le_refl (1 : ENNReal))
  · rw [encodingHashCharge, if_neg he, add_zero]
    exact (collisionSigningBaseCharge_le_structural key cache input).trans
      (signingStructuralCharge_le_nonMessage_add_nonMessageNonSecret key cache input)

theorem expectedPreExceptionCharge_collisionBase_sign_add_nonEncoding_le_nonMessage
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception (collisionSigningBaseCharge key) (sign key message) cache hit +
      expectedPreExceptionCharge exception (nonMessageNonEncodingHashCharge key.parameter) (sign key message) cache hit ≤
        expectedPreExceptionCharge exception (nonMessageHashCharge key.parameter) (sign key message) cache hit :=
  (add_le_add (expectedPreExceptionCharge_mono exception _ _ (collisionSigningBaseCharge_le_structural key)
    (sign key message) cache hit) le_rfl).trans
      (expectedPreExceptionCharge_sign_add_nonEncoding_le_nonMessage exception key message cache hit)

namespace JointOriginal

theorem beforeFailureCollisionBase_add_signingNonEncoding_add_encoding_le
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedBeforeFailureCharge exception (collisionSigningBaseCharge (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable computation frame cache hit failed +
      expectedBeforeFailureSigningCharge exception (nonMessageNonEncodingHashCharge parameter)
        parameter root otsTable ftsTable computation frame cache hit failed +
      expectedBeforeFailureOuterCharge exception (encodingHashCharge parameter)
        parameter root otsTable ftsTable computation frame cache hit failed ≤
      expectedBeforeFailureCharge exception (nonMessageHashCharge parameter)
        parameter root otsTable ftsTable computation frame cache hit failed +
      expectedBeforeFailureOuterCharge exception (fun _ input => if NonMessageNonSecretHashInput parameter input then 1 else 0)
        parameter root otsTable ftsTable computation frame cache hit failed :=
  beforeFailureCharge_add_signingNonEncoding_add_outerReserve_le exception parameter root otsTable ftsTable
    (collisionSigningBaseCharge (secretKey parameter root otsTable ftsTable)) (encodingHashCharge parameter)
    (expectedPreExceptionCharge_collisionBase_sign_add_nonEncoding_le_nonMessage exception (secretKey parameter root otsTable ftsTable))
    (collisionSigningBaseCharge_add_encoding_le (secretKey parameter root otsTable ftsTable))
    computation frame cache hit failed

end JointOriginal
end FtsProbeSimulation
end SphincsSecurity.Concrete
