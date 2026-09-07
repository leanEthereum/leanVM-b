import SphincsSecurity.Proof.BeforeFailureSigningCharge

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def encodingHashCharge (parameter : PublicParameter) (_ : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  if ∃ position : EncodingPosition, AtEncodingPosition parameter input position then 1 else 0

noncomputable def nonMessageNonEncodingHashCharge (parameter : PublicParameter) (_ : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  if MessageHashInput parameter input then 0 else
    if ∃ position : EncodingPosition, AtEncodingPosition parameter input position then 0 else 1

theorem nonMessageHashCharge_eq_encoding_add_remaining (parameter : PublicParameter) (cache : QueryCache HashSpec) (input : HashInput) :
    nonMessageHashCharge parameter cache input = encodingHashCharge parameter cache input + nonMessageNonEncodingHashCharge parameter cache input := by
  by_cases hm : MessageHashInput parameter input
  · have he : ¬ ∃ position : EncodingPosition, AtEncodingPosition parameter input position := by
      rintro ⟨position, hat⟩
      exact hm.not_atEncoding position hat
    simp only [nonMessageHashCharge, encodingHashCharge, nonMessageNonEncodingHashCharge, if_pos hm, if_neg he, add_zero]
  · simp only [nonMessageHashCharge, encodingHashCharge, nonMessageNonEncodingHashCharge, if_neg hm]
    split_ifs <;> simp

theorem expectedPreExceptionCharge_sign_add_nonEncoding_le_nonMessage
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception (signingStructuralCharge key) (sign key message) cache hit +
      expectedPreExceptionCharge exception (nonMessageNonEncodingHashCharge key.parameter) (sign key message) cache hit ≤
        expectedPreExceptionCharge exception (nonMessageHashCharge key.parameter) (sign key message) cache hit := by
  have hencoding : ∀ current input position, AtEncodingPosition key.parameter input position → 1 ≤ encodingHashCharge key.parameter current input := by
    intro current input position hat
    simp only [encodingHashCharge, if_pos (show ∃ position, AtEncodingPosition key.parameter input position from ⟨position, hat⟩), le_refl]
  apply (add_le_add (expectedPreExceptionCharge_sign_le_encodingCharge exception key _ hencoding message cache hit) le_rfl).trans_eq
  rw [← expectedPreExceptionCharge_add]
  have heq : (fun current input => encodingHashCharge key.parameter current input + nonMessageNonEncodingHashCharge key.parameter current input) =
      nonMessageHashCharge key.parameter := by
    funext current input
    exact (nonMessageHashCharge_eq_encoding_add_remaining key.parameter current input).symm
  rw [heq]

end SphincsSecurity.Concrete.FtsProbeSimulation
