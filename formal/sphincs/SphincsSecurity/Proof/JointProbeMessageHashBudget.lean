import SphincsSecurity.Proof.JointProbeMessageReserve
import SphincsSecurity.Proof.SigningStoppedEncodingChargeBudget

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

theorem MessageHashInput.not_atEncoding {parameter : PublicParameter} {input : HashInput}
    (hmessage : MessageHashInput parameter input) (position : EncodingPosition) :
    ¬ AtEncodingPosition parameter input position := by
  obtain ⟨payload, rfl⟩ := hmessage
  rintro ⟨otherPayload, hinput⟩
  have hdomain := (tweakableHashInput_injective parameter (by trivial) (by trivial) hinput).1
  simp [EncodingPosition.domain] at hdomain

noncomputable def nonMessageHashCharge (parameter : PublicParameter) (_ : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  if MessageHashInput parameter input then 0 else 1

noncomputable def messageHashCharge (parameter : PublicParameter) (_ : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  if MessageHashInput parameter input then 1 else 0

theorem signingStructuralCharge_le_nonMessage_add_nonMessageNonSecret
    (key : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) :
    signingStructuralCharge key cache input ≤ nonMessageHashCharge key.parameter cache input +
      if NonMessageNonSecretHashInput key.parameter input then 1 else 0 := by
  by_cases hm : MessageHashInput key.parameter input
  · obtain ⟨payload, rfl⟩ := hm
    rw [signingStructuralCharge_message_eq_zero]
    exact bot_le
  · simpa only [nonMessageHashCharge, if_neg hm] using
      signingStructuralCharge_le_one_add_nonMessageNonSecret key cache input

theorem expectedPreExceptionCharge_sign_le_nonMessageHashCharge
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception (signingStructuralCharge key) (sign key message) cache hit ≤
      expectedPreExceptionCharge exception (nonMessageHashCharge key.parameter) (sign key message) cache hit := by
  apply expectedPreExceptionCharge_sign_le_encodingCharge exception key (nonMessageHashCharge key.parameter) _ message cache hit
  intro current input position hat
  have hnot : ¬ MessageHashInput key.parameter input := fun hm => hm.not_atEncoding position hat
  simp only [nonMessageHashCharge, if_neg hnot, le_refl]

namespace JointOriginal

theorem expectedBeforeFailureCharge_add
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (first second : QueryCache HashSpec → HashInput → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedBeforeFailureCharge exception (fun cache input => first cache input + second cache input)
        parameter root otsTable ftsTable computation frame cache hit failed =
      expectedBeforeFailureCharge exception first parameter root otsTable ftsTable computation frame cache hit failed +
        expectedBeforeFailureCharge exception second parameter root otsTable ftsTable computation frame cache hit failed := by
  induction computation using OracleComp.inductionOn generalizing frame cache hit failed with
  | pure value => simp
  | query_bind input next ih =>
      simp only [expectedBeforeFailureCharge_query_bind, expectedPreExceptionCharge_add, ih]
      cases failed <;> simp only [Bool.false_eq_true, if_false, if_true, zero_add, mul_add, ENNReal.tsum_add]
      all_goals ac_rfl

noncomputable def sampledBeforeFailureHashCharge
    (charge : PublicParameter → QueryCache HashSpec → HashInput → ENNReal) (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        ∑' initial, Pr[= initial | initializeRoot parameter table (curryFtsTableEquiv ftsSecret) q fuel] *
          expectedBeforeFailureCharge (parentException parameter table (curryFtsTableEquiv ftsSecret)) (charge parameter)
            parameter initial.2.1 table (curryFtsTableEquiv ftsSecret) (retainedComputation adversary parameter initial.2.1 q)
              initial.1 initial.2.2 false initial.1.isNone

theorem sampledBeforeFailureRestHashCharge_eq_nonMessage_add_message (adversary : Adversary) (q fuel : Nat) :
    sampledBeforeFailureRestHashCharge adversary q fuel =
      sampledBeforeFailureHashCharge nonMessageHashCharge adversary q fuel +
        sampledBeforeFailureHashCharge messageHashCharge adversary q fuel := by
  have hsplit : (fun (_ : PublicParameter) (_ : QueryCache HashSpec) (_ : HashInput) => (1 : ENNReal)) =
      fun parameter cache input => nonMessageHashCharge parameter cache input + messageHashCharge parameter cache input := by
    funext parameter cache input
    by_cases hm : MessageHashInput parameter input <;> simp [nonMessageHashCharge, messageHashCharge, hm]
  change sampledBeforeFailureHashCharge (fun _ _ _ => 1) adversary q fuel = _
  rw [hsplit]
  unfold sampledBeforeFailureHashCharge
  simp_rw [expectedBeforeFailureCharge_add]
  simp only [mul_add, ENNReal.tsum_add]

theorem beforeFailureStructural_le_nonMessageHash_add_nonMessageNonSecret
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedBeforeFailureCharge exception (signingStructuralCharge (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable computation frame cache hit failed ≤
      expectedBeforeFailureCharge exception (nonMessageHashCharge parameter) parameter root otsTable ftsTable computation frame cache hit failed +
        expectedBeforeFailureOuterCharge exception (fun _ input => if NonMessageNonSecretHashInput parameter input then 1 else 0)
          parameter root otsTable ftsTable computation frame cache hit failed :=
  expectedBeforeFailureCharge_le_add_outer exception parameter root otsTable ftsTable _ _ _
    (signingStructuralCharge_le_nonMessage_add_nonMessageNonSecret (secretKey parameter root otsTable ftsTable))
    (expectedPreExceptionCharge_sign_le_nonMessageHashCharge exception (secretKey parameter root otsTable ftsTable))
    computation frame cache hit failed

theorem sampledBeforeFailureStructural_le_nonMessageHash_add_nonMessageNonSecret (adversary : Adversary) (q fuel : Nat) :
    sampledBeforeFailureStructuralCharge adversary q fuel ≤
      sampledBeforeFailureHashCharge nonMessageHashCharge adversary q fuel +
        sampledBeforeFailureSelectedCharge NonMessageNonSecretHashInput adversary q fuel := by
  unfold sampledBeforeFailureStructuralCharge initializedBeforeFailureStructuralCharge
    sampledBeforeFailureHashCharge sampledBeforeFailureSelectedCharge
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro parameter
  rw [← mul_add, ← ENNReal.tsum_add]
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro ftsSecret
  rw [← mul_add, ← ENNReal.tsum_add]
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro table
  rw [← mul_add, ← ENNReal.tsum_add]
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro initial
  rw [← mul_add]
  exact mul_le_mul' le_rfl (beforeFailureStructural_le_nonMessageHash_add_nonMessageNonSecret
    (parentException parameter table (curryFtsTableEquiv ftsSecret)) parameter initial.2.1 table (curryFtsTableEquiv ftsSecret)
    (retainedComputation adversary parameter initial.2.1 q) initial.1 initial.2.2 false initial.1.isNone)

end JointOriginal
end SphincsSecurity.Concrete.FtsProbeSimulation
