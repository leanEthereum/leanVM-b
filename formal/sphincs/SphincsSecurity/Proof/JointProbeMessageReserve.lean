import SphincsSecurity.Proof.JointProbeBeforeFailureErasure

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

def MessageHashInput (parameter : PublicParameter) (input : HashInput) : Prop :=
  ∃ payload, tweakableHashInput parameter .message payload = input

def NonMessageNonSecretHashInput (parameter : PublicParameter) (input : HashInput) : Prop :=
  NonSecretHashInput parameter input ∧ ¬ MessageHashInput parameter input

theorem MessageHashInput.nonSecret {parameter : PublicParameter} {input : HashInput}
    (hmessage : MessageHashInput parameter input) : NonSecretHashInput parameter input := by
  obtain ⟨payload, rfl⟩ := hmessage
  have hnposition : ∀ position, ¬ AtPosition parameter (tweakableHashInput parameter .message payload) position := by
    rintro position ⟨otherPayload, hinput⟩
    have hdomain := (tweakableHashInput_injective parameter (by trivial) (Position.domain_inRange position) hinput).1
    cases position <;> simp [Position.domain] at hdomain
  refine ⟨?_, ?_⟩
  · rintro ⟨position, _, hat⟩
    exact hnposition position hat
  · rw [decodeProbe?_eq_none_iff]
    intro probe heq
    apply hnposition (.ftsLeaf probe.index probe.tree probe.leafIdx)
    rw [← heq]
    exact ⟨digestBytes probe.candidate, rfl⟩

theorem signingStructuralCharge_le_one_add_nonMessageNonSecret
    (key : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) :
    signingStructuralCharge key cache input ≤
      1 + if NonMessageNonSecretHashInput key.parameter input then 1 else 0 := by
  by_cases hm : MessageHashInput key.parameter input
  · obtain ⟨payload, rfl⟩ := hm
    rw [signingStructuralCharge_message_eq_zero]
    exact bot_le
  · simpa only [signingStructuralCharge, NonMessageNonSecretHashInput, hm, not_false_eq_true, and_true] using
      parentStoppedEncoding_add_ftsParent_le_one_add_nonSecret key cache input

noncomputable def selectedJointQueryCharge (select : HashInput → Prop) : JointQueryCharge :=
  fun input _ _ _ _ => if JointOriginal.IsSelectedOuterHash select input then 1 else 0

noncomputable def sampledSelectedJointQueryCharge (select : PublicParameter → HashInput → Prop)
    (adversary : Adversary) (q : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      expectedJointRetainedCharge adversary parameter (curryFtsTableEquiv ftsSecret) q (selectedJointQueryCharge (select parameter))

theorem jointNonSecretQueryCharge_eq_nonMessage_add_message (parameter : PublicParameter) :
    jointNonSecretQueryCharge parameter = fun input context cache state ftsCache =>
      selectedJointQueryCharge (NonMessageNonSecretHashInput parameter) input context cache state ftsCache +
        selectedJointQueryCharge (MessageHashInput parameter) input context cache state ftsCache := by
  funext input context cache state ftsCache
  cases input with
  | inl query =>
      cases query with
      | inl sample => simp [jointNonSecretQueryCharge, selectedJointQueryCharge, JointOriginal.IsSelectedOuterHash]
      | inr input =>
          by_cases hm : MessageHashInput parameter input
          · simp [jointNonSecretQueryCharge, selectedJointQueryCharge, JointOriginal.IsSelectedOuterHash,
              NonMessageNonSecretHashInput, hm, hm.nonSecret]
          · simp [jointNonSecretQueryCharge, selectedJointQueryCharge, JointOriginal.IsSelectedOuterHash,
              NonMessageNonSecretHashInput, hm]
  | inr message => simp [jointNonSecretQueryCharge, selectedJointQueryCharge, JointOriginal.IsSelectedOuterHash]

theorem sampledJointNonSecretQueryCharge_eq_nonMessage_add_message (adversary : Adversary) (q : Nat) :
    sampledJointNonSecretQueryCharge adversary q =
      sampledSelectedJointQueryCharge NonMessageNonSecretHashInput adversary q +
        sampledSelectedJointQueryCharge MessageHashInput adversary q := by
  unfold sampledJointNonSecretQueryCharge sampledSelectedJointQueryCharge
  simp_rw [jointNonSecretQueryCharge_eq_nonMessage_add_message, expectedJointRetainedCharge_add,
    mul_add, ENNReal.tsum_add]
  simp only [mul_add, ENNReal.tsum_add]

namespace JointOriginal

noncomputable def sampledBeforeFailureSelectedCharge (select : PublicParameter → HashInput → Prop)
    (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        ∑' initial, Pr[= initial | initializeRoot parameter table (curryFtsTableEquiv ftsSecret) q fuel] *
          expectedBeforeFailureOuterCharge (parentException parameter table (curryFtsTableEquiv ftsSecret))
            (fun _ input => if select parameter input then 1 else 0)
            parameter initial.2.1 table (curryFtsTableEquiv ftsSecret) (retainedComputation adversary parameter initial.2.1 q)
              initial.1 initial.2.2 false initial.1.isNone

theorem sampledBeforeFailureSelectedCharge_le_erased (select : PublicParameter → HashInput → Prop)
    (adversary : Adversary) (q fuel : Nat) :
    sampledBeforeFailureSelectedCharge select adversary q fuel ≤ sampledSelectedJointQueryCharge select adversary q := by
  unfold sampledBeforeFailureSelectedCharge sampledSelectedJointQueryCharge
  apply ENNReal.tsum_le_tsum
  intro parameter
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro ftsSecret
  exact mul_le_mul' le_rfl (beforeFailureOuterSelectedCharge_le_erased adversary parameter (curryFtsTableEquiv ftsSecret) q fuel (select parameter))

theorem beforeFailureStructural_le_hash_add_nonMessageNonSecret
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedBeforeFailureCharge exception (signingStructuralCharge (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable computation frame cache hit failed ≤
      expectedBeforeFailureCharge exception (fun _ _ => 1) parameter root otsTable ftsTable computation frame cache hit failed +
        expectedBeforeFailureOuterCharge exception (fun _ input => if NonMessageNonSecretHashInput parameter input then 1 else 0)
          parameter root otsTable ftsTable computation frame cache hit failed :=
  expectedBeforeFailureCharge_le_add_outer exception parameter root otsTable ftsTable _ _ _
    (signingStructuralCharge_le_one_add_nonMessageNonSecret (secretKey parameter root otsTable ftsTable))
    (expectedPreExceptionCharge_sign_le_preHashQueries exception (secretKey parameter root otsTable ftsTable))
    computation frame cache hit failed

theorem sampledBeforeFailureStructural_le_restHash_add_nonMessageNonSecret (adversary : Adversary) (q fuel : Nat) :
    sampledBeforeFailureStructuralCharge adversary q fuel ≤
      sampledBeforeFailureRestHashCharge adversary q fuel +
        sampledBeforeFailureSelectedCharge NonMessageNonSecretHashInput adversary q fuel := by
  unfold sampledBeforeFailureStructuralCharge initializedBeforeFailureStructuralCharge
    sampledBeforeFailureRestHashCharge sampledBeforeFailureSelectedCharge
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
  exact mul_le_mul' le_rfl (beforeFailureStructural_le_hash_add_nonMessageNonSecret
    (parentException parameter table (curryFtsTableEquiv ftsSecret)) parameter initial.2.1 table (curryFtsTableEquiv ftsSecret)
    (retainedComputation adversary parameter initial.2.1 q) initial.1 initial.2.2 false initial.1.isNone)

end JointOriginal
end SphincsSecurity.Concrete.FtsProbeSimulation
