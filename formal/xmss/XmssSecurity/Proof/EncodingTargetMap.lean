import XmssSecurity.Proof.WinningEventReduction
import XmssSecurity.Proof.HashInputLemmas

open OracleSpec

namespace XmssSecurity

/-- Recover the epoch tag from a well-formed serialized encoding input. Inputs outside the encoding domain return `none`. -/
noncomputable def encodingInputEpoch? (parameter : PublicParameter)
    (candidate : HashInput) : Option Epoch :=
  if h : ∃ epoch input,
      Concrete.CacheView.encodingInput parameter epoch input = candidate then
    some (Classical.choose h)
  else
    none

@[simp]
theorem encodingInputEpoch?_encodingInput (parameter : PublicParameter)
    (epoch : Epoch) (input : Message × Randomness) :
    encodingInputEpoch? parameter
      (Concrete.CacheView.encodingInput parameter epoch input) = some epoch := by
  unfold encodingInputEpoch?
  split <;> rename_i h
  · obtain ⟨chosenInput, hchosen⟩ := Classical.choose_spec h
    have hepoch : Classical.choose h = epoch :=
      Concrete.CacheView.epoch_eq_of_encodingInput_eq parameter hchosen
    rw [hepoch]
  · exfalso
    exact h ⟨epoch, input, rfl⟩

theorem exists_encodingInput_of_encodingInputEpoch?_eq_some
    (parameter : PublicParameter) (candidate : HashInput) (epoch : Epoch)
    (hepoch : encodingInputEpoch? parameter candidate = some epoch) :
    ∃ input : Message × Randomness,
      Concrete.CacheView.encodingInput parameter epoch input = candidate := by
  unfold encodingInputEpoch? at hepoch
  split at hepoch <;> rename_i h
  · obtain ⟨input, hinput⟩ := Classical.choose_spec h
    have heq : Classical.choose h = epoch := Option.some.inj hepoch
    rw [heq] at hinput
    exact ⟨input, hinput⟩
  · contradiction

/-- `target` is the serialized input of the unique returned signature at the epoch encoded by `candidate`. -/
def IsSignedEncodingTarget (parameter : PublicParameter)
    (log : QueryLog SigningSpec) (candidate target : HashInput) : Prop :=
  ∃ request signature,
    SigningTranscript.Returned log request signature ∧
    encodingInputEpoch? parameter candidate = some request.epoch ∧
    target = Concrete.CacheView.encodingInput parameter request.epoch
      (request.message, signature.randomness)

theorem IsSignedEncodingTarget.unique
    {parameter : PublicParameter} {log : QueryLog SigningSpec}
    (hvalid : SigningTranscript.Valid log) {candidate left right : HashInput}
    (hleft : IsSignedEncodingTarget parameter log candidate left)
    (hright : IsSignedEncodingTarget parameter log candidate right) :
    left = right := by
  obtain ⟨leftRequest, leftSignature, hleftReturned, hleftEpoch, rfl⟩ := hleft
  obtain ⟨rightRequest, rightSignature, hrightReturned, hrightEpoch, rfl⟩ := hright
  have hepoch : leftRequest.epoch = rightRequest.epoch :=
    Option.some.inj (hleftEpoch.symm.trans hrightEpoch)
  obtain ⟨hrequest, hsignature⟩ :=
    SigningTranscript.returned_eq_of_same_epoch hvalid hleftReturned hrightReturned hepoch
  subst rightRequest
  subst rightSignature
  rfl

/-- Select the returned signature input at the candidate input's epoch. If no signature was returned at that epoch, leave the candidate unchanged. -/
noncomputable def signedEncodingTargetInput (parameter : PublicParameter)
    (log : QueryLog SigningSpec) (candidate : HashInput) : HashInput := by
  classical
  exact if h : ∃ target, IsSignedEncodingTarget parameter log candidate target then
      Classical.choose h
    else
      candidate

theorem signedEncodingTargetInput_eq_of_target
    {parameter : PublicParameter} {log : QueryLog SigningSpec}
    (hvalid : SigningTranscript.Valid log) {candidate target : HashInput}
    (htarget : IsSignedEncodingTarget parameter log candidate target) :
    signedEncodingTargetInput parameter log candidate = target := by
  classical
  unfold signedEncodingTargetInput
  split <;> rename_i h
  · exact IsSignedEncodingTarget.unique hvalid (Classical.choose_spec h) htarget
  · exact (h ⟨target, htarget⟩).elim

end XmssSecurity
