import SphincsSecurity.Proof.FirstExceptionRefinement
import SphincsSecurity.Proof.AdaptiveNearUniformRaw

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec
open FtsProbeSimulation (MessageHashInput)

theorem atPosition_not_message {parameter : PublicParameter} {input : HashInput} {position : Position}
    (hat : AtPosition parameter input position) : ¬ MessageHashInput parameter input := by
  obtain ⟨otherPayload, hposition⟩ := hat
  rintro ⟨payload, hmessage⟩
  have hdomain := (tweakableHashInput_injective parameter (by trivial)
    (Position.domain_inRange position) (hmessage.trans hposition)).1
  cases position <;> simp [Position.domain] at hdomain

theorem messageAdmissibleDeficit_cacheQuery_nonmessage
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (input : HashInput) (answer : HashOutput)
    (hfresh : cache input = none) (hmessage : ¬ MessageHashInput key.parameter input) :
    messageAdmissibleDeficit key message (cache.cacheQuery input answer) = messageAdmissibleDeficit key message cache := by
  have hnot : ¬ ∃ randomness, input = tweakableHashInput key.parameter .message
      (messageDigestPayload key.root message randomness) := by
    rintro ⟨randomness, hinput⟩
    exact hmessage ⟨messageDigestPayload key.root message randomness, hinput.symm⟩
  unfold messageAdmissibleDeficit
  rw [cachedMessageEntryCount_cacheQuery_eq key.parameter key.root message cache input answer hfresh,
    cachedMessageEntryCountWhere_cacheQuery_eq key.parameter key.root message cache input answer hfresh]
  simp only [hnot, false_and, if_false, add_zero]

theorem messageDeficitExceptional_cacheQuery_nonmessage
    (key : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) (answer : HashOutput)
    (hfresh : cache input = none) (hmessage : ¬ MessageHashInput key.parameter input) :
    MessageDeficitExceptional key (cache.cacheQuery input answer) ↔ MessageDeficitExceptional key cache := by
  unfold MessageDeficitExceptional
  simp only [messageAdmissibleDeficit_cacheQuery_nonmessage key _ cache input answer hfresh hmessage]

namespace FtsProbeSimulation.JointOriginal

theorem firstDeficitExceptionRecord_nonmessage
    (key : SecretKey) (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (hclean : ¬ MessageDeficitExceptional key cache)
    (result : α × QueryCache HashSpec) (record : ExceptionRecord)
    (hresult : (result, some record) ∈ support
      (runFirstException (deficitStoppingException key exception) computation cache none))
    (hmessage : ¬ MessageHashInput key.parameter record.input) :
    exception record.cache record.input record.answer := by
  have hbefore := firstExceptionRecord_cache_clean (MessageDeficitExceptional key)
    (deficitStoppingException key exception) (fun _ _ _ h => Or.inr h)
    computation cache hclean result record hresult
  have hvalid := runFirstException_none_valid (deficitStoppingException key exception) computation cache
    hresult record (by simp)
  rcases hvalid.2.2.1 with hparent | hbad
  · exact hparent
  · exact False.elim (hbefore ((messageDeficitExceptional_cacheQuery_nonmessage key record.cache
      record.input record.answer hvalid.2.1 hmessage).mp hbad))

theorem firstDeficitExceptionRecord_support_nonmessage
    (key : SecretKey) (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (hclean : ¬ MessageDeficitExceptional key cache)
    (result : α × QueryCache HashSpec) (record : ExceptionRecord)
    (hresult : (result, some record) ∈ support
      (runFirstException (deficitStoppingException key exception) computation cache none))
    (hmessage : ¬ MessageHashInput key.parameter record.input) :
    (result, some record) ∈ support (runFirstException exception computation cache none) :=
  firstExceptionRecord_support_of_imp exception (deficitStoppingException key exception) (fun _ _ _ h => Or.inl h)
    computation cache result record hresult
    (firstDeficitExceptionRecord_nonmessage key exception computation cache hclean result record hresult hmessage)

end FtsProbeSimulation.JointOriginal
end SphincsSecurity.Concrete
