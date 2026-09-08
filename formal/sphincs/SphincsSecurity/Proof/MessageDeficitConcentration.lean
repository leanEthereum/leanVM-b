import SphincsSecurity.Proof.MessageDeficitMomentGrowth

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

def MessageDeficitExceptional (key : SecretKey) (cache : QueryCache HashSpec) : Prop :=
  ∃ message, ((2 ^ 83 : Nat) : ENNReal) < Concrete.messageAdmissibleDeficit key message cache

theorem positiveScoreMoment_eq_pow_ofReal (score : ℝ) (power : Nat) :
    positiveScoreMoment score power = ENNReal.ofReal score ^ power := by
  rw [positiveScoreMoment, ENNReal.ofReal_pow (le_max_right _ _)]
  simp only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left (show 0 ≤ ENNReal.ofReal score from zero_le)]

theorem messageDeficitExceptional_fourthMoment_le (key : SecretKey)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (hbad : MessageDeficitExceptional key cache) :
    (2 : ENNReal) ^ 372 ≤ messageDeficitMoment key.parameter key.root cache 4 := by
  obtain ⟨message, hmessage⟩ := hbad
  have hscaled : (2 : ENNReal) ^ 93 ≤ 1024 * Concrete.messageAdmissibleDeficit key message cache := by
    calc
      _ = 1024 * ((2 ^ 83 : Nat) : ENNReal) := by norm_num
      _ ≤ _ := mul_le_mul' le_rfl hmessage.le
  calc
    (2 : ENNReal) ^ 372 = ((2 : ENNReal) ^ 93) ^ 4 := by rw [← pow_mul]
    _ ≤ (1024 * Concrete.messageAdmissibleDeficit key message cache) ^ 4 := pow_le_pow_left' hscaled 4
    _ = positiveScoreMoment (messageDeficitScore key.parameter key.root message cache) 4 := by
      rw [positiveScoreMoment_eq_pow_ofReal, messageDeficitScore_ofReal_eq key message cache hfinite]
    _ ≤ _ := positiveScoreMoment_le_messageDeficitMoment key.parameter key.root cache 4 message

theorem cachedMessageEntryCount_zero_of_no_inputs (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (hnone : ∀ payload, cache (tweakableHashInput parameter .message payload) = none)
    (message : Message) : cachedMessageEntryCount cache parameter root message = 0 := by
  have hempty : cachedMessageInputSet cache parameter root message = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ⟨input, answer⟩ ⟨hcached, randomness, hinput⟩
    change cache input = some answer at hcached
    have h := hnone (Concrete.messageDigestPayload root message randomness)
    rw [← hinput, hcached] at h
    cases h
  simp only [cachedMessageEntryCount, hempty, Set.encard_empty, ENat.toENNReal_zero]

theorem probEvent_messageDeficitExceptional_le (key : SecretKey)
    (computation : OracleComp OracleWorld α) (q : Nat)
    (hbound : computation.IsQueryBoundP (· matches Sum.inr _) q) (hq : q ≤ 2 ^ 127)
    (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (hnone : ∀ payload, cache (tweakableHashInput key.parameter .message payload) = none) :
    Pr[fun result => result.2 = true |
      runExceptionMonitor (cacheEntryException (MessageDeficitExceptional key)) computation cache false] ≤
        (q : ENNReal) / 2 ^ 223 := by
  apply probEvent_cacheEntryException_le_fourthMoment (MessageDeficitExceptional key)
    (fun cache => messageDeficitMoment key.parameter key.root cache 2)
    (fun cache => messageDeficitMoment key.parameter key.root cache 4)
    (fun cache hfinite hbad => messageDeficitExceptional_fourthMoment_le key cache hfinite hbad)
    (fun cache hfinite input hfresh => expected_messageDeficit_second_le key.parameter key.root cache hfinite input hfresh)
    (fun cache hfinite input hfresh => expected_messageDeficit_fourth_le key.parameter key.root cache hfinite input hfresh)
    computation q hbound hq cache hfinite
  · exact messageDeficitMoment_zero_of_no_inputs key.parameter key.root cache
      (cachedMessageEntryCount_zero_of_no_inputs key.parameter key.root cache hnone) 2 (by decide)
  · exact messageDeficitMoment_zero_of_no_inputs key.parameter key.root cache
      (cachedMessageEntryCount_zero_of_no_inputs key.parameter key.root cache hnone) 4 (by decide)

theorem messageDeficitExceptional_not_of_no_inputs (key : SecretKey) (cache : QueryCache HashSpec)
    (hnone : ∀ payload, cache (tweakableHashInput key.parameter .message payload) = none) :
    ¬ MessageDeficitExceptional key cache := by
  rintro ⟨message, hmessage⟩
  have hzero := cachedMessageEntryCount_zero_of_no_inputs key.parameter key.root cache hnone message
  simp only [Concrete.messageAdmissibleDeficit, hzero, zero_mul, zero_tsub] at hmessage
  exact (not_lt_of_ge zero_le) hmessage

end SphincsSecurity
