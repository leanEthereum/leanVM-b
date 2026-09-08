import SphincsSecurity.Proof.MessageDeficitScore
import SphincsSecurity.Proof.AdmissibleHashMoments

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

noncomputable def messageDeficitMoment (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (power : Nat) : ENNReal :=
  ∑ message : Message, positiveScoreMoment (messageDeficitScore parameter root message cache) power

theorem positiveScoreMoment_le_messageDeficitMoment (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (power : Nat) (message : Message) :
    positiveScoreMoment (messageDeficitScore parameter root message cache) power ≤
      messageDeficitMoment parameter root cache power := by
  unfold messageDeficitMoment
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun message : Message => positiveScoreMoment (messageDeficitScore parameter root message cache) power)
    (fun _ _ => zero_le) (Finset.mem_univ message)

theorem expected_messageScoreMoment_of_not_matching (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) (hfresh : cache input = none)
    (hmessage : ¬ MessageInputFor parameter root input message) (power : Nat) :
    (∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      positiveScoreMoment (messageDeficitScore parameter root message (cache.cacheQuery input answer)) power) =
      positiveScoreMoment (messageDeficitScore parameter root message cache) power := by
  simp_rw [messageDeficitScore_cacheQuery parameter root message cache hfinite input _ hfresh,
    if_neg hmessage, add_zero]
  rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]

theorem expected_messageScore_second_le (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) (hfresh : cache input = none) :
    (∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      positiveScoreMoment (messageDeficitScore parameter root message (cache.cacheQuery input answer)) 2) ≤
      positiveScoreMoment (messageDeficitScore parameter root message cache) 2 +
        if MessageInputFor parameter root input message then 1023 else 0 := by
  by_cases hmessage : MessageInputFor parameter root input message
  · simp_rw [messageDeficitScore_cacheQuery parameter root message cache hfinite input _ hfresh, if_pos hmessage]
    exact expected_admissibleScore_second_le _
  · rw [expected_messageScoreMoment_of_not_matching parameter root message cache hfinite input hfresh hmessage,
      if_neg hmessage, add_zero]

theorem expected_messageScore_fourth_le (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) (hfresh : cache input = none) :
    (∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      positiveScoreMoment (messageDeficitScore parameter root message (cache.cacheQuery input answer)) 4) ≤
      positiveScoreMoment (messageDeficitScore parameter root message cache) 4 +
        if MessageInputFor parameter root input message then
          6138 * positiveScoreMoment (messageDeficitScore parameter root message cache) 2 + 2 ^ 30 else 0 := by
  by_cases hmessage : MessageInputFor parameter root input message
  · simp_rw [messageDeficitScore_cacheQuery parameter root message cache hfinite input _ hfresh, if_pos hmessage]
    simpa only [add_assoc] using expected_admissibleScore_fourth_le (messageDeficitScore parameter root message cache)
  · rw [expected_messageScoreMoment_of_not_matching parameter root message cache hfinite input hfresh hmessage,
      if_neg hmessage, add_zero]

theorem expected_messageDeficitMoment_eq_sum (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (input : HashInput) (power : Nat) :
    (∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      messageDeficitMoment parameter root (cache.cacheQuery input answer) power) =
      ∑ message : Message, ∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        positiveScoreMoment (messageDeficitScore parameter root message (cache.cacheQuery input answer)) power := by
  simp only [messageDeficitMoment, Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)

theorem expected_messageDeficit_second_le (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) (hfresh : cache input = none) :
    (∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      messageDeficitMoment parameter root (cache.cacheQuery input answer) 2) ≤
      messageDeficitMoment parameter root cache 2 + 1023 := by
  rw [expected_messageDeficitMoment_eq_sum]
  apply (Finset.sum_le_sum (fun message _ =>
    expected_messageScore_second_le parameter root message cache hfinite input hfresh)).trans
  rw [Finset.sum_add_distrib]
  apply add_le_add le_rfl
  by_cases hmatch : ∃ message, MessageInputFor parameter root input message
  · obtain ⟨selected, hselected⟩ := hmatch
    have hiff (message : Message) : MessageInputFor parameter root input message ↔ message = selected :=
      ⟨fun h => h.unique hselected, fun h => h.symm ▸ hselected⟩
    simp only [hiff]
    simp
  · have hnone (message : Message) : ¬ MessageInputFor parameter root input message := fun h => hmatch ⟨message, h⟩
    simp [hnone]

theorem expected_messageDeficit_fourth_le (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) (hfresh : cache input = none) :
    (∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      messageDeficitMoment parameter root (cache.cacheQuery input answer) 4) ≤
      messageDeficitMoment parameter root cache 4 + 6138 * messageDeficitMoment parameter root cache 2 + 2 ^ 30 := by
  rw [expected_messageDeficitMoment_eq_sum, add_assoc]
  apply (Finset.sum_le_sum (fun message _ =>
    expected_messageScore_fourth_le parameter root message cache hfinite input hfresh)).trans
  rw [Finset.sum_add_distrib]
  apply add_le_add le_rfl
  by_cases hmatch : ∃ message, MessageInputFor parameter root input message
  · obtain ⟨selected, hselected⟩ := hmatch
    have hiff (message : Message) : MessageInputFor parameter root input message ↔ message = selected :=
      ⟨fun h => h.unique hselected, fun h => h.symm ▸ hselected⟩
    simp only [hiff]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ selected)]
    exact add_le_add (mul_le_mul' le_rfl (positiveScoreMoment_le_messageDeficitMoment parameter root cache 2 selected)) le_rfl
  · have hnone (message : Message) : ¬ MessageInputFor parameter root input message := fun h => hmatch ⟨message, h⟩
    simp [hnone]

theorem messageDeficitMoment_zero_of_no_inputs (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (hcount : ∀ message, cachedMessageEntryCount cache parameter root message = 0)
    (power : Nat) (hpower : power ≠ 0) : messageDeficitMoment parameter root cache power = 0 := by
  apply Finset.sum_eq_zero
  intro message _
  exact positiveScoreMoment_zero_of_nonpos _
    (messageDeficitScore_of_no_inputs parameter root message cache (hcount message)) power hpower

end SphincsSecurity
