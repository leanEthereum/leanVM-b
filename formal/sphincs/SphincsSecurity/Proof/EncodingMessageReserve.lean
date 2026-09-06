import SphincsSecurity.Proof.EncodingSelectionPotential

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

noncomputable def encodingMessageReserveAt (cache : QueryCache HashSpec) (secretKey : SecretKey) (position : EncodingPosition) : Nat :=
  open Classical in
  if EncodingMessageSettledAt cache secretKey position then 0
  else (encodingCachedAt secretKey.parameter cache position).ncard

noncomputable def encodingMessageReserve (cache : QueryCache HashSpec) (secretKey : SecretKey) : Nat :=
  ∑ position : EncodingPosition, encodingMessageReserveAt cache secretKey position

noncomputable def encodingMessageIncrement (cache : QueryCache HashSpec) (secretKey : SecretKey) (position : EncodingPosition) : Nat :=
  open Classical in
  if EncodingMessageSettledAt cache secretKey position then 0 else 1

@[simp] theorem encodingMessageReserve_empty (secretKey : SecretKey) : encodingMessageReserve ∅ secretKey = 0 := by
  classical
  rw [encodingMessageReserve]
  apply Finset.sum_eq_zero
  intro position _
  have hcached : encodingCachedAt secretKey.parameter (∅ : QueryCache HashSpec) position = ∅ := by
    ext input
    simp [encodingCachedAt]
  simp [encodingMessageReserveAt, hcached]

theorem encodingMessageReserveAt_cacheQuery_le_of_not_atPosition
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {input : HashInput} {answer : HashOutput} {position : EncodingPosition}
    (hfresh : cache input = none) (hnotAt : ¬ AtEncodingPosition secretKey.parameter input position) :
    encodingMessageReserveAt (cache.cacheQuery input answer) secretKey position ≤ encodingMessageReserveAt cache secretKey position := by
  classical
  have hle := le_cacheQuery (answer := answer) hfresh
  have hcached := encodingCachedAt_cacheQuery_of_not_atPosition (cache := cache) (answer := answer) hnotAt
  by_cases hbefore : EncodingMessageSettledAt cache secretKey position
  · simp [encodingMessageReserveAt, hbefore, hbefore.mono hle]
  · simp only [encodingMessageReserveAt, if_neg hbefore]
    split_ifs
    · exact Nat.zero_le _
    · rw [hcached]

theorem encodingMessageReserveAt_cacheQuery_le_increment
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {input : HashInput} {answer : HashOutput} {position : EncodingPosition}
    (hfresh : cache input = none) (hat : AtEncodingPosition secretKey.parameter input position) :
    encodingMessageReserveAt (cache.cacheQuery input answer) secretKey position ≤
      encodingMessageReserveAt cache secretKey position + encodingMessageIncrement cache secretKey position := by
  classical
  have hle := le_cacheQuery (answer := answer) hfresh
  by_cases hbefore : EncodingMessageSettledAt cache secretKey position
  · simp [encodingMessageReserveAt, encodingMessageIncrement, hbefore, hbefore.mono hle]
  · simp only [encodingMessageReserveAt, encodingMessageIncrement, if_neg hbefore]
    split_ifs
    · exact Nat.zero_le _
    · rw [encodingCachedAt_cacheQuery_self hat]
      exact Set.ncard_insert_le _ _

theorem encodingMessageReserve_cacheQuery_le_increment
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {input : HashInput} {answer : HashOutput} {position : EncodingPosition}
    (hfresh : cache input = none) (hat : AtEncodingPosition secretKey.parameter input position) :
    encodingMessageReserve (cache.cacheQuery input answer) secretKey ≤
      encodingMessageReserve cache secretKey + encodingMessageIncrement cache secretKey position := by
  classical
  rw [encodingMessageReserve, encodingMessageReserve]
  calc
    _ ≤ ∑ candidate : EncodingPosition, (encodingMessageReserveAt cache secretKey candidate +
        if candidate = position then encodingMessageIncrement cache secretKey position else 0) := by
      apply Finset.sum_le_sum
      intro candidate _
      by_cases heq : candidate = position
      · rw [heq, if_pos rfl]
        exact encodingMessageReserveAt_cacheQuery_le_increment (answer := answer) hfresh hat
      · rw [if_neg heq, Nat.add_zero]
        exact encodingMessageReserveAt_cacheQuery_le_of_not_atPosition hfresh
          (fun hc => heq (atEncodingPosition_unique hc hat))
    _ = _ := by rw [Finset.sum_add_distrib, Fintype.sum_ite_eq']

theorem encodingMessageReserve_cacheQuery_le_of_not_atEncoding
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    (hfresh : cache input = none) (hnotAt : ∀ position : EncodingPosition, ¬ AtEncodingPosition secretKey.parameter input position) :
    encodingMessageReserve (cache.cacheQuery input answer) secretKey ≤ encodingMessageReserve cache secretKey := by
  classical
  rw [encodingMessageReserve, encodingMessageReserve]
  apply Finset.sum_le_sum
  intro position _
  exact encodingMessageReserveAt_cacheQuery_le_of_not_atPosition hfresh (hnotAt position)

theorem encodingMessageReserve_add_messageTargets_card_le_of_new_message
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    {position : EncodingPosition}
    (hfresh : cache input = none) (hnotAt : ∀ candidate : EncodingPosition, ¬ AtEncodingPosition secretKey.parameter input candidate)
    (hbefore : ¬ EncodingMessageSettledAt cache secretKey position)
    (hafter : EncodingMessageSettledAt (cache.cacheQuery input answer) secretKey position) :
    encodingMessageReserve (cache.cacheQuery input answer) secretKey + (encodingMessageTargets secretKey.parameter cache hfinite position).card ≤
      encodingMessageReserve cache secretKey := by
  classical
  have hselected : encodingMessageReserveAt (cache.cacheQuery input answer) secretKey position +
      (encodingMessageTargets secretKey.parameter cache hfinite position).card ≤ encodingMessageReserveAt cache secretKey position := by
    rw [encodingMessageReserveAt, if_pos hafter, Nat.zero_add, encodingMessageReserveAt, if_neg hbefore]
    exact encodingMessageTargets_card_le hfinite position
  rw [encodingMessageReserve, encodingMessageReserve,
    Fintype.sum_eq_add_sum_subtype_ne _ position, Fintype.sum_eq_add_sum_subtype_ne _ position]
  have hother : (∑ candidate : {candidate : EncodingPosition // candidate ≠ position},
      encodingMessageReserveAt (cache.cacheQuery input answer) secretKey candidate) ≤
      ∑ candidate : {candidate : EncodingPosition // candidate ≠ position}, encodingMessageReserveAt cache secretKey candidate := by
    apply Finset.sum_le_sum
    intro candidate _
    exact encodingMessageReserveAt_cacheQuery_le_of_not_atPosition hfresh (hnotAt candidate)
  omega

end SphincsSecurity.Concrete
