import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.EncodingLatent

/-!
# Two-stage encoding potential

Before an encoding position's honest message is settled, each cached input pays once for the
message-selection query and once for the later fresh target answer. After the message is settled,
only the second unit remains. Installing the canonical target releases that final unit.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

set_option maxRecDepth 100000

noncomputable def encodingStageContribution (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (position : EncodingPosition) : Nat :=
  open Classical in
    if HasEncodingTarget cache secretKey position then 0
    else if EncodingMessageSettledAt cache secretKey position then
      (encodingCachedAt secretKey.parameter cache position).ncard
    else 2 * (encodingCachedAt secretKey.parameter cache position).ncard

noncomputable def encodingStagePotential (cache : QueryCache HashSpec)
    (secretKey : SecretKey) : Nat :=
  ∑ position : EncodingPosition, encodingStageContribution cache secretKey position

@[simp] theorem encodingStagePotential_empty (secretKey : SecretKey) :
    encodingStagePotential ∅ secretKey = 0 := by
  rw [encodingStagePotential]
  apply Fintype.sum_eq_zero
  intro position
  rw [encodingStageContribution]
  split
  · rfl
  · split
    · have hempty : encodingCachedAt secretKey.parameter
          (∅ : QueryCache HashSpec) position = ∅ := by
        ext input
        simp [encodingCachedAt]
      rw [hempty, Set.ncard_empty]
    · have hempty : encodingCachedAt secretKey.parameter
          (∅ : QueryCache HashSpec) position = ∅ := by
        ext input
        simp [encodingCachedAt]
      rw [hempty, Set.ncard_empty, Nat.mul_zero]

theorem encodingStageContribution_cacheQuery_le_of_not_atPosition
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {input : HashInput} {answer : HashOutput} {position : EncodingPosition}
    (huncached : cache input = none)
    (hnotAt : ¬ AtEncodingPosition secretKey.parameter input position) :
    encodingStageContribution (cache.cacheQuery input answer) secretKey position ≤
      encodingStageContribution cache secretKey position := by
  classical
  have hle := le_cacheQuery (cache := cache) (input := input) (answer := answer) huncached
  have hcachedAt := encodingCachedAt_cacheQuery_of_not_atPosition
    (parameter := secretKey.parameter) (cache := cache) (answer := answer) hnotAt
  rw [encodingStageContribution, encodingStageContribution]
  by_cases htarget : HasEncodingTarget cache secretKey position
  · rw [if_pos htarget, if_pos (htarget.mono hle)]
  · rw [if_neg htarget]
    by_cases htarget' : HasEncodingTarget (cache.cacheQuery input answer) secretKey position
    · rw [if_pos htarget']
      exact Nat.zero_le _
    · rw [if_neg htarget']
      by_cases hsettled : EncodingMessageSettledAt cache secretKey position
      · rw [if_pos hsettled, if_pos (hsettled.mono hle), hcachedAt]
      · rw [if_neg hsettled]
        by_cases hsettled' : EncodingMessageSettledAt
            (cache.cacheQuery input answer) secretKey position
        · rw [if_pos hsettled', hcachedAt]
          omega
        · rw [if_neg hsettled', hcachedAt]

theorem encodingStageContribution_cacheQuery_le_of_atPosition
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {input : HashInput} {answer : HashOutput} {position : EncodingPosition}
    (huncached : cache input = none)
    (hposition : AtEncodingPosition secretKey.parameter input position) :
    encodingStageContribution (cache.cacheQuery input answer) secretKey position ≤
      encodingStageContribution cache secretKey position + 2 := by
  classical
  have hle := le_cacheQuery (cache := cache) (input := input) (answer := answer) huncached
  have hcard : (encodingCachedAt secretKey.parameter
      (cache.cacheQuery input answer) position).ncard ≤
        (encodingCachedAt secretKey.parameter cache position).ncard + 1 := by
    rw [encodingCachedAt_cacheQuery_self hposition]
    exact Set.ncard_insert_le _ _
  rw [encodingStageContribution, encodingStageContribution]
  by_cases htarget : HasEncodingTarget cache secretKey position
  · rw [if_pos htarget, if_pos (htarget.mono hle)]
    omega
  · rw [if_neg htarget]
    by_cases htarget' : HasEncodingTarget (cache.cacheQuery input answer) secretKey position
    · rw [if_pos htarget']
      exact Nat.zero_le _
    · rw [if_neg htarget']
      by_cases hsettled : EncodingMessageSettledAt cache secretKey position
      · rw [if_pos hsettled, if_pos (hsettled.mono hle)]
        omega
      · rw [if_neg hsettled]
        by_cases hsettled' : EncodingMessageSettledAt
            (cache.cacheQuery input answer) secretKey position
        · rw [if_pos hsettled']
          omega
        · rw [if_neg hsettled']
          omega

theorem encodingStagePotential_cacheQuery_le
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {input : HashInput} {answer : HashOutput} (huncached : cache input = none) :
    encodingStagePotential (cache.cacheQuery input answer) secretKey ≤
      encodingStagePotential cache secretKey + 2 := by
  classical
  by_cases hat : ∃ position,
      AtEncodingPosition secretKey.parameter input position
  · obtain ⟨queriedPosition, hqueried⟩ := hat
    rw [encodingStagePotential, encodingStagePotential]
    calc
      ∑ position : EncodingPosition,
          encodingStageContribution (cache.cacheQuery input answer) secretKey position ≤
        ∑ position : EncodingPosition,
          (encodingStageContribution cache secretKey position +
            if position = queriedPosition then 2 else 0) := by
          apply Finset.sum_le_sum
          intro position _
          by_cases heq : position = queriedPosition
          · rw [if_pos heq]
            simpa only [heq] using
              encodingStageContribution_cacheQuery_le_of_atPosition huncached hqueried
          · rw [if_neg heq, Nat.add_zero]
            apply encodingStageContribution_cacheQuery_le_of_not_atPosition huncached
            intro hposition
            exact heq (atEncodingPosition_unique hposition hqueried)
      _ = (∑ position : EncodingPosition,
          encodingStageContribution cache secretKey position) + 2 := by
        rw [Finset.sum_add_distrib, Fintype.sum_ite_eq']
  · rw [encodingStagePotential, encodingStagePotential]
    calc
      ∑ position : EncodingPosition,
          encodingStageContribution (cache.cacheQuery input answer) secretKey position ≤
        ∑ position : EncodingPosition,
          encodingStageContribution cache secretKey position := by
            apply Finset.sum_le_sum
            intro position _
            exact encodingStageContribution_cacheQuery_le_of_not_atPosition huncached
              (fun hposition => hat ⟨position, hposition⟩)
      _ ≤ _ := Nat.le_add_right _ 2

theorem encodingStagePotential_cacheQuery_le_of_not_atEncoding
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {input : HashInput} {answer : HashOutput} (huncached : cache input = none)
    (hnotAt : ∀ position : EncodingPosition,
      ¬ AtEncodingPosition secretKey.parameter input position) :
    encodingStagePotential (cache.cacheQuery input answer) secretKey ≤
      encodingStagePotential cache secretKey := by
  classical
  rw [encodingStagePotential, encodingStagePotential]
  apply Finset.sum_le_sum
  intro position _
  exact encodingStageContribution_cacheQuery_le_of_not_atPosition huncached
    (hnotAt position)

theorem HasEncodingTarget.messageSettled {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {position : EncodingPosition}
    (htarget : HasEncodingTarget cache secretKey position) :
    EncodingMessageSettledAt cache secretKey position := by
  obtain ⟨payload, index, counter, htree, hleaf, hsettled, hrest⟩ := htarget
  exact ⟨index, htree, hleaf, hsettled⟩

theorem encodingStagePotential_add_messageTargets_card_le_of_new_message
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    {position : EncodingPosition}
    (huncached : cache input = none)
    (hnotAt : ∀ candidate : EncodingPosition,
      ¬ AtEncodingPosition secretKey.parameter input candidate)
    (hunsettled : ¬ EncodingMessageSettledAt cache secretKey position)
    (hsettled : EncodingMessageSettledAt
      (cache.cacheQuery input answer) secretKey position) :
    encodingStagePotential (cache.cacheQuery input answer) secretKey +
        (encodingMessageTargets secretKey.parameter cache hfinite position).card ≤
      encodingStagePotential cache secretKey := by
  classical
  have htarget : ¬ HasEncodingTarget cache secretKey position :=
    fun htarget => hunsettled htarget.messageSettled
  have hcachedAt := encodingCachedAt_cacheQuery_of_not_atPosition
    (parameter := secretKey.parameter) (cache := cache) (answer := answer)
      (hnotAt position)
  have hselected : encodingStageContribution (cache.cacheQuery input answer)
        secretKey position +
      (encodingMessageTargets secretKey.parameter cache hfinite position).card ≤
        encodingStageContribution cache secretKey position := by
    simp only [encodingStageContribution, htarget, hunsettled, if_false]
    by_cases htarget' : HasEncodingTarget
        (cache.cacheQuery input answer) secretKey position
    · rw [if_pos htarget', zero_add]
      have hcard := encodingMessageTargets_card_le
        (parameter := secretKey.parameter) hfinite position
      omega
    · rw [if_neg htarget', if_pos hsettled, hcachedAt]
      have hcard := encodingMessageTargets_card_le
        (parameter := secretKey.parameter) hfinite position
      omega
  rw [encodingStagePotential, encodingStagePotential]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ position,
    Fintype.sum_eq_add_sum_subtype_ne _ position]
  have hother : (∑ candidate : {candidate : EncodingPosition // candidate ≠ position},
      encodingStageContribution (cache.cacheQuery input answer) secretKey candidate) ≤
      ∑ candidate : {candidate : EncodingPosition // candidate ≠ position},
        encodingStageContribution cache secretKey candidate := by
    apply Finset.sum_le_sum
    intro candidate _
    exact encodingStageContribution_cacheQuery_le_of_not_atPosition huncached
      (hnotAt candidate)
  calc
    (encodingStageContribution (cache.cacheQuery input answer) secretKey position +
        ∑ candidate : {candidate : EncodingPosition // candidate ≠ position},
          encodingStageContribution (cache.cacheQuery input answer) secretKey candidate) +
        (encodingMessageTargets secretKey.parameter cache hfinite position).card =
      (encodingStageContribution (cache.cacheQuery input answer) secretKey position +
        (encodingMessageTargets secretKey.parameter cache hfinite position).card) +
        ∑ candidate : {candidate : EncodingPosition // candidate ≠ position},
          encodingStageContribution (cache.cacheQuery input answer) secretKey candidate := by
      omega
    _ ≤ encodingStageContribution cache secretKey position +
        ∑ candidate : {candidate : EncodingPosition // candidate ≠ position},
          encodingStageContribution cache secretKey candidate :=
      Nat.add_le_add hselected hother

noncomputable def encodingStructuralPotential (cache : QueryCache HashSpec)
    (secretKey : SecretKey) : Nat :=
  potential secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache +
    encodingStagePotential cache secretKey

@[simp] theorem encodingStructuralPotential_empty (secretKey : SecretKey) :
    encodingStructuralPotential ∅ secretKey = 0 := by
  rw [encodingStructuralPotential, potential_empty, encodingStagePotential_empty,
    Nat.zero_add]

end SphincsSecurity.Concrete
