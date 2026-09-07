import SphincsSecurity.Proof.EncodingCollisionCount
import SphincsSecurity.Proof.EncodingMessageConservation

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition instFintypeEncodingPosition validCacheEntries digestCollisionCount
set_option backward.isDefEq.respectTransparency false

noncomputable def encodingCollisionReserveAt (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (key : SecretKey) (position : EncodingPosition) : Nat :=
  if EncodingMessageSettledAt cache key position then 0
  else (encodingCollisionPairs key.parameter cache hfinite position).card

noncomputable def encodingCollisionReserve (cache : QueryCache HashSpec) (hfinite : Finite cache) (key : SecretKey) : Nat :=
  ∑ position : EncodingPosition, encodingCollisionReserveAt cache hfinite key position

theorem encodingCollisionReserve_le_validCache_count (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (key : SecretKey) :
    encodingCollisionReserve cache hfinite key ≤ digestCollisionCount (validCacheEntries cache) := by
  apply le_trans ?_ (encodingCollisionPairs_sum_card_le_validCache_count key.parameter cache hfinite)
  apply Finset.sum_le_sum
  intro position _
  unfold encodingCollisionReserveAt
  split_ifs <;> omega

@[simp] theorem encodingCollisionReserve_empty (key : SecretKey) :
    encodingCollisionReserve ∅ finite_empty key = 0 := by
  apply Nat.eq_zero_of_le_zero
  have h := encodingCollisionReserve_le_validCache_count ∅ finite_empty key
  simpa only [validCacheEntries_empty, digestCollisionCount, Finset.sum_empty] using h

theorem encodingCollisionReserveAt_cacheQuery_le_of_not_atPosition
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {key : SecretKey}
    {input : HashInput} {answer : HashOutput} {position : EncodingPosition}
    (hfresh : cache input = none) (hnotAt : ¬ AtEncodingPosition key.parameter input position) :
    encodingCollisionReserveAt (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) key position ≤
      encodingCollisionReserveAt cache hfinite key position := by
  have hle := le_cacheQuery (answer := answer) hfresh
  have hpairs : encodingCollisionPairs key.parameter (cache.cacheQuery input answer)
      (finite_cacheQuery hfinite input answer) position = encodingCollisionPairs key.parameter cache hfinite position := by
    simp only [encodingCollisionPairs, encodingSelectionCandidates_cacheQuery_of_not_atPosition hfinite hnotAt]
  by_cases hs : EncodingMessageSettledAt cache key position
  · simp only [encodingCollisionReserveAt, if_pos hs, if_pos (hs.mono hle), le_refl]
  · simp only [encodingCollisionReserveAt, if_neg hs]
    split_ifs
    · exact Nat.zero_le _
    · rw [hpairs]

theorem encodingCollisionReserve_cacheQuery_le_of_not_atEncoding
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {key : SecretKey}
    {input : HashInput} {answer : HashOutput} (hfresh : cache input = none)
    (hnotAt : ∀ position, ¬ AtEncodingPosition key.parameter input position) :
    encodingCollisionReserve (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) key ≤
      encodingCollisionReserve cache hfinite key := by
  apply Finset.sum_le_sum
  intro position _
  exact encodingCollisionReserveAt_cacheQuery_le_of_not_atPosition hfinite hfresh (hnotAt position)

theorem encodingCollisionReserve_add_targets_le_of_new_message
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {key : SecretKey}
    {input : HashInput} {answer : HashOutput} {position : EncodingPosition}
    (hfresh : cache input = none) (hnotAt : ∀ candidate, ¬ AtEncodingPosition key.parameter input candidate)
    (hbefore : ¬ EncodingMessageSettledAt cache key position)
    (hafter : EncodingMessageSettledAt (cache.cacheQuery input answer) key position) :
    encodingCollisionReserve (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) key +
      (encodingCollisionMessageTargets key.parameter cache hfinite position).card ≤
      encodingCollisionReserve cache hfinite key := by
  have hselected : encodingCollisionReserveAt (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) key position +
      (encodingCollisionMessageTargets key.parameter cache hfinite position).card ≤
      encodingCollisionReserveAt cache hfinite key position := by
    rw [encodingCollisionReserveAt, if_pos hafter, Nat.zero_add, encodingCollisionReserveAt, if_neg hbefore]
    exact encodingCollisionMessageTargets_card_le_pairs key.parameter cache hfinite position
  rw [encodingCollisionReserve, encodingCollisionReserve,
    Fintype.sum_eq_add_sum_subtype_ne _ position, Fintype.sum_eq_add_sum_subtype_ne _ position]
  have hother : (∑ candidate : {candidate : EncodingPosition // candidate ≠ position},
      encodingCollisionReserveAt (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) key candidate) ≤
      ∑ candidate : {candidate : EncodingPosition // candidate ≠ position}, encodingCollisionReserveAt cache hfinite key candidate := by
    apply Finset.sum_le_sum
    intro candidate _
    exact encodingCollisionReserveAt_cacheQuery_le_of_not_atPosition hfinite hfresh (hnotAt candidate)
  omega

theorem encodingCollisionReserveAt_cacheQuery_le_add_matches
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {key : SecretKey}
    {input : HashInput} {answer : HashOutput} {position : EncodingPosition}
    (hfresh : cache input = none) (hat : AtEncodingPosition key.parameter input position) :
    encodingCollisionReserveAt (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) key position ≤
      encodingCollisionReserveAt cache hfinite key position +
        2 * ∑ entry ∈ validCacheEntries cache, if entry.2 = truncateHash answer then 1 else 0 := by
  have hsettled : EncodingMessageSettledAt (cache.cacheQuery input answer) key position ↔
      EncodingMessageSettledAt cache key position :=
    ⟨fun h => h.of_cacheQuery_of_atEncoding hfresh hat, fun h => h.mono (le_cacheQuery hfresh)⟩
  simp only [encodingCollisionReserveAt, hsettled]
  by_cases hs : EncodingMessageSettledAt cache key position
  · simp only [if_pos hs, Nat.zero_add, Nat.zero_le]
  · simp only [if_neg hs, encodingCollisionPairs_card_eq,
      encodingSelectionCandidates_cacheQuery_self hfinite hfresh hat]
    have hf : ∀ entry ∈ encodingSelectionCandidates key.parameter cache hfinite position, entry.1 ≠ input :=
      fun entry he => validCacheEntries_fresh hfinite hfresh entry
        (encodingSelectionCandidates_subset_validCacheEntries key.parameter cache hfinite position he)
    apply (digestCollisionCount_insertValid_le _ input answer hf).trans
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul_left
    exact Finset.sum_le_sum_of_subset (encodingSelectionCandidates_subset_validCacheEntries key.parameter cache hfinite position)

theorem encodingCollisionReserve_cacheQuery_le_add_matches
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {key : SecretKey}
    {input : HashInput} {answer : HashOutput} {position : EncodingPosition}
    (hfresh : cache input = none) (hat : AtEncodingPosition key.parameter input position) :
    encodingCollisionReserve (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) key ≤
      encodingCollisionReserve cache hfinite key +
        2 * ∑ entry ∈ validCacheEntries cache, if entry.2 = truncateHash answer then 1 else 0 := by
  rw [encodingCollisionReserve, encodingCollisionReserve]
  calc
    _ ≤ ∑ candidate : EncodingPosition, (encodingCollisionReserveAt cache hfinite key candidate +
        if candidate = position then 2 * ∑ entry ∈ validCacheEntries cache, if entry.2 = truncateHash answer then 1 else 0 else 0) := by
      apply Finset.sum_le_sum
      intro candidate _
      by_cases heq : candidate = position
      · subst candidate
        rw [if_pos rfl]
        exact encodingCollisionReserveAt_cacheQuery_le_add_matches hfinite hfresh hat
      · rw [if_neg heq, Nat.add_zero]
        exact encodingCollisionReserveAt_cacheQuery_le_of_not_atPosition hfinite hfresh
          (fun hc => heq (atEncodingPosition_unique hc hat))
    _ = _ := by rw [Finset.sum_add_distrib, Fintype.sum_ite_eq']

theorem uniform_encodingCollisionReserve_cacheQuery_le
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {key : SecretKey}
    {input : HashInput} {position : EncodingPosition}
    (hfresh : cache input = none) (hat : AtEncodingPosition key.parameter input position) :
    (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (encodingCollisionReserve (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) key : ENNReal)) ≤
      (encodingCollisionReserve cache hfinite key : ENNReal) +
        2 * (validCacheEntries cache).card * (Fintype.card Digest : ENNReal)⁻¹ := by
  calc
    _ ≤ ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        ((encodingCollisionReserve cache hfinite key : ENNReal) +
          2 * ((∑ entry ∈ validCacheEntries cache, if entry.2 = truncateHash answer then 1 else 0 : Nat) : ENNReal)) := by
      apply ENNReal.tsum_le_tsum
      intro answer
      apply mul_le_mul' le_rfl
      exact_mod_cast encodingCollisionReserve_cacheQuery_le_add_matches (answer := answer) hfinite hfresh hat
    _ = _ := by
      simp_rw [mul_add, mul_left_comm (Pr[= _ | _]) (2 : ENNReal)]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul,
        ENNReal.tsum_mul_left, uniform_digestMatchCount, mul_assoc]

end SphincsSecurity.Concrete
