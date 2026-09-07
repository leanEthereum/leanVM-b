import SphincsSecurity.Proof.EncodingProbability

namespace SphincsSecurity

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

noncomputable def digestCollisionCount (entries : Finset (HashInput × Digest)) : Nat :=
  ∑ first ∈ entries, ∑ second ∈ entries,
    if first.1 ≠ second.1 ∧ first.2 = second.2 then 1 else 0

theorem digestCollisionCount_insert (entries : Finset (HashInput × Digest)) (input : HashInput) (digest : Digest)
    (hfresh : ∀ entry ∈ entries, entry.1 ≠ input) :
    digestCollisionCount (insert (input, digest) entries) = digestCollisionCount entries +
      2 * ∑ entry ∈ entries, if entry.2 = digest then 1 else 0 := by
  have hnot : (input, digest) ∉ entries := fun h => hfresh _ h rfl
  unfold digestCollisionCount
  rw [Finset.sum_insert hnot]
  simp_rw [Finset.sum_insert hnot]
  simp only [ne_eq, not_true_eq_false, false_and, if_false, zero_add]
  have hleft (entry) (hentry : entry ∈ entries) :
      (if input ≠ entry.1 ∧ digest = entry.2 then 1 else 0) =
        (if entry.2 = digest then 1 else 0 : Nat) := by
    by_cases heq : entry.2 = digest
    · rw [if_pos ⟨Ne.symm (hfresh entry hentry), heq.symm⟩, if_pos heq]
    · rw [if_neg (fun h => heq h.2.symm), if_neg heq]
  have hright (entry) (hentry : entry ∈ entries) :
      (if entry.1 ≠ input ∧ entry.2 = digest then 1 else 0) =
        (if entry.2 = digest then 1 else 0 : Nat) := by
    by_cases heq : entry.2 = digest
    · rw [if_pos ⟨hfresh entry hentry, heq⟩, if_pos heq]
    · rw [if_neg (fun h => heq h.2), if_neg heq]
  rw [Finset.sum_congr rfl hleft, Finset.sum_add_distrib, Finset.sum_congr rfl hright]
  omega

noncomputable def insertValidDigest (entries : Finset (HashInput × Digest)) (input : HashInput) (output : HashOutput) :
    Finset (HashInput × Digest) :=
  if TargetSum.ValidDigest (truncateHash output) then insert (input, truncateHash output) entries else entries

theorem digestCollisionCount_insertValid_le (entries : Finset (HashInput × Digest)) (input : HashInput) (output : HashOutput)
    (hfresh : ∀ entry ∈ entries, entry.1 ≠ input) :
    digestCollisionCount (insertValidDigest entries input output) ≤ digestCollisionCount entries +
      2 * ∑ entry ∈ entries, if entry.2 = truncateHash output then 1 else 0 := by
  unfold insertValidDigest
  split_ifs
  · exact le_of_eq (digestCollisionCount_insert entries input _ hfresh)
  · exact Nat.le_add_right _ _

theorem insertValidDigest_card (entries : Finset (HashInput × Digest)) (input : HashInput) (output : HashOutput)
    (hfresh : ∀ entry ∈ entries, entry.1 ≠ input) :
    (insertValidDigest entries input output).card = entries.card +
      if TargetSum.ValidDigest (truncateHash output) then 1 else 0 := by
  have hnot : (input, truncateHash output) ∉ entries := fun h => hfresh _ h rfl
  unfold insertValidDigest
  split_ifs <;> simp only [Finset.card_insert_of_notMem hnot, Nat.add_zero]

theorem uniform_digestMatchCount (entries : Finset (HashInput × Digest)) :
    (∑' output : HashOutput, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      ((∑ entry ∈ entries, if entry.2 = truncateHash output then 1 else 0 : Nat) : ENNReal)) =
      (entries.card : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ := by
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  have hone (entry : HashInput × Digest) :
      (∑' output : HashOutput, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (if entry.2 = truncateHash output then 1 else 0 : ENNReal)) = (Fintype.card Digest : ENNReal)⁻¹ := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [← probEvent_eq_tsum_ite]
    simpa only [eq_comm] using probEvent_uniform_truncateHash_eq entry.2
  simp_rw [hone]
  simp

theorem uniform_digestCollisionCount_insertValid_le (entries : Finset (HashInput × Digest)) (input : HashInput)
    (hfresh : ∀ entry ∈ entries, entry.1 ≠ input) :
    (∑' output : HashOutput, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (digestCollisionCount (insertValidDigest entries input output) : ENNReal)) ≤
      (digestCollisionCount entries : ENNReal) + 2 * (entries.card : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ := by
  calc
    _ ≤ ∑' output : HashOutput, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
        ((digestCollisionCount entries : ENNReal) + 2 *
          ((∑ entry ∈ entries, if entry.2 = truncateHash output then 1 else 0 : Nat) : ENNReal)) := by
      apply ENNReal.tsum_le_tsum
      intro output
      apply mul_le_mul' le_rfl
      exact_mod_cast digestCollisionCount_insertValid_le entries input output hfresh
    _ = _ := by
      simp_rw [mul_add, mul_left_comm (Pr[= _ | _]) (2 : ENNReal)]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul,
        ENNReal.tsum_mul_left, uniform_digestMatchCount]
      rw [mul_assoc]

theorem uniform_insertValidDigest_card (entries : Finset (HashInput × Digest)) (input : HashInput)
    (hfresh : ∀ entry ∈ entries, entry.1 ≠ input) :
    (∑' output : HashOutput, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      ((insertValidDigest entries input output).card : ENNReal)) = (entries.card : ENNReal) +
      (TargetSum.validDigests.card : ENNReal) / (Fintype.card Digest : ENNReal) := by
  simp_rw [insertValidDigest_card entries input _ hfresh]
  simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_add, mul_ite, mul_one, mul_zero]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul,
    ← probEvent_eq_tsum_ite, probEvent_uniform_encoding_valid]

end SphincsSecurity
