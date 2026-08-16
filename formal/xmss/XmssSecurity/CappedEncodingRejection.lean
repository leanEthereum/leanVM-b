import XmssSecurity.EncodingOracleSimulation

open OracleComp ENNReal

namespace XmssSecurity

set_option maxRecDepth 100000

namespace TargetSum

def ValidDigest (digest : Digest) : Prop :=
  ∃ encoding, decodeDigest digest = some encoding

noncomputable instance : DecidablePred ValidDigest :=
  Classical.decPred _

noncomputable def validDigests : Finset Digest :=
  Finset.univ.filter ValidDigest

def exampleValidEncoding : Encoding := fun chain =>
  if chain.val < 27 then ⟨7, by decide⟩
  else if chain.val = 27 then ⟨6, by decide⟩
  else ⟨0, by decide⟩

theorem exampleValidEncoding_valid : Valid exampleValidEncoding := by
  unfold Valid sum
  rw [Finset.sum_fin_eq_sum_range]
  norm_num [exampleValidEncoding, targetSum, numChains, chainLength,
    Finset.sum_range_succ]

theorem card_digest_eq_card_encodingView :
    Fintype.card Digest = Fintype.card EncodingView := by
  simp [digestBits, EncodingView, numChains, chainLength, winternitzBits]

theorem digestView_surjective : Function.Surjective digestView :=
  ((Fintype.bijective_iff_injective_and_card digestView).2
    ⟨digestView_injective, card_digest_eq_card_encodingView⟩).2

theorem validDigests_nonempty : validDigests.Nonempty := by
  obtain ⟨digest, hdigest⟩ := digestView_surjective (exampleValidEncoding, 0)
  refine ⟨digest, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  refine ⟨exampleValidEncoding, decodeDigest_eq_some_iff.mpr ?_⟩
  exact ⟨hdigest, exampleValidEncoding_valid⟩

theorem validDigests_card_pos : 0 < validDigests.card :=
  Finset.card_pos.mpr validDigests_nonempty

theorem mem_validDigests_iff (digest : Digest) :
    digest ∈ validDigests ↔ ValidDigest digest := by
  simp [validDigests]

theorem uniformHashOutput_validDigest_probability :
    Pr[fun output : HashOutput => ValidDigest (truncateHash output) |
      $ᵗ HashOutput] =
      (validDigests.card : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  calc
    Pr[fun output : HashOutput => ValidDigest (truncateHash output) |
        $ᵗ HashOutput] =
      Pr[ValidDigest | truncateHash <$> ($ᵗ HashOutput)] := by
        rw [probEvent_map]
        congr 1
    _ = Pr[ValidDigest | $ᵗ Digest] := by
      exact probEvent_congr' (fun _ _ => Iff.rfl)
        Rom.evalDist_truncate_uniformHashOutput
    _ = (validDigests.card : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
      rw [probEvent_uniformSample]
      rfl

noncomputable def boundedValidDigest : Nat → ProbComp (Option Digest)
  | 0 => pure none
  | attempts + 1 => do
      let digest ← $ᵗ Digest
      if ValidDigest digest then pure (some digest)
      else boundedValidDigest attempts

theorem boundedValidDigest_some_support_valid
    (attempts : Nat) (digest : Digest)
    (hmem : some digest ∈ support (boundedValidDigest attempts)) :
    ValidDigest digest := by
  induction attempts with
  | zero => simp [boundedValidDigest] at hmem
  | succ attempts ih =>
      rw [boundedValidDigest, mem_support_bind_iff] at hmem
      obtain ⟨sampled, _hsampled, hrest⟩ := hmem
      by_cases hvalid : ValidDigest sampled
      · simp only [hvalid, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hrest
        have heq : digest = sampled := Option.some.inj hrest
        rw [heq]
        exact hvalid
      · simp only [hvalid, ↓reduceIte] at hrest
        exact ih hrest

theorem boundedValidDigest_hits_finset_le
    (attempts : Nat) (targets : Finset Digest) :
    Pr[fun result : Option Digest => ∃ digest ∈ targets, result = some digest |
      boundedValidDigest attempts] ≤
      (attempts : ℝ≥0∞) * (targets.card : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  induction attempts with
  | zero => simp [boundedValidDigest]
  | succ attempts ih =>
      rw [boundedValidDigest]
      refine (probEvent_bind_le_probEvent_add
        (p := fun digest : Digest => digest ∈ targets)
        (ε := (attempts : ℝ≥0∞) * (targets.card : ℝ≥0∞) /
          (Fintype.card Digest : ℝ≥0∞)) ?_).trans ?_
      · intro digest _hdigest hmiss
        by_cases hvalid : ValidDigest digest
        · refine le_of_eq_of_le (probEvent_eq_zero ?_) zero_le
          intro result hresult hevent
          simp only [hvalid, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hresult
          obtain ⟨target, htarget, heq⟩ := hevent
          have hreturned : result = some digest := hresult
          have htargetEq : target = digest := Option.some.inj (heq.symm.trans hreturned)
          exact hmiss (htargetEq ▸ htarget)
        · simpa only [hvalid, ↓reduceIte] using ih
      · rw [probEvent_uniformSample]
        rw [show Finset.univ.filter (fun digest : Digest => digest ∈ targets) =
          targets by ext digest; simp]
        rw [Nat.cast_succ]
        ring_nf
        simp only [div_eq_mul_inv]
        rw [add_mul]
        rw [add_comm]

theorem boundedValidDigest_some_probability_eq
    (attempts : Nat) (left right : Digest)
    (hleft : ValidDigest left) (hright : ValidDigest right) :
    Pr[= some left | boundedValidDigest attempts] =
      Pr[= some right | boundedValidDigest attempts] := by
  induction attempts with
  | zero => simp [boundedValidDigest]
  | succ attempts ih =>
      rw [boundedValidDigest, probOutput_bind_eq_sum_fintype,
        probOutput_bind_eq_sum_fintype]
      apply Finset.sum_bij (fun digest _ => if digest = left then right
        else if digest = right then left else digest)
      · intro digest hdigest
        simp only [Finset.mem_univ]
      · intro first _ second _ heq
        by_cases hfirstLeft : first = left <;>
          by_cases hfirstRight : first = right <;>
          by_cases hsecondLeft : second = left <;>
          by_cases hsecondRight : second = right <;>
          simp_all
      · intro digest _
        refine ⟨if digest = left then right else if digest = right then left else digest,
          Finset.mem_univ _, ?_⟩
        by_cases hdleft : digest = left <;> by_cases hdright : digest = right <;>
          simp_all
      · intro digest hdigest
        by_cases hdleft : digest = left
        · subst digest
          simp [hleft, hright]
        · by_cases hdright : digest = right
          · subst digest
            simp [hleft, hright, hdleft, Ne.symm hdleft]
          · by_cases hvalid : ValidDigest digest
            · simp [hvalid, hdleft, hdright, Ne.symm hdleft, Ne.symm hdright]
            · simp [hvalid, hdleft, hdright, ih]

theorem boundedValidDigest_some_probability_le_inv_card
    (attempts : Nat) (target : Digest) (hvalid : ValidDigest target) :
    Pr[= some target | boundedValidDigest attempts] ≤
      (validDigests.card : ℝ≥0∞)⁻¹ := by
  have hsum :
      (validDigests.card : ℝ≥0∞) *
          Pr[= some target | boundedValidDigest attempts] ≤ 1 := by
    calc
      (validDigests.card : ℝ≥0∞) *
          Pr[= some target | boundedValidDigest attempts] =
        ∑ digest ∈ validDigests,
          Pr[= some target | boundedValidDigest attempts] := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = ∑ digest ∈ validDigests,
          Pr[= some digest | boundedValidDigest attempts] := by
            apply Finset.sum_congr rfl
            intro digest hdigest
            exact boundedValidDigest_some_probability_eq attempts target digest hvalid
              ((mem_validDigests_iff digest).mp hdigest)
      _ ≤ ∑ digest : Digest,
          Pr[= some digest | boundedValidDigest attempts] := by
            exact Finset.sum_le_sum_of_subset (Finset.subset_univ validDigests)
      _ ≤ 1 := sum_probOutput_some_le_one
        (mx := boundedValidDigest attempts)
  apply ENNReal.le_inv_iff_mul_le.mpr
  rw [mul_comm]
  exact hsum

theorem boundedValidDigest_hits_finset_le_inv_valid_card
    (attempts : Nat) (targets : Finset Digest) :
    Pr[fun result : Option Digest => ∃ digest ∈ targets, result = some digest |
      boundedValidDigest attempts] ≤
      (targets.card : ℝ≥0∞) * (validDigests.card : ℝ≥0∞)⁻¹ := by
  calc
    Pr[fun result : Option Digest => ∃ digest ∈ targets, result = some digest |
        boundedValidDigest attempts] ≤
      ∑ digest ∈ targets,
        Pr[= some digest | boundedValidDigest attempts] :=
          by
            simpa only [probEvent_eq_eq_probOutput] using
              probEvent_exists_finset_le_sum targets (boundedValidDigest attempts)
                (fun digest result => result = some digest)
    _ ≤ ∑ _digest ∈ targets,
        (validDigests.card : ℝ≥0∞)⁻¹ := by
          apply Finset.sum_le_sum
          intro digest hdigest
          by_cases hvalid : ValidDigest digest
          · exact boundedValidDigest_some_probability_le_inv_card
              attempts digest hvalid
          · have hzero : Pr[= some digest | boundedValidDigest attempts] = 0 := by
              apply probOutput_eq_zero
              intro hmem
              exact hvalid (boundedValidDigest_some_support_valid attempts digest hmem)
            rw [hzero]
            exact zero_le
    _ = (targets.card : ℝ≥0∞) *
        (validDigests.card : ℝ≥0∞)⁻¹ := by
          rw [Finset.sum_const, nsmul_eq_mul]

noncomputable def queryThenBoundedValidDigestCollision
    (attempts : Nat) : ProbComp Bool := do
  let queried ← $ᵗ Digest
  let signed ← boundedValidDigest attempts
  return signed = some queried

noncomputable def boundedValidDigestThenQueryCollision
    (attempts : Nat) : ProbComp Bool := do
  let signed ← boundedValidDigest attempts
  let queried ← $ᵗ Digest
  return signed = some queried

theorem queryThenBoundedValidDigestCollision_probability_le
    (attempts : Nat) :
    Pr[= true | queryThenBoundedValidDigestCollision attempts] ≤
      (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  unfold queryThenBoundedValidDigestCollision
  rw [probOutput_bind_eq_tsum]
  simp_rw [probOutput_uniformSample]
  have hinner : ∀ digest : Digest,
      Pr[= true | do
        let signed ← boundedValidDigest attempts
        pure (decide (signed = some digest))] =
      Pr[= some digest | boundedValidDigest attempts] := by
    intro digest
    rw [← probEvent_true_eq_probOutput, probEvent_bind_eq_tsum]
    simp
  have hsum :
      ∑' digest : Digest,
          Pr[= some digest | boundedValidDigest attempts] ≤ 1 := by
    rw [tsum_fintype]
    exact sum_probOutput_some_le_one (mx := boundedValidDigest attempts)
  simp_rw [hinner]
  rw [ENNReal.tsum_mul_left]
  exact (mul_le_mul' le_rfl hsum).trans_eq (mul_one _)

theorem boundedValidDigestThenQueryCollision_probability_le
    (attempts : Nat) :
    Pr[= true | boundedValidDigestThenQueryCollision attempts] ≤
      (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  unfold boundedValidDigestThenQueryCollision
  rw [← probEvent_true_eq_probOutput]
  refine probEvent_bind_le_of_forall_le fun signed _hsigned => ?_
  cases signed with
  | none => simp
  | some digest =>
      change Pr[(· = true) |
        (fun queried : Digest => decide (some digest = some queried)) <$>
          ($ᵗ Digest)] ≤
        (Fintype.card Digest : ℝ≥0∞)⁻¹
      rw [probEvent_map]
      calc
        Pr[((fun x => x = true) ∘
            fun queried : Digest => decide (some digest = some queried)) |
            $ᵗ Digest] =
          Pr[(digest = ·) | $ᵗ Digest] := by
            apply probEvent_ext
            intro queried _
            simp
        _ = (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
          rw [probEvent_eq_eq_probOutput', probOutput_uniformSample]
        _ ≤ (Fintype.card Digest : ℝ≥0∞)⁻¹ := le_refl _

end TargetSum

end XmssSecurity
