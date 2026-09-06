import SphincsSecurity.Proof.FewTimeOriginPadding

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

abbrev UsedFewTimePattern (signatures distinct : Nat) :=
  {pattern : FewTimePattern signatures distinct // Function.Surjective pattern.assignment}

theorem FewTimeCover.pattern_assignment_surjective {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {signingLog : QueryLog SigningSpec}
    {index : Index} {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves) :
    Function.Surjective cover.pattern.assignment := by
  intro selected
  obtain ⟨entry, _, hentry⟩ := Finset.mem_image.mp selected.2
  refine ⟨cover.representativeTree entry, ?_⟩
  apply Subtype.ext
  change cover.logIndex ⟨(cover.select (cover.representativeTree entry)).entry.flat, _⟩ = selected.1
  rw [← hentry]
  congr 1
  exact Subtype.ext (cover.representativeTree_spec entry)

theorem FewTimePattern.pad_assignment_surjective {small large distinct : Nat}
    (pattern : FewTimePattern small distinct) (hle : small ≤ large)
    (hsurjective : Function.Surjective pattern.assignment) :
    Function.Surjective (pattern.pad hle).assignment := by
  intro selected
  obtain ⟨position, hposition, hselected⟩ := Finset.mem_map.mp selected.2
  obtain ⟨tree, htree⟩ := hsurjective ⟨position, hposition⟩
  refine ⟨tree, Subtype.ext ?_⟩
  change finCastLEEmbedding hle (pattern.assignment tree).1 = selected.1
  rw [htree]
  exact hselected

noncomputable def surjectiveAssignmentEquiv {α β γ : Type} (e : β ≃ γ) :
    {f : α → β // Function.Surjective f} ≃ {f : α → γ // Function.Surjective f} where
  toFun f := ⟨e ∘ f.1, e.surjective.comp f.2⟩
  invFun f := ⟨e.symm ∘ f.1, e.symm.surjective.comp f.2⟩
  left_inv f := by apply Subtype.ext; funext x; simp
  right_inv f := by apply Subtype.ext; funext x; simp

noncomputable def usedFewTimePatternEquiv (signatures distinct : Nat) :
    UsedFewTimePattern signatures distinct ≃
      Σ selected : {s : Finset (Fin signatures) // s.card = distinct},
        {assignment : FtsTree → selected.1 // Function.Surjective assignment} where
  toFun pattern := ⟨⟨pattern.1.selected, pattern.1.card_selected⟩, ⟨pattern.1.assignment, pattern.2⟩⟩
  invFun pattern := ⟨⟨pattern.1.1, pattern.1.2, pattern.2.1⟩, pattern.2.2⟩
  left_inv pattern := by rcases pattern with ⟨⟨selected, hcard, assignment⟩, hsurjective⟩; rfl
  right_inv pattern := by rcases pattern with ⟨⟨selected, hcard⟩, ⟨assignment, hsurjective⟩⟩; rfl

noncomputable instance (signatures distinct : Nat) : Fintype (UsedFewTimePattern signatures distinct) :=
  by classical exact Subtype.fintype _

theorem usedFewTimePattern_card (signatures distinct : Nat) :
    Fintype.card (UsedFewTimePattern signatures distinct) =
      Nat.choose signatures distinct * Fintype.card {f : FtsTree → Fin distinct // Function.Surjective f} := by
  classical
  rw [Fintype.card_congr (usedFewTimePatternEquiv signatures distinct), Fintype.card_sigma]
  have hcard (selected : {s : Finset (Fin signatures) // s.card = distinct}) :
      Fintype.card {f : FtsTree → selected.1 // Function.Surjective f} =
        Fintype.card {f : FtsTree → Fin distinct // Function.Surjective f} := by
    let e : selected.1 ≃ Fin distinct := Fintype.equivOfCardEq (by simp only [Fintype.card_coe, Fintype.card_fin, selected.2])
    exact Fintype.card_congr (surjectiveAssignmentEquiv e)
  simp_rw [hcard]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset_len, Fintype.card_fin, nsmul_eq_mul]
  simp

theorem usedFewTimePattern_card_scaled_le_signatureLimit {signatures distinct : Nat}
    (hsignatures : signatures ≤ signatureLimit) :
    Nat.factorial distinct * Fintype.card (UsedFewTimePattern signatures distinct) ≤
      2 ^ (24 * distinct) * Fintype.card {f : FtsTree → Fin distinct // Function.Surjective f} := by
  rw [usedFewTimePattern_card, ← Nat.mul_assoc]
  apply (Nat.mul_le_mul_right _ (factorial_mul_choose_le_pow signatures distinct)).trans
  have hpow := Nat.pow_le_pow_left hsignatures distinct
  rw [signatureLimit, ← pow_mul] at hpow
  exact Nat.mul_le_mul_right _ hpow

end SphincsSecurity.Concrete
