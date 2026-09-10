import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FewTimePatterns

/-!
# Probability of a fixed few-time coverage pattern

The relevant part of an admissible digest is its 26-bit index and its fourteen opened 10-bit leaf
coordinates.  For a fixed assignment of trees to distinct signing results, the successful tuples
are in bijection with one free index and one free leaf vector per signing result.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

abbrev FewTimeView := Index × (FtsTree → FtsLeaf)

noncomputable def FewTimeCover.entryView {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (entry : cover.entries) : FewTimeView :=
  (digestIndex (cover.entryDigest entry),
    fun tree => digestLeaves (cover.entryDigest entry) (ftsIndexOf tree))

def fewTimeTargetView (index : Index) (targetLeaves : DigestTree → FtsLeaf) : FewTimeView :=
  (index, fun tree => targetLeaves (ftsIndexOf tree))

def FixedFewTimePatternHit {Selected : Type} (assignment : FtsTree → Selected)
    (sample : (Selected → FewTimeView) × FewTimeView) : Prop :=
  (∀ selected, (sample.1 selected).1 = sample.2.1)
    ∧ ∀ tree, sample.2.2 tree = (sample.1 (assignment tree)).2 tree

noncomputable instance instDecidablePredProdForallFewTimeViewFixedFewTimePatternHitOfDecidableEq {Selected : Type} [DecidableEq Selected] (assignment : FtsTree → Selected) :
    DecidablePred (FixedFewTimePatternHit assignment) := by
  classical
  intro sample
  exact inferInstance

def fixedFewTimePatternHitEquiv {Selected : Type} [Fintype Selected]
    (assignment : FtsTree → Selected) :
    {sample : (Selected → FewTimeView) × FewTimeView //
        FixedFewTimePatternHit assignment sample} ≃
      Index × (Selected → FtsTree → FtsLeaf) where
  toFun sample := (sample.1.2.1, fun selected => (sample.1.1 selected).2)
  invFun free := ⟨
    (fun selected => (free.1, free.2 selected),
      (free.1, fun tree => free.2 (assignment tree) tree)),
    ⟨fun _ => rfl, fun _ => rfl⟩⟩
  left_inv sample := by
    apply Subtype.ext
    apply Prod.ext
    · funext selected
      apply Prod.ext
      · exact (sample.2.1 selected).symm
      · rfl
    · apply Prod.ext
      · rfl
      · funext tree
        exact (sample.2.2 tree).symm
  right_inv free := rfl

theorem fixedFewTimePatternHit_card {Selected : Type} [Fintype Selected]
    [DecidableEq Selected] (assignment : FtsTree → Selected) :
    Fintype.card {sample : (Selected → FewTimeView) × FewTimeView //
        FixedFewTimePatternHit assignment sample} =
      2 ^ totalHeight * (2 ^ (ftsTreeHeight * (ftsTrees - 1))) ^ Fintype.card Selected := by
  rw [Fintype.card_congr (fixedFewTimePatternHitEquiv assignment), Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin]
  simp only [FtsTree, FtsLeaf, Fintype.card_fun, Fintype.card_fin]
  rw [pow_mul]

theorem fewTimeView_card : Fintype.card FewTimeView =
    2 ^ (totalHeight + ftsTreeHeight * (ftsTrees - 1)) := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin, ← pow_mul, ← pow_add]

theorem fixedFewTimeSample_card (Selected : Type) [Fintype Selected] [DecidableEq Selected] :
    Fintype.card ((Selected → FewTimeView) × FewTimeView) =
      (2 ^ (totalHeight + ftsTreeHeight * (ftsTrees - 1))) ^
        (Fintype.card Selected + 1) := by
  rw [Fintype.card_prod, Fintype.card_fun, fewTimeView_card, pow_succ]

noncomputable local instance instSampleableTypeOfFintypeOfNonempty_sphincsSecurity {R : Type} [Fintype R] [Nonempty R] : SampleableType R :=
  SampleableType.ofFintype R

theorem probEvent_fixedFewTimePatternHit {Selected : Type} [Fintype Selected]
    [DecidableEq Selected] [Nonempty Selected] (assignment : FtsTree → Selected) :
    Pr[FixedFewTimePatternHit assignment |
        ($ᵗ ((Selected → FewTimeView) × FewTimeView) :
          ProbComp ((Selected → FewTimeView) × FewTimeView))] =
      (Fintype.card {sample : (Selected → FewTimeView) × FewTimeView //
          FixedFewTimePatternHit assignment sample} : Nat) /
        Fintype.card ((Selected → FewTimeView) × FewTimeView) := by
  rw [probEvent_uniformSample]
  congr 1
  exact_mod_cast (Fintype.card_subtype (FixedFewTimePatternHit assignment)).symm

theorem fixedFewTimePatternHit_card_ratio_eq_inv {Selected : Type} [Fintype Selected]
    [DecidableEq Selected] (assignment : FtsTree → Selected) :
    (Fintype.card {sample : (Selected → FewTimeView) × FewTimeView //
        FixedFewTimePatternHit assignment sample} : ℝ≥0∞) /
      Fintype.card ((Selected → FewTimeView) × FewTimeView) =
      ((2 ^ (totalHeight * Fintype.card Selected +
        ftsTreeHeight * (ftsTrees - 1)) : Nat) : ℝ≥0∞)⁻¹ := by
  rw [fixedFewTimePatternHit_card, fixedFewTimeSample_card]
  let d := Fintype.card Selected
  have hnum : 2 ^ totalHeight * (2 ^ (ftsTreeHeight * (ftsTrees - 1))) ^ d =
      2 ^ (totalHeight + ftsTreeHeight * (ftsTrees - 1) * d) := by
    rw [← pow_mul, pow_add]
  have hexponent :
      (totalHeight + ftsTreeHeight * (ftsTrees - 1)) * (d + 1) =
        (totalHeight + ftsTreeHeight * (ftsTrees - 1) * d) +
          (totalHeight * d + ftsTreeHeight * (ftsTrees - 1)) := by
    ring
  have hden :
      (2 ^ (totalHeight + ftsTreeHeight * (ftsTrees - 1))) ^ (d + 1) =
        2 ^ (totalHeight + ftsTreeHeight * (ftsTrees - 1) * d) *
          2 ^ (totalHeight * d + ftsTreeHeight * (ftsTrees - 1)) := by
    rw [← pow_mul, hexponent, pow_add]
  rw [hnum, hden]
  rw [div_eq_mul_inv]
  have hzero :
      ((2 ^ (totalHeight + ftsTreeHeight * (ftsTrees - 1) * d) : Nat) : ℝ≥0∞) ≠ 0 := by
    positivity
  have htop :
      ((2 ^ (totalHeight + ftsTreeHeight * (ftsTrees - 1) * d) : Nat) : ℝ≥0∞) ≠ ∞ := by
    simp
  rw [Nat.cast_mul, ENNReal.mul_inv (Or.inl hzero) (Or.inl htop)]
  rw [← mul_assoc, ENNReal.mul_inv_cancel hzero htop, one_mul]

theorem probEvent_fixedFewTimePatternHit_eq_inv {Selected : Type} [Fintype Selected]
    [DecidableEq Selected] [Nonempty Selected] (assignment : FtsTree → Selected) :
    Pr[FixedFewTimePatternHit assignment |
        ($ᵗ ((Selected → FewTimeView) × FewTimeView) :
          ProbComp ((Selected → FewTimeView) × FewTimeView))] =
      ((2 ^ (totalHeight * Fintype.card Selected +
        ftsTreeHeight * (ftsTrees - 1)) : Nat) : ℝ≥0∞)⁻¹ := by
  rw [probEvent_fixedFewTimePatternHit]
  exact fixedFewTimePatternHit_card_ratio_eq_inv assignment

theorem probEvent_fixedFewTimePatternHit_eq_inv_of_evalDist {Selected : Type}
    [Fintype Selected] [DecidableEq Selected] [Nonempty Selected]
    (assignment : FtsTree → Selected)
    (sampler : ProbComp ((Selected → FewTimeView) × FewTimeView))
    (hsampler : 𝒟[sampler] =
      𝒟[($ᵗ ((Selected → FewTimeView) × FewTimeView) :
        ProbComp ((Selected → FewTimeView) × FewTimeView))]) :
    Pr[FixedFewTimePatternHit assignment | sampler] =
      ((2 ^ (totalHeight * Fintype.card Selected +
        ftsTreeHeight * (ftsTrees - 1)) : Nat) : ℝ≥0∞)⁻¹ :=
  (probEvent_congr' (fun _ _ => Iff.rfl) hsampler).trans
    (probEvent_fixedFewTimePatternHit_eq_inv assignment)

theorem fewTimePattern_term_common_denominator (signatures distinct : Nat)
    (hdistinct : distinct ≤ 14) :
    (Fintype.card (FewTimePattern signatures distinct) : ℝ≥0∞) *
        ((2 ^ (26 * distinct + 140) : Nat) : ℝ≥0∞)⁻¹ =
      (Fintype.card (FewTimePattern signatures distinct) *
          2 ^ (26 * (14 - distinct)) : ℕ) *
        ((2 ^ 504 : Nat) : ℝ≥0∞)⁻¹ := by
  let factor : ℝ≥0∞ := (2 ^ (26 * (14 - distinct)) : ℕ)
  have hfactorZero : factor ≠ 0 := by positivity
  have hfactorTop : factor ≠ ∞ := by simp [factor]
  rw [← div_eq_mul_inv, ← div_eq_mul_inv,
    ← ENNReal.mul_div_mul_right
      (Fintype.card (FewTimePattern signatures distinct) : ℝ≥0∞)
      ((2 ^ (26 * distinct + 140) : Nat) : ℝ≥0∞) hfactorZero hfactorTop]
  have hexponent : 26 * distinct + 140 + 26 * (14 - distinct) = 504 := by omega
  apply congrArg₂ (· / ·)
  · rw [Nat.cast_mul]
  · change ((2 ^ (26 * distinct + 140) : Nat) : ℝ≥0∞) *
        ((2 ^ (26 * (14 - distinct)) : Nat) : ℝ≥0∞) =
      ((2 ^ 504 : Nat) : ℝ≥0∞)
    rw [← Nat.cast_mul, ← pow_add, hexponent]

set_option exponentiation.threshold 400 in
theorem fewTimePattern_unionBound_le {signatures : Nat}
    (hsignatures : signatures ≤ signatureLimit) :
    (∑ distinct ∈ Finset.Icc 1 14,
      (Fintype.card (FewTimePattern signatures distinct) : ℝ≥0∞) *
        ((2 ^ (26 * distinct + 140) : Nat) : ℝ≥0∞)⁻¹) ≤
      ((2 ^ 122 : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  calc
    (∑ distinct ∈ Finset.Icc 1 14,
        (Fintype.card (FewTimePattern signatures distinct) : ℝ≥0∞) *
          ((2 ^ (26 * distinct + 140) : Nat) : ℝ≥0∞)⁻¹) =
        ∑ distinct ∈ Finset.Icc 1 14,
          (Fintype.card (FewTimePattern signatures distinct) *
              2 ^ (26 * (14 - distinct)) : Nat) *
            ((2 ^ 504 : Nat) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_congr rfl
      intro distinct hdistinct
      exact fewTimePattern_term_common_denominator signatures distinct
        (Finset.mem_Icc.mp hdistinct).2
    _ = ((∑ distinct ∈ Finset.Icc 1 14,
          Fintype.card (FewTimePattern signatures distinct) *
            2 ^ (26 * (14 - distinct)) : Nat) : ℝ≥0∞) *
          ((2 ^ 504 : Nat) : ℝ≥0∞)⁻¹ := by
      rw [← Finset.sum_mul, Nat.cast_sum]
    _ ≤ ((2 ^ 382 : Nat) : ℝ≥0∞) * ((2 ^ 504 : Nat) : ℝ≥0∞)⁻¹ := by
      gcongr
      exact_mod_cast fewTimePattern_sum_le hsignatures
    _ = ((2 ^ 122 : Nat) : ℝ≥0∞)⁻¹ := by
      have hzero : ((2 ^ 382 : Nat) : ℝ≥0∞) ≠ 0 := by positivity
      have htop : ((2 ^ 382 : Nat) : ℝ≥0∞) ≠ ∞ := by simp
      rw [show 504 = 382 + 122 by norm_num, pow_add, Nat.cast_mul,
        ENNReal.mul_inv (Or.inl hzero) (Or.inl htop), ← mul_assoc,
        ENNReal.mul_inv_cancel hzero htop, one_mul]

end SphincsSecurity.Concrete
