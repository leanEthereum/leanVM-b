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

theorem FewTimeCover.fixedPatternHit {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves) :
    FixedFewTimePatternHit cover.entryAssignment
      (cover.entryView, fewTimeTargetView index targetLeaves) := by
  constructor
  · intro entry
    exact cover.entryDigest_index entry
  · intro tree
    exact (cover.entryDigest_assigned_leaf tree).symm

noncomputable instance {Selected : Type} [DecidableEq Selected] (assignment : FtsTree → Selected) :
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

noncomputable local instance {R : Type} [Fintype R] [Nonempty R] : SampleableType R :=
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

def splitFunctionEquiv {Domain Range : Type} [DecidableEq Domain]
    (selected : Finset Domain) :
    (Domain → Range) ≃ (selected → Range) × ({index : Domain // index ∉ selected} → Range) where
  toFun table := (fun index => table index.1, fun index => table index.1)
  invFun tables := fun index => if h : index ∈ selected then tables.1 ⟨index, h⟩
    else tables.2 ⟨index, h⟩
  left_inv table := by
    funext index
    by_cases h : index ∈ selected <;> simp [h]
  right_inv tables := by
    apply Prod.ext <;> funext index
    · simp [index.2]
    · simp [index.2]

def splitPatternSampleEquiv {Domain Range : Type} [DecidableEq Domain]
    (selected : Finset Domain) :
    ((Domain → Range) × Range) ≃
      (((selected → Range) × Range) ×
        ({index : Domain // index ∉ selected} → Range)) where
  toFun sample :=
    (((splitFunctionEquiv selected sample.1).1, sample.2),
      (splitFunctionEquiv selected sample.1).2)
  invFun sample :=
    ((splitFunctionEquiv selected).symm (sample.1.1, sample.2), sample.1.2)
  left_inv sample := by
    apply Prod.ext
    · exact (splitFunctionEquiv selected).symm_apply_apply sample.1
    · rfl
  right_inv sample := by
    have hsplit := (splitFunctionEquiv selected).apply_symm_apply (sample.1.1, sample.2)
    exact congrArg (fun tables => ((tables.1, sample.1.2), tables.2)) hsplit

def FewTimePattern.restrictSample {signatures distinct : Nat}
    (pattern : FewTimePattern signatures distinct)
    (sample : (Fin signatures → FewTimeView) × FewTimeView) :
    (pattern.selected → FewTimeView) × FewTimeView :=
  (fun selected => sample.1 selected.1, sample.2)

def FewTimePattern.Hit {signatures distinct : Nat}
    (pattern : FewTimePattern signatures distinct)
    (sample : (Fin signatures → FewTimeView) × FewTimeView) : Prop :=
  FixedFewTimePatternHit pattern.assignment (pattern.restrictSample sample)

noncomputable instance {signatures distinct : Nat}
    (pattern : FewTimePattern signatures distinct) : DecidablePred pattern.Hit := by
  classical
  intro sample
  exact inferInstance

theorem evalDist_restrictPatternSample_uniform {signatures distinct : Nat}
    (pattern : FewTimePattern signatures distinct) :
    𝒟[(pattern.restrictSample <$> ($ᵗ ((Fin signatures → FewTimeView) × FewTimeView) :
        ProbComp ((Fin signatures → FewTimeView) × FewTimeView)))] =
      𝒟[($ᵗ ((pattern.selected → FewTimeView) × FewTimeView) :
        ProbComp ((pattern.selected → FewTimeView) × FewTimeView))] := by
  classical
  let split := splitPatternSampleEquiv (Range := FewTimeView) pattern.selected
  have hrewrite : pattern.restrictSample = Prod.fst ∘ split := by
    funext sample
    rfl
  have hmap :
      pattern.restrictSample <$> ($ᵗ ((Fin signatures → FewTimeView) × FewTimeView) :
        ProbComp ((Fin signatures → FewTimeView) × FewTimeView)) =
        Prod.fst <$> (split <$> ($ᵗ ((Fin signatures → FewTimeView) × FewTimeView) :
          ProbComp ((Fin signatures → FewTimeView) × FewTimeView))) := by
    simp only [Functor.map_map, hrewrite, Function.comp_def]
  rw [hmap]
  have hsplit :
      𝒟[(split <$> ($ᵗ ((Fin signatures → FewTimeView) × FewTimeView) :
          ProbComp ((Fin signatures → FewTimeView) × FewTimeView)))] =
        𝒟[($ᵗ (((pattern.selected → FewTimeView) × FewTimeView) ×
          ({index : Fin signatures // index ∉ pattern.selected} → FewTimeView)) :
          ProbComp (((pattern.selected → FewTimeView) × FewTimeView) ×
            ({index : Fin signatures // index ∉ pattern.selected} → FewTimeView)))] :=
    evalDist_map_bijective_uniform_cross
      (α := (Fin signatures → FewTimeView) × FewTimeView)
      (β := ((pattern.selected → FewTimeView) × FewTimeView) ×
        ({index : Fin signatures // index ∉ pattern.selected} → FewTimeView))
      split split.bijective
  rw [evalDist_map, hsplit, ← evalDist_map]
  exact evalDist_map_fst_uniformSample_prod

def subtypeProdLeftEquiv {A B : Type} (P : A → Prop) :
    {pair : A × B // P pair.1} ≃ {a : A // P a} × B where
  toFun pair := (⟨pair.1.1, pair.2⟩, pair.1.2)
  invFun pair := ⟨(pair.1.1, pair.2), pair.1.2⟩
  left_inv pair := by cases pair; rfl
  right_inv pair := by cases pair with | mk left right => cases left; rfl

def fewTimePatternHitEquiv {signatures distinct : Nat}
    (pattern : FewTimePattern signatures distinct) :
    {sample : (Fin signatures → FewTimeView) × FewTimeView // pattern.Hit sample} ≃
      {sample : (pattern.selected → FewTimeView) × FewTimeView //
          FixedFewTimePatternHit pattern.assignment sample} ×
        ({index : Fin signatures // index ∉ pattern.selected} → FewTimeView) :=
  ((splitPatternSampleEquiv (Range := FewTimeView) pattern.selected).subtypeEquiv
      (fun _ => Iff.rfl)).trans (subtypeProdLeftEquiv _)

theorem probEvent_fewTimePatternHit_eq_inv {signatures distinct : Nat}
    (pattern : FewTimePattern signatures distinct) :
    Pr[pattern.Hit |
        ($ᵗ ((Fin signatures → FewTimeView) × FewTimeView) :
          ProbComp ((Fin signatures → FewTimeView) × FewTimeView))] =
      ((2 ^ (totalHeight * distinct + ftsTreeHeight * (ftsTrees - 1)) : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  let complement := {index : Fin signatures // index ∉ pattern.selected} → FewTimeView
  have hnum :
      Fintype.card {sample : (Fin signatures → FewTimeView) × FewTimeView //
          pattern.Hit sample} =
        Fintype.card {sample : (pattern.selected → FewTimeView) × FewTimeView //
            FixedFewTimePatternHit pattern.assignment sample} * Fintype.card complement := by
    rw [Fintype.card_congr (fewTimePatternHitEquiv pattern), Fintype.card_prod]
  have hden : Fintype.card ((Fin signatures → FewTimeView) × FewTimeView) =
      Fintype.card ((pattern.selected → FewTimeView) × FewTimeView) *
        Fintype.card complement := by
    rw [Fintype.card_congr (splitPatternSampleEquiv
      (Range := FewTimeView) pattern.selected), Fintype.card_prod]
  rw [probEvent_uniformSample, ← Fintype.card_subtype pattern.Hit, hnum, hden,
    Nat.cast_mul, Nat.cast_mul]
  rw [ENNReal.mul_div_mul_right _ _ (by
    exact_mod_cast (Fintype.card_ne_zero (α := complement))) (by simp)]
  rw [fixedFewTimePatternHit_card_ratio_eq_inv, Fintype.card_coe,
    pattern.card_selected]

def AnyFewTimePatternHit (signatures distinct : Nat)
    (sample : (Fin signatures → FewTimeView) × FewTimeView) : Prop :=
  ∃ pattern : FewTimePattern signatures distinct, pattern.Hit sample

noncomputable instance (signatures distinct : Nat) :
    DecidablePred (AnyFewTimePatternHit signatures distinct) :=
  fun sample => Classical.propDecidable (AnyFewTimePatternHit signatures distinct sample)

theorem probEvent_anyFewTimePatternHit_le {signatures distinct : Nat} :
    Pr[AnyFewTimePatternHit signatures distinct |
        ($ᵗ ((Fin signatures → FewTimeView) × FewTimeView) :
          ProbComp ((Fin signatures → FewTimeView) × FewTimeView))] ≤
      (Fintype.card (FewTimePattern signatures distinct) : ℝ≥0∞) *
        ((2 ^ (totalHeight * distinct + ftsTreeHeight * (ftsTrees - 1)) : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  let sampler := ($ᵗ ((Fin signatures → FewTimeView) × FewTimeView) :
    ProbComp ((Fin signatures → FewTimeView) × FewTimeView))
  calc
    Pr[AnyFewTimePatternHit signatures distinct | sampler] =
        Pr[fun sample => ∃ pattern ∈ (Finset.univ :
            Finset (FewTimePattern signatures distinct)), pattern.Hit sample | sampler] := by
      congr 1
      funext sample
      simp [AnyFewTimePatternHit]
    _ ≤ ∑ pattern ∈ (Finset.univ : Finset (FewTimePattern signatures distinct)),
          Pr[pattern.Hit | sampler] :=
      probEvent_exists_finset_le_sum Finset.univ sampler
        (fun (pattern : FewTimePattern signatures distinct) sample => pattern.Hit sample)
    _ = ∑ _pattern ∈ (Finset.univ : Finset (FewTimePattern signatures distinct)),
          ((2 ^ (totalHeight * distinct + ftsTreeHeight * (ftsTrees - 1)) : Nat) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_congr rfl
      intro pattern _
      exact probEvent_fewTimePatternHit_eq_inv pattern
    _ = (Fintype.card (FewTimePattern signatures distinct) : ℝ≥0∞) *
          ((2 ^ (totalHeight * distinct + ftsTreeHeight * (ftsTrees - 1)) : Nat) : ℝ≥0∞)⁻¹ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

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

def SomeFewTimePatternHit (signatures : Nat)
    (sample : (Fin signatures → FewTimeView) × FewTimeView) : Prop :=
  ∃ distinct ∈ Finset.Icc 1 14, AnyFewTimePatternHit signatures distinct sample

noncomputable instance (signatures : Nat) : DecidablePred (SomeFewTimePatternHit signatures) :=
  fun sample => Classical.propDecidable (SomeFewTimePatternHit signatures sample)

set_option exponentiation.threshold 400 in
theorem probEvent_someFewTimePatternHit_le {signatures : Nat}
    (hsignatures : signatures ≤ signatureLimit) :
    Pr[SomeFewTimePatternHit signatures |
        ($ᵗ ((Fin signatures → FewTimeView) × FewTimeView) :
          ProbComp ((Fin signatures → FewTimeView) × FewTimeView))] ≤
      ((2 ^ 122 : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  let sampler := ($ᵗ ((Fin signatures → FewTimeView) × FewTimeView) :
    ProbComp ((Fin signatures → FewTimeView) × FewTimeView))
  calc
    Pr[SomeFewTimePatternHit signatures | sampler] =
        Pr[fun sample => ∃ distinct ∈ Finset.Icc 1 14,
          AnyFewTimePatternHit signatures distinct sample | sampler] := rfl
    _ ≤ ∑ distinct ∈ Finset.Icc 1 14,
          Pr[AnyFewTimePatternHit signatures distinct | sampler] :=
      probEvent_exists_finset_le_sum (Finset.Icc 1 14) sampler
        (fun distinct sample => AnyFewTimePatternHit signatures distinct sample)
    _ ≤ ∑ distinct ∈ Finset.Icc 1 14,
          (Fintype.card (FewTimePattern signatures distinct) : ℝ≥0∞) *
            ((2 ^ (26 * distinct + 140) : Nat) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_le_sum
      intro distinct _
      simpa only [totalHeight, ftsTreeHeight, ftsTrees] using
        (probEvent_anyFewTimePatternHit_le (signatures := signatures) (distinct := distinct))
    _ = ∑ distinct ∈ Finset.Icc 1 14,
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

noncomputable def FewTimeCover.transcriptViews {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves) :
    Fin signingLog.length → FewTimeView :=
  Function.extend cover.logIndex cover.entryView (fun _ => default)

theorem FewTimeCover.patternHit {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves) :
    cover.pattern.Hit (cover.transcriptViews, fewTimeTargetView index targetLeaves) := by
  constructor
  · intro selected
    obtain ⟨entry, _, hentry⟩ := Finset.mem_image.1 selected.2
    have hview : cover.transcriptViews selected.1 = cover.entryView entry := by
      rw [← hentry]
      exact cover.logIndex_injective.extend_apply cover.entryView (fun _ => default) entry
    change (cover.transcriptViews selected.1).1 = index
    rw [hview]
    exact cover.entryDigest_index entry
  · intro tree
    change targetLeaves (ftsIndexOf tree) =
      (cover.transcriptViews (cover.logIndex (cover.entryAssignment tree))).2 tree
    rw [FewTimeCover.transcriptViews,
      cover.logIndex_injective.extend_apply cover.entryView (fun _ => default)]
    exact (cover.entryDigest_assigned_leaf tree).symm

theorem FewTimeCover.somePatternHit {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves) :
    SomeFewTimePatternHit signingLog.length
      (cover.transcriptViews, fewTimeTargetView index targetLeaves) := by
  refine ⟨cover.entries.card, Finset.mem_Icc.2
    ⟨cover.entries_card_pos, cover.entries_card_le_trees⟩, cover.pattern, cover.patternHit⟩

end SphincsSecurity.Concrete
