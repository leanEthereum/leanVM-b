import SphincsSecurity.Proof.EncodingRetry

/-!
# Conditional encoding selection risk

A retry schedule records an input identifier together with the digest already cached there, or
`none` when that input is still missing. Completing the missing inputs with fresh oracle answers
and taking the first admissible digest gives the conditional distribution of the canonical encoding
target. Candidates retain their input identifiers, so the selected input is never mistaken for a
collision with itself.
-/

namespace SphincsSecurity.EncodingSelection

open OracleComp ENNReal

set_option maxRecDepth 100000

noncomputable def selectFirst {ι : Type} [DecidableEq ι] :
    List (ι × Option Digest) → ProbComp (Option (ι × Digest))
  | [] => pure none
  | (identifier, some digest) :: rest =>
      if TargetSum.ValidDigest digest then
        pure (some (identifier, digest))
      else
        selectFirst rest
  | (identifier, none) :: rest => do
      let output ← ($ᵗ HashOutput : ProbComp HashOutput)
      let digest := truncateHash output
      if TargetSum.ValidDigest digest then
        pure (some (identifier, digest))
      else
        selectFirst rest

def selectedHits {ι : Type} [DecidableEq ι] (targets : Finset (ι × Digest)) :
    Option (ι × Digest) → Prop
  | none => False
  | some selected =>
      ∃ candidate ∈ targets,
        candidate.1 ≠ selected.1 ∧ candidate.2 = selected.2

noncomputable def selectionRisk {ι : Type} [DecidableEq ι]
    (schedule : List (ι × Option Digest)) (targets : Finset (ι × Digest)) : ℝ≥0∞ :=
  Pr[selectedHits targets | selectFirst schedule]

theorem selectFirst_support_some_valid {ι : Type} [DecidableEq ι]
    {schedule : List (ι × Option Digest)} {identifier : ι} {digest : Digest}
    (hmem : some (identifier, digest) ∈ support (selectFirst schedule)) :
    TargetSum.ValidDigest digest := by
  induction schedule with
  | nil => simp [selectFirst] at hmem
  | cons head rest ih =>
      obtain ⟨headIdentifier, headDigest⟩ := head
      cases headDigest with
      | none =>
          rw [selectFirst, mem_support_bind_iff] at hmem
          obtain ⟨output, _houtput, hmem⟩ := hmem
          by_cases hvalid : TargetSum.ValidDigest (truncateHash output)
          · have heq : (identifier, digest) =
                (headIdentifier, truncateHash output) := by
              simpa [hvalid] using hmem
            have hdigest : digest = truncateHash output := by
              simpa using congrArg Prod.snd heq
            rw [hdigest]
            exact hvalid
          · simp only [hvalid] at hmem
            exact ih hmem
      | some cachedDigest =>
          rw [selectFirst] at hmem
          by_cases hvalid : TargetSum.ValidDigest cachedDigest
          · have heq : (identifier, digest) = (headIdentifier, cachedDigest) := by
              simpa [hvalid] using hmem
            have hdigest : digest = cachedDigest := by
              simpa using congrArg Prod.snd heq
            rw [hdigest]
            exact hvalid
          · simp only [hvalid] at hmem
            exact ih hmem

@[simp] theorem selectionRisk_nil {ι : Type} [DecidableEq ι]
    (targets : Finset (ι × Digest)) :
    selectionRisk [] targets = 0 := by
  simp [selectionRisk, selectFirst, selectedHits]

theorem selectionRisk_cons_some_of_valid_of_hit {ι : Type} [DecidableEq ι]
    (identifier : ι) (digest : Digest) (rest : List (ι × Option Digest))
    (targets : Finset (ι × Digest)) (hvalid : TargetSum.ValidDigest digest)
    (hhit : selectedHits targets (some (identifier, digest))) :
    selectionRisk ((identifier, some digest) :: rest) targets = 1 := by
  classical
  rw [selectionRisk, selectFirst, if_pos hvalid, probEvent_pure, if_pos hhit]

theorem selectionRisk_cons_some_of_valid_of_miss {ι : Type} [DecidableEq ι]
    (identifier : ι) (digest : Digest) (rest : List (ι × Option Digest))
    (targets : Finset (ι × Digest)) (hvalid : TargetSum.ValidDigest digest)
    (hmiss : ¬ selectedHits targets (some (identifier, digest))) :
    selectionRisk ((identifier, some digest) :: rest) targets = 0 := by
  classical
  rw [selectionRisk, selectFirst, if_pos hvalid, probEvent_pure, if_neg hmiss]

theorem selectionRisk_cons_some_of_invalid {ι : Type} [DecidableEq ι]
    (identifier : ι) (digest : Digest) (rest : List (ι × Option Digest))
    (targets : Finset (ι × Digest)) (hinvalid : ¬ TargetSum.ValidDigest digest) :
    selectionRisk ((identifier, some digest) :: rest) targets =
      selectionRisk rest targets := by
  simp [selectionRisk, selectFirst, hinvalid]

theorem selectionRisk_cons_none_eq {ι : Type} [DecidableEq ι]
    (identifier : ι) (rest : List (ι × Option Digest))
    (targets : Finset (ι × Digest)) :
    selectionRisk ((identifier, none) :: rest) targets =
      ∑' output : HashOutput,
        Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
          selectionRisk ((identifier, some (truncateHash output)) :: rest) targets := by
  have hselect : selectFirst ((identifier, none) :: rest) =
      ($ᵗ HashOutput : ProbComp HashOutput) >>= fun output =>
        selectFirst ((identifier, some (truncateHash output)) :: rest) := by
    rw [selectFirst]
    apply bind_congr
    intro output
    rw [selectFirst]
  rw [selectionRisk, hselect, probEvent_bind_eq_tsum]
  rfl

inductive FirstValid {ι : Type} [DecidableEq ι] :
    List (ι × Option Digest) → ι → Digest → Prop where
  | here (identifier : ι) (digest : Digest) (rest : List (ι × Option Digest))
      (valid : TargetSum.ValidDigest digest) :
      FirstValid ((identifier, some digest) :: rest) identifier digest
  | there (headIdentifier : ι) (headDigest : Digest)
      (rest : List (ι × Option Digest)) (identifier : ι) (digest : Digest)
      (invalid : ¬ TargetSum.ValidDigest headDigest)
      (tail : FirstValid rest identifier digest) :
      FirstValid ((headIdentifier, some headDigest) :: rest) identifier digest

theorem FirstValid.selectFirst_eq_pure {ι : Type} [DecidableEq ι]
    {schedule : List (ι × Option Digest)} {identifier : ι} {digest : Digest}
    (hfirst : FirstValid schedule identifier digest) :
    selectFirst schedule = pure (some (identifier, digest)) := by
  induction hfirst with
  | here identifier digest rest hvalid =>
      rw [selectFirst, if_pos hvalid]
  | there headIdentifier headDigest rest identifier digest hinvalid htail ih =>
      rw [selectFirst, if_neg hinvalid, ih]

theorem selectionRisk_eq_one_of_firstValid_hit {ι : Type} [DecidableEq ι]
    {schedule : List (ι × Option Digest)} {identifier : ι} {digest : Digest}
    {targets : Finset (ι × Digest)}
    (hfirst : FirstValid schedule identifier digest)
    (hhit : selectedHits targets (some (identifier, digest))) :
    selectionRisk schedule targets = 1 := by
  classical
  rw [selectionRisk, hfirst.selectFirst_eq_pure, probEvent_pure, if_pos hhit]

@[simp] theorem selectionRisk_empty_targets {ι : Type} [DecidableEq ι]
    (schedule : List (ι × Option Digest)) :
    selectionRisk schedule ∅ = 0 := by
  rw [selectionRisk]
  apply probEvent_eq_zero
  intro selected _ hhit
  cases selected with
  | none => exact hhit
  | some selected =>
      obtain ⟨candidate, hcandidate, _⟩ := hhit
      simp at hcandidate

noncomputable def candidateTargets {ι : Type} [DecidableEq ι]
    (identifier : ι) (targets : Finset (ι × Digest))
    (output : HashOutput) : Finset (ι × Digest) :=
  if TargetSum.ValidDigest (truncateHash output) then
    insert (identifier, truncateHash output) targets
  else
    targets

noncomputable def candidatePair {ι : Type} [DecidableEq ι]
    (schedule : List (ι × Option Digest)) :
    ProbComp (HashOutput × Option (ι × Digest)) := do
  let output ← ($ᵗ HashOutput : ProbComp HashOutput)
  let selected ← selectFirst schedule
  pure (output, selected)

def candidateMatches {ι : Type} [DecidableEq ι] (identifier : ι)
    (pair : HashOutput × Option (ι × Digest)) : Prop :=
  ∃ selectedIdentifier,
    pair.2 = some (selectedIdentifier, truncateHash pair.1)
      ∧ identifier ≠ selectedIdentifier

theorem candidatePair_oldRisk_eq {ι : Type} [DecidableEq ι]
    (schedule : List (ι × Option Digest)) (targets : Finset (ι × Digest)) :
    Pr[fun pair => selectedHits targets pair.2 | candidatePair schedule] =
      selectionRisk schedule targets := by
  rw [candidatePair, probEvent_bind_eq_tsum]
  simp_rw [show (fun selected => pure (_, selected)) =
      pure ∘ fun selected => (_, selected) from rfl, probEvent_bind_pure_comp]
  change (∑' output : HashOutput,
      Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
        selectionRisk schedule targets) = selectionRisk schedule targets
  rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]

theorem candidatePair_matchesSelection_le {ι : Type} [DecidableEq ι]
    (identifier : ι) (schedule : List (ι × Option Digest)) :
    Pr[candidateMatches identifier | candidatePair schedule] ≤
      (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  rw [candidatePair]
  rw [probEvent_bind_bind_swap
    ($ᵗ HashOutput : ProbComp HashOutput) (selectFirst schedule)
    (fun output selected => pure (output, selected))]
  refine probEvent_bind_le_of_forall_le fun selected _hselected => ?_
  rw [show (fun output => pure (output, selected)) =
    pure ∘ fun output => (output, selected) from rfl, probEvent_bind_pure_comp]
  cases selected with
  | none =>
      calc
        _ = 0 := probEvent_eq_zero (by
          intro output _ hmatch
          obtain ⟨selectedIdentifier, helected, _⟩ := hmatch
          simp at helected)
        _ ≤ _ := bot_le
  | some selected =>
      obtain ⟨selectedIdentifier, digest⟩ := selected
      by_cases heq : identifier = selectedIdentifier
      · calc
          _ = 0 := probEvent_eq_zero (by
            intro output _ hmatch
            obtain ⟨foundIdentifier, helected, hne⟩ := hmatch
            have hidentifier : foundIdentifier = selectedIdentifier := by
              have hpairs : (selectedIdentifier, digest) =
                  (foundIdentifier, truncateHash output) := Option.some.inj helected
              exact (congrArg Prod.fst hpairs).symm
            exact hne (heq.trans hidentifier.symm))
          _ ≤ _ := bot_le
      · rw [show ((candidateMatches identifier) ∘
            fun output : HashOutput => (output, some (selectedIdentifier, digest))) =
          fun output => truncateHash output = digest by
            funext output
            apply propext
            constructor
            · rintro ⟨foundIdentifier, helected, _⟩
              have hpairs : (selectedIdentifier, digest) =
                  (foundIdentifier, truncateHash output) := Option.some.inj helected
              exact (congrArg Prod.snd hpairs).symm
            · intro hdigest
              exact ⟨selectedIdentifier, by simp [hdigest], heq⟩]
        exact le_of_eq (SphincsSecurity.probEvent_uniform_truncateHash_eq digest)

theorem candidatePair_newRisk_le {ι : Type} [DecidableEq ι]
    (identifier : ι) (schedule : List (ι × Option Digest))
    (targets : Finset (ι × Digest)) :
    Pr[fun pair => selectedHits
          (candidateTargets identifier targets pair.1) pair.2 |
        candidatePair schedule] ≤
      selectionRisk schedule targets +
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  let old : HashOutput × Option (ι × Digest) → Prop :=
    fun pair => selectedHits targets pair.2
  let matched : HashOutput × Option (ι × Digest) → Prop :=
    candidateMatches identifier
  calc
    Pr[fun pair => selectedHits (candidateTargets identifier targets pair.1) pair.2 |
        candidatePair schedule] ≤
      Pr[fun pair => old pair ∨ matched pair | candidatePair schedule] := by
        apply probEvent_mono
        intro pair _ hnew
        obtain ⟨output, selected⟩ := pair
        cases selected with
        | none => exact hnew.elim
        | some selected =>
            obtain ⟨selectedIdentifier, selectedDigest⟩ := selected
            obtain ⟨candidate, hcandidate, hidentifier, hdigest⟩ := hnew
            by_cases hvalid : TargetSum.ValidDigest (truncateHash output)
            · rw [candidateTargets, if_pos hvalid, Finset.mem_insert] at hcandidate
              rcases hcandidate with heq | hold
              · subst candidate
                exact Or.inr ⟨selectedIdentifier, by
                  rw [show truncateHash (output, some
                    (selectedIdentifier, selectedDigest)).1 = selectedDigest from hdigest]
                , hidentifier⟩
              · exact Or.inl ⟨candidate, hold, hidentifier, hdigest⟩
            · rw [candidateTargets, if_neg hvalid] at hcandidate
              exact Or.inl ⟨candidate, hcandidate, hidentifier, hdigest⟩
    _ ≤ Pr[old | candidatePair schedule] +
        Pr[matched | candidatePair schedule] :=
      probEvent_or_le _ old matched
    _ ≤ selectionRisk schedule targets +
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
      rw [candidatePair_oldRisk_eq]
      exact add_le_add le_rfl
        (candidatePair_matchesSelection_le identifier schedule)

theorem candidatePair_newRisk_eq_sum {ι : Type} [DecidableEq ι]
    (identifier : ι) (schedule : List (ι × Option Digest))
    (targets : Finset (ι × Digest)) :
    Pr[fun pair => selectedHits
          (candidateTargets identifier targets pair.1) pair.2 |
        candidatePair schedule] =
      ∑' output : HashOutput,
        Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
          selectionRisk schedule (candidateTargets identifier targets output) := by
  rw [candidatePair, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro output
  congr 1
  rw [show (fun selected => pure (output, selected)) =
    pure ∘ fun selected => (output, selected) from rfl, probEvent_bind_pure_comp]
  rfl

theorem uniform_candidateTargets_selectionRisk_sum_le
    {ι : Type} [DecidableEq ι]
    (identifier : ι) (schedule : List (ι × Option Digest))
    (targets : Finset (ι × Digest)) :
    (∑' output : HashOutput,
      Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
        selectionRisk schedule (candidateTargets identifier targets output)) ≤
      selectionRisk schedule targets +
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  rw [← candidatePair_newRisk_eq_sum]
  exact candidatePair_newRisk_le identifier schedule targets

end SphincsSecurity.EncodingSelection
