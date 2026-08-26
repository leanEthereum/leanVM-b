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

noncomputable def targetDigests {ι : Type} [DecidableEq ι]
    (targets : Finset (ι × Digest)) : Finset Digest :=
  targets.image Prod.snd

theorem digest_mem_targetDigests_of_selectedHits
    {ι : Type} [DecidableEq ι] {targets : Finset (ι × Digest)}
    {identifier : ι} {digest : Digest}
    (hhit : selectedHits targets (some (identifier, digest))) :
    digest ∈ targetDigests targets := by
  obtain ⟨candidate, hcandidate, _, hdigest⟩ := hhit
  rw [targetDigests, Finset.mem_image]
  exact ⟨candidate, hcandidate, hdigest⟩

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

theorem selectionRisk_cons_some_of_valid_suffix_eq
    {ι : Type} [DecidableEq ι] (identifier : ι) (digest : Digest)
    (left right : List (ι × Option Digest)) (targets : Finset (ι × Digest))
    (hvalid : TargetSum.ValidDigest digest) :
    selectionRisk ((identifier, some digest) :: left) targets =
      selectionRisk ((identifier, some digest) :: right) targets := by
  by_cases hhit : selectedHits targets (some (identifier, digest))
  · rw [selectionRisk_cons_some_of_valid_of_hit _ _ _ _ hvalid hhit,
      selectionRisk_cons_some_of_valid_of_hit _ _ _ _ hvalid hhit]
  · rw [selectionRisk_cons_some_of_valid_of_miss _ _ _ _ hvalid hhit,
      selectionRisk_cons_some_of_valid_of_miss _ _ _ _ hvalid hhit]

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

inductive AllMissing {ι : Type} [DecidableEq ι] :
    List (ι × Option Digest) → Prop where
  | nil : AllMissing []
  | cons (identifier : ι) (rest : List (ι × Option Digest))
      (tail : AllMissing rest) :
      AllMissing ((identifier, none) :: rest)

theorem AllMissing.selectionRisk_le_pendingRisk
    {ι : Type} [DecidableEq ι]
    {schedule : List (ι × Option Digest)} (hmissing : AllMissing schedule)
    (targets : Finset (ι × Digest)) :
    selectionRisk schedule targets ≤
      EncodingRetry.pendingRisk (targetDigests targets) := by
  induction hmissing with
  | nil =>
      rw [selectionRisk_nil]
      exact bot_le
  | cons identifier rest _ ih =>
      rw [selectionRisk_cons_none_eq]
      calc
        _ ≤ ∑' output : HashOutput,
            Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
              (if TargetSum.ValidDigest (truncateHash output) then
                if truncateHash output ∈ targetDigests targets then 1 else 0
              else EncodingRetry.pendingRisk (targetDigests targets)) := by
            apply ENNReal.tsum_le_tsum
            intro output
            apply mul_le_mul_right
            by_cases hvalid : TargetSum.ValidDigest (truncateHash output)
            · by_cases hhit : selectedHits targets
                  (some (identifier, truncateHash output))
              · have hmem := digest_mem_targetDigests_of_selectedHits hhit
                rw [selectionRisk_cons_some_of_valid_of_hit _ _ _ _ hvalid hhit,
                  if_pos hvalid, if_pos hmem]
              · rw [selectionRisk_cons_some_of_valid_of_miss _ _ _ _ hvalid hhit,
                  if_pos hvalid]
                split <;> simp
            · rw [selectionRisk_cons_some_of_invalid _ _ _ _ hvalid,
                if_neg hvalid]
              exact ih
        _ ≤ EncodingRetry.pendingRisk (targetDigests targets) := by
          exact SphincsSecurity.uniformHashOutput_select_bonus_sum_le
            (targetDigests targets)

theorem uniform_reveal_append_sum_eq {ι : Type} [DecidableEq ι]
    (initial : List (ι × Option Digest)) (identifier : ι)
    (rest : List (ι × Option Digest)) (targets : Finset (ι × Digest)) :
    (∑' output : HashOutput,
      Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
        selectionRisk
          (initial ++ (identifier, some (truncateHash output)) :: rest) targets) =
      selectionRisk (initial ++ (identifier, none) :: rest) targets := by
  induction initial with
  | nil =>
      exact (selectionRisk_cons_none_eq identifier rest targets).symm
  | cons head initial ih =>
      obtain ⟨headIdentifier, headDigest⟩ := head
      cases headDigest with
      | some digest =>
          by_cases hvalid : TargetSum.ValidDigest digest
          · by_cases hhit : selectedHits targets (some (headIdentifier, digest))
            · simp_rw [List.cons_append,
                selectionRisk_cons_some_of_valid_of_hit _ _ _ _ hvalid hhit]
              rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
            · simp_rw [List.cons_append,
                selectionRisk_cons_some_of_valid_of_miss _ _ _ _ hvalid hhit]
              simp
          · simp_rw [List.cons_append,
              selectionRisk_cons_some_of_invalid _ _ _ _ hvalid]
            exact ih
      | none =>
          simp_rw [List.cons_append, selectionRisk_cons_none_eq]
          simp_rw [← ENNReal.tsum_mul_left]
          rw [ENNReal.tsum_comm]
          apply tsum_congr
          intro headOutput
          simp_rw [mul_left_comm]
          rw [ENNReal.tsum_mul_left]
          congr 1
          by_cases hvalid : TargetSum.ValidDigest (truncateHash headOutput)
          · by_cases hhit : selectedHits targets
                (some (headIdentifier, truncateHash headOutput))
            · simp_rw [selectionRisk_cons_some_of_valid_of_hit _ _ _ _ hvalid hhit]
              rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
            · simp_rw [selectionRisk_cons_some_of_valid_of_miss _ _ _ _ hvalid hhit]
              simp
          · simp_rw [selectionRisk_cons_some_of_invalid _ _ _ _ hvalid]
            exact ih

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

inductive ReachableCachedValid {ι : Type} [DecidableEq ι] :
    List (ι × Option Digest) → ι → Digest → Prop where
  | here (identifier : ι) (digest : Digest) (rest : List (ι × Option Digest))
      (valid : TargetSum.ValidDigest digest) :
      ReachableCachedValid ((identifier, some digest) :: rest) identifier digest
  | thereSome (headIdentifier : ι) (headDigest : Digest)
      (rest : List (ι × Option Digest)) (identifier : ι) (digest : Digest)
      (invalid : ¬ TargetSum.ValidDigest headDigest)
      (tail : ReachableCachedValid rest identifier digest) :
      ReachableCachedValid ((headIdentifier, some headDigest) :: rest) identifier digest
  | thereNone (headIdentifier : ι) (rest : List (ι × Option Digest))
      (identifier : ι) (digest : Digest)
      (tail : ReachableCachedValid rest identifier digest) :
      ReachableCachedValid ((headIdentifier, none) :: rest) identifier digest

theorem reachableCachedValid_cons_none_iff
    {ι : Type} [DecidableEq ι] (headIdentifier identifier : ι)
    (rest : List (ι × Option Digest)) (digest : Digest) :
    ReachableCachedValid ((headIdentifier, none) :: rest) identifier digest ↔
      ReachableCachedValid rest identifier digest := by
  constructor
  · intro hreach
    cases hreach with
    | thereNone _ _ _ _ htail => exact htail
  · exact ReachableCachedValid.thereNone headIdentifier rest identifier digest

theorem reachableCachedValid_cons_some_iff
    {ι : Type} [DecidableEq ι] (headIdentifier identifier : ι)
    (headDigest : Digest) (rest : List (ι × Option Digest)) (digest : Digest) :
    ReachableCachedValid ((headIdentifier, some headDigest) :: rest)
        identifier digest ↔
      (identifier = headIdentifier ∧ digest = headDigest ∧
        TargetSum.ValidDigest headDigest)
        ∨ (¬ TargetSum.ValidDigest headDigest ∧
          ReachableCachedValid rest identifier digest) := by
  constructor
  · intro hreach
    cases hreach with
    | here _ _ _ hvalid => exact Or.inl ⟨rfl, rfl, hvalid⟩
    | thereSome _ _ _ _ _ hinvalid htail => exact Or.inr ⟨hinvalid, htail⟩
  · rintro (⟨rfl, rfl, hvalid⟩ | ⟨hinvalid, htail⟩)
    · exact .here _ _ _ hvalid
    · exact .thereSome _ _ _ _ _ hinvalid htail

def HasCachedHit {ι : Type} [DecidableEq ι]
    (schedule : List (ι × Option Digest))
    (targets : Finset (ι × Digest)) : Prop :=
  ∃ identifier digest,
    ReachableCachedValid schedule identifier digest ∧
      selectedHits targets (some (identifier, digest))

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

theorem selectionRisk_le_pendingRisk_of_not_hasCachedHit
    {ι : Type} [DecidableEq ι]
    (schedule : List (ι × Option Digest)) (targets : Finset (ι × Digest))
    (hclean : ¬ HasCachedHit schedule targets) :
    selectionRisk schedule targets ≤
      EncodingRetry.pendingRisk (targetDigests targets) := by
  induction schedule with
  | nil =>
      rw [selectionRisk_nil]
      exact bot_le
  | cons head rest ih =>
      obtain ⟨identifier, digest⟩ := head
      cases digest with
      | some digest =>
          by_cases hvalid : TargetSum.ValidDigest digest
          · have hmiss : ¬ selectedHits targets (some (identifier, digest)) := by
              intro hhit
              exact hclean ⟨identifier, digest,
                .here identifier digest rest hvalid, hhit⟩
            rw [selectionRisk_cons_some_of_valid_of_miss _ _ _ _ hvalid hmiss]
            exact bot_le
          · rw [selectionRisk_cons_some_of_invalid _ _ _ _ hvalid]
            apply ih
            rintro ⟨selectedIdentifier, selectedDigest, hfirst, hhit⟩
            exact hclean ⟨selectedIdentifier, selectedDigest,
              .thereSome identifier digest rest selectedIdentifier selectedDigest
                hvalid hfirst, hhit⟩
      | none =>
          rw [selectionRisk_cons_none_eq]
          have htail : ¬ HasCachedHit rest targets := by
            rintro ⟨selectedIdentifier, selectedDigest, hfirst, hhit⟩
            exact hclean ⟨selectedIdentifier, selectedDigest,
              .thereNone identifier rest selectedIdentifier selectedDigest hfirst, hhit⟩
          calc
            _ ≤ ∑' output : HashOutput,
                Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
                  (if TargetSum.ValidDigest (truncateHash output) then
                    if truncateHash output ∈ targetDigests targets then 1 else 0
                  else EncodingRetry.pendingRisk (targetDigests targets)) := by
                apply ENNReal.tsum_le_tsum
                intro output
                apply mul_le_mul_right
                by_cases hvalid : TargetSum.ValidDigest (truncateHash output)
                · by_cases hhit : selectedHits targets
                      (some (identifier, truncateHash output))
                  · have hmem := digest_mem_targetDigests_of_selectedHits hhit
                    rw [selectionRisk_cons_some_of_valid_of_hit _ _ _ _ hvalid hhit,
                      if_pos hvalid, if_pos hmem]
                  · rw [selectionRisk_cons_some_of_valid_of_miss _ _ _ _ hvalid hhit,
                      if_pos hvalid]
                    split <;> simp
                · rw [selectionRisk_cons_some_of_invalid _ _ _ _ hvalid,
                    if_neg hvalid]
                  exact ih htail
            _ ≤ EncodingRetry.pendingRisk (targetDigests targets) :=
              SphincsSecurity.uniformHashOutput_select_bonus_sum_le
                (targetDigests targets)

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

theorem selectedHits_mono {ι : Type} [DecidableEq ι]
    {left right : Finset (ι × Digest)} (hsubset : left ⊆ right)
    {selected : Option (ι × Digest)}
    (hhit : selectedHits left selected) : selectedHits right selected := by
  cases selected with
  | none => exact hhit
  | some selected =>
      obtain ⟨candidate, hcandidate, hidentifier, hdigest⟩ := hhit
      exact ⟨candidate, hsubset hcandidate, hidentifier, hdigest⟩

theorem candidateTargets_subset {ι : Type} [DecidableEq ι]
    (identifier : ι) (targets : Finset (ι × Digest)) (output : HashOutput) :
    targets ⊆ candidateTargets identifier targets output := by
  intro candidate hcandidate
  rw [candidateTargets]
  split
  · exact Finset.mem_insert_of_mem hcandidate
  · exact hcandidate

theorem selectedHits_candidateTargets_self_iff
    {ι : Type} [DecidableEq ι] (identifier : ι)
    (targets : Finset (ι × Digest)) (output : HashOutput) :
    selectedHits (candidateTargets identifier targets output)
        (some (identifier, truncateHash output)) ↔
      selectedHits targets (some (identifier, truncateHash output)) := by
  constructor
  · intro hhit
    obtain ⟨candidate, hcandidate, hidentifier, hdigest⟩ := hhit
    rw [candidateTargets] at hcandidate
    split at hcandidate
    · rw [Finset.mem_insert] at hcandidate
      rcases hcandidate with heq | hold
      · subst candidate
        exact (hidentifier rfl).elim
      · exact ⟨candidate, hold, hidentifier, hdigest⟩
    · exact ⟨candidate, hcandidate, hidentifier, hdigest⟩
  · exact selectedHits_mono (candidateTargets_subset identifier targets output)

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

theorem candidatePair_oldRisk_le_newRisk {ι : Type} [DecidableEq ι]
    (identifier : ι) (schedule : List (ι × Option Digest))
    (targets : Finset (ι × Digest)) :
    selectionRisk schedule targets ≤
      Pr[fun pair => selectedHits
          (candidateTargets identifier targets pair.1) pair.2 |
        candidatePair schedule] := by
  rw [← candidatePair_oldRisk_eq schedule targets]
  apply probEvent_mono
  intro pair _ hold
  exact selectedHits_mono (candidateTargets_subset identifier targets pair.1) hold

theorem selectionRisk_reveal_head_candidate_eq
    {ι : Type} [DecidableEq ι] (identifier : ι)
    (rest : List (ι × Option Digest)) (targets : Finset (ι × Digest))
    (output : HashOutput) :
    selectionRisk ((identifier, some (truncateHash output)) :: rest)
        (candidateTargets identifier targets output) =
      selectionRisk ((identifier, some (truncateHash output)) :: rest) targets := by
  by_cases hvalid : TargetSum.ValidDigest (truncateHash output)
  · by_cases hhit : selectedHits targets (some (identifier, truncateHash output))
    · rw [selectionRisk_cons_some_of_valid_of_hit _ _ _ _ hvalid hhit,
        selectionRisk_cons_some_of_valid_of_hit _ _ _ _ hvalid
          ((selectedHits_candidateTargets_self_iff identifier targets output).2 hhit)]
    · rw [selectionRisk_cons_some_of_valid_of_miss _ _ _ _ hvalid hhit,
        selectionRisk_cons_some_of_valid_of_miss _ _ _ _ hvalid
          (fun hnew => hhit
            ((selectedHits_candidateTargets_self_iff identifier targets output).1 hnew))]
  · rw [selectionRisk_cons_some_of_invalid _ _ _ _ hvalid,
      selectionRisk_cons_some_of_invalid _ _ _ _ hvalid,
      candidateTargets, if_neg hvalid]

theorem uniform_reveal_head_candidate_sum_le_independent
    {ι : Type} [DecidableEq ι] (identifier : ι)
    (rest : List (ι × Option Digest)) (targets : Finset (ι × Digest)) :
    (∑' output : HashOutput,
      Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
        selectionRisk ((identifier, some (truncateHash output)) :: rest)
          (candidateTargets identifier targets output)) ≤
      Pr[fun pair => selectedHits
          (candidateTargets identifier targets pair.1) pair.2 |
        candidatePair ((identifier, none) :: rest)] := by
  rw [show (∑' output : HashOutput,
      Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
        selectionRisk ((identifier, some (truncateHash output)) :: rest)
          (candidateTargets identifier targets output)) =
      selectionRisk ((identifier, none) :: rest) targets by
        rw [selectionRisk_cons_none_eq]
        apply tsum_congr
        intro output
        rw [selectionRisk_reveal_head_candidate_eq]]
  exact candidatePair_oldRisk_le_newRisk identifier
    ((identifier, none) :: rest) targets

inductive InvalidPrefix {ι : Type} [DecidableEq ι] :
    List (ι × Option Digest) → Prop where
  | nil : InvalidPrefix []
  | cons (identifier : ι) (digest : Digest)
      (rest : List (ι × Option Digest))
      (invalid : ¬ TargetSum.ValidDigest digest)
      (tail : InvalidPrefix rest) :
      InvalidPrefix ((identifier, some digest) :: rest)

theorem InvalidPrefix.firstValid_append {ι : Type} [DecidableEq ι]
    {initial : List (ι × Option Digest)} (hinitial : InvalidPrefix initial)
    (identifier : ι) (digest : Digest) (rest : List (ι × Option Digest))
    (hvalid : TargetSum.ValidDigest digest) :
    FirstValid (initial ++ (identifier, some digest) :: rest) identifier digest := by
  induction hinitial with
  | nil => exact .here identifier digest rest hvalid
  | cons headIdentifier headDigest initial hinvalid _ ih =>
      rw [List.cons_append]
      exact .there headIdentifier headDigest _ identifier digest hinvalid ih

theorem InvalidPrefix.selectionRisk_append {ι : Type} [DecidableEq ι]
    {initial : List (ι × Option Digest)} (hinitial : InvalidPrefix initial)
    (suffix : List (ι × Option Digest)) (targets : Finset (ι × Digest)) :
    selectionRisk (initial ++ suffix) targets = selectionRisk suffix targets := by
  induction hinitial with
  | nil => rfl
  | cons identifier digest rest hinvalid htail ih =>
      rw [List.cons_append,
        selectionRisk_cons_some_of_invalid identifier digest _ targets hinvalid, ih]

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

theorem uniform_reveal_after_invalidPrefix_candidate_sum_le
    {ι : Type} [DecidableEq ι]
    {initial : List (ι × Option Digest)} (hinitial : InvalidPrefix initial)
    (identifier : ι) (rest : List (ι × Option Digest))
    (targets : Finset (ι × Digest)) :
    (∑' output : HashOutput,
      Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
        selectionRisk
          (initial ++ (identifier, some (truncateHash output)) :: rest)
          (candidateTargets identifier targets output)) ≤
      selectionRisk (initial ++ (identifier, none) :: rest) targets +
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  simp_rw [hinitial.selectionRisk_append]
  exact (uniform_reveal_head_candidate_sum_le_independent identifier rest targets).trans
    (candidatePair_newRisk_le identifier ((identifier, none) :: rest) targets)

theorem uniform_reveal_append_candidate_sum_le
    {ι : Type} [DecidableEq ι]
    (initial : List (ι × Option Digest)) (identifier : ι)
    (rest : List (ι × Option Digest)) (targets : Finset (ι × Digest)) :
    (∑' output : HashOutput,
      Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
        selectionRisk
          (initial ++ (identifier, some (truncateHash output)) :: rest)
          (candidateTargets identifier targets output)) ≤
      selectionRisk (initial ++ (identifier, none) :: rest) targets +
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  induction initial with
  | nil =>
      simpa using uniform_reveal_after_invalidPrefix_candidate_sum_le
        (InvalidPrefix.nil : InvalidPrefix ([] : List (ι × Option Digest)))
        identifier rest targets
  | cons head initial ih =>
      obtain ⟨headIdentifier, headDigest⟩ := head
      have validBound (digest : Digest) (hvalid : TargetSum.ValidDigest digest) :
          (∑' output : HashOutput,
            Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
              selectionRisk
                ((headIdentifier, some digest) ::
                  (initial ++ (identifier, some (truncateHash output)) :: rest))
                (candidateTargets identifier targets output)) ≤
            selectionRisk
                ((headIdentifier, some digest) ::
                  (initial ++ (identifier, none) :: rest)) targets +
              (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
        calc
          _ = ∑' output : HashOutput,
              Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
                selectionRisk [(headIdentifier, some digest)]
                  (candidateTargets identifier targets output) := by
              apply tsum_congr
              intro output
              congr 1
              exact selectionRisk_cons_some_of_valid_suffix_eq
                headIdentifier digest _ _ _ hvalid
          _ ≤ selectionRisk [(headIdentifier, some digest)] targets +
                (Fintype.card Digest : ℝ≥0∞)⁻¹ :=
              uniform_candidateTargets_selectionRisk_sum_le identifier
                [(headIdentifier, some digest)] targets
          _ = _ := by
              congr 1
              exact selectionRisk_cons_some_of_valid_suffix_eq
                headIdentifier digest _ _ _ hvalid
      cases headDigest with
      | some digest =>
          by_cases hvalid : TargetSum.ValidDigest digest
          · simpa only [List.cons_append] using validBound digest hvalid
          · simp_rw [List.cons_append,
              selectionRisk_cons_some_of_invalid _ _ _ _ hvalid]
            exact ih
      | none =>
          have conditionalBound (headOutput : HashOutput) :
              (∑' output : HashOutput,
                Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
                  selectionRisk
                    ((headIdentifier, some (truncateHash headOutput)) ::
                      (initial ++ (identifier, some (truncateHash output)) :: rest))
                    (candidateTargets identifier targets output)) ≤
                selectionRisk
                    ((headIdentifier, some (truncateHash headOutput)) ::
                      (initial ++ (identifier, none) :: rest)) targets +
                  (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
            by_cases hvalid : TargetSum.ValidDigest (truncateHash headOutput)
            · exact validBound (truncateHash headOutput) hvalid
            · simp_rw [selectionRisk_cons_some_of_invalid _ _ _ _ hvalid]
              exact ih
          simp_rw [List.cons_append, selectionRisk_cons_none_eq]
          calc
            _ = ∑' headOutput : HashOutput,
                Pr[= headOutput | ($ᵗ HashOutput : ProbComp HashOutput)] *
                  (∑' output : HashOutput,
                    Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
                      selectionRisk
                        ((headIdentifier, some (truncateHash headOutput)) ::
                          (initial ++
                            (identifier, some (truncateHash output)) :: rest))
                        (candidateTargets identifier targets output)) := by
                simp_rw [← ENNReal.tsum_mul_left]
                rw [ENNReal.tsum_comm]
                apply tsum_congr
                intro headOutput
                simp_rw [mul_left_comm]
            _ ≤ ∑' headOutput : HashOutput,
                Pr[= headOutput | ($ᵗ HashOutput : ProbComp HashOutput)] *
                  (selectionRisk
                      ((headIdentifier, some (truncateHash headOutput)) ::
                        (initial ++ (identifier, none) :: rest)) targets +
                    (Fintype.card Digest : ℝ≥0∞)⁻¹) := by
                apply ENNReal.tsum_le_tsum
                intro headOutput
                exact mul_le_mul_right (conditionalBound headOutput) _
            _ = (∑' headOutput : HashOutput,
                  Pr[= headOutput | ($ᵗ HashOutput : ProbComp HashOutput)] *
                    selectionRisk
                      ((headIdentifier, some (truncateHash headOutput)) ::
                        (initial ++ (identifier, none) :: rest)) targets) +
                  (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
                simp_rw [mul_add]
                rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
                  tsum_probOutput_of_liftM_PMF, one_mul]
            _ = _ := rfl

end SphincsSecurity.EncodingSelection
