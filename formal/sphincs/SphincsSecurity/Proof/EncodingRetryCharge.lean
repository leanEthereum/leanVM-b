import SphincsSecurity.Proof.EncodingCharge
import SphincsSecurity.Proof.EncodingRetry

/-!
# Cache potential for encoding retries

At an encoding position without a canonical target, every distinct admissible digest already in the
cache is pending risk. Pinning the target consumes the whole contribution at that position.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

def encodingValidAnswers (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (position : EncodingPosition) : Set Digest :=
  {digest | TargetSum.ValidDigest digest ∧
    ∃ input answer, cache input = some answer ∧
      AtEncodingPosition parameter input position ∧ truncateHash answer = digest}

theorem encodingValidAnswers_finite {parameter : PublicParameter}
    {cache : QueryCache HashSpec} (hfinite : Finite cache) (position : EncodingPosition) :
    (encodingValidAnswers parameter cache position).Finite := by
  let answers : Set HashOutput := {answer | ∃ input, cache input = some answer ∧
    AtEncodingPosition parameter input position}
  have hanswers : answers.Finite := by
    let cachedInputs : Set HashInput := {input | cache input ≠ none}
    have hcachedInputs : cachedInputs.Finite := hfinite
    let answerOf : HashInput → HashOutput := fun input => (cache input).getD 0
    apply (hcachedInputs.image answerOf).subset
    rintro answer ⟨input, hcached, hposition⟩
    refine ⟨input, by simp [cachedInputs, hcached], ?_⟩
    simp [answerOf, hcached]
  apply (hanswers.image truncateHash).subset
  rintro digest ⟨_, input, answer, hcached, hposition, rfl⟩
  exact ⟨answer, ⟨input, hcached, hposition⟩, rfl⟩

theorem encodingValidAnswers_eq_validAnswerTargets {parameter : PublicParameter}
    {cache : QueryCache HashSpec} (hfinite : Finite cache) (position : EncodingPosition) :
    encodingValidAnswers parameter cache position =
      ↑(encodingValidAnswerTargets parameter cache hfinite position) := by
  ext digest
  constructor
  · rintro ⟨hvalid, input, answer, hcached, hposition, rfl⟩
    exact cachedValidAnswer_mem_encodingValidAnswerTargets hfinite hcached hposition hvalid
  · intro hmem
    change digest ∈ encodingValidAnswerTargets parameter cache hfinite position at hmem
    rw [encodingValidAnswerTargets, Finset.mem_filter, encodingAnswerTargets,
      Finset.mem_image] at hmem
    obtain ⟨⟨input, hinput, hdigest⟩, hvalid⟩ := hmem
    rw [Set.Finite.mem_toFinset] at hinput
    obtain ⟨hcached, hposition⟩ := hinput
    obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hcached
    refine ⟨hvalid, input, answer, hanswer, hposition, ?_⟩
    simpa only [fromCache, hanswer, Option.getD_some] using hdigest

theorem encodingValidAnswers_ncard_eq_validAnswerTargets_card
    {parameter : PublicParameter} {cache : QueryCache HashSpec}
    (hfinite : Finite cache) (position : EncodingPosition) :
    (encodingValidAnswers parameter cache position).ncard =
      (encodingValidAnswerTargets parameter cache hfinite position).card := by
  rw [encodingValidAnswers_eq_validAnswerTargets hfinite position, Set.ncard_coe_finset]

theorem encodingValidAnswers_mono {parameter : PublicParameter}
    {cache cache' : QueryCache HashSpec} (hle : cache ≤ cache')
    (position : EncodingPosition) :
    encodingValidAnswers parameter cache position ⊆
      encodingValidAnswers parameter cache' position := by
  rintro digest ⟨hvalid, input, answer, hcached, hposition, hdigest⟩
  exact ⟨hvalid, input, answer, hle hcached, hposition, hdigest⟩

theorem encodingValidAnswers_cacheQuery_subset_insert
    {parameter : PublicParameter} {cache : QueryCache HashSpec}
    {input : HashInput} {answer : HashOutput} (position : EncodingPosition) :
    encodingValidAnswers parameter (cache.cacheQuery input answer) position ⊆
      insert (truncateHash answer) (encodingValidAnswers parameter cache position) := by
  rintro digest ⟨hvalid, cachedInput, cachedAnswer, hcached, hposition, hdigest⟩
  by_cases heq : cachedInput = input
  · subst cachedInput
    have hanswer : cachedAnswer = answer := by
      rw [QueryCache.cacheQuery_self] at hcached
      exact Option.some.inj hcached.symm
    subst cachedAnswer
    exact Set.mem_insert_iff.mpr (Or.inl hdigest.symm)
  · apply Set.mem_insert_of_mem
    exact ⟨hvalid, cachedInput, cachedAnswer, by
      rwa [QueryCache.cacheQuery_of_ne _ _ heq] at hcached, hposition, hdigest⟩

theorem encodingValidAnswers_cacheQuery_ncard_le
    {parameter : PublicParameter} {cache : QueryCache HashSpec}
    (hfinite : Finite cache) {input : HashInput} {answer : HashOutput}
    (position : EncodingPosition) :
    (encodingValidAnswers parameter (cache.cacheQuery input answer) position).ncard ≤
      (encodingValidAnswers parameter cache position).ncard + 1 := by
  have hold := encodingValidAnswers_finite (parameter := parameter) hfinite position
  exact (Set.ncard_le_ncard
    (encodingValidAnswers_cacheQuery_subset_insert position) (hold.insert _)).trans
      (Set.ncard_insert_le _ _)

theorem encodingValidAnswers_cacheQuery_eq_of_not_atPosition
    {parameter : PublicParameter} {cache : QueryCache HashSpec}
    {input : HashInput} {answer : HashOutput} (huncached : cache input = none)
    (position : EncodingPosition)
    (hnotAt : ¬ AtEncodingPosition parameter input position) :
    encodingValidAnswers parameter (cache.cacheQuery input answer) position =
      encodingValidAnswers parameter cache position := by
  apply Set.Subset.antisymm
  · rintro digest ⟨hvalid, cachedInput, cachedAnswer, hcached, hposition, hdigest⟩
    have hne : cachedInput ≠ input := by
      intro heq
      subst cachedInput
      exact hnotAt hposition
    exact ⟨hvalid, cachedInput, cachedAnswer, by
      rwa [QueryCache.cacheQuery_of_ne _ _ hne] at hcached, hposition, hdigest⟩
  · exact encodingValidAnswers_mono
      (le_cacheQuery (cache := cache) (input := input) (answer := answer) huncached) position

theorem encodingValidAnswers_cacheQuery_eq_of_invalid
    {parameter : PublicParameter} {cache : QueryCache HashSpec}
    {input : HashInput} {answer : HashOutput} (huncached : cache input = none)
    (position : EncodingPosition)
    (hinvalid : ¬ TargetSum.ValidDigest (truncateHash answer)) :
    encodingValidAnswers parameter (cache.cacheQuery input answer) position =
      encodingValidAnswers parameter cache position := by
  apply Set.Subset.antisymm
  · rintro digest ⟨hvalid, cachedInput, cachedAnswer, hcached, hposition, hdigest⟩
    have hne : cachedInput ≠ input := by
      intro heq
      subst cachedInput
      have hanswer : cachedAnswer = answer := by
        rw [QueryCache.cacheQuery_self] at hcached
        exact Option.some.inj hcached.symm
      subst cachedAnswer
      exact hinvalid (hdigest ▸ hvalid)
    exact ⟨hvalid, cachedInput, cachedAnswer, by
      rwa [QueryCache.cacheQuery_of_ne _ _ hne] at hcached, hposition, hdigest⟩
  · exact encodingValidAnswers_mono
      (le_cacheQuery (cache := cache) (input := input) (answer := answer) huncached) position

noncomputable def encodingRetryContribution (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (position : EncodingPosition) : ℝ≥0∞ :=
  open Classical in
    if HasEncodingTarget cache secretKey position then 0
    else ((encodingValidAnswers secretKey.parameter cache position).ncard : ℝ≥0∞) *
      (TargetSum.validDigests.card : ℝ≥0∞)⁻¹

noncomputable def encodingRetryPotential (cache : QueryCache HashSpec)
    (secretKey : SecretKey) : ℝ≥0∞ :=
  ∑ position : EncodingPosition, encodingRetryContribution cache secretKey position

theorem encodingRetryContribution_eq_zero_of_target
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {position : EncodingPosition}
    (htarget : HasEncodingTarget cache secretKey position) :
    encodingRetryContribution cache secretKey position = 0 := by
  classical
  rw [encodingRetryContribution, if_pos htarget]

theorem encodingRetryContribution_eq_pendingRisk
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {position : EncodingPosition}
    (hnotTarget : ¬ HasEncodingTarget cache secretKey position) :
    encodingRetryContribution cache secretKey position =
      EncodingRetry.pendingRisk
        (encodingValidAnswerTargets secretKey.parameter cache hfinite position) := by
  classical
  rw [encodingRetryContribution, if_neg hnotTarget, EncodingRetry.pendingRisk,
    encodingValidAnswers_ncard_eq_validAnswerTargets_card hfinite position]

theorem encodingRetryContribution_cacheQuery_le_of_not_atPosition
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {input : HashInput} {answer : HashOutput} (huncached : cache input = none)
    (position : EncodingPosition)
    (hnotAt : ¬ AtEncodingPosition secretKey.parameter input position) :
    encodingRetryContribution (cache.cacheQuery input answer) secretKey position ≤
      encodingRetryContribution cache secretKey position := by
  classical
  have hle := le_cacheQuery (cache := cache) (input := input) (answer := answer) huncached
  rw [encodingRetryContribution, encodingRetryContribution]
  by_cases htarget : HasEncodingTarget cache secretKey position
  · rw [if_pos htarget, if_pos (htarget.mono hle)]
  · rw [if_neg htarget]
    by_cases htarget' : HasEncodingTarget (cache.cacheQuery input answer) secretKey position
    · rw [if_pos htarget']
      exact bot_le
    · rw [if_neg htarget', encodingValidAnswers_cacheQuery_eq_of_not_atPosition
        huncached position hnotAt]

theorem encodingRetryContribution_cacheQuery_le
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {secretKey : SecretKey}
    {input : HashInput} {answer : HashOutput} (huncached : cache input = none)
    (position : EncodingPosition) :
    encodingRetryContribution (cache.cacheQuery input answer) secretKey position ≤
      encodingRetryContribution cache secretKey position +
        if TargetSum.ValidDigest (truncateHash answer) then
          (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ else 0 := by
  classical
  have hle := le_cacheQuery (cache := cache) (input := input) (answer := answer) huncached
  rw [encodingRetryContribution, encodingRetryContribution]
  by_cases htarget : HasEncodingTarget cache secretKey position
  · rw [if_pos htarget, if_pos (htarget.mono hle)]
    exact bot_le
  · rw [if_neg htarget]
    by_cases htarget' : HasEncodingTarget (cache.cacheQuery input answer) secretKey position
    · rw [if_pos htarget']
      exact bot_le
    · rw [if_neg htarget']
      by_cases hvalid : TargetSum.ValidDigest (truncateHash answer)
      · rw [if_pos hvalid]
        calc
          ((encodingValidAnswers secretKey.parameter
              (cache.cacheQuery input answer) position).ncard : ℝ≥0∞) *
                (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ ≤
            (((encodingValidAnswers secretKey.parameter cache position).ncard + 1 : Nat) :
              ℝ≥0∞) * (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ := by
                gcongr
                exact_mod_cast encodingValidAnswers_cacheQuery_ncard_le hfinite position
          _ = ((encodingValidAnswers secretKey.parameter cache position).ncard : ℝ≥0∞) *
                (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ +
              (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ := by
                push_cast
                rw [add_mul, one_mul]
      · rw [if_neg hvalid, add_zero,
          encodingValidAnswers_cacheQuery_eq_of_invalid huncached position hvalid]

theorem encodingRetryPotential_cacheQuery_le
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {secretKey : SecretKey}
    {input : HashInput} {answer : HashOutput} (huncached : cache input = none) :
    encodingRetryPotential (cache.cacheQuery input answer) secretKey ≤
      encodingRetryPotential cache secretKey +
        if TargetSum.ValidDigest (truncateHash answer) then
          (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ else 0 := by
  classical
  by_cases hat : ∃ position, AtEncodingPosition secretKey.parameter input position
  · obtain ⟨queriedPosition, hqueried⟩ := hat
    rw [encodingRetryPotential, encodingRetryPotential]
    calc
      ∑ position : EncodingPosition,
          encodingRetryContribution (cache.cacheQuery input answer) secretKey position ≤
        ∑ position : EncodingPosition,
          (encodingRetryContribution cache secretKey position +
            if position = queriedPosition then
              (if TargetSum.ValidDigest (truncateHash answer) then
                (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ else 0) else 0) := by
          apply Finset.sum_le_sum
          intro position _
          by_cases heq : position = queriedPosition
          · rw [if_pos heq]
            exact encodingRetryContribution_cacheQuery_le hfinite huncached position
          · rw [if_neg heq, add_zero]
            apply encodingRetryContribution_cacheQuery_le_of_not_atPosition huncached position
            intro hposition
            exact heq (atEncodingPosition_unique hposition hqueried)
      _ = (∑ position : EncodingPosition,
          encodingRetryContribution cache secretKey position) +
            if TargetSum.ValidDigest (truncateHash answer) then
              (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ else 0 := by
          rw [Finset.sum_add_distrib, Fintype.sum_ite_eq']
  · rw [encodingRetryPotential, encodingRetryPotential]
    calc
      ∑ position : EncodingPosition,
          encodingRetryContribution (cache.cacheQuery input answer) secretKey position ≤
        ∑ position : EncodingPosition,
          encodingRetryContribution cache secretKey position := by
            apply Finset.sum_le_sum
            intro position _
            exact encodingRetryContribution_cacheQuery_le_of_not_atPosition huncached position
              (fun hposition => hat ⟨position, hposition⟩)
      _ ≤ _ := le_add_right le_rfl

theorem encodingRetryPotential_add_contribution_le_of_new_target
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {input : HashInput} {answer : HashOutput} {position : EncodingPosition}
    (huncached : cache input = none)
    (hnotTarget : ¬ HasEncodingTarget cache secretKey position)
    (htarget : HasEncodingTarget (cache.cacheQuery input answer) secretKey position) :
    encodingRetryPotential (cache.cacheQuery input answer) secretKey +
        encodingRetryContribution cache secretKey position ≤
      encodingRetryPotential cache secretKey := by
  classical
  have hother : ∀ otherPosition : EncodingPosition, otherPosition ≠ position →
      encodingRetryContribution (cache.cacheQuery input answer) secretKey otherPosition ≤
        encodingRetryContribution cache secretKey otherPosition := by
    intro otherPosition hne
    apply encodingRetryContribution_cacheQuery_le_of_not_atPosition huncached otherPosition
    intro hinput
    have htargetOld := htarget.of_cacheQuery_of_other_encodingPosition huncached hinput
      hne
    exact hnotTarget htargetOld
  rw [encodingRetryPotential, encodingRetryPotential]
  calc
    (∑ otherPosition : EncodingPosition,
        encodingRetryContribution (cache.cacheQuery input answer) secretKey otherPosition) +
        encodingRetryContribution cache secretKey position =
      ∑ otherPosition : EncodingPosition,
        (encodingRetryContribution (cache.cacheQuery input answer) secretKey otherPosition +
          if otherPosition = position then
            encodingRetryContribution cache secretKey position else 0) := by
      rw [Finset.sum_add_distrib, Fintype.sum_ite_eq']
    _ ≤ ∑ otherPosition : EncodingPosition,
        encodingRetryContribution cache secretKey otherPosition := by
      apply Finset.sum_le_sum
      intro otherPosition _
      by_cases heq : otherPosition = position
      · have htargetOther :
            HasEncodingTarget (cache.cacheQuery input answer) secretKey otherPosition :=
          heq.symm ▸ htarget
        have hzero := encodingRetryContribution_eq_zero_of_target htargetOther
        exact le_of_eq <| calc
          encodingRetryContribution (cache.cacheQuery input answer) secretKey otherPosition +
              (if otherPosition = position then
                encodingRetryContribution cache secretKey position else 0) =
            encodingRetryContribution (cache.cacheQuery input answer) secretKey otherPosition +
              encodingRetryContribution cache secretKey position := by
                exact congrArg _ (if_pos heq)
          _ = 0 + encodingRetryContribution cache secretKey position :=
            congrArg (fun value => value + encodingRetryContribution cache secretKey position)
              hzero
          _ = encodingRetryContribution cache secretKey position := zero_add _
          _ = encodingRetryContribution cache secretKey otherPosition :=
            congrArg (fun selectedPosition =>
              encodingRetryContribution cache secretKey selectedPosition) heq.symm
      · calc
          encodingRetryContribution (cache.cacheQuery input answer) secretKey otherPosition +
              (if otherPosition = position then
                encodingRetryContribution cache secretKey position else 0) =
            encodingRetryContribution (cache.cacheQuery input answer) secretKey otherPosition +
              0 := congrArg _ (if_neg heq)
          _ = encodingRetryContribution (cache.cacheQuery input answer) secretKey otherPosition :=
            add_zero _
          _ ≤ encodingRetryContribution cache secretKey otherPosition :=
            hother otherPosition heq

theorem encodingRetryPotential_add_pendingRisk_le_of_new_target
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {secretKey : SecretKey}
    {input : HashInput} {answer : HashOutput} {position : EncodingPosition}
    (huncached : cache input = none)
    (hnotTarget : ¬ HasEncodingTarget cache secretKey position)
    (htarget : HasEncodingTarget (cache.cacheQuery input answer) secretKey position) :
    encodingRetryPotential (cache.cacheQuery input answer) secretKey +
        EncodingRetry.pendingRisk
          (encodingValidAnswerTargets secretKey.parameter cache hfinite position) ≤
      encodingRetryPotential cache secretKey := by
  rw [← encodingRetryContribution_eq_pendingRisk hfinite hnotTarget]
  exact encodingRetryPotential_add_contribution_le_of_new_target huncached hnotTarget htarget

theorem uniformHashOutput_retryPotential_cacheQuery_sum_le
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {secretKey : SecretKey}
    {input : HashInput} (huncached : cache input = none) :
    ∑' answer : HashOutput,
        Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
          encodingRetryPotential (cache.cacheQuery input answer) secretKey ≤
      encodingRetryPotential cache secretKey +
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  calc
    _ ≤ ∑' answer : HashOutput,
        Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (encodingRetryPotential cache secretKey +
            if TargetSum.ValidDigest (truncateHash answer) then
              (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ else 0) := by
      apply ENNReal.tsum_le_tsum
      intro answer
      gcongr
      exact encodingRetryPotential_cacheQuery_le hfinite huncached
    _ = encodingRetryPotential cache secretKey +
        ∑' answer : HashOutput,
          Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
            (if TargetSum.ValidDigest (truncateHash answer) then
              (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ else 0) := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
        tsum_probOutput_of_liftM_PMF, one_mul]
    _ = _ := by
      rw [uniformHashOutput_valid_bonus_sum_eq]

@[simp] theorem encodingValidAnswers_empty (parameter : PublicParameter)
    (position : EncodingPosition) : encodingValidAnswers parameter ∅ position = ∅ := by
  ext digest
  simp [encodingValidAnswers]

@[simp] theorem encodingRetryContribution_empty (secretKey : SecretKey)
    (position : EncodingPosition) : encodingRetryContribution ∅ secretKey position = 0 := by
  rw [encodingRetryContribution, if_neg]
  · rw [encodingValidAnswers_empty, Set.ncard_empty, Nat.cast_zero, zero_mul]
  · rintro ⟨payload, _, _, _, _, _, _, _, _, hcached⟩
    simp at hcached

@[simp] theorem encodingRetryPotential_empty (secretKey : SecretKey) :
    encodingRetryPotential ∅ secretKey = 0 := by
  rw [encodingRetryPotential]
  simp

end SphincsSecurity.Concrete
