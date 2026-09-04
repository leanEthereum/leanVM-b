import SphincsSecurity.Proof.TightEncodingSettlement
import SphincsSecurity.Proof.TightChargeStep

namespace SphincsSecurity.Concrete.TightEncoding

open OracleComp OracleSpec ENNReal

noncomputable def encodingStructuralPotential (cache : QueryCache HashSpec)
    (secretKey : SecretKey) : Nat :=
  tightPotential secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache +
    encodingStagePotential cache secretKey

@[simp] theorem encodingStructuralPotential_empty (secretKey : SecretKey) :
    encodingStructuralPotential ∅ secretKey = 0 := by
  rw [encodingStructuralPotential, tightPotential_empty, encodingStagePotential_empty,
    Nat.zero_add]

/-- Joint structural and encoding risk; a structural collision saturates the potential. -/
noncomputable def encodingSelectionTotalPotential
    (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (secretKey : SecretKey) : ℝ≥0∞ :=
  open Classical in
  if Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache then 1
  else min 1 ((encodingStructuralPotential cache secretKey : ℝ≥0∞) *
      (Fintype.card Digest : ℝ≥0∞)⁻¹ +
    encodingSelectionPotential cache hfinite secretKey)

theorem encodingSelection_hasCachedHit_mem_settlingTargets_of_prematureSettlement
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    {position : EncodingPosition} {index : Index} {queriedPosition : Position}
    (huncached : cache input = none)
    (htree : treeIndexAt index position.lay = position.tree)
    (hleaf : leafIndexAt index position.lay = position.leafIdx)
    (hunsettled : ¬ Settled secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret cache (layerMessagePosition index position.lay))
    (hsettled : Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
      (cache.cacheQuery input answer) (layerMessagePosition index position.lay))
    (hnotMessage : ¬ AtPosition secretKey.parameter input
      (layerMessagePosition index position.lay))
    (hqueried : AtPosition secretKey.parameter input queriedPosition)
    (hhit : EncodingSelection.HasCachedHit
      (encodingRetrySchedule secretKey.parameter (cache.cacheQuery input answer)
        position (encodingSettledMessage (cache.cacheQuery input answer) secretKey position))
      (encodingSelectionCandidates secretKey.parameter (cache.cacheQuery input answer)
        (finite_cacheQuery hfinite input answer) position)) :
    truncateHash answer ∈
      tightSettlingTargets secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache hfinite queriedPosition := by
  have hbad := latentEncodingBadAt_of_newlySettled_of_encodingSelection_hasCachedHit
    hfinite (show EncodingMessageSettledAt
      (cache.cacheQuery input answer) secretKey position from
        ⟨index, htree, hleaf, hsettled⟩) hhit
  obtain ⟨targetIndex, counter, targetPayload, otherPayload, targetAnswer,
    otherAnswer, htargetTree, htargetLeaf, htargetSettled, hpayload,
    htargetAnswer, htargetValid, hbefore, hpayloadNe, hotherAnswer,
    hcollision⟩ := hbad
  have hmessagePosition : layerMessagePosition index position.lay =
      layerMessagePosition targetIndex position.lay :=
    layerMessagePosition_eq_of_position_eq index targetIndex position.lay
      (htree.trans htargetTree.symm) (hleaf.trans htargetLeaf.symm)
  have hpremature : PrematureLayerMessageSettlement cache secretKey input answer :=
    ⟨position, targetIndex, htargetTree, htargetLeaf,
      by rwa [← hmessagePosition], htargetSettled,
      by rwa [← hmessagePosition]⟩
  obtain ⟨candidate, hcandidate, _, _, hmem⟩ :=
      hpremature.mem_tightSettlingTargets hfinite huncached
  have heq : candidate = queriedPosition :=
    atPosition_unique secretKey.parameter hcandidate hqueried
  simpa only [heq] using hmem

theorem encodingSelectionPotential_cacheQuery_le_of_avoids_settlementTargets
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    {queriedPosition : Position}
    (huncached : cache input = none)
    (hqueried : AtPosition secretKey.parameter input queriedPosition)
    (havoidMessage : ∀ (position : EncodingPosition) (index : Index),
      treeIndexAt index position.lay = position.tree →
      leafIndexAt index position.lay = position.leafIdx →
      AtPosition secretKey.parameter input (layerMessagePosition index position.lay) →
      truncateHash answer ∉
        encodingMessageTargets secretKey.parameter cache hfinite position)
    (havoidSettling : truncateHash answer ∉
      tightSettlingTargets secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache hfinite queriedPosition) :
    encodingSelectionPotential (cache.cacheQuery input answer)
        (finite_cacheQuery hfinite input answer) secretKey ≤
      encodingSelectionPotential cache hfinite secretKey := by
  rw [encodingSelectionPotential, encodingSelectionPotential]
  apply Finset.sum_le_sum
  intro position _
  have hnotAt : ¬ AtEncodingPosition secretKey.parameter input position :=
    fun hencoding => hencoding.not_atPosition queriedPosition hqueried
  by_cases hmessageSettled : EncodingMessageSettledAt cache secretKey position
  · exact le_of_eq
      (encodingSelectionContribution_cacheQuery_eq_of_settled_of_not_atPosition
        hfinite huncached hmessageSettled hnotAt)
  · by_cases hmessageSettledAfter : EncodingMessageSettledAt
        (cache.cacheQuery input answer) secretKey position
    · by_cases hhit : EncodingSelection.HasCachedHit
          (encodingRetrySchedule secretKey.parameter (cache.cacheQuery input answer)
            position (encodingSettledMessage (cache.cacheQuery input answer) secretKey position))
          (encodingSelectionCandidates secretKey.parameter (cache.cacheQuery input answer)
            (finite_cacheQuery hfinite input answer) position)
      · obtain ⟨index, htree, hleaf, hsettled⟩ :=
          (show EncodingMessageSettledAt
            (cache.cacheQuery input answer) secretKey position from hmessageSettledAfter)
        have hunsettled : ¬ Settled secretKey.parameter secretKey.otsSecret
            secretKey.ftsSecret cache (layerMessagePosition index position.lay) := by
          intro hposition
          exact hmessageSettled ⟨index, htree, hleaf, hposition⟩
        by_cases hmessage : AtPosition secretKey.parameter input
            (layerMessagePosition index position.lay)
        · exact (havoidMessage position index htree hleaf hmessage
            (encodingSelection_hasCachedHit_mem_messageTargets_of_newlySettled
              hfinite huncached htree hleaf hunsettled hsettled hmessage hhit)).elim
        · exact (havoidSettling
            (encodingSelection_hasCachedHit_mem_settlingTargets_of_prematureSettlement
              hfinite huncached htree hleaf hunsettled hsettled hmessage hqueried hhit)).elim
      · exact encodingSelectionContribution_cacheQuery_le_of_newlySettled_of_not_hasCachedHit
          hfinite hmessageSettled hmessageSettledAfter hnotAt hhit
    · exact
        encodingSelectionContribution_cacheQuery_le_of_unsettled_of_stillUnsettled_of_not_atPosition
          hfinite huncached hmessageSettled hmessageSettledAfter hnotAt

theorem encodingStructuralPotential_cacheQuery_le_of_atEncoding
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {input : HashInput} {answer : HashOutput} {position : EncodingPosition}
    (hclean : ¬ Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache)
    (huncached : cache input = none)
    (hposition : AtEncodingPosition secretKey.parameter input position) :
    encodingStructuralPotential (cache.cacheQuery input answer) secretKey ≤
      encodingStructuralPotential cache secretKey + 2 := by
  have hstructural :=
    (clean_and_tightPotential_cacheQuery_of_not_atPosition secretKey.parameter
      secretKey.otsSecret secretKey.ftsSecret (answer := answer) hclean huncached
      (fun structuralPosition hat =>
        hposition.not_atPosition structuralPosition hat)).2
  have hencoding := encodingStagePotential_cacheQuery_le
    (secretKey := secretKey) (answer := answer) huncached
  rw [encodingStructuralPotential, encodingStructuralPotential]
  omega

theorem encodingSelectionTotalPotential_eq_one_of_clean_of_encodingBad
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey}
    (hclean : ¬ Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache)
    (hbad : EncodingBad cache secretKey) :
    encodingSelectionTotalPotential cache hfinite secretKey = 1 := by
  rw [encodingSelectionTotalPotential, if_neg hclean, min_eq_left]
  exact (one_le_encodingSelectionPotential_of_encodingBad hfinite hbad).trans
    (le_add_left le_rfl)

theorem encodingSelectionTotalPotential_eq_one_of_bad_or_encodingBad
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {secretKey : SecretKey}
    (hevent : Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache ∨
      EncodingBad cache secretKey) :
    encodingSelectionTotalPotential cache hfinite secretKey = 1 := by
  by_cases hbad : Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
  · rw [encodingSelectionTotalPotential, if_pos hbad]
  · exact encodingSelectionTotalPotential_eq_one_of_clean_of_encodingBad
      hfinite hbad (hevent.resolve_left hbad)

theorem encodingSelectionTotalPotential_le_one
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    (secretKey : SecretKey) :
    encodingSelectionTotalPotential cache hfinite secretKey ≤ 1 := by
  rw [encodingSelectionTotalPotential]
  split
  · exact le_rfl
  · exact min_le_left _ _

theorem encodingSelectionTotalPotential_le_uncapped
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    (secretKey : SecretKey)
    (hclean : ¬Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache) :
    encodingSelectionTotalPotential cache hfinite secretKey ≤
      (encodingStructuralPotential cache secretKey : ℝ≥0∞) *
          (Fintype.card Digest : ℝ≥0∞)⁻¹ +
        encodingSelectionPotential cache hfinite secretKey := by
  rw [encodingSelectionTotalPotential, if_neg hclean]
  exact min_le_right _ _

theorem expected_encodingSelectionTotalPotential_le_one
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    (secretKey : SecretKey) (input : HashInput) :
    (∑' answer : HashOutput,
      Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        encodingSelectionTotalPotential (cache.cacheQuery input answer)
          (finite_cacheQuery hfinite input answer) secretKey) ≤ 1 := by
  calc
    _ ≤ ∑' answer : HashOutput,
        Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] * 1 := by
      apply ENNReal.tsum_le_tsum
      intro answer
      exact mul_le_mul_right (encodingSelectionTotalPotential_le_one _ secretKey) _
    _ = 1 := by simp only [mul_one, tsum_probOutput_of_liftM_PMF]

theorem uniform_encodingSelectionTotalPotential_cacheQuery_atPosition_sum_le
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {position : EncodingPosition}
    (huncached : cache input = none)
    (hposition : AtEncodingPosition secretKey.parameter input position) :
    (∑' answer : HashOutput,
      Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        encodingSelectionTotalPotential (cache.cacheQuery input answer)
          (finite_cacheQuery hfinite input answer) secretKey) ≤
      encodingSelectionTotalPotential cache hfinite secretKey +
        3 * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  let eps := (Fintype.card Digest : ℝ≥0∞)⁻¹
  by_cases hbad : Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
  · have hbefore : encodingSelectionTotalPotential cache hfinite secretKey = 1 := by
      rw [encodingSelectionTotalPotential, if_pos hbad]
    rw [hbefore]
    exact (expected_encodingSelectionTotalPotential_le_one hfinite secretKey input).trans
      (le_add_right le_rfl)
  · let uncapped := (encodingStructuralPotential cache secretKey : ℝ≥0∞) * eps +
      encodingSelectionPotential cache hfinite secretKey
    by_cases hone : 1 ≤ uncapped
    · calc
        _ ≤ ∑' answer : HashOutput,
            Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] * 1 := by
              apply ENNReal.tsum_le_tsum
              intro answer
              exact mul_le_mul_right
                (encodingSelectionTotalPotential_le_one _ secretKey) _
        _ = 1 := by
              simp only [mul_one, tsum_probOutput_of_liftM_PMF]
        _ = encodingSelectionTotalPotential cache hfinite secretKey := by
              rw [encodingSelectionTotalPotential, if_neg hbad, min_eq_left]
              simpa only [uncapped] using hone
        _ ≤ encodingSelectionTotalPotential cache hfinite secretKey + 3 * eps :=
              le_add_right le_rfl
    · have huncappedLe : uncapped ≤ 1 := le_of_not_ge hone
      have hbefore : encodingSelectionTotalPotential cache hfinite secretKey = uncapped := by
        rw [encodingSelectionTotalPotential, if_neg hbad, min_eq_right]
        exact huncappedLe
      calc
        _ ≤ ∑' answer : HashOutput,
            Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
              (((encodingStructuralPotential cache secretKey + 2 : Nat) : ℝ≥0∞) * eps +
                encodingSelectionPotential (cache.cacheQuery input answer)
                  (finite_cacheQuery hfinite input answer) secretKey) := by
              apply ENNReal.tsum_le_tsum
              intro answer
              apply mul_le_mul_right
              have hcleanAfter :=
                (clean_and_tightPotential_cacheQuery_of_not_atPosition secretKey.parameter
                  secretKey.otsSecret secretKey.ftsSecret (answer := answer) hbad huncached
                  (fun structuralPosition hat => hposition.not_atPosition structuralPosition hat)).1
              refine (encodingSelectionTotalPotential_le_uncapped _ secretKey hcleanAfter).trans ?_
              have hstructuralNat :=
                encodingStructuralPotential_cacheQuery_le_of_atEncoding
                  (answer := answer) hbad huncached hposition
              have hstructural :
                  (encodingStructuralPotential (cache.cacheQuery input answer)
                    secretKey : ℝ≥0∞) ≤
                    ((encodingStructuralPotential cache secretKey + 2 : Nat) : ℝ≥0∞) :=
                Nat.cast_le.mpr hstructuralNat
              exact add_le_add (mul_le_mul_left hstructural eps) le_rfl
        _ = (((encodingStructuralPotential cache secretKey + 2 : Nat) : ℝ≥0∞) * eps) +
            ∑' answer : HashOutput,
              Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                encodingSelectionPotential (cache.cacheQuery input answer)
                  (finite_cacheQuery hfinite input answer) secretKey := by
              simp_rw [mul_add]
              rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
                tsum_probOutput_of_liftM_PMF, one_mul]
        _ ≤ (((encodingStructuralPotential cache secretKey + 2 : Nat) : ℝ≥0∞) * eps) +
            (encodingSelectionPotential cache hfinite secretKey + eps) := by
              exact add_le_add le_rfl
                (uniform_encodingSelectionPotential_cacheQuery_atPosition_sum_le
                  (cache := cache) (secretKey := secretKey) (input := input)
                  (position := position) hfinite huncached hposition)
        _ = uncapped + 3 * eps := by
              simp only [Nat.cast_add, Nat.cast_ofNat]
              dsimp only [uncapped]
              ring
        _ = encodingSelectionTotalPotential cache hfinite secretKey + 3 * eps := by
              rw [hbefore]

theorem uniform_encodingSelectionTotalPotential_cacheQuery_le_of_no_new_messages
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput}
    (huncached : cache input = none)
    (hnotEncoding : ∀ position : EncodingPosition,
      ¬ AtEncodingPosition secretKey.parameter input position)
    (hnoNew : ∀ (answer : HashOutput) (position : EncodingPosition),
      EncodingMessageSettledAt (cache.cacheQuery input answer) secretKey position →
        EncodingMessageSettledAt cache secretKey position) :
    (∑' answer : HashOutput,
      Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        encodingSelectionTotalPotential (cache.cacheQuery input answer)
          (finite_cacheQuery hfinite input answer) secretKey) ≤
      encodingSelectionTotalPotential cache hfinite secretKey +
        2 * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  let eps := (Fintype.card Digest : ℝ≥0∞)⁻¹
  by_cases hbad : Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
  · have hbefore : encodingSelectionTotalPotential cache hfinite secretKey = 1 := by
      rw [encodingSelectionTotalPotential, if_pos hbad]
    rw [hbefore]
    exact (expected_encodingSelectionTotalPotential_le_one hfinite secretKey input).trans
      (le_add_right le_rfl)
  · let uncapped := (encodingStructuralPotential cache secretKey : ℝ≥0∞) * eps +
      encodingSelectionPotential cache hfinite secretKey
    by_cases hone : 1 ≤ uncapped
    · calc
        _ ≤ ∑' answer : HashOutput,
            Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] * 1 := by
              apply ENNReal.tsum_le_tsum
              intro answer
              exact mul_le_mul_right
                (encodingSelectionTotalPotential_le_one _ secretKey) _
        _ = 1 := by simp only [mul_one, tsum_probOutput_of_liftM_PMF]
        _ = encodingSelectionTotalPotential cache hfinite secretKey := by
              rw [encodingSelectionTotalPotential, if_neg hbad, min_eq_left]
              simpa only [uncapped] using hone
        _ ≤ encodingSelectionTotalPotential cache hfinite secretKey + 2 * eps :=
              le_add_right le_rfl
    · have huncappedLe : uncapped ≤ 1 := le_of_not_ge hone
      have hbefore : encodingSelectionTotalPotential cache hfinite secretKey = uncapped := by
        rw [encodingSelectionTotalPotential, if_neg hbad, min_eq_right]
        exact huncappedLe
      obtain ⟨targets, hcard, hsafe⟩ := tight_bad_step secretKey.parameter
        secretKey.otsSecret secretKey.ftsSecret cache hfinite hbad input huncached
      let credit := tightPotential secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
        + 2 - targets.card
      have hcredit : credit + targets.card =
          tightPotential secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache + 2 :=
        Nat.sub_add_cancel hcard
      have hpointwise (answer : HashOutput) :
          encodingSelectionTotalPotential (cache.cacheQuery input answer)
              (finite_cacheQuery hfinite input answer) secretKey ≤
            ((credit + encodingStagePotential cache secretKey : Nat) : ℝ≥0∞) * eps +
              encodingSelectionPotential cache hfinite secretKey +
                if truncateHash answer ∈ targets then 1 else 0 := by
        by_cases hmem : truncateHash answer ∈ targets
        · rw [if_pos hmem]
          exact (encodingSelectionTotalPotential_le_one _ secretKey).trans
            (le_add_left le_rfl)
        · rw [if_neg hmem, add_zero]
          obtain ⟨hcleanAfter, hpaid⟩ := hsafe answer hmem
          have hstructural : tightPotential secretKey.parameter secretKey.otsSecret
              secretKey.ftsSecret (cache.cacheQuery input answer) ≤ credit := by
            dsimp only [credit]
            omega
          have hstage := encodingStagePotential_cacheQuery_le_of_not_atEncoding
            (secretKey := secretKey) (answer := answer) huncached hnotEncoding
          have hsum : encodingStructuralPotential (cache.cacheQuery input answer) secretKey ≤
              credit + encodingStagePotential cache secretKey := by
            rw [encodingStructuralPotential]
            omega
          refine (encodingSelectionTotalPotential_le_uncapped _ secretKey hcleanAfter).trans ?_
          exact add_le_add (mul_le_mul_left (Nat.cast_le.mpr hsum) eps)
            (encodingSelectionPotential_cacheQuery_le_of_no_new_messages
              (answer := answer) hfinite huncached hnotEncoding (hnoNew answer))
      calc
        _ ≤ ∑' answer : HashOutput,
            Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
              (((credit + encodingStagePotential cache secretKey : Nat) : ℝ≥0∞) * eps +
                encodingSelectionPotential cache hfinite secretKey +
                  if truncateHash answer ∈ targets then 1 else 0) := by
          apply ENNReal.tsum_le_tsum
          intro answer
          exact mul_le_mul_right (hpointwise answer) _
        _ = (((credit + encodingStagePotential cache secretKey : Nat) : ℝ≥0∞) * eps +
              encodingSelectionPotential cache hfinite secretKey) +
            ∑' answer : HashOutput,
              Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                (if truncateHash answer ∈ targets then 1 else 0) := by
          simp_rw [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_add,
            ENNReal.tsum_mul_right, ENNReal.tsum_mul_right,
            tsum_probOutput_of_liftM_PMF, one_mul]
          ring
        _ = (((credit + encodingStagePotential cache secretKey : Nat) : ℝ≥0∞) * eps +
              encodingSelectionPotential cache hfinite secretKey) +
            (targets.card : ℝ≥0∞) * eps := by
          rw [uniformHashOutput_mem_bonus_sum_eq]
        _ = uncapped + 2 * eps := by
          have hcast := congrArg (fun n : Nat => (n : ℝ≥0∞)) hcredit
          push_cast at hcast ⊢
          dsimp only [uncapped, encodingStructuralPotential]
          push_cast
          calc
            _ = ((credit : ℝ≥0∞) + targets.card) * eps +
                (encodingStagePotential cache secretKey : ℝ≥0∞) * eps +
                  encodingSelectionPotential cache hfinite secretKey := by ring
            _ = _ := by rw [hcast]; ring
        _ = encodingSelectionTotalPotential cache hfinite secretKey + 2 * eps := by
          rw [hbefore]

theorem uniform_encodingSelectionTotalPotential_cacheQuery_le_of_settles
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {queriedPosition : Position}
    (hclean : ¬ Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache)
    (huncached : cache input = none)
    (hqueried : AtPosition secretKey.parameter input queriedPosition)
    (hsafe : ∀ answer : HashOutput,
      truncateHash answer ∉ tightSettlingTargets secretKey.parameter secretKey.otsSecret
        secretKey.ftsSecret cache hfinite queriedPosition →
      ¬Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret (cache.cacheQuery input answer))
    (messageTargets : Finset Digest)
    (hdirectTargets : ∀ (position : EncodingPosition) (index : Index),
      treeIndexAt index position.lay = position.tree →
      leafIndexAt index position.lay = position.leafIdx →
      layerMessagePosition index position.lay = queriedPosition →
      encodingMessageTargets secretKey.parameter cache hfinite position ⊆ messageTargets)
    (hdrop : ∀ answer : HashOutput,
      encodingStructuralPotential (cache.cacheQuery input answer) secretKey +
          (messageTargets ∪
            tightSettlingTargets secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache hfinite queriedPosition).card ≤
        encodingStructuralPotential cache secretKey) :
    (∑' answer : HashOutput,
      Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        encodingSelectionTotalPotential (cache.cacheQuery input answer)
          (finite_cacheQuery hfinite input answer) secretKey) ≤
      encodingSelectionTotalPotential cache hfinite secretKey := by
  let eps := (Fintype.card Digest : ℝ≥0∞)⁻¹
  let targets := messageTargets ∪
    tightSettlingTargets secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache hfinite queriedPosition
  let credit := encodingStructuralPotential cache secretKey - targets.card
  have hcard : targets.card ≤ encodingStructuralPotential cache secretKey := by
    have hpaid := hdrop 0
    simp only [targets]
    omega
  have hcredit : credit + targets.card = encodingStructuralPotential cache secretKey := by
    exact Nat.sub_add_cancel hcard
  let uncapped := (encodingStructuralPotential cache secretKey : ℝ≥0∞) * eps +
    encodingSelectionPotential cache hfinite secretKey
  by_cases hone : 1 ≤ uncapped
  · calc
      _ ≤ ∑' answer : HashOutput,
          Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] * 1 := by
            apply ENNReal.tsum_le_tsum
            intro answer
            exact mul_le_mul_right
              (encodingSelectionTotalPotential_le_one _ secretKey) _
      _ = 1 := by simp only [mul_one, tsum_probOutput_of_liftM_PMF]
      _ = encodingSelectionTotalPotential cache hfinite secretKey := by
            rw [encodingSelectionTotalPotential, if_neg hclean, min_eq_left]
            simpa only [uncapped] using hone
  · have huncappedLe : uncapped ≤ 1 := le_of_not_ge hone
    have hbefore : encodingSelectionTotalPotential cache hfinite secretKey = uncapped := by
      rw [encodingSelectionTotalPotential, if_neg hclean, min_eq_right]
      exact huncappedLe
    have hstructural (answer : HashOutput) :
        encodingStructuralPotential (cache.cacheQuery input answer) secretKey ≤ credit := by
      have hpaid := hdrop answer
      change encodingStructuralPotential (cache.cacheQuery input answer) secretKey ≤
        encodingStructuralPotential cache secretKey -
          (messageTargets ∪
            tightSettlingTargets secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache hfinite queriedPosition).card
      omega
    have hpointwise (answer : HashOutput) :
        encodingSelectionTotalPotential (cache.cacheQuery input answer)
            (finite_cacheQuery hfinite input answer) secretKey ≤
          (credit : ℝ≥0∞) * eps + encodingSelectionPotential cache hfinite secretKey +
            if truncateHash answer ∈ targets then 1 else 0 := by
      by_cases hmem : truncateHash answer ∈ targets
      · rw [if_pos hmem]
        exact (encodingSelectionTotalPotential_le_one _ secretKey).trans
          (le_add_left le_rfl)
      · rw [if_neg hmem, add_zero]
        have hcleanAfter := hsafe answer (fun htarget =>
          hmem (Finset.mem_union_right _ htarget))
        refine (encodingSelectionTotalPotential_le_uncapped _ secretKey hcleanAfter).trans ?_
        have hstructuralCast :
            (encodingStructuralPotential (cache.cacheQuery input answer)
              secretKey : ℝ≥0∞) ≤ (credit : ℝ≥0∞) :=
          Nat.cast_le.mpr (hstructural answer)
        have hselection :=
          encodingSelectionPotential_cacheQuery_le_of_avoids_settlementTargets
            (answer := answer) hfinite huncached hqueried
            (fun position index htree hleaf hmessage hmemMessage => by
              apply hmem
              change truncateHash answer ∈ messageTargets ∪
                tightSettlingTargets secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache hfinite queriedPosition
              rw [Finset.mem_union]
              apply Or.inl
              apply hdirectTargets position index htree hleaf
                (atPosition_unique secretKey.parameter hmessage hqueried)
              exact hmemMessage)
            (fun hmemSettling => by
              apply hmem
              change truncateHash answer ∈ messageTargets ∪
                tightSettlingTargets secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache hfinite queriedPosition
              rw [Finset.mem_union]
              exact Or.inr hmemSettling)
        exact add_le_add (mul_le_mul_left hstructuralCast eps) hselection
    calc
      _ ≤ ∑' answer : HashOutput,
          Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
            ((credit : ℝ≥0∞) * eps + encodingSelectionPotential cache hfinite secretKey +
              if truncateHash answer ∈ targets then 1 else 0) := by
            apply ENNReal.tsum_le_tsum
            intro answer
            exact mul_le_mul_right (hpointwise answer) _
      _ = ((credit : ℝ≥0∞) * eps +
            encodingSelectionPotential cache hfinite secretKey) +
          ∑' answer : HashOutput,
            Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
              (if truncateHash answer ∈ targets then 1 else 0) := by
            simp_rw [mul_add]
            rw [ENNReal.tsum_add, ENNReal.tsum_add,
              ENNReal.tsum_mul_right, ENNReal.tsum_mul_right,
              tsum_probOutput_of_liftM_PMF, one_mul]
            ring
      _ = ((credit : ℝ≥0∞) * eps +
            encodingSelectionPotential cache hfinite secretKey) +
          (targets.card : ℝ≥0∞) * eps := by
            rw [uniformHashOutput_mem_bonus_sum_eq]
      _ = uncapped := by
            dsimp only [uncapped]
            calc
              (credit : ℝ≥0∞) * eps + encodingSelectionPotential cache hfinite secretKey +
                    (targets.card : ℝ≥0∞) * eps =
                  ((credit : ℝ≥0∞) + (targets.card : ℝ≥0∞)) * eps +
                    encodingSelectionPotential cache hfinite secretKey := by ring
              _ = _ := by rw [← Nat.cast_add, hcredit]
      _ = encodingSelectionTotalPotential cache hfinite secretKey := hbefore.symm

theorem uniform_encodingSelectionTotalPotential_cacheQuery_le_of_settlingPosition
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {queriedPosition : Position}
    (hclean : ¬ Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache)
    (huncached : cache input = none)
    (hqueried : AtPosition secretKey.parameter input queriedPosition)
    (hunsettled : ¬ Settled secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret cache queriedPosition)
    (hsettles : ∀ answer : HashOutput,
      Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
        (cache.cacheQuery input answer) queriedPosition) :
    (∑' answer : HashOutput,
      Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        encodingSelectionTotalPotential (cache.cacheQuery input answer)
          (finite_cacheQuery hfinite input answer) secretKey) ≤
      encodingSelectionTotalPotential cache hfinite secretKey := by
  have hnotEncoding : ∀ position : EncodingPosition,
      ¬ AtEncodingPosition secretKey.parameter input position := by
    intro position hposition
    exact hposition.not_atPosition queriedPosition hqueried
  by_cases hdirect : ∃ (position : EncodingPosition) (index : Index),
      treeIndexAt index position.lay = position.tree ∧
        leafIndexAt index position.lay = position.leafIdx ∧
        layerMessagePosition index position.lay = queriedPosition
  · obtain ⟨directPosition, directIndex, hdirectTree, hdirectLeaf,
      hdirectMessage⟩ := hdirect
    let messageTargets := encodingMessageTargets secretKey.parameter cache hfinite directPosition
    apply uniform_encodingSelectionTotalPotential_cacheQuery_le_of_settles
      hfinite hclean huncached hqueried
      (fun answer havoid => clean_cacheQuery_of_settling_of_avoids_tight
        secretKey.parameter secretKey.otsSecret secretKey.ftsSecret hfinite hclean
        huncached hqueried hunsettled (hsettles answer) havoid) messageTargets
    · intro position index htree hleaf hmessage
      have heq : position = directPosition :=
        encodingPosition_eq_of_layerMessagePosition_eq htree hleaf
          hdirectTree hdirectLeaf (hmessage.trans hdirectMessage.symm)
      subst position
      exact Finset.Subset.rfl
    · intro answer
      have hstructural := tightPotential_add_settlingTargets_card_le
        secretKey.parameter secretKey.otsSecret secretKey.ftsSecret hfinite
        huncached hqueried hunsettled (hsettles answer)
      have hmessageUnsettled : ¬ EncodingMessageSettledAt cache secretKey directPosition := by
        rintro ⟨index, htree, hleaf, hsettled⟩
        have hpositionEq := layerMessagePosition_eq_of_position_eq directIndex index
          directPosition.lay (hdirectTree.trans htree.symm)
          (hdirectLeaf.trans hleaf.symm)
        apply hunsettled
        rwa [← hdirectMessage, hpositionEq]
      have hmessageSettled : EncodingMessageSettledAt
          (cache.cacheQuery input answer) secretKey directPosition :=
        ⟨directIndex, hdirectTree, hdirectLeaf, by
          rw [hdirectMessage]
          exact hsettles answer⟩
      have hstage := encodingStagePotential_add_messageTargets_card_le_of_new_message
        hfinite huncached hnotEncoding hmessageUnsettled hmessageSettled
      have hunion : (messageTargets ∪
          tightSettlingTargets secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache hfinite queriedPosition).card ≤
          messageTargets.card +
            (tightSettlingTargets secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache hfinite queriedPosition).card :=
        Finset.card_union_le _ _
      rw [encodingStructuralPotential, encodingStructuralPotential]
      dsimp only [messageTargets] at hstage hunion ⊢
      omega
  · apply uniform_encodingSelectionTotalPotential_cacheQuery_le_of_settles
      hfinite hclean huncached hqueried
      (fun answer havoid => clean_cacheQuery_of_settling_of_avoids_tight
        secretKey.parameter secretKey.otsSecret secretKey.ftsSecret hfinite hclean
        huncached hqueried hunsettled (hsettles answer) havoid) ∅
    · intro position index htree hleaf hmessage
      exact (hdirect ⟨position, index, htree, hleaf, hmessage⟩).elim
    · intro answer
      have hstructural := tightPotential_add_settlingTargets_card_le
        secretKey.parameter secretKey.otsSecret secretKey.ftsSecret hfinite
        huncached hqueried hunsettled (hsettles answer)
      have hstage := encodingStagePotential_cacheQuery_le_of_not_atEncoding
        (answer := answer) huncached hnotEncoding
      rw [encodingStructuralPotential, encodingStructuralPotential]
      simp only [Finset.empty_union]
      omega

theorem uniform_encodingSelectionTotalPotential_cacheQuery_sum_le
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput}
    (huncached : cache input = none) :
    (∑' answer : HashOutput,
      Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        encodingSelectionTotalPotential (cache.cacheQuery input answer)
          (finite_cacheQuery hfinite input answer) secretKey) ≤
      encodingSelectionTotalPotential cache hfinite secretKey +
        3 * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  let eps := (Fintype.card Digest : ℝ≥0∞)⁻¹
  by_cases hencoding : ∃ position : EncodingPosition,
      AtEncodingPosition secretKey.parameter input position
  · obtain ⟨position, hposition⟩ := hencoding
    exact uniform_encodingSelectionTotalPotential_cacheQuery_atPosition_sum_le
      hfinite huncached hposition
  · have hnotEncoding : ∀ position : EncodingPosition,
        ¬ AtEncodingPosition secretKey.parameter input position :=
      fun position hposition => hencoding ⟨position, hposition⟩
    by_cases hstructural : ∃ position : Position,
        AtPosition secretKey.parameter input position
    · obtain ⟨position, hposition⟩ := hstructural
      by_cases hsettled : Settled secretKey.parameter secretKey.otsSecret
          secretKey.ftsSecret cache position
      · have hbound :=
          uniform_encodingSelectionTotalPotential_cacheQuery_le_of_no_new_messages
            hfinite huncached hnotEncoding
            (fun answer candidate hafter =>
              hafter.of_cacheQuery_of_at_settled huncached hposition hsettled)
        calc
          _ ≤ encodingSelectionTotalPotential cache hfinite secretKey + 2 * eps := hbound
          _ ≤ encodingSelectionTotalPotential cache hfinite secretKey + 3 * eps := by
            gcongr
            norm_num
      · by_cases hnever : ∀ answer : HashOutput,
            ¬ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
              (cache.cacheQuery input answer) position
        · have hbound :=
            uniform_encodingSelectionTotalPotential_cacheQuery_le_of_no_new_messages
              hfinite huncached hnotEncoding
              (fun answer candidate hafter =>
                hafter.of_cacheQuery_of_at_unsettledAfter huncached hposition
                  (hnever answer))
          calc
            _ ≤ encodingSelectionTotalPotential cache hfinite secretKey + 2 * eps := hbound
            _ ≤ encodingSelectionTotalPotential cache hfinite secretKey + 3 * eps := by
              gcongr
              norm_num
        · push Not at hnever
          obtain ⟨settlingAnswer, hsettling⟩ := hnever
          obtain ⟨hinput, hchildren⟩ :=
            eq_cachedInput_and_children_of_settled_cacheQuery secretKey.parameter
              secretKey.otsSecret secretKey.ftsSecret huncached hposition hsettled hsettling
          have hsettles : ∀ answer : HashOutput,
              Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
                (cache.cacheQuery input answer) position := by
            intro answer
            have hle := le_cacheQuery (cache := cache) (input := input)
              (answer := answer) huncached
            have hchildrenAfter : ∀ child ∈ position.children,
                Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
                  (cache.cacheQuery input answer) child :=
              fun child hchild => (hchildren child hchild).mono hle
            have hvalues : ∀ child ∈ position.children,
                honestValue (fromCache (cache.cacheQuery input answer)) secretKey.parameter
                    secretKey.otsSecret secretKey.ftsSecret child =
                  honestValue (fromCache cache) secretKey.parameter secretKey.otsSecret
                    secretKey.ftsSecret child :=
              fun child hchild => honestValue_eq_of_settled
                (agreesWithFn_fromCache_of_le hle) (hchildren child hchild)
            have hpinned : cachedInput secretKey.parameter secretKey.otsSecret
                  secretKey.ftsSecret (cache.cacheQuery input answer) position =
                cachedInput secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
                  cache position :=
              honestInput_congr _ _ secretKey.parameter secretKey.otsSecret
                secretKey.ftsSecret hsettling.valid hvalues
            rw [settled_iff]
            refine ⟨hsettling.valid, ?_, hchildrenAfter⟩
            rw [hpinned, ← hinput, QueryCache.cacheQuery_self]
            simp
          by_cases hbad : Bad secretKey.parameter secretKey.otsSecret
              secretKey.ftsSecret cache
          · have hbefore : encodingSelectionTotalPotential cache hfinite secretKey = 1 := by
              rw [encodingSelectionTotalPotential, if_pos hbad]
            rw [hbefore]
            exact (expected_encodingSelectionTotalPotential_le_one hfinite secretKey input).trans
              (le_add_right le_rfl)
          · exact (uniform_encodingSelectionTotalPotential_cacheQuery_le_of_settlingPosition
              hfinite hbad huncached hposition hsettled hsettles).trans
                (le_add_right le_rfl)
    · have hbound :=
        uniform_encodingSelectionTotalPotential_cacheQuery_le_of_no_new_messages
          hfinite huncached hnotEncoding
          (fun answer candidate hafter =>
            hafter.of_cacheQuery_of_not_atPosition huncached
              (fun position hposition => hstructural ⟨position, hposition⟩))
      calc
        _ ≤ encodingSelectionTotalPotential cache hfinite secretKey + 2 * eps := hbound
        _ ≤ encodingSelectionTotalPotential cache hfinite secretKey + 3 * eps := by
          gcongr
          norm_num

@[simp] theorem encodingSelectionTotalPotential_empty (secretKey : SecretKey) :
    encodingSelectionTotalPotential ∅ finite_empty secretKey = 0 := by
  rw [encodingSelectionTotalPotential,
    if_neg (not_bad_empty secretKey.parameter secretKey.otsSecret secretKey.ftsSecret),
    encodingStructuralPotential_empty, encodingSelectionPotential_empty]
  simp

end SphincsSecurity.Concrete.TightEncoding
