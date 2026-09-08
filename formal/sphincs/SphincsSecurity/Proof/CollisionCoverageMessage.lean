import SphincsSecurity.Proof.CollisionCoveragePotential
import SphincsSecurity.Proof.JointProbeMessageHashBudget

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem FtsProbeSimulation.MessageHashInput.not_atPosition {parameter : PublicParameter} {input : HashInput}
    (hmessage : MessageHashInput parameter input) (position : Position) : ¬ AtPosition parameter input position := by
  obtain ⟨payload, rfl⟩ := hmessage
  rintro ⟨otherPayload, hinput⟩
  have hdomain := (tweakableHashInput_injective parameter (by trivial) (Position.domain_inRange position) hinput).1
  cases position <;> simp [Position.domain] at hdomain

theorem collisionStructuralRecordPotential_cacheQuery_nonstructural_le
    (key : SecretKey) (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) (answer : HashOutput)
    (hfresh : cache input = none) (hencoding : ∀ position : EncodingPosition, ¬ AtEncodingPosition key.parameter input position)
    (hstructural : ∀ position : Position, ¬ AtPosition key.parameter input position) :
    collisionStructuralRecordPotential key (cache.cacheQuery input answer) none ≤ collisionStructuralRecordPotential key cache none := by
  have hp := parentReserve_cacheQuery_le_charge key.parameter key.otsSecret key.ftsSecret
    (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) (answer := answer) hfresh
  have hcharge : parentReserveCharge key.parameter key.otsSecret key.ftsSecret
      (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) cache input = 0 := by
    rw [parentReserveCharge, if_neg]
    rintro ⟨position, hat, _⟩
    exact hstructural position hat
  rw [hcharge, Nat.add_zero] at hp
  simp only [collisionStructuralRecordPotential, collisionAnswerEncodingMonitorPotential, Option.isSome_none, Bool.false_eq_true, if_false,
    collisionAnswerEncodingAdaptivePotential_eq (finite_cacheQuery hfinite input answer), collisionAnswerEncodingAdaptivePotential_eq hfinite,
    ftsParentSelectionPotential, firstExceptionSelectionPotential]
  exact add_le_add (collisionAnswerEncodingTotalPotential_cacheQuery_le_of_nonstructural hfinite hfresh hencoding hstructural)
    (mul_le_mul' (Nat.cast_le.mpr hp) le_rfl)

theorem collisionStructuralRecordPotential_message_query_le
    (key : SecretKey) (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput)
    (hmessage : MessageHashInput key.parameter input) (result : HashOutput × QueryCache HashSpec)
    (hr : result ∈ support ((randomOracle input).run cache)) :
    collisionStructuralRecordPotential key result.2 none ≤ collisionStructuralRecordPotential key cache none := by
  by_cases hfresh : cache input = none
  · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, support_map] at hr
    obtain ⟨answer, _, rfl⟩ := hr
    exact collisionStructuralRecordPotential_cacheQuery_nonstructural_le key cache hfinite input answer hfresh
      (fun position => FtsProbeSimulation.MessageHashInput.not_atEncoding hmessage position)
      (fun position => FtsProbeSimulation.MessageHashInput.not_atPosition hmessage position)
  · obtain ⟨answer, ha⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [randomOracle, QueryImpl.withCaching_run_some _ ha, mem_support_pure_iff] at hr
    subst result
    exact le_rfl

namespace FtsProbeSimulation.JointOriginal

open OtsProbeSimulation (OtsSecretIndex)

theorem collisionSurvivingStructuralPotential_message_step_le
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : HashInput) (frame : Option Frame) (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (hmessage : MessageHashInput parameter input) (result)
    (hr : result ∈ support (stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      (.inl (.inr input)) frame cache false false)) :
    collisionSurvivingStructuralPotential (secretKey parameter root otsTable ftsTable) result.1.2.1.2 result.1.2.2 result.2 ≤
      collisionStructuralRecordPotential (secretKey parameter root otsTable ftsTable) cache none := by
  have horiginal := stepWithFailure_original_support (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
    (.inl (.inr input)) frame cache false false result hr
  have hno : ∀ answer, ¬ parentException parameter otsTable ftsTable cache input answer := by
    intro answer he
    obtain ⟨child, parent, hat, _⟩ := he.2.exists_full_parent_input parameter _ _ le_rfl
    exact hmessage.not_atPosition child hat
  change result.1.2 ∈ support (do
    let middle ← (randomOracle input).run cache
    pure (middle, false || queryException (parentException parameter otsTable ftsTable) cache (.inr input) middle.1)) at horiginal
  rw [mem_support_bind_iff] at horiginal
  obtain ⟨middle, hm, he⟩ := horiginal
  simp only [queryException, hno, and_false, decide_false, Bool.false_or, mem_support_pure_iff] at he
  have hhit : result.1.2.2 = false := congrArg Prod.snd he
  have hcache : result.1.2.1.2 = middle.2 := congrArg (fun current => current.1.2) he
  unfold collisionSurvivingStructuralPotential
  rw [hhit]
  simp only [Bool.false_eq_true, if_false]
  split_ifs
  · exact zero_le
  · rw [hcache]
    exact collisionStructuralRecordPotential_message_query_le (secretKey parameter root otsTable ftsTable) cache hfinite input hmessage middle hm

theorem expected_jointCollisionCoverage_message_le
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (hcap : cap ≤ 2 ^ 127) (hbudget : 1 ≤ budget) (input : HashInput) (frame : Option Frame) (state : CoverLogState)
    (hfinite : Finite state.1) (hsigned : SigningDigestsCached parameter state.1 root state.2)
    (hcache : QueryCache.enncard state.1 ≤ cap) (hmessage : MessageHashInput parameter input) :
    (∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      (.inl (.inr input)) frame state.1 false false] *
      jointCollisionCoveragePotential (secretKey parameter root otsTable ftsTable) cap (budget - 1)
        (stepSigningLogState (.inl (.inr input)) state.2 result) result.1.2.2 result.2) ≤
      jointCollisionCoveragePotential (secretKey parameter root otsTable ftsTable) cap budget state false false +
        (1 - min 1 (collisionStructuralRecordPotential (secretKey parameter root otsTable ftsTable) state.1 none)) *
          ∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
            (.inl (.inr input)) frame state.1 false false] *
            (if result.2 then 1 - boundedRemainingCoveragePotential (secretKey parameter root otsTable ftsTable) cap (budget - 1)
              (stepSigningLogState (.inl (.inr input)) state.2 result) else 0) := by
  let key := secretKey parameter root otsTable ftsTable
  have hcoverage := (le_self_add.trans (expected_logTraced_remainingCoverage_add_unused_le key cap budget hcap state hsigned hcache
    (.inl (.inr input)) hbudget ∅ Finset.univ (by constructor <;> simp)))
  have hscaled := mul_le_mul' hcoverage (le_refl (((2 ^ 140 : Nat) : ENNReal)⁻¹))
  rw [← ENNReal.tsum_mul_right] at hscaled
  simp only [mul_assoc] at hscaled
  change (∑' result, Pr[= result | (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable) (.inl (.inr input))).run (state.1, state.2)] *
    (remainingCoveragePotential key cap (budget - 1) result.2 ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹)) ≤ _ at hscaled
  rw [← stepWithFailure_expect_logged (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
    (.inl (.inr input)) frame state.1 state.2 false false
      (fun _ current => remainingCoveragePotential key cap (budget - 1) current ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹)] at hscaled
  exact expected_boundedUnionPotential_stopped_le
    (stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable (.inl (.inr input)) frame state.1 false false)
    (fun result => collisionSurvivingStructuralPotential key result.1.2.1.2 result.1.2.2 result.2)
    (fun result => remainingCoveragePotential key cap (budget - 1) (stepSigningLogState (.inl (.inr input)) state.2 result)
      ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹) (fun result => result.2)
    (collisionStructuralRecordPotential key state.1 none)
    (remainingCoveragePotential key cap budget state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹)
    (fun result hr _ => collisionSurvivingStructuralPotential_message_step_le parameter root otsTable ftsTable input frame state.1 hfinite hmessage result hr)
    hscaled

noncomputable def jointCollisionCoverageHashCharge
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : HashInput) (frame : Option Frame) (state : CoverLogState) : ENNReal :=
  let key := secretKey parameter root otsTable ftsTable
  let computation := stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
    (.inl (.inr input)) frame state.1 false false
  if MessageHashInput parameter input then
    (1 - min 1 (collisionStructuralRecordPotential key state.1 none)) *
      ∑' result, Pr[= result | computation] *
        (if result.2 then 1 - boundedRemainingCoveragePotential key cap (budget - 1)
          (stepSigningLogState (.inl (.inr input)) state.2 result) else 0)
  else
    (1 - boundedRemainingCoveragePotential key cap (budget - 1) state) *
      (Pr[fun result => result.2 = true | computation] +
        expectedPreExceptionCharge (parentException parameter otsTable ftsTable) (collisionSigningStructuralCharge key)
          (expandedAdversaryImpl key (.inl (.inr input))) state.1 false * (Fintype.card Digest : ENNReal)⁻¹)

noncomputable def jointCollisionCoverageHashCredit (key : SecretKey) (cap budget : Nat) (input : HashInput) (state : CoverLogState) : ENNReal :=
  if MessageHashInput key.parameter input then 0 else
    (boundedRemainingCoveragePotential key cap budget state - boundedRemainingCoveragePotential key cap (budget - 1) state) *
      (1 - min 1 (collisionStructuralRecordPotential key state.1 none))

theorem expected_jointCollisionCoverage_hash_add_credit_le
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (hcap : cap ≤ 2 ^ 127) (hbudget : 1 ≤ budget) (input : HashInput) (frame : Frame) (state : CoverLogState)
    (hfinite : Finite state.1) (henabled : frame.Enabled parameter otsTable ftsTable (.inl (.inr input)) state.1 false)
    (hcomputed : OtsProbeSimulation.DeferredComputationsClosed frame.context)
    (hsigned : SigningDigestsCached parameter state.1 root state.2) (hcache : QueryCache.enncard state.1 ≤ cap) :
    (∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      (.inl (.inr input)) (some frame) state.1 false false] *
      jointCollisionCoveragePotential (secretKey parameter root otsTable ftsTable) cap (budget - 1)
        (stepSigningLogState (.inl (.inr input)) state.2 result) result.1.2.2 result.2) +
      jointCollisionCoverageHashCredit (secretKey parameter root otsTable ftsTable) cap budget input state ≤
      jointCollisionCoveragePotential (secretKey parameter root otsTable ftsTable) cap budget state false false +
        jointCollisionCoverageHashCharge parameter root otsTable ftsTable cap budget input (some frame) state := by
  by_cases hm : MessageHashInput parameter input
  · simp only [jointCollisionCoverageHashCredit, jointCollisionCoverageHashCharge, secretKey, if_pos hm, add_zero]
    exact expected_jointCollisionCoverage_message_le parameter root otsTable ftsTable cap budget hcap hbudget input (some frame) state
      hfinite hsigned hcache hm
  · simp only [jointCollisionCoverageHashCredit, jointCollisionCoverageHashCharge, secretKey, if_neg hm]
    exact expected_jointCollisionCoverage_nonmessage_add_decrease_le parameter root otsTable ftsTable cap budget input frame state
      hfinite henabled hcomputed hsigned hm

end FtsProbeSimulation.JointOriginal

end SphincsSecurity.Concrete
