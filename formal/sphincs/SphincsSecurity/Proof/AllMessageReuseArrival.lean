import SphincsSecurity.Proof.AllMessageReuse
import SphincsSecurity.Proof.CachedReuseArrival

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def allMessageTargetRow (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (output : HashOutput) : ENNReal :=
  cacheMessageWeight key.parameter (fun sourceInput source =>
    if MessageHashInput key.parameter input ∧ Admissible (truncateMessageDigest output) then
      targetCoverageInputIncrement remaining key before log (payloadOf input) (hashOutputFewTimeView output) sourceInput source else 0) before

theorem allMessageTargetReuseCharge_cacheQuery (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log) (q : Nat) :
    allMessageTargetReuseCharge remaining key (before.cacheQuery input output) log q =
      allMessageTargetReuseCharge remaining key before log q +
        (allMessageTargetRow remaining key before log input output +
          if MessageHashInput key.parameter input ∧ Admissible (truncateMessageDigest output) then
            cachedTargetFutureIncrement remaining key before log input (hashOutputFewTimeView output) else 0) * digestReuseWeight q := by
  have hweight : cachedTargetFutureIncrement remaining key (before.cacheQuery input output) log =
      (fun sourceInput source => cachedTargetFutureIncrement remaining key before log sourceInput source +
        if MessageHashInput key.parameter input ∧ Admissible (truncateMessageDigest output) then
          targetCoverageInputIncrement remaining key before log (payloadOf input) (hashOutputFewTimeView output) sourceInput source else 0) := by
    funext sourceInput source
    exact cachedTargetFutureIncrement_cacheQuery remaining key before log input sourceInput output hfresh hsigned source
  unfold allMessageTargetReuseCharge
  rw [cacheMessageWeight_cacheQuery _ _ _ _ _ hfresh]
  simp only [cachedTargetFutureIncrement_cacheQuery_self remaining key before log input output hfresh hsigned]
  rw [hweight, cacheMessageWeight_add]
  unfold allMessageTargetRow
  ring

theorem allMessageTargetRow_fresh (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hmessage : MessageHashInput key.parameter input) :
    allMessageTargetRow remaining key before log input output =
      cacheMessageWeight key.parameter (fun _ source => if Admissible (truncateMessageDigest output) then
        futureFewTimeCoverageIncrement remaining
          (uncoveredFewTimeTrees (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log)
            (hashOutputFewTimeView output)) (hashOutputFewTimeView output) source else 0) before := by
  obtain ⟨payload, rfl⟩ := hmessage
  have hviews := eligibleSigningViews_fresh_eq_observed key.parameter key.root before log payload hfresh hsigned
  unfold allMessageTargetRow cacheMessageWeight
  apply tsum_congr
  intro sourceInput
  unfold cacheMessageEntryWeight
  cases hsource : before sourceInput with
  | none => rfl
  | some sourceOutput =>
      have hne : sourceInput ≠ tweakableHashInput key.parameter .message payload := by
        intro heq
        rw [heq, hfresh] at hsource
        contradiction
      simp only [show MessageHashInput key.parameter (tweakableHashInput key.parameter .message payload) from ⟨payload, rfl⟩,
        true_and, payloadOf_tweakableHashInput, targetCoverageInputIncrement, if_neg hne, hviews]

theorem expected_allMessageTargetRow_le (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hmessage : MessageHashInput key.parameter input) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] * allMessageTargetRow remaining key before log input output) ≤
      cacheMessageWeight key.parameter (fun _ source => coverageOccupancyCompletionIncrement
        (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) remaining source) before *
          ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
  simp only [allMessageTargetRow_fresh remaining key before log input _ hfresh hsigned hmessage, expected_cacheMessageWeight]
  apply (cacheMessageWeight_mono key.parameter _ _ before (fun _ source =>
    expected_uniformHashOutput_futureCoverageIncrement_le _ remaining source)).trans_eq
  exact cacheMessageWeight_mul_right _ _ _ _

theorem expected_allMessageTargetReuseCharge_cacheQuery_le (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hmessage : MessageHashInput key.parameter input) (q : Nat) :
    ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * cachedFutureCoverage remaining key.parameter key.root before log * digestReuseWeight q +
      (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
        allMessageTargetReuseCharge remaining key (before.cacheQuery input output) log q) ≤
      allMessageTargetReuseCharge remaining key before log q +
        ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * cachedFutureCoverage (remaining + 1) key.parameter key.root before log * digestReuseWeight q +
        allMessageOccupancyReuseCharge remaining key before log q * ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
  have hmass : (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)]) = 1 :=
    tsum_probOutput_eq_one' (by simp)
  have heq : (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      allMessageTargetReuseCharge remaining key (before.cacheQuery input output) log q) =
      allMessageTargetReuseCharge remaining key before log q +
        ((∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] * allMessageTargetRow remaining key before log input output) +
          ∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
            (if Admissible (truncateMessageDigest output) then
              cachedTargetFutureIncrement remaining key before log input (hashOutputFewTimeView output) else 0)) * digestReuseWeight q := by
    simp only [allMessageTargetReuseCharge_cacheQuery remaining key before log input _ hfresh hsigned q,
      hmessage, true_and, mul_add, ← mul_assoc, ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul, add_mul]
  calc
    _ = allMessageTargetReuseCharge remaining key before log q +
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * cachedFutureCoverage remaining key.parameter key.root before log +
          ∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
            (if Admissible (truncateMessageDigest output) then
              cachedTargetFutureIncrement remaining key before log input (hashOutputFewTimeView output) else 0)) * digestReuseWeight q +
        (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] * allMessageTargetRow remaining key before log input output) * digestReuseWeight q := by
      rw [heq]
      ring
    _ = allMessageTargetReuseCharge remaining key before log q +
        ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * cachedFutureCoverage (remaining + 1) key.parameter key.root before log * digestReuseWeight q +
        (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] * allMessageTargetRow remaining key before log input output) * digestReuseWeight q := by
      rw [expected_freshHashOutput_cachedTargetFutureIncrement remaining key before log input hfresh]
    _ ≤ _ := by
      apply add_le_add le_rfl
      apply (mul_le_mul' (expected_allMessageTargetRow_le remaining key before log input hfresh hsigned hmessage) le_rfl).trans_eq
      unfold allMessageOccupancyReuseCharge
      ring

theorem expected_randomOracle_allMessageTargetReuseCharge_le (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hmessage : MessageHashInput key.parameter input) (q : Nat) :
    ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * cachedFutureCoverage remaining key.parameter key.root before log * digestReuseWeight q +
      (∑' result, Pr[= result | (randomOracle input).run before] * allMessageTargetReuseCharge remaining key result.2 log q) ≤
      allMessageTargetReuseCharge remaining key before log q +
        ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * cachedFutureCoverage (remaining + 1) key.parameter key.root before log * digestReuseWeight q +
        allMessageOccupancyReuseCharge remaining key before log q * ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
  rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
  exact expected_allMessageTargetReuseCharge_cacheQuery_le remaining key before log input hfresh hsigned hmessage q

theorem allMessageTargetRow_of_not_message (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (output : HashOutput)
    (hmessage : ¬ MessageHashInput key.parameter input) :
    allMessageTargetRow remaining key before log input output = 0 := by
  unfold allMessageTargetRow cacheMessageWeight
  apply ENNReal.tsum_eq_zero.mpr
  intro sourceInput
  unfold cacheMessageEntryWeight
  cases before sourceInput <;> simp only [hmessage, false_and, if_false, ite_self]

theorem allMessageTargetReuseCharge_cacheQuery_of_not_message (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hmessage : ¬ MessageHashInput key.parameter input) (q : Nat) :
    allMessageTargetReuseCharge remaining key (before.cacheQuery input output) log q =
      allMessageTargetReuseCharge remaining key before log q := by
  rw [allMessageTargetReuseCharge_cacheQuery remaining key before log input output hfresh hsigned q,
    allMessageTargetRow_of_not_message remaining key before log input output hmessage]
  simp only [hmessage, false_and, if_false, add_zero, zero_mul]

end SphincsSecurity.Concrete
