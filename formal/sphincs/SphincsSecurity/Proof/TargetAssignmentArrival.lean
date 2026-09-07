import SphincsSecurity.Proof.TargetAssignmentReuse
import SphincsSecurity.Proof.CachedTargetIncrement

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def cachedTargetAssignmentCount (remaining : Nat) (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) : ENNReal :=
  cacheMessageWeight parameter (fun input target =>
    futureTargetAssignmentCount (eligibleSigningViews (messageAnswers parameter cache) root (payloadOf input) log) remaining target) cache

theorem cachedTargetAssignmentIncrement_of_fresh (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hfresh : before input = none) (source : FewTimeView) :
    cachedTargetAssignmentIncrement remaining key before log input source =
      cacheMessageWeight key.parameter (fun targetInput target => futureTargetAssignmentIncrement (eligibleSigningViews (FtsProbeSimulation.messageAnswers key.parameter before)
          key.root (payloadOf targetInput) log) remaining target source) before := by
  unfold cachedTargetAssignmentIncrement cacheMessageWeight
  apply tsum_congr
  intro targetInput
  unfold cacheMessageEntryWeight
  cases htarget : before targetInput with
  | none => rfl
  | some output =>
      simp only
      split_ifs with hgood
      · obtain ⟨payload, rfl⟩ := hgood.1
        rw [payloadOf_tweakableHashInput]
        apply if_neg
        intro heq
        rw [heq, htarget] at hfresh
        contradiction
      · rfl

theorem expected_fresh_cachedTargetAssignmentIncrement (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hfresh : before input = none) :
    cachedTargetAssignmentCount remaining key.parameter key.root before log +
      (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
        cachedTargetAssignmentIncrement remaining key before log input source) =
      cachedTargetAssignmentCount (remaining + 1) key.parameter key.root before log := by
  simp only [cachedTargetAssignmentIncrement_of_fresh remaining key before log input hfresh]
  rw [expected_cacheMessageWeight, cachedTargetAssignmentCount, ← cacheMessageWeight_add]
  unfold cachedTargetAssignmentCount
  congr 1
  funext targetInput target
  exact expected_source_futureTargetAssignmentIncrement _ remaining target

theorem expected_freshHashOutput_cachedTargetAssignmentIncrement (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hfresh : before input = none) :
    ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * cachedTargetAssignmentCount remaining key.parameter key.root before log +
      (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (if Admissible (truncateMessageDigest output) then
          cachedTargetAssignmentIncrement remaining key before log input (hashOutputFewTimeView output) else 0)) =
      ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * cachedTargetAssignmentCount (remaining + 1) key.parameter key.root before log := by
  rw [expected_uniformHashOutput_admissible_weight, ← mul_add,
    expected_fresh_cachedTargetAssignmentIncrement remaining key before log input hfresh]

noncomputable def allMessageAssignmentTargetRow (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (output : HashOutput) : ENNReal :=
  cacheMessageWeight key.parameter (fun sourceInput source =>
    if MessageHashInput key.parameter input ∧ Admissible (truncateMessageDigest output) then
      targetAssignmentInputIncrement remaining key before log (payloadOf input) (hashOutputFewTimeView output) sourceInput source else 0) before

theorem allMessageTargetAssignmentReuseCharge_cacheQuery (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log) (q : Nat) :
    allMessageTargetAssignmentReuseCharge remaining key (before.cacheQuery input output) log q =
      allMessageTargetAssignmentReuseCharge remaining key before log q +
        (allMessageAssignmentTargetRow remaining key before log input output +
          if MessageHashInput key.parameter input ∧ Admissible (truncateMessageDigest output) then
            cachedTargetAssignmentIncrement remaining key before log input (hashOutputFewTimeView output) else 0) * digestReuseWeight q := by
  have hweight : cachedTargetAssignmentIncrement remaining key (before.cacheQuery input output) log =
      (fun sourceInput source => cachedTargetAssignmentIncrement remaining key before log sourceInput source +
        if MessageHashInput key.parameter input ∧ Admissible (truncateMessageDigest output) then
          targetAssignmentInputIncrement remaining key before log (payloadOf input) (hashOutputFewTimeView output) sourceInput source else 0) := by
    funext sourceInput source
    exact cachedTargetAssignmentIncrement_cacheQuery remaining key before log input sourceInput output hfresh hsigned source
  unfold allMessageTargetAssignmentReuseCharge
  rw [cacheMessageWeight_cacheQuery _ _ _ _ _ hfresh]
  simp only [cachedTargetAssignmentIncrement_cacheQuery_self remaining key before log input output hfresh hsigned]
  rw [hweight, cacheMessageWeight_add]
  unfold allMessageAssignmentTargetRow
  ring

theorem allMessageAssignmentTargetRow_fresh (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hmessage : MessageHashInput key.parameter input) :
    allMessageAssignmentTargetRow remaining key before log input output =
      cacheMessageWeight key.parameter (fun _ source => if Admissible (truncateMessageDigest output) then
        futureTargetAssignmentIncrement
          (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log)
            remaining (hashOutputFewTimeView output) source else 0) before := by
  obtain ⟨payload, rfl⟩ := hmessage
  have hviews := eligibleSigningViews_fresh_eq_observed key.parameter key.root before log payload hfresh hsigned
  unfold allMessageAssignmentTargetRow cacheMessageWeight
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
        true_and, payloadOf_tweakableHashInput, targetAssignmentInputIncrement, if_neg hne, hviews]

theorem expected_allMessageAssignmentTargetRow (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hmessage : MessageHashInput key.parameter input) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] * allMessageAssignmentTargetRow remaining key before log input output) =
      cacheMessageWeight key.parameter (fun _ source => coverageOccupancyCompletionIncrement
        (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) remaining source) before *
          ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
  simp only [allMessageAssignmentTargetRow_fresh remaining key before log input _ hfresh hsigned hmessage, expected_cacheMessageWeight]
  simp only [expected_uniformHashOutput_futureTargetAssignmentIncrement]
  exact cacheMessageWeight_mul_right _ _ _ _

theorem expected_allMessageTargetAssignmentReuseCharge_cacheQuery (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hmessage : MessageHashInput key.parameter input) (q : Nat) :
    ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * cachedTargetAssignmentCount remaining key.parameter key.root before log * digestReuseWeight q +
      (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
        allMessageTargetAssignmentReuseCharge remaining key (before.cacheQuery input output) log q) =
      allMessageTargetAssignmentReuseCharge remaining key before log q +
        ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * cachedTargetAssignmentCount (remaining + 1) key.parameter key.root before log * digestReuseWeight q +
        allMessageOccupancyReuseCharge remaining key before log q * ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
  have hmass : (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)]) = 1 :=
    tsum_probOutput_eq_one' (by simp)
  have heq : (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      allMessageTargetAssignmentReuseCharge remaining key (before.cacheQuery input output) log q) =
      allMessageTargetAssignmentReuseCharge remaining key before log q +
        ((∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] * allMessageAssignmentTargetRow remaining key before log input output) +
          ∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
            (if Admissible (truncateMessageDigest output) then
              cachedTargetAssignmentIncrement remaining key before log input (hashOutputFewTimeView output) else 0)) * digestReuseWeight q := by
    simp only [allMessageTargetAssignmentReuseCharge_cacheQuery remaining key before log input _ hfresh hsigned q,
      hmessage, true_and, mul_add, ← mul_assoc, ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul, add_mul]
  calc
    _ = allMessageTargetAssignmentReuseCharge remaining key before log q +
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * cachedTargetAssignmentCount remaining key.parameter key.root before log +
          ∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
            (if Admissible (truncateMessageDigest output) then
              cachedTargetAssignmentIncrement remaining key before log input (hashOutputFewTimeView output) else 0)) * digestReuseWeight q +
        (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] * allMessageAssignmentTargetRow remaining key before log input output) * digestReuseWeight q := by
      rw [heq]
      ring
    _ = allMessageTargetAssignmentReuseCharge remaining key before log q +
        ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * cachedTargetAssignmentCount (remaining + 1) key.parameter key.root before log * digestReuseWeight q +
        (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] * allMessageAssignmentTargetRow remaining key before log input output) * digestReuseWeight q := by
      rw [expected_freshHashOutput_cachedTargetAssignmentIncrement remaining key before log input hfresh]
    _ = _ := by
      rw [expected_allMessageAssignmentTargetRow remaining key before log input hfresh hsigned hmessage]
      unfold allMessageOccupancyReuseCharge
      ring

end SphincsSecurity.Concrete
