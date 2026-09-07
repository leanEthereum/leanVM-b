import SphincsSecurity.Proof.CachedReusePairs

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def cachedTargetFutureIncrement (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (source : FewTimeView) : ENNReal :=
  cacheMessageWeight key.parameter (fun targetInput target =>
    targetCoverageInputIncrement remaining key before log (payloadOf targetInput) target input source) before

theorem cachedSignerInputWeight_cachedTargetFutureIncrement (remaining : Nat) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (sourceInput : HashInput) :
    cachedSignerInputWeight key message before (cachedTargetFutureIncrement remaining key before log) sourceInput =
      ∑' targetInput, cachedTargetSourceIncrement remaining key message before log targetInput sourceInput := by
  unfold cachedSignerInputWeight cachedTargetSourceIncrement cacheMessageEntryWeight
  cases hsource : before sourceInput with
  | none =>
      apply (ENNReal.tsum_eq_zero.mpr ?_).symm
      intro targetInput
      cases before targetInput <;> simp only [cachedSignerInputWeight, hsource, ite_self]
  | some output =>
      simp only
      split_ifs with hgood
      · unfold cachedTargetFutureIncrement cacheMessageWeight
        apply tsum_congr
        intro targetInput
        unfold cacheMessageEntryWeight
        cases before targetInput <;> simp only [cachedSignerInputWeight, hsource, if_pos hgood]
      · apply (ENNReal.tsum_eq_zero.mpr ?_).symm
        intro targetInput
        cases before targetInput <;> simp only [cachedSignerInputWeight, hsource, if_neg hgood, ite_self]

theorem cachedFutureCoverageReuseCharge_eq_sources (remaining : Nat) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (q : Nat) :
    cachedFutureCoverageReuseCharge remaining key message before log q =
      (∑' sourceInput, cachedSignerInputWeight key message before
        (cachedTargetFutureIncrement remaining key before log) sourceInput) * digestReuseWeight q := by
  rw [cachedFutureCoverageReuseCharge_eq_pairs, ENNReal.tsum_comm]
  simp only [cachedSignerInputWeight_cachedTargetFutureIncrement]

theorem cachedTargetFutureIncrement_of_fresh (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hfresh : before input = none) (source : FewTimeView) :
    cachedTargetFutureIncrement remaining key before log input source =
      cacheMessageWeight key.parameter (fun targetInput target => futureFewTimeCoverageIncrement remaining
        (uncoveredFewTimeTrees (eligibleSigningViews (FtsProbeSimulation.messageAnswers key.parameter before)
          key.root (payloadOf targetInput) log) target) target source) before := by
  unfold cachedTargetFutureIncrement cacheMessageWeight
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
        apply targetCoverageInputIncrement_of_ne
        intro heq
        rw [heq, htarget] at hfresh
        contradiction
      · rfl

theorem expected_fresh_cachedTargetFutureIncrement (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hfresh : before input = none) :
    cachedFutureCoverage remaining key.parameter key.root before log +
      (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
        cachedTargetFutureIncrement remaining key before log input source) =
      cachedFutureCoverage (remaining + 1) key.parameter key.root before log := by
  simp only [cachedTargetFutureIncrement_of_fresh remaining key before log input hfresh]
  rw [expected_cacheMessageWeight, cachedFutureCoverage, ← cacheMessageWeight_add]
  unfold cachedFutureCoverage
  congr 1
  funext targetInput target
  exact expected_futureFewTimeCoverageIncrement remaining _ target

theorem expected_freshHashOutput_cachedTargetFutureIncrement (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hfresh : before input = none) :
    ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * cachedFutureCoverage remaining key.parameter key.root before log +
      (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (if Admissible (truncateMessageDigest output) then
          cachedTargetFutureIncrement remaining key before log input (hashOutputFewTimeView output) else 0)) =
      ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * cachedFutureCoverage (remaining + 1) key.parameter key.root before log := by
  rw [expected_uniformHashOutput_admissible_weight, ← mul_add,
    expected_fresh_cachedTargetFutureIncrement remaining key before log input hfresh]

theorem cachedTargetFutureIncrement_cacheQuery_self (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (source : FewTimeView) :
    cachedTargetFutureIncrement remaining key (before.cacheQuery input output) log input source =
      cachedTargetFutureIncrement remaining key before log input source := by
  have hweight : (fun targetInput target => targetCoverageInputIncrement remaining key
        (before.cacheQuery input output) log (payloadOf targetInput) target input source) =
      (fun targetInput target => targetCoverageInputIncrement remaining key before log (payloadOf targetInput) target input source) := by
    funext targetInput target
    exact targetCoverageInputIncrement_cache_stable remaining key before _ log _ target source input
      (QueryCache.le_cacheQuery before hfresh) hsigned
  rw [cachedTargetFutureIncrement, hweight, cacheMessageWeight_cacheQuery _ _ _ _ _ hfresh]
  have hzero : (if FtsProbeSimulation.MessageHashInput key.parameter input ∧ Admissible (truncateMessageDigest output) then
      targetCoverageInputIncrement remaining key before log (payloadOf input) (hashOutputFewTimeView output) input source else 0) = 0 := by
    split_ifs with hgood
    · obtain ⟨payload, rfl⟩ := hgood.1
      rw [payloadOf_tweakableHashInput, targetCoverageInputIncrement_self]
    · rfl
  rw [hzero, add_zero]
  rfl

theorem cachedSignerInputWeight_freshSource (remaining : Nat) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log) :
    cachedSignerInputWeight key message (before.cacheQuery input output)
        (cachedTargetFutureIncrement remaining key (before.cacheQuery input output) log) input =
      if (∃ randomness, input = tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) ∧
          Admissible (truncateMessageDigest output) then
        cachedTargetFutureIncrement remaining key before log input (hashOutputFewTimeView output) else 0 := by
  simp only [cachedSignerInputWeight, QueryCache.cacheQuery_self,
    cachedTargetFutureIncrement_cacheQuery_self remaining key before log input output hfresh hsigned]

theorem expected_freshSourceReuseColumn (remaining : Nat) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hmessage : ∃ randomness, input = tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) :
    ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * cachedFutureCoverage remaining key.parameter key.root before log +
      (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
        cachedSignerInputWeight key message (before.cacheQuery input output)
          (cachedTargetFutureIncrement remaining key (before.cacheQuery input output) log) input) =
      ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * cachedFutureCoverage (remaining + 1) key.parameter key.root before log := by
  simp only [cachedSignerInputWeight_freshSource remaining key message before log input _ hfresh hsigned,
    hmessage, true_and]
  exact expected_freshHashOutput_cachedTargetFutureIncrement remaining key before log input hfresh

end SphincsSecurity.Concrete
