import XmssSecurity.CappedEncodingPrehitExpectedBound
import XmssSecurity.CappedGlobalChainExpectedAccounting
import XmssSecurity.CappedVerifierUpperBound
import XmssSecurity.LossDecomposition
import XmssSecurity.Statement

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

def HasExpectedGlobalChainOriginBound
    (adversary : Adversary Concrete.scheme) : Prop :=
  Pr[fun result =>
      CappedChain.GlobalWinningOutcomeChainValueHasKeygenOrigin
        result.1.2 result.2.2 result.1.1.2 result.2.1 |
    CappedChain.detailedGameWithKeygenCache adversary] ≤
    (expectedPostKeygenGlobalChainRelevantQueries adversary +
        verifierHashQueryUpperBound + numChains) /
      ((2 ^ digestBits : Nat) : ENNReal)

theorem capped_encodingPrehit_probability_le_expectedDigest
    (adversary : Adversary Concrete.scheme) :
    Pr[WinningEncodingPrehitOccurs |
      cappedDetailedGameWithEncodingTrace adversary] ≤
      CappedEncodingMonitor.expectedPostKeygenEncodingQueries adversary /
        ((2 ^ digestBits : Nat) : ENNReal) := by
  calc
    _ = Pr[fun execution : GameOutcome ×
          (QueryCache HashSpec × SigningCacheTrace) =>
        WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding ∧
          execution.2.2.HasEncodingInputPrehit execution.1.secretKey |
        cappedDetailedGameWithSigningTrace adversary] := by
      rw [← cappedDetailedGameWithEncodingTrace_projection, probEvent_map]
      rfl
    _ ≤ _ :=
      cappedDetailedGameWithSigningTrace_winning_prehit_probability_le_expectedDigest
        adversary

theorem capped_winningEncodingCollision_probability_le_expected
    (adversary : Adversary Concrete.scheme) :
    Pr[fun execution : CappedEncodingTraceExecution =>
      WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
        CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
          execution.2.2 = true |
      cappedDetailedGameWithEncodingTrace adversary] ≤
      CappedEncodingMonitor.expectedPostKeygenEncodingQueries adversary /
        ((2 ^ digestBits : Nat) : ENNReal) := by
  apply (cappedWinning_encoding_monitorHit_probability_le_sampled_external
    adversary).trans
  simpa [HiddenValue.card_digest, div_eq_mul_inv] using
    CappedEncodingMonitor.cappedSampledDetailedGame_externalCollision_probability_le_expected
      adversary

theorem capped_globalWinningChainValueRevealed_probability_le_expected
    (adversary : Adversary Concrete.scheme)
    (hchain : HasExpectedGlobalChainOriginBound adversary) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      GlobalWinningChainValueRevealed execution.2 execution.1 |
      detailedGameWithCache Concrete.scheme adversary] ≤
      (expectedPostKeygenGlobalChainRelevantQueries adversary +
          verifierHashQueryUpperBound + numChains) /
        ((2 ^ digestBits : Nat) : ENNReal) := by
  calc
    _ ≤ Pr[fun result =>
          CappedChain.GlobalWinningOutcomeGuessesKeygenChainValue
            result.1.2 result.2.2 result.1.1.2 result.2.1 |
          CappedChain.detailedGameWithKeygenCache adversary] :=
      CappedChain.globalWinningChainValueRevealed_probability_le_globalKeygenValueGuess
        adversary
    _ ≤ Pr[fun result =>
          CappedChain.GlobalWinningOutcomeChainValueHasKeygenOrigin
            result.1.2 result.2.2 result.1.1.2 result.2.1 |
          CappedChain.detailedGameWithKeygenCache adversary] :=
      CappedChain.globalWinningKeygenValueGuess_probability_le_origin adversary
    _ ≤ _ := hchain

theorem capped_winningDigestBadEvent_probability_le_expected
    (adversary : Adversary Concrete.scheme)
    (hchain : HasExpectedGlobalChainOriginBound adversary) :
    Pr[WinningDigestBadEventOccurs |
      cappedDetailedGameWithEncodingTrace adversary] ≤
      CappedEncodingMonitor.expectedPostKeygenEncodingQueries adversary /
          ((2 ^ digestBits : Nat) : ENNReal) +
        (expectedPostKeygenGlobalChainRelevantQueries adversary +
            verifierHashQueryUpperBound + numChains) /
          ((2 ^ digestBits : Nat) : ENNReal) +
        expectedPostKeygenStructuralQueries adversary /
          ((2 ^ digestBits : Nat) : ENNReal) := by
  let encoding := fun execution : CappedEncodingTraceExecution =>
    WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
      CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
        execution.2.2 = true
  let chain := fun execution : CappedEncodingTraceExecution =>
    GlobalWinningChainValueRevealed execution.2.1.1 execution.1
  let structural := fun execution : CappedEncodingTraceExecution =>
    WinningStructuralCollisionOccurs execution.2.1.1 execution.1
  calc
    Pr[WinningDigestBadEventOccurs |
        cappedDetailedGameWithEncodingTrace adversary] =
      Pr[fun execution => encoding execution ∨
          (chain execution ∨ structural execution) |
        cappedDetailedGameWithEncodingTrace adversary] := by rfl
    _ ≤ Pr[encoding | cappedDetailedGameWithEncodingTrace adversary] +
        (Pr[chain | cappedDetailedGameWithEncodingTrace adversary] +
          Pr[structural | cappedDetailedGameWithEncodingTrace adversary]) := by
      apply (probEvent_or_le _ _ _).trans
      gcongr
      exact probEvent_or_le _ _ _
    _ ≤ CappedEncodingMonitor.expectedPostKeygenEncodingQueries adversary /
          ((2 ^ digestBits : Nat) : ENNReal) +
        ((expectedPostKeygenGlobalChainRelevantQueries adversary +
            verifierHashQueryUpperBound + numChains) /
          ((2 ^ digestBits : Nat) : ENNReal) +
        expectedPostKeygenStructuralQueries adversary /
          ((2 ^ digestBits : Nat) : ENNReal)) := by
      apply add_le_add
      · exact capped_winningEncodingCollision_probability_le_expected adversary
      · apply add_le_add
        · change Pr[fun execution : CappedEncodingTraceExecution =>
            GlobalWinningChainValueRevealed execution.2.1.1 execution.1 |
            cappedDetailedGameWithEncodingTrace adversary] ≤ _
          calc
            _ = Pr[fun execution : GameOutcome × QueryCache HashSpec =>
                  GlobalWinningChainValueRevealed execution.2 execution.1 |
                detailedGameWithCache Concrete.scheme adversary] := by
              rw [← cappedDetailedGameWithEncodingTrace_cache_projection,
                probEvent_map]
              rfl
            _ ≤ _ := capped_globalWinningChainValueRevealed_probability_le_expected
              adversary hchain
        · change Pr[fun execution : CappedEncodingTraceExecution =>
            WinningStructuralCollisionOccurs execution.2.1.1 execution.1 |
            cappedDetailedGameWithEncodingTrace adversary] ≤ _
          calc
            _ = Pr[fun execution : GameOutcome × QueryCache HashSpec =>
                  WinningStructuralCollisionOccurs execution.2 execution.1 |
                detailedGameWithCache Concrete.scheme adversary] := by
              rw [← cappedDetailedGameWithEncodingTrace_cache_projection,
                probEvent_map]
              rfl
            _ ≤ _ :=
              winningStructuralCollision_probability_le_expectedPostKeygenStructuralQueries
                adversary
    _ = _ := by ring

theorem capped_expected_loss_budget_le_127
    (q : Nat) (encoding chain structural : ENNReal)
    (hkeygen : treeHashQueryCount treeHeight ≤ q)
    (hencodingChain : encoding + chain ≤
      (q - treeHashQueryCount treeHeight : Nat))
    (hencodingStructural : encoding + structural ≤
      (q - treeHashQueryCount treeHeight : Nat)) :
    encoding / ((2 ^ digestBits : Nat) : ENNReal) +
        (encoding / ((2 ^ digestBits : Nat) : ENNReal) +
          (chain + verifierHashQueryUpperBound + numChains) /
            ((2 ^ digestBits : Nat) : ENNReal) +
          structural / ((2 ^ digestBits : Nat) : ENNReal)) ≤
      (q : ENNReal) / ((2 ^ 127 : Nat) : ENNReal) := by
  simp only [div_eq_mul_inv]
  have hnumerator :
      encoding + (encoding +
          (chain + verifierHashQueryUpperBound + numChains) +
            structural) ≤
        2 * (q : ENNReal) := by
    calc
      encoding + (encoding +
          (chain + verifierHashQueryUpperBound + numChains) +
            structural) =
          (encoding + chain) + (encoding + structural) +
            (verifierHashQueryUpperBound + numChains) := by ring
      _ ≤ ((q - treeHashQueryCount treeHeight : Nat) : ENNReal) +
          (q - treeHashQueryCount treeHeight : Nat) +
            (verifierHashQueryUpperBound + numChains) := by
        exact add_le_add (add_le_add hencodingChain hencodingStructural) le_rfl
      _ = 2 * (q - treeHashQueryCount treeHeight : Nat) +
          (verifierHashQueryUpperBound + numChains) := by ring
      _ ≤ 2 * (q : ENNReal) := by
        exact_mod_cast (show
          2 * (q - treeHashQueryCount treeHeight) +
              (verifierHashQueryUpperBound + numChains) ≤ 2 * q by
            have hconstant :
                verifierHashQueryUpperBound + numChains ≤
                  2 * treeHashQueryCount treeHeight := by
              decide
            omega)
  calc
    encoding * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
        (encoding * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
          (chain + verifierHashQueryUpperBound + numChains) *
            ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
          structural * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) =
      (encoding + (encoding +
        (chain + verifierHashQueryUpperBound + numChains) +
          structural)) *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by ring
    _ ≤ (2 * (q : ENNReal)) *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by gcongr
    _ = (q : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
        ENNReal.toReal_natCast]
      norm_num [digestBits]
      ring

theorem capped_xmss_forgeAdvantage_le_127_of_globalChainOriginBound
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (hchain : HasExpectedGlobalChainOriginBound adversary) :
    forgeAdvantage Concrete.scheme adversary ≤
      (q : ENNReal) / ((2 ^ 127 : Nat) : ENNReal) := by
  apply (capped_forgeAdvantage_le_encodingPrehit_add_digestBad adversary).trans
  apply (add_le_add
    (capped_encodingPrehit_probability_le_expectedDigest adversary)
    (capped_winningDigestBadEvent_probability_le_expected adversary
      hchain)).trans
  exact capped_expected_loss_budget_le_127 q
    (CappedEncodingMonitor.expectedPostKeygenEncodingQueries adversary)
    (expectedPostKeygenGlobalChainRelevantQueries adversary)
    (expectedPostKeygenStructuralQueries adversary)
    (keygen_hashQueryCount_le adversary q hbound)
    (postKeygenEncoding_add_globalChainRelevant_expected_le q adversary hbound)
    (postKeygenEncoding_add_structural_expected_le q adversary hbound)

def HasExpectedGlobalChainOriginBounds : Prop :=
  ∀ adversary : Adversary Concrete.scheme,
    HasExpectedGlobalChainOriginBound adversary

theorem xmss_has_127_bits_of_classical_security_of_globalChainOriginBounds
    (hchain : HasExpectedGlobalChainOriginBounds) :
    XmssHasClassicalSecurityBits 127 := by
  change HasClassicalSecurityBits xmssScheme 127
  intro q _hq
  unfold forgeAtMost
  refine iSup_le fun adversary => iSup_le fun hbound => ?_
  exact capped_xmss_forgeAdvantage_le_127_of_globalChainOriginBound
    q adversary hbound (hchain adversary)

end XmssSecurity
