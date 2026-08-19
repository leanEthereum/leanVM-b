import XmssSecurity.CappedEncodingPrehitExpectedBound
import XmssSecurity.CappedUnifiedExpectedDigest
import XmssSecurity.LossDecomposition
import XmssSecurity.Statement

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

def WinningFirstLaneBadEventOccurs
    (execution : CappedEncodingTraceExecution) : Prop :=
  (WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
      CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
        execution.2.2 = true) ∨
    GlobalWinningChainValueRevealed execution.2.1.1 execution.1

def WinningSecondLaneBadEventOccurs
    (execution : CappedEncodingTraceExecution) : Prop :=
  WinningEncodingPrehitOccurs execution ∨
    WinningStructuralCollisionOccurs execution.2.1.1 execution.1

def HasFirstLaneBound
    (q : Nat) (adversary : Adversary Concrete.scheme) : Prop :=
  Pr[WinningFirstLaneBadEventOccurs |
      cappedDetailedGameWithEncodingTrace adversary] ≤
    ((q - treeHashQueryCount treeHeight : Nat) + numChains : Nat) /
      ((2 ^ digestBits : Nat) : ENNReal)

def HasSecondLaneBound
    (q : Nat) (adversary : Adversary Concrete.scheme) : Prop :=
  Pr[WinningSecondLaneBadEventOccurs |
      cappedDetailedGameWithEncodingTrace adversary] ≤
    (q - treeHashQueryCount treeHeight : Nat) /
      ((2 ^ digestBits : Nat) : ENNReal)

theorem capped_encodingPrehit_probability_le_expectedDigest_for_lane
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

theorem hasSecondLaneBound_of_hashQueryBound
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    HasSecondLaneBound q adversary := by
  let encoding := CappedEncodingMonitor.expectedPostKeygenEncodingQueries adversary
  let structural := expectedPostKeygenStructuralQueries adversary
  have hstructural :
      Pr[fun execution : CappedEncodingTraceExecution =>
          WinningStructuralCollisionOccurs execution.2.1.1 execution.1 |
        cappedDetailedGameWithEncodingTrace adversary] ≤
      structural / ((2 ^ digestBits : Nat) : ENNReal) := by
    change Pr[fun execution : CappedEncodingTraceExecution =>
          WinningStructuralCollisionOccurs execution.2.1.1 execution.1 |
        cappedDetailedGameWithEncodingTrace adversary] ≤
      expectedPostKeygenStructuralQueries adversary /
        ((2 ^ digestBits : Nat) : ENNReal)
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
  unfold HasSecondLaneBound WinningSecondLaneBadEventOccurs
  calc
    Pr[fun execution : CappedEncodingTraceExecution =>
        WinningEncodingPrehitOccurs execution ∨
          WinningStructuralCollisionOccurs execution.2.1.1 execution.1 |
      cappedDetailedGameWithEncodingTrace adversary] ≤
      Pr[WinningEncodingPrehitOccurs |
          cappedDetailedGameWithEncodingTrace adversary] +
        Pr[fun execution : CappedEncodingTraceExecution =>
            WinningStructuralCollisionOccurs execution.2.1.1 execution.1 |
          cappedDetailedGameWithEncodingTrace adversary] :=
      probEvent_or_le _ _ _
    _ ≤ encoding / ((2 ^ digestBits : Nat) : ENNReal) +
        structural / ((2 ^ digestBits : Nat) : ENNReal) :=
      add_le_add
        (capped_encodingPrehit_probability_le_expectedDigest_for_lane adversary)
        hstructural
    _ = (encoding + structural) /
        ((2 ^ digestBits : Nat) : ENNReal) := by
      simp only [div_eq_mul_inv, add_mul]
    _ ≤ (q - treeHashQueryCount treeHeight : Nat) /
        ((2 ^ digestBits : Nat) : ENNReal) := by
      gcongr
      exact postKeygenEncoding_add_structural_expected_le q adversary hbound

theorem capped_winning_implies_firstLane_or_secondLane
    (adversary : Adversary Concrete.scheme)
    (execution : CappedEncodingTraceExecution)
    (hmem : execution ∈ support
      (cappedDetailedGameWithEncodingTrace adversary))
    (hwin : execution.1.won = true) :
    WinningFirstLaneBadEventOccurs execution ∨
      WinningSecondLaneBadEventOccurs execution := by
  rcases capped_winning_implies_encodingPrehit_or_digestBad
      adversary execution hmem hwin with hprehit | hdigest
  · exact Or.inr (Or.inl hprehit)
  · rcases hdigest with hencoding | hchain | hstructural
    · exact Or.inl (Or.inl hencoding)
    · exact Or.inl (Or.inr hchain)
    · exact Or.inr (Or.inr hstructural)

theorem capped_forgeAdvantage_le_firstLane_add_secondLane
    (adversary : Adversary Concrete.scheme) :
    forgeAdvantage Concrete.scheme adversary ≤
      Pr[WinningFirstLaneBadEventOccurs |
        cappedDetailedGameWithEncodingTrace adversary] +
      Pr[WinningSecondLaneBadEventOccurs |
        cappedDetailedGameWithEncodingTrace adversary] := by
  calc
    forgeAdvantage Concrete.scheme adversary =
        Pr[fun execution : CappedEncodingTraceExecution =>
          execution.1.won = true |
          cappedDetailedGameWithEncodingTrace adversary] := by
      rw [forgeAdvantage_eq_detailedGameWithCache,
        ← cappedDetailedGameWithEncodingTrace_cache_projection, probEvent_map]
      rfl
    _ ≤ Pr[fun execution : CappedEncodingTraceExecution =>
          WinningFirstLaneBadEventOccurs execution ∨
            WinningSecondLaneBadEventOccurs execution |
          cappedDetailedGameWithEncodingTrace adversary] := by
      apply probEvent_mono
      intro execution hmem hwin
      exact capped_winning_implies_firstLane_or_secondLane
        adversary execution hmem hwin
    _ ≤ _ := probEvent_or_le _ _ _

theorem capped_two_lane_loss_budget_le_127
    (q : Nat) (hkeygen : treeHashQueryCount treeHeight ≤ q) :
    ((q - treeHashQueryCount treeHeight : Nat) + numChains : Nat) /
          ((2 ^ digestBits : Nat) : ENNReal) +
        (q - treeHashQueryCount treeHeight : Nat) /
          ((2 ^ digestBits : Nat) : ENNReal) ≤
      (q : ENNReal) / ((2 ^ 127 : Nat) : ENNReal) := by
  simp only [div_eq_mul_inv]
  have hnumerator :
      (((q - treeHashQueryCount treeHeight : Nat) + numChains : Nat) :
          ENNReal) +
        (q - treeHashQueryCount treeHeight : Nat) ≤ 2 * (q : ENNReal) := by
    exact_mod_cast (show
      (q - treeHashQueryCount treeHeight + numChains) +
          (q - treeHashQueryCount treeHeight) ≤ 2 * q by
      have hconstant : numChains ≤ 2 * treeHashQueryCount treeHeight := by
        decide
      omega)
  calc
    (((q - treeHashQueryCount treeHeight : Nat) + numChains : Nat) :
        ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
        (q - treeHashQueryCount treeHeight : Nat) *
          ((2 ^ digestBits : Nat) : ENNReal)⁻¹ =
      ((((q - treeHashQueryCount treeHeight : Nat) + numChains : Nat) :
          ENNReal) +
        (q - treeHashQueryCount treeHeight : Nat)) *
          ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by ring
    _ ≤ (2 * (q : ENNReal)) *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by gcongr
    _ = (q : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
        ENNReal.toReal_natCast]
      norm_num [digestBits]
      ring

theorem capped_xmss_forgeAdvantage_le_127_of_twoLaneBounds
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (hfirst : HasFirstLaneBound q adversary)
    (hsecond : HasSecondLaneBound q adversary) :
    forgeAdvantage Concrete.scheme adversary ≤
      (q : ENNReal) / ((2 ^ 127 : Nat) : ENNReal) := by
  calc
    forgeAdvantage Concrete.scheme adversary ≤
        Pr[WinningFirstLaneBadEventOccurs |
          cappedDetailedGameWithEncodingTrace adversary] +
        Pr[WinningSecondLaneBadEventOccurs |
          cappedDetailedGameWithEncodingTrace adversary] :=
      capped_forgeAdvantage_le_firstLane_add_secondLane adversary
    _ ≤ ((q - treeHashQueryCount treeHeight : Nat) + numChains : Nat) /
          ((2 ^ digestBits : Nat) : ENNReal) +
        (q - treeHashQueryCount treeHeight : Nat) /
          ((2 ^ digestBits : Nat) : ENNReal) := add_le_add hfirst hsecond
    _ ≤ _ := capped_two_lane_loss_budget_le_127 q
      (keygen_hashQueryCount_le adversary q hbound)

def HasFirstLaneBounds : Prop :=
  ∀ (q : Nat) (adversary : Adversary Concrete.scheme),
    HasHashQueryBound Concrete.scheme adversary q →
      HasFirstLaneBound q adversary

theorem xmss_has_127_bits_of_classical_security_of_firstLaneBounds
    (hfirst : HasFirstLaneBounds) :
    XmssHasClassicalSecurityBits 127 := by
  change HasClassicalSecurityBits xmssScheme 127
  intro q _hq
  unfold forgeAtMost
  refine iSup_le fun adversary => iSup_le fun hbound => ?_
  exact capped_xmss_forgeAdvantage_le_127_of_twoLaneBounds
    q adversary hbound (hfirst q adversary hbound)
      (hasSecondLaneBound_of_hashQueryBound q adversary hbound)

end XmssSecurity
