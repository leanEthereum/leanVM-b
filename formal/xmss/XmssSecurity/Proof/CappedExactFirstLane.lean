import XmssSecurity.Proof.CappedJointExactLoss

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

def WinningExactFirstLaneBadEventOccurs
    (execution : CappedEncodingTraceExecution) : Prop :=
  ((WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
      ¬WinningEncodingPrehitOccurs execution) ∨
    GlobalWinningChainValueRevealed execution.2.1.1 execution.1)

def HasExactFirstLaneBound
    (q : Nat) (adversary : Adversary) : Prop :=
  Pr[WinningExactFirstLaneBadEventOccurs |
      cappedDetailedGameWithEncodingTrace adversary] ≤
    ((q - treeHashQueryCount treeHeight : Nat) + numChains : Nat) /
      ((2 ^ digestBits : Nat) : ENNReal)

theorem capped_winning_implies_exactFirstLane_or_secondLane
    (adversary : Adversary)
    (execution : CappedEncodingTraceExecution)
    (hmem : execution ∈ support
      (cappedDetailedGameWithEncodingTrace adversary))
    (hwin : execution.1.won = true) :
    WinningExactFirstLaneBadEventOccurs execution ∨
      WinningSecondLaneBadEventOccurs execution := by
  by_cases hprehit : WinningEncodingPrehitOccurs execution
  · exact Or.inr (Or.inl hprehit)
  · rcases capped_winning_implies_encodingPrehit_or_digestBad
        adversary execution hmem hwin with hprehit' | hdigest
    · exact (hprehit hprehit').elim
    · rcases hdigest with hencoding | hchain | hstructural
      · exact Or.inl (Or.inl ⟨hencoding.1, hprehit⟩)
      · exact Or.inl (Or.inr hchain)
      · exact Or.inr (Or.inr hstructural)

theorem capped_forgeAdvantage_le_exactFirstLane_add_secondLane
    (adversary : Adversary) :
    forgeAdvantage Concrete.scheme adversary ≤
      Pr[WinningExactFirstLaneBadEventOccurs |
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
          WinningExactFirstLaneBadEventOccurs execution ∨
            WinningSecondLaneBadEventOccurs execution |
          cappedDetailedGameWithEncodingTrace adversary] := by
      apply probEvent_mono
      intro execution hmem hwin
      exact capped_winning_implies_exactFirstLane_or_secondLane
        adversary execution hmem hwin
    _ ≤ _ := probEvent_or_le _ _ _

theorem capped_xmss_forgeAdvantage_le_127_of_exactTwoLaneBounds
    (q : Nat) (adversary : Adversary)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (hfirst : HasExactFirstLaneBound q adversary)
    (hsecond : HasSecondLaneBound q adversary) :
    forgeAdvantage Concrete.scheme adversary ≤
      (q : ENNReal) / ((2 ^ 127 : Nat) : ENNReal) := by
  calc
    forgeAdvantage Concrete.scheme adversary ≤
        Pr[WinningExactFirstLaneBadEventOccurs |
          cappedDetailedGameWithEncodingTrace adversary] +
        Pr[WinningSecondLaneBadEventOccurs |
          cappedDetailedGameWithEncodingTrace adversary] :=
      capped_forgeAdvantage_le_exactFirstLane_add_secondLane adversary
    _ ≤ ((q - treeHashQueryCount treeHeight : Nat) + numChains : Nat) /
          ((2 ^ digestBits : Nat) : ENNReal) +
        (q - treeHashQueryCount treeHeight : Nat) /
          ((2 ^ digestBits : Nat) : ENNReal) := add_le_add hfirst hsecond
    _ ≤ _ := capped_two_lane_loss_budget_le_127 q
      (keygen_hashQueryCount_le adversary q hbound)

def HasExactFirstLaneBounds : Prop :=
  ∀ (q : Nat) (adversary : Adversary),
    HasHashQueryBound Concrete.scheme adversary q →
      HasExactFirstLaneBound q adversary

theorem xmss_has_127_bits_of_classical_security_of_exactFirstLaneBounds
    (hfirst : HasExactFirstLaneBounds) :
    HasClassicalSecurityBits Concrete.scheme 127 := by
  intro q _hq adversary hbound
  exact capped_xmss_forgeAdvantage_le_127_of_exactTwoLaneBounds
    q adversary hbound (hfirst q adversary hbound)
      (hasSecondLaneBound_of_hashQueryBound q adversary hbound)

end XmssSecurity
