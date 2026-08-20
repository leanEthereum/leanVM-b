import XmssSecurity.Proof.CappedEncodingPrehitExpectedBound
import XmssSecurity.Proof.CappedUnifiedExpectedDigest
import XmssSecurity.Proof.LossDecomposition

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

def WinningSecondLaneBadEventOccurs
    (execution : CappedEncodingTraceExecution) : Prop :=
  WinningEncodingPrehitOccurs execution ∨
    WinningStructuralCollisionOccurs execution.2.1.1 execution.1

def HasSecondLaneBound
    (q : Nat) (adversary : Adversary) : Prop :=
  Pr[WinningSecondLaneBadEventOccurs |
      cappedDetailedGameWithEncodingTrace adversary] ≤
    (q - treeHashQueryCount treeHeight : Nat) /
      ((2 ^ digestBits : Nat) : ENNReal)

theorem capped_encodingPrehit_probability_le_expectedDigest_for_lane
    (adversary : Adversary) :
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
    (q : Nat) (adversary : Adversary)
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

end XmssSecurity
