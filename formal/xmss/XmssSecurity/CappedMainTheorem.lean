import XmssSecurity.CappedSigningLogReplay
import XmssSecurity.MainTheorem

namespace XmssSecurity

open OracleSpec

/-- The remaining capped-signer proof obligation is a weighted bound for each concrete bad event below the digest-space size. -/
theorem capped_xmss_badEvent_probability_le_below_digest_space
    (q : Nat) (hq : 1 ≤ q) (hqlt : q < 2 ^ digestBits)
    (adversary : Adversary Concrete.cappedScheme)
    (hbound : HasHashQueryBound Concrete.cappedScheme adversary q)
    (event : BadEvent) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      WinningOutcomeBadEventOccurs execution.2 execution.1 event |
      detailedGameWithCache Concrete.cappedScheme adversary] ≤
      (badEventWeight event : ENNReal) *
        ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) := by
  sorry

theorem capped_xmss_badEvent_probability_le
    (q : Nat) (hq : 1 ≤ q)
    (adversary : Adversary Concrete.cappedScheme)
    (hbound : HasHashQueryBound Concrete.cappedScheme adversary q)
    (event : BadEvent) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      WinningOutcomeBadEventOccurs execution.2 execution.1 event |
      detailedGameWithCache Concrete.cappedScheme adversary] ≤
      (badEventWeight event : ENNReal) *
        ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) := by
  by_cases hqlt : q < 2 ^ digestBits
  · exact capped_xmss_badEvent_probability_le_below_digest_space
      q hq hqlt adversary hbound event
  · apply probEvent_le_one.trans
    have hbase : 1 ≤ (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
      rw [ENNReal.le_div_iff_mul_le]
      · exact_mod_cast Nat.le_of_not_gt hqlt
      · simp
      · simp
    calc
      1 ≤ (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := hbase
      _ ≤ (badEventWeight event : ENNReal) *
          ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) := by
        cases event <;> simp [badEventWeight]
        all_goals
          rw [two_mul]
          exact le_add_right (α := ENNReal) le_rfl

theorem capped_xmss_forgeAdvantage_le
    (q : Nat) (hq : 1 ≤ q)
    (adversary : Adversary Concrete.cappedScheme)
    (hbound : HasHashQueryBound Concrete.cappedScheme adversary q) :
    forgeAdvantage Concrete.cappedScheme adversary ≤
      (q : ENNReal) / ((2 ^ 120 : Nat) : ENNReal) := by
  refine (capped_forgeAdvantage_le_winningOutcomeBadEvent_sum adversary).trans ?_
  apply badEvent_weighted_sum_le_120
  intro event
  exact capped_xmss_badEvent_probability_le q hq adversary hbound event

/-- The concrete XMSS scheme with at most `2^23` encoding attempts per signing request has at least 120 bits of classical security in the random-oracle game. -/
theorem xmss_has_120_bits_of_classical_security :
    HasClassicalSecurityBits Concrete.cappedScheme 120 := by
  intro q hq
  unfold forgeAtMost
  refine iSup_le fun adversary => iSup_le fun hbound => ?_
  exact capped_xmss_forgeAdvantage_le q hq adversary hbound

end XmssSecurity
