import XmssSecurity.Encoding
import XmssSecurity.ConcreteScheme
import XmssSecurity.ForgeryCases
import XmssSecurity.HiddenValue
import XmssSecurity.IndexedHiddenValue
import XmssSecurity.LeafEventProbability
import XmssSecurity.Merkle
import XmssSecurity.SecurityBudget
import XmssSecurity.SecurityGame
import XmssSecurity.SigningLogReplay
import XmssSecurity.Wots

namespace XmssSecurity

open OracleSpec

/-- The remaining non-leaf cryptographic argument below the digest-space size bounds one concrete event with 128-bit loss. -/
theorem xmss_nonLeaf_badEvent_probability_le_below_digest_space (q : Nat) (hq : 1 ≤ q)
    (hqlt : q < 2 ^ digestBits)
    (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) (event : BadEvent)
    (hne : event ≠ .leaf) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      OutcomeBadEventOccurs execution.2 execution.1 event |
      detailedGameWithCache Concrete.scheme adversary] ≤
      (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  sorry

/-- Every event below the digest-space size has cost at most `q / 2^128`; the leaf case is fully proved. -/
theorem xmss_badEvent_probability_le_below_digest_space (q : Nat) (hq : 1 ≤ q)
    (hqlt : q < 2 ^ digestBits)
    (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) (event : BadEvent) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      OutcomeBadEventOccurs execution.2 execution.1 event |
      detailedGameWithCache Concrete.scheme adversary] ≤
      (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  by_cases hleaf : event = .leaf
  · subst event
    exact leaf_outcomeBadEvent_probability_le q adversary hbound
  · exact xmss_nonLeaf_badEvent_probability_le_below_digest_space q hq hqlt adversary
      hbound event hleaf

/-- Every concrete event has probability at most `q / 2^128`; above `2^128` queries this is the trivial probability bound. -/
theorem xmss_badEvent_probability_le (q : Nat) (hq : 1 ≤ q)
    (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) (event : BadEvent) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      OutcomeBadEventOccurs execution.2 execution.1 event |
      detailedGameWithCache Concrete.scheme adversary] ≤
      (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  by_cases hqlt : q < 2 ^ digestBits
  · exact xmss_badEvent_probability_le_below_digest_space q hq hqlt adversary hbound event
  · apply probEvent_le_one.trans
    rw [ENNReal.le_div_iff_mul_le]
    · exact_mod_cast Nat.le_of_not_gt hqlt
    · simp
    · simp

/-- Every bounded adversary has forging probability at most `q / 2^120`. -/
theorem xmss_forgeAdvantage_le (q : Nat) (hq : 1 ≤ q)
    (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    forgeAdvantage Concrete.scheme adversary ≤ (q : ENNReal) / ((2 ^ 120 : Nat) : ENNReal) := by
  refine (forgeAdvantage_le_outcomeBadEvent_sum adversary).trans ?_
  apply badEvent_sum_le_120
  intro event
  exact xmss_badEvent_probability_le q hq adversary hbound event

/-- The concrete XMSS scheme has at least 120 bits of classical security in the random-oracle game. -/
theorem xmss_has_120_bits_of_classical_security :
    HasClassicalSecurityBits Concrete.scheme 120 := by
  intro q hq
  unfold forgeAtMost
  refine iSup_le fun adversary => iSup_le fun hbound => ?_
  exact xmss_forgeAdvantage_le q hq adversary hbound

end XmssSecurity
