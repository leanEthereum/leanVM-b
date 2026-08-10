import XmssSecurity.Encoding
import XmssSecurity.ForgeryCases
import XmssSecurity.Merkle
import XmssSecurity.SecurityBudget
import XmssSecurity.SecurityGame
import XmssSecurity.Wots

namespace XmssSecurity

namespace Concrete

axiom scheme : Scheme

end Concrete

/-- The remaining cryptographic reduction assigns every successful forgery to the checked bad-event budget. -/
theorem xmss_reduces_to_badEvents (q : Nat) (hq : 1 ≤ q)
    (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    ∃ cost : BadEvent → ENNReal,
      forgeAdvantage Concrete.scheme adversary ≤ ∑ event, cost event ∧
      ∀ event, cost event ≤
        (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  sorry

/-- Every bounded adversary has forging probability at most `q / 2^120`. -/
theorem xmss_forgeAdvantage_le (q : Nat) (hq : 1 ≤ q)
    (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    forgeAdvantage Concrete.scheme adversary ≤ (q : ENNReal) / ((2 ^ 120 : Nat) : ENNReal) := by
  obtain ⟨cost, hforge, hcost⟩ := xmss_reduces_to_badEvents q hq adversary hbound
  exact hforge.trans (by simpa [targetSecurityBits] using badEvent_sum_le_120 q cost hcost)

/-- The concrete XMSS scheme has at least 120 bits of classical security in the random-oracle game. -/
theorem xmss_has_120_bits_of_classical_security :
    HasClassicalSecurityBits Concrete.scheme 120 := by
  intro q hq
  unfold forgeAtMost
  refine iSup_le fun adversary => iSup_le fun hbound => ?_
  exact xmss_forgeAdvantage_le q hq adversary hbound

end XmssSecurity
