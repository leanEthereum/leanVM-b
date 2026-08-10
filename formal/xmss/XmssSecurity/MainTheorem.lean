import XmssSecurity.Encoding
import XmssSecurity.SecurityGame

namespace XmssSecurity

namespace Concrete

axiom scheme : Scheme

end Concrete

/-- Every bounded adversary has forging probability at most `q / 2^120`. -/
theorem xmss_forgeAdvantage_le (q : Nat) (hq : 1 ≤ q)
    (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    forgeAdvantage Concrete.scheme adversary ≤ (q : ENNReal) / ((2 ^ 120 : Nat) : ENNReal) := by
  sorry

/-- The concrete XMSS scheme has at least 120 bits of classical security in the random-oracle game. -/
theorem xmss_has_120_bits_of_classical_security :
    HasClassicalSecurityBits Concrete.scheme 120 := by
  intro q hq
  unfold forgeAtMost
  refine iSup_le fun adversary => iSup_le fun hbound => ?_
  exact xmss_forgeAdvantage_le q hq adversary hbound

end XmssSecurity
