import XmssSecurity.CappedSigningLogReplay
import XmssSecurity.MainTheorem

namespace XmssSecurity

/-- The concrete XMSS scheme with at most `2^23` encoding attempts per signing request has at least 120 bits of classical security in the random-oracle game. -/
theorem xmss_has_120_bits_of_classical_security :
    HasClassicalSecurityBits Concrete.cappedScheme 120 := by
  sorry

end XmssSecurity
