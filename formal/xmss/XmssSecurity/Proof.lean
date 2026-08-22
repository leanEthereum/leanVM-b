import XmssSecurity.Proof.CappedExactFirstLaneBound

namespace XmssSecurity.Proof

theorem concreteScheme_has_127_bits_of_classical_security :
    HasClassicalSecurityBits Concrete.scheme 127 :=
  xmss_has_127_bits_of_classical_security_of_exactFirstLaneBounds
    CappedChain.hasExactFirstLaneBounds

end XmssSecurity.Proof
