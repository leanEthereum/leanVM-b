import XmssSecurity.Proof.PostKeygenFirstLane

namespace XmssSecurity.Proof

theorem concreteScheme_has_127_bits_of_classical_security :
    HasPostKeygenClassicalSecurityBits Concrete.scheme 127 :=
  CappedChain.concreteScheme_has_postKeygen_127_bits_of_classical_security

end XmssSecurity.Proof
