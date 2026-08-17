import XmssSecurity.PrecomputedSign

open OracleComp

namespace XmssSecurity.Concrete

noncomputable def precomputedCappedScheme : Scheme where
  keygen := precomputedKeygen
  sign := precomputedCappedSign
  verify := fun publicKey epoch message signature =>
    liftM (verify publicKey epoch message signature : OracleComp HashSpec Bool)

end XmssSecurity.Concrete
