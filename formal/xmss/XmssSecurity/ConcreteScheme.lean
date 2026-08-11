import XmssSecurity.ConcreteKeygen
import XmssSecurity.ConcreteSign
import XmssSecurity.ConcreteVerify

namespace XmssSecurity.Concrete

noncomputable def scheme : Scheme where
  keygen := Concrete.keygen
  sign := Concrete.sign
  verify := fun publicKey epoch message signature =>
    liftM (Concrete.verify publicKey epoch message signature : OracleComp HashSpec Bool)

end XmssSecurity.Concrete
