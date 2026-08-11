import XmssSecurity.ConcreteKeygen
import XmssSecurity.ConcreteSign
import XmssSecurity.ConcreteVerify

namespace XmssSecurity.Concrete

noncomputable def scheme : Scheme where
  keygen := Concrete.keygen
  sign := Concrete.sign
  verify := Concrete.verify

end XmssSecurity.Concrete
