import XmssSecurity.PrecomputedSign

namespace XmssSecurity.Concrete

noncomputable def singleAttemptScheme : Scheme where
  keygen := Concrete.keygen
  sign := Concrete.sign
  verify := fun publicKey epoch message signature =>
    liftM (Concrete.verify publicKey epoch message signature : OracleComp HashSpec Bool)

noncomputable def scheme : Scheme where
  keygen := Concrete.precomputedKeygen
  sign := Concrete.precomputedCappedSign
  verify := fun publicKey epoch message signature =>
    liftM (Concrete.verify publicKey epoch message signature : OracleComp HashSpec Bool)

end XmssSecurity.Concrete
