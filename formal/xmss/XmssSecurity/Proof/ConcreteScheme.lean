import XmssSecurity.Proof.CacheReplayEval
import XmssSecurity.Proof.LazyScheme

namespace XmssSecurity.Concrete

noncomputable def singleAttemptScheme : Scheme where
  keygen := Concrete.keygen
  sign := Concrete.sign
  verify := fun publicKey epoch message signature =>
    liftM (Concrete.verify publicKey epoch message signature : OracleComp HashSpec Bool)

end XmssSecurity.Concrete
