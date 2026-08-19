import XmssSecurity.Proof.HashAddress
import VCVio.OracleComp.QueryTracking.SubSpec

open OracleComp OracleSpec

namespace XmssSecurity

def IsEncodingHashQueryAt (parameter : PublicParameter) (epoch : Epoch) :
    OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr hashInput => AtHashAddress parameter (.encoding epoch) hashInput

noncomputable instance (parameter : PublicParameter) (epoch : Epoch) :
    DecidablePred (IsEncodingHashQueryAt parameter epoch) :=
  Classical.decPred _

end XmssSecurity
