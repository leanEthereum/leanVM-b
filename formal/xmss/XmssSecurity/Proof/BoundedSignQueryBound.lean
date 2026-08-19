import XmssSecurity.Proof.BoundedSign
import XmssSecurity.Proof.EncodingAddressQueryBound

open OracleComp OracleSpec

namespace XmssSecurity

theorem Concrete.signingRandomness_queryBound_zero_encodingAddress
    (parameter : PublicParameter) (epoch : Epoch) :
    (liftM Concrete.signingRandomness : OracleComp OracleWorld Randomness).IsQueryBoundP
      (IsEncodingHashQueryAt parameter epoch) 0 := by
  apply OracleComp.IsQueryBoundP.liftComp_subSpec
    (p := fun _ : unifSpec.Domain => False)
  · intro input
    change False ↔ IsEncodingHashQueryAt parameter epoch (Sum.inl input)
    simp [IsEncodingHashQueryAt]
  · simp

end XmssSecurity
