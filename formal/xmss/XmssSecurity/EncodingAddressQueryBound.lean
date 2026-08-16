import XmssSecurity.ConcreteQueryBound
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

theorem Concrete.signAttempt_queryBound_encodingAddress
    (secretKey : SecretKey) (epoch targetEpoch : Epoch)
    (message : Message) (randomness : Randomness) :
    (Concrete.signAttempt secretKey epoch message randomness :
      OracleComp HashSpec (Option Signature)).IsQueryBoundP
        (AtHashAddress secretKey.parameter (.encoding targetEpoch))
        (if epoch = targetEpoch then 1 else 0) := by
  rw [Concrete.signAttempt]
  by_cases hepoch : epoch = targetEpoch
  · subst targetEpoch
    rw [if_pos rfl]
    refine OracleComp.isQueryBoundP_bind (m := 0) ?_ ?_
    · simpa [Concrete.encodingHash] using
        Concrete.tweakableHash_queryBound_atAddress secretKey.parameter
          (.encoding epoch) (Concrete.encodingPayload message randomness)
    · intro digest _
      split
      · simp
      · apply (OracleComp.isQueryBoundP_map_iff _
            (fun signature => some signature) 0).2
        exact (Concrete.signWithEncoding_queryBound_zero_encodingAddress
          secretKey epoch epoch randomness _)
  · simp only [if_neg hepoch]
    refine OracleComp.isQueryBoundP_bind (m := 0) ?_ ?_
    · simpa [Concrete.encodingHash] using
        Concrete.tweakableHash_queryBound_atOtherAddress secretKey.parameter
          (.encoding targetEpoch) (.encoding epoch)
            (Concrete.encodingPayload message randomness) (by
              simpa only [HashDomain.encoding.injEq, ne_eq] using hepoch)
    · intro digest _
      split
      · simp
      · apply (OracleComp.isQueryBoundP_map_iff _
            (fun signature => some signature) 0).2
        exact Concrete.signWithEncoding_queryBound_zero_encodingAddress
          secretKey epoch targetEpoch randomness _

end XmssSecurity
