import XmssSecurity.Proof.ConcreteQueryBound

open OracleComp OracleSpec

namespace XmssSecurity

theorem Concrete.precomputedSignAttempt_queryBound_zero_at_other_encodingInput
    (secretKey : SecretKey) (epoch targetEpoch : Epoch)
    (message : Message) (randomness : Randomness) (targetInput : Message × Randomness)
    (hne : Concrete.CacheView.encodingInput secretKey.parameter epoch
        (message, randomness) ≠
      Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) :
    (Concrete.precomputedSignAttempt secretKey epoch message randomness :
      OracleComp HashSpec (Option Signature)).IsQueryBoundP
        (· = Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) 0 := by
  rw [Concrete.precomputedSignAttempt]
  refine OracleComp.isQueryBoundP_bind (m := 0)
    (Concrete.encodingHash_queryBound_zero_at_other_input secretKey.parameter epoch
      message randomness
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) hne) ?_
  intro digest _
  split <;> simp

end XmssSecurity
