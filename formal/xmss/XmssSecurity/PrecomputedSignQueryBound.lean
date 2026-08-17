import XmssSecurity.PrecomputedSign
import XmssSecurity.BoundedSignQueryBound

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

theorem Concrete.precomputedSignAttempt_queryBound_encodingAddress
    (secretKey : SecretKey) (epoch targetEpoch : Epoch)
    (message : Message) (randomness : Randomness) :
    (Concrete.precomputedSignAttempt secretKey epoch message randomness :
      OracleComp HashSpec (Option Signature)).IsQueryBoundP
        (AtHashAddress secretKey.parameter (.encoding targetEpoch))
        (if epoch = targetEpoch then 1 else 0) := by
  rw [Concrete.precomputedSignAttempt]
  by_cases hepoch : epoch = targetEpoch
  · subst targetEpoch
    rw [if_pos rfl]
    refine OracleComp.isQueryBoundP_bind (m := 0) ?_ ?_
    · simpa [Concrete.encodingHash] using
        Concrete.tweakableHash_queryBound_atAddress secretKey.parameter
          (.encoding epoch) (Concrete.encodingPayload message randomness)
    · intro digest _
      split <;> simp
  · rw [if_neg hepoch]
    refine OracleComp.isQueryBoundP_bind (m := 0) ?_ ?_
    · simpa [Concrete.encodingHash] using
        Concrete.tweakableHash_queryBound_atOtherAddress secretKey.parameter
          (.encoding targetEpoch) (.encoding epoch)
            (Concrete.encodingPayload message randomness) (by
              simpa only [HashDomain.encoding.injEq, ne_eq] using hepoch)
    · intro digest _
      split <;> simp

theorem Concrete.precomputedSignAttempt_lift_queryBound_encodingAddress
    (secretKey : SecretKey) (epoch targetEpoch : Epoch)
    (message : Message) (randomness : Randomness) :
    (liftM (Concrete.precomputedSignAttempt secretKey epoch message randomness :
      OracleComp HashSpec (Option Signature)) :
        OracleComp OracleWorld (Option Signature)).IsQueryBoundP
      (IsEncodingHashQueryAt secretKey.parameter targetEpoch)
      (if epoch = targetEpoch then 1 else 0) := by
  apply OracleComp.IsQueryBoundP.liftComp_subSpec
    (p := AtHashAddress secretKey.parameter (.encoding targetEpoch))
  · intro input
    change AtHashAddress secretKey.parameter (.encoding targetEpoch) input ↔
      IsEncodingHashQueryAt secretKey.parameter targetEpoch (Sum.inr input)
    rfl
  · exact Concrete.precomputedSignAttempt_queryBound_encodingAddress
      secretKey epoch targetEpoch message randomness

theorem Concrete.precomputedSignBoundedAttempts_queryBound_encodingAddress
    (attempts : Nat) (secretKey : SecretKey) (epoch targetEpoch : Epoch)
    (message : Message) :
    (Concrete.precomputedSignBoundedAttempts attempts secretKey epoch message).IsQueryBoundP
      (IsEncodingHashQueryAt secretKey.parameter targetEpoch)
      (attempts * if epoch = targetEpoch then 1 else 0) := by
  induction attempts with
  | zero => simp [Concrete.precomputedSignBoundedAttempts]
  | succ attempts ih =>
      rw [Concrete.precomputedSignBoundedAttempts]
      refine (OracleComp.isQueryBoundP_bind
        (n := 0)
        (m := (if epoch = targetEpoch then 1 else 0) +
          attempts * if epoch = targetEpoch then 1 else 0)
        (Concrete.signingRandomness_queryBound_zero_encodingAddress
          secretKey.parameter targetEpoch) ?_).mono (by
            by_cases hepoch : epoch = targetEpoch
            · simp [hepoch]
              omega
            · simp [hepoch])
      intro randomness _
      refine (OracleComp.isQueryBoundP_bind
        (n := if epoch = targetEpoch then 1 else 0)
        (m := attempts * if epoch = targetEpoch then 1 else 0)
        (Concrete.precomputedSignAttempt_lift_queryBound_encodingAddress
          secretKey epoch targetEpoch message randomness) ?_).mono (by omega)
      intro result _
      cases result with
      | none => exact ih
      | some signature => simp

theorem Concrete.precomputedCappedSign_queryBound_encodingAddress
    (publicKey : PublicKey) (secretKey : SecretKey) (epoch targetEpoch : Epoch)
    (message : Message) :
    (Concrete.precomputedCappedSign publicKey secretKey epoch message).IsQueryBoundP
      (IsEncodingHashQueryAt secretKey.parameter targetEpoch)
      (signingAttemptLimit * if epoch = targetEpoch then 1 else 0) := by
  unfold Concrete.precomputedCappedSign
  exact Concrete.precomputedSignBoundedAttempts_queryBound_encodingAddress
    signingAttemptLimit secretKey epoch targetEpoch message

end XmssSecurity
