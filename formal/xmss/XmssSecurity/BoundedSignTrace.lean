import XmssSecurity.BoundedSignQueryBound

open OracleComp OracleSpec

namespace XmssSecurity

theorem Concrete.signBoundedAttempts_traced_sign_epoch_count_le
    (attempts : Nat) (secretKey : SecretKey)
    (epoch targetEpoch : Epoch) (message : Message)
    (cache : QueryCache HashSpec)
    (result : (Option Signature × QueryCache HashSpec) × EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((simulateQ (splitXmssRomImpl secretKey.parameter .sign)
          (Concrete.signBoundedAttempts attempts secretKey epoch message)).run cache)).run)) :
    (EncodingMonitor.observedSignEpochs result.2).count targetEpoch ≤
      attempts * if epoch = targetEpoch then 1 else 0 := by
  apply encodingSamplingTrace_sign_epoch_count_le targetEpoch
    ((simulateQ (splitXmssRomImpl secretKey.parameter .sign)
      (Concrete.signBoundedAttempts attempts secretKey epoch message)).run cache)
    (attempts * if epoch = targetEpoch then 1 else 0)
  · exact splitXmssRom_sign_epochSample_bound secretKey.parameter targetEpoch
      (Concrete.signBoundedAttempts attempts secretKey epoch message)
      (attempts * if epoch = targetEpoch then 1 else 0)
      (Concrete.signBoundedAttempts_queryBound_encodingAddress attempts secretKey epoch
        targetEpoch message) cache
  · exact hmem

theorem Concrete.cappedSign_traced_sign_epoch_count_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (epoch targetEpoch : Epoch) (message : Message)
    (cache : QueryCache HashSpec)
    (result : (Option Signature × QueryCache HashSpec) × EncodingActionTrace)
    (hmem : result ∈ support
      ((simulateQ encodingSamplingTraceImpl
        ((simulateQ (splitXmssRomImpl secretKey.parameter .sign)
          (Concrete.cappedSign publicKey secretKey epoch message)).run cache)).run)) :
    (EncodingMonitor.observedSignEpochs result.2).count targetEpoch ≤
      signingAttemptLimit * if epoch = targetEpoch then 1 else 0 := by
  rw [Concrete.cappedSign_eq] at hmem
  exact Concrete.signBoundedAttempts_traced_sign_epoch_count_le signingAttemptLimit
    secretKey epoch targetEpoch message cache result hmem

end XmssSecurity
