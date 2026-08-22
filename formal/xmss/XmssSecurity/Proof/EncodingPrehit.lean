import XmssSecurity.Proof.SigningCacheTrace

namespace XmssSecurity

def SigningCacheTrace.HasEncodingInputPrehitAt
    (trace : SigningCacheTrace) (secretKey : SecretKey)
    (targetEpoch : Epoch) : Prop :=
  ∃ entry ∈ trace,
    entry.request.epoch = targetEpoch ∧ entry.EncodingInputPrehit secretKey

def SigningCacheTrace.HasEncodingInputPrehit
    (trace : SigningCacheTrace) (secretKey : SecretKey) : Prop :=
  ∃ entry ∈ trace, entry.EncodingInputPrehit secretKey

end XmssSecurity
