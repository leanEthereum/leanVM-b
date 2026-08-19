import XmssSecurity.Statement.ConcreteSign
import XmssSecurity.Statement.PrecomputedKeygen

open OracleComp OracleSpec

namespace XmssSecurity.Concrete

def precomputedSignedChainValues (secretKey : SecretKey) (epoch : Epoch)
    (encoding : Encoding) : ChainIndex → Digest :=
  fun chain => secretKey.chainValue epoch chain (encoding chain)

def precomputedAuthenticationPath (secretKey : SecretKey) (epoch : Epoch) :
    Fin treeHeight → Digest :=
  fun level => secretKey.treeValue ⟨level.val, by omega⟩
    (authenticationPathNode epoch level)

def precomputedSignWithEncoding (secretKey : SecretKey) (epoch : Epoch)
    (randomness : Randomness) (encoding : Encoding) : Signature :=
  ⟨randomness, precomputedSignedChainValues secretKey epoch encoding,
    precomputedAuthenticationPath secretKey epoch⟩

noncomputable def precomputedSignAttempt {m : Type → Type} [Monad m]
    [HasQuery HashSpec m] (secretKey : SecretKey) (epoch : Epoch)
    (message : Message) (randomness : Randomness) : m (Option Signature) := do
  let digest ← encodingHash secretKey.parameter epoch message randomness
  match TargetSum.decodeDigest digest with
  | none => pure none
  | some encoding =>
      pure (some (precomputedSignWithEncoding secretKey epoch randomness encoding))

noncomputable def precomputedSignBoundedAttempts :
    Nat → SecretKey → Epoch → Message →
      OracleComp OracleWorld (Option Signature)
  | 0, _secretKey, _epoch, _message => pure none
  | attempts + 1, secretKey, epoch, message => do
      let randomness ← liftM signingRandomness
      let result ← liftM
        (precomputedSignAttempt secretKey epoch message randomness :
          OracleComp HashSpec (Option Signature))
      match result with
      | some signature => pure (some signature)
      | none => precomputedSignBoundedAttempts attempts secretKey epoch message

noncomputable def precomputedCappedSign (_publicKey : PublicKey)
    (secretKey : SecretKey) (epoch : Epoch) (message : Message) :
    OracleComp OracleWorld (Option Signature) :=
  precomputedSignBoundedAttempts signingAttemptLimit secretKey epoch message

attribute [irreducible] precomputedCappedSign

end XmssSecurity.Concrete
