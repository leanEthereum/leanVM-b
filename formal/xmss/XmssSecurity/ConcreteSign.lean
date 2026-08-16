import XmssSecurity.ConcreteKeygen
import VCVio.OracleComp.Constructions.SampleableType

open OracleComp OracleSpec

namespace XmssSecurity.Concrete

noncomputable local instance : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

noncomputable def signingRandomness : ProbComp Randomness :=
  $ᵗ Randomness

theorem signingRandomness_eq : signingRandomness = $ᵗ Randomness := rfl

attribute [irreducible] signingRandomness

def signedChainValues {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (secretKey : SecretKey) (epoch : Epoch) (encoding : Encoding) :
    m (ChainIndex → Digest) :=
  sequenceFin fun chain =>
    chainWalk secretKey.parameter epoch chain 0 (encoding chain).val
      (secretKey.chainStart epoch chain)

def authenticationPathNode (epoch : Epoch) (level : MerkleLevel) : MerkleNode :=
  merkleNodeOfNat (Nat.xor (epoch.val / 2 ^ level.val) 1)

def authenticationPath {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (secretKey : SecretKey) (epoch : Epoch) : m (Fin treeHeight → Digest) :=
  sequenceFin fun level =>
    treeNode secretKey.parameter secretKey.chainStart level.val
      (authenticationPathNode epoch level)

def signWithEncoding {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (secretKey : SecretKey) (epoch : Epoch) (randomness : Randomness)
    (encoding : Encoding) : m Signature := do
  let chainValue ← signedChainValues secretKey epoch encoding
  let authPath ← authenticationPath secretKey epoch
  return ⟨randomness, chainValue, authPath⟩

noncomputable def signAttempt {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (randomness : Randomness) : m (Option Signature) := do
  let digest ← encodingHash secretKey.parameter epoch message randomness
  match TargetSum.decodeDigest digest with
  | none => pure none
  | some encoding => some <$> signWithEncoding secretKey epoch randomness encoding

noncomputable def sign (_publicKey : PublicKey) (secretKey : SecretKey)
    (epoch : Epoch) (message : Message) : OracleComp OracleWorld (Option Signature) := do
  let randomness ← liftM signingRandomness
  liftM (signAttempt secretKey epoch message randomness :
    OracleComp HashSpec (Option Signature))

theorem sign_eq (publicKey : PublicKey) (secretKey : SecretKey)
    (epoch : Epoch) (message : Message) :
    sign publicKey secretKey epoch message = (do
      let randomness ← liftM signingRandomness
      liftM (signAttempt secretKey epoch message randomness :
        OracleComp HashSpec (Option Signature))) := rfl

attribute [irreducible] sign

noncomputable def signBoundedAttempts : Nat → SecretKey → Epoch → Message →
    OracleComp OracleWorld (Option Signature)
  | 0, _secretKey, _epoch, _message => pure none
  | attempts + 1, secretKey, epoch, message => do
      let randomness ← liftM signingRandomness
      let result ← liftM (signAttempt secretKey epoch message randomness :
        OracleComp HashSpec (Option Signature))
      match result with
      | some signature => pure (some signature)
      | none => signBoundedAttempts attempts secretKey epoch message

noncomputable def cappedSign (_publicKey : PublicKey) (secretKey : SecretKey)
    (epoch : Epoch) (message : Message) : OracleComp OracleWorld (Option Signature) :=
  signBoundedAttempts signingAttemptLimit secretKey epoch message

theorem cappedSign_eq (publicKey : PublicKey) (secretKey : SecretKey)
    (epoch : Epoch) (message : Message) :
    cappedSign publicKey secretKey epoch message =
      signBoundedAttempts signingAttemptLimit secretKey epoch message := rfl

attribute [irreducible] cappedSign

end XmssSecurity.Concrete
