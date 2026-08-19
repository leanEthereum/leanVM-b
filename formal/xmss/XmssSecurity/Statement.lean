import XmssSecurity.Proof

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

/-!
# Classical random-oracle security of the concrete XMSS instance

This is the reviewer-facing statement of the formalization. The proof is kept in the modules imported above. Nothing below describes a reduction or an intermediate game. The cryptographic implementation types and algorithms are imported, but every interface and security notion used by the theorem is defined here.

The concrete instance has 32-byte messages, 32-bit epochs, 128-bit digests, a 256-bit random-oracle output truncated to 128 bits, 42 Winternitz chains of length 8, and a Merkle tree of height 32. A signing attempt samples 192 fresh bits and queries the random oracle once to encode the message. The signer retries at most `2^23` times and returns `none` if every attempt fails.

The secret key is the ideal precomputed key from the specification: it contains every Winternitz chain value and every Merkle node. Key generation obtains those values through the random oracle. Reading them while signing is local computation and therefore does not count as a random-oracle query.
-/

/-- A hash query takes an arbitrary byte string and returns 32 bytes. -/
abbrev XmssHashSpec := HashInput →ₒ HashOutput

/-- The experiment may sample uniform values or query the shared random oracle. Uniform sampling is kept separate because it is not charged as a hash query. -/
abbrev XmssOracleWorld := unifSpec + XmssHashSpec

/-- A signing request contains a 32-bit epoch and a 32-byte message. The response is either a signature or `none` if all `2^23` encoding attempts fail. -/
abbrev XmssSigningSpec := SignRequest →ₒ Option Signature

/-- The interface of a synchronized signature scheme in the random-oracle experiment. -/
structure XmssScheme where
  keygen : OracleComp XmssOracleWorld (PublicKey × SecretKey)
  sign : PublicKey → SecretKey → Epoch → Message →
    OracleComp XmssOracleWorld (Option Signature)
  verify : PublicKey → Epoch → Message → Signature →
    OracleComp XmssOracleWorld Bool

/-- The concrete XMSS scheme. Key generation constructs the precomputed secret key, signing performs at most `2^23` encoding attempts, and verification is the ordinary XMSS verifier. -/
noncomputable def xmssScheme : XmssScheme where
  keygen := Concrete.precomputedKeygen
  sign := Concrete.precomputedCappedSign
  verify := fun publicKey epoch message signature =>
    liftM (Concrete.verify publicKey epoch message signature :
      OracleComp HashSpec Bool)

/-- A classical adaptive adversary. After receiving the public key, it may query the shared random oracle, request signatures, and finally return a claimed forgery containing an epoch, message, and signature. -/
structure XmssAdversary (_scheme : XmssScheme) where
  main : PublicKey →
    OracleComp (XmssOracleWorld + XmssSigningSpec) Forgery

/-- A signing transcript is valid exactly when no epoch occurs twice. Thus the adversary may make adaptive signing requests, but may not request two signatures at the same epoch. -/
def XmssSigningTranscriptValid (log : QueryLog XmssSigningSpec) : Prop :=
  (log.map fun entry => entry.1.epoch).Nodup

/-- The signer returned the claimed forgery exactly when the transcript contains the same epoch, message, and signature. A different signature for a signed message is therefore a valid strong forgery. -/
def XmssForgeryWasReturned
    (log : QueryLog XmssSigningSpec) (forgery : Forgery) : Prop :=
  ∃ entry ∈ log,
    entry.1 = forgery.request ∧ entry.2 = some forgery.signature

/-- The signing oracle used in the game. It records every request and response while forwarding the request to the concrete signer. -/
noncomputable def xmssSigningOracle
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl XmssSigningSpec
      (WriterT (QueryLog XmssSigningSpec) (OracleComp XmssOracleWorld)) :=
  QueryImpl.withLogging fun request =>
    xmssScheme.sign publicKey secretKey request.epoch request.message

/-- The complete strong-unforgeability experiment.

The random oracle is sampled lazily by the semantics of `OracleWorld`. Key generation, the adversary, the signing oracle, and final verification all share the same oracle. The game returns `true` precisely when the signing transcript uses every epoch at most once, the claimed forgery is not an exact replay, and the signature verifies. -/
noncomputable def xmssGame (adversary : XmssAdversary xmssScheme) :
    OracleComp XmssOracleWorld Bool := by
  classical
  exact do
    let (publicKey, secretKey) ← xmssScheme.keygen
    let forward : QueryImpl XmssOracleWorld
        (WriterT (QueryLog XmssSigningSpec)
          (OracleComp XmssOracleWorld)) :=
      (HasQuery.toQueryImpl (spec := XmssOracleWorld)
        (m := OracleComp XmssOracleWorld)).liftTarget _
    let ((forgery, log) : Forgery × QueryLog XmssSigningSpec) ←
      (simulateQ (forward + xmssSigningOracle publicKey secretKey)
        (adversary.main publicKey)).run
    let verified ← xmssScheme.verify publicKey forgery.epoch
      forgery.message forgery.signature
    return decide (XmssSigningTranscriptValid log ∧
      ¬XmssForgeryWasReturned log forgery) && verified

/-- The probability that the adversary wins, over key generation, signer randomness, and the random oracle. -/
noncomputable def xmssForgeAdvantage
    (adversary : XmssAdversary xmssScheme) : ENNReal :=
  Pr[= true | Rom.runtime.evalDist (xmssGame adversary)]

/-- The whole experiment makes at most `q` random-oracle queries on every execution path. The count includes queries during key generation, adversarial hashing, signing, and final verification. Uniform sampling operations are not hash queries. -/
def XmssHasHashQueryBound
    (adversary : XmssAdversary xmssScheme) (q : Nat) : Prop :=
  (xmssGame adversary).IsQueryBoundP (· matches .inr _) q

/-- The best forgery probability among all classical adaptive adversaries whose complete experiment has hash-query bound `q`. -/
noncomputable def xmssForgeAtMost (q : Nat) : ENNReal :=
  ⨆ (adversary : XmssAdversary xmssScheme),
    ⨆ (_ : XmssHasHashQueryBound adversary q),
      xmssForgeAdvantage adversary

/-- Having `bits` bits of classical security means that, for every nonzero query budget `q`, the optimal forgery probability is at most `q / 2^bits`. -/
noncomputable def XmssHasClassicalSecurityBits (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → xmssForgeAtMost q ≤
    (q : ENNReal) / ((2 ^ bits : Nat) : ENNReal)

/-- The complete public security claim. -/
abbrev XmssSecurityStatement : Prop :=
  XmssHasClassicalSecurityBits 127

/-- The concrete XMSS instance has 127 bits of classical security in the random-oracle model. -/
theorem xmss_has_127_bits_of_classical_security :
    ∀ q, 1 ≤ q → xmssForgeAtMost q ≤
      (q : ENNReal) / ((2 ^ 127 : Nat) : ENNReal) := by
  intro q hq
  unfold xmssForgeAtMost
  refine iSup_le fun adversary => iSup_le fun hbound => ?_
  let internalAdversary : Adversary Concrete.scheme := ⟨adversary.main⟩
  have internalBound :
      HasHashQueryBound Concrete.scheme internalAdversary q := by
    exact hbound
  calc
    xmssForgeAdvantage adversary =
        forgeAdvantage Concrete.scheme internalAdversary := rfl
    _ ≤ forgeAtMost Concrete.scheme q :=
      le_iSup_of_le internalAdversary
        (le_iSup_of_le internalBound le_rfl)
    _ ≤ (q : ENNReal) / ((2 ^ 127 : Nat) : ENNReal) :=
      Proof.concreteScheme_has_127_bits_of_classical_security q hq

end XmssSecurity
