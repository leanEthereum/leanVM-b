import XmssSecurity.Statement.Algorithms
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.SimSemantics.StateT.BundledSemantics

/-!
# Classical random-oracle security of the concrete XMSS instance

This is the reviewer-facing statement of the formalization. This module and the two definitional modules it imports, `Statement.Spec` and `Statement.Algorithms`, contain everything the statement depends on: the concrete parameters and algorithms, the strong-unforgeability experiment, and the security claim `XmssSecurityStatement`. Nothing here imports proof machinery, and nothing below describes a reduction or an intermediate game. The theorem itself is stated and proved in the root module `XmssSecurity`.

The concrete instance has 32-byte messages, 32-bit epochs, 128-bit digests, a 256-bit random-oracle output truncated to 128 bits, 42 Winternitz chains of length 8, and a Merkle tree of height 32. Its ideal secret key contains every Winternitz chain value and every Merkle node. Key generation obtains those values through the random oracle. The security budget starts after key generation, so these fixed honest setup queries are free. All later random-oracle queries by the adversary, signer, and final verifier are charged.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

namespace Rom

/-- The random-oracle semantics: hash queries are answered lazily and consistently by uniform sampling, starting from the empty cache. -/
noncomputable def runtime : ProbCompRuntime (OracleComp OracleWorld) where
  toSPMFSemantics := SPMFSemantics.withStateOracle
    (hashImpl := (randomOracle : QueryImpl HashSpec (StateT HashSpec.QueryCache ProbComp))) ∅
  toProbCompLift := ProbCompLift.ofMonadLift _

end Rom

/-- A signing request contains a 32-bit epoch and a 32-byte message. -/
structure SignRequest where
  epoch : Epoch
  message : Message
deriving DecidableEq

/-- A claimed forgery: an epoch, a message, and a signature. -/
structure Forgery where
  epoch : Epoch
  message : Message
  signature : Signature
deriving DecidableEq

def Forgery.request (forgery : Forgery) : SignRequest :=
  ⟨forgery.epoch, forgery.message⟩

/-- The interface of a synchronized signature scheme in the random-oracle experiment. -/
structure Scheme where
  keygen : OracleComp OracleWorld (PublicKey × SecretKey)
  sign : PublicKey → SecretKey → Epoch → Message → OracleComp OracleWorld (Option Signature)
  verify : PublicKey → Epoch → Message → Signature → OracleComp OracleWorld Bool

/-- The signing oracle answers a request with either a signature or `none` if the signer fails. -/
abbrev SigningSpec := SignRequest →ₒ Option Signature

/-- A classical adaptive adversary. After receiving the public key, it may query the shared random oracle, request signatures, and finally return a claimed forgery. -/
structure Adversary (_scheme : Scheme) where
  main : PublicKey → OracleComp (OracleWorld + SigningSpec) Forgery

namespace SigningTranscript

/-- A signing transcript is valid exactly when no epoch occurs twice. Thus the adversary may make adaptive signing requests, but may not request two signatures at the same epoch. -/
def Valid (log : QueryLog SigningSpec) : Prop :=
  (log.map fun entry => entry.1.epoch).Nodup

/-- The signer returned the claimed forgery exactly when the transcript contains the same epoch, message, and signature. A different signature for a signed message is therefore a valid strong forgery. -/
def Contains (log : QueryLog SigningSpec) (forgery : Forgery) : Prop :=
  ∃ entry ∈ log, entry.1 = forgery.request ∧ entry.2 = some forgery.signature

end SigningTranscript

/-- The signing oracle used in the game. It records every request and response while forwarding the request to the scheme's signer. -/
def signingOracle (scheme : Scheme) (pk : PublicKey) (sk : SecretKey) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request => scheme.sign pk sk request.epoch request.message

/-- The post-keygen part of the strong-unforgeability experiment. The adversary, signing oracle, and final verifier share the random oracle initialized during key generation. The game returns `true` precisely when the signing transcript uses every epoch at most once, the claimed forgery is not an exact replay, and the signature verifies. -/
noncomputable def gameAfterKeygen (scheme : Scheme) (adversary : Adversary scheme)
    (pk : PublicKey) (sk : SecretKey) : OracleComp OracleWorld Bool := by
  classical
  exact do
    let forward : QueryImpl OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
      (HasQuery.toQueryImpl (spec := OracleWorld) (m := OracleComp OracleWorld)).liftTarget _
    let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
      (simulateQ (forward + signingOracle scheme pk sk) (adversary.main pk)).run
    let verified ← scheme.verify pk forgery.epoch forgery.message forgery.signature
    return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

/-- The complete strong-unforgeability experiment. Key generation and the post-keygen game use one shared lazily sampled random oracle. -/
noncomputable def gameCore (scheme : Scheme) (adversary : Adversary scheme) :
    OracleComp OracleWorld Bool := do
  let (pk, sk) ← scheme.keygen
  gameAfterKeygen scheme adversary pk sk

/-- The probability that the adversary wins, over key generation, signer randomness, and the random oracle. -/
noncomputable def forgeAdvantage (scheme : Scheme) (adversary : Adversary scheme) : ℝ≥0∞ :=
  Pr[= true | Rom.runtime.evalDist (gameCore scheme adversary)]

/-- The complete experiment makes at most `q` random-oracle queries on every execution path. This whole-game bound is useful internally when a proof reintroduces the exact key-generation cost. -/
def HasHashQueryBound (scheme : Scheme) (adversary : Adversary scheme) (q : Nat) : Prop :=
  (gameCore scheme adversary).IsQueryBoundP (· matches .inr _) q

/-- The best forgery probability under a whole-game hash-query budget. -/
noncomputable def forgeAtMost (scheme : Scheme) (q : Nat) : ℝ≥0∞ :=
  ⨆ (adversary : Adversary scheme), ⨆ (_ : HasHashQueryBound scheme adversary q),
    forgeAdvantage scheme adversary

/-- Whole-game security accounting, including honest key generation. The public theorem below uses the stronger post-keygen accounting instead. -/
noncomputable def HasClassicalSecurityBits (scheme : Scheme) (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → forgeAtMost scheme q ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

/-- For every key pair that key generation can produce, the post-keygen experiment makes at most `q` random-oracle queries on every execution path. Honest key-generation queries are free. The count includes adversarial hashing, signing, and final verification. Uniform sampling operations are not hash queries. -/
def HasPostKeygenHashQueryBound
    (scheme : Scheme) (adversary : Adversary scheme) (q : Nat) : Prop :=
  ∀ key ∈ support scheme.keygen,
    (gameAfterKeygen scheme adversary key.1 key.2).IsQueryBoundP
      (· matches .inr _) q

/-- The best forgery probability among all classical adaptive adversaries whose post-keygen experiment has hash-query bound `q`. -/
noncomputable def postKeygenForgeAtMost (scheme : Scheme) (q : Nat) : ℝ≥0∞ :=
  ⨆ (adversary : Adversary scheme),
    ⨆ (_ : HasPostKeygenHashQueryBound scheme adversary q),
    forgeAdvantage scheme adversary

/-- Having `bits` bits of classical security means that, for every nonzero query budget `q`, the optimal forgery probability is at most `q / 2^bits`. -/
noncomputable def HasPostKeygenClassicalSecurityBits
    (scheme : Scheme) (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → postKeygenForgeAtMost scheme q ≤
    q / ((2 ^ bits : Nat) : ℝ≥0∞)

/-- The concrete XMSS scheme: the precomputed key generation, the capped retry signer, and the ordinary verifier from `Statement.Algorithms`. -/
noncomputable def Concrete.scheme : Scheme where
  keygen := Concrete.precomputedKeygen
  sign := Concrete.precomputedCappedSign
  verify := fun publicKey epoch message signature =>
    liftM (Concrete.verify publicKey epoch message signature : OracleComp HashSpec Bool)

/-- The complete public security claim. -/
abbrev XmssSecurityStatement : Prop :=
  HasPostKeygenClassicalSecurityBits Concrete.scheme 127

end XmssSecurity
