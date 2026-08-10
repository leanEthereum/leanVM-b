import XmssSecurity.Scheme
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.QueryBound

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

structure Adversary (_scheme : Scheme) where
  main : PublicKey → OracleComp (OracleWorld + SigningSpec) Forgery

namespace SigningTranscript

def Valid (log : QueryLog SigningSpec) : Prop :=
  (log.map fun entry => entry.1.epoch).Nodup

def Contains (log : QueryLog SigningSpec) (forgery : Forgery) : Prop :=
  ∃ entry ∈ log, entry.1 = forgery.request ∧ entry.2 = some forgery.signature

end SigningTranscript

def signingOracle (scheme : Scheme) (pk : PublicKey) (sk : SecretKey) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request => scheme.sign pk sk request.epoch request.message

noncomputable def gameCore (scheme : Scheme) (adversary : Adversary scheme) :
    OracleComp OracleWorld Bool := by
  classical
  exact do
    let (pk, sk) ← scheme.keygen
    let forward : QueryImpl OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
      (HasQuery.toQueryImpl (spec := OracleWorld) (m := OracleComp OracleWorld)).liftTarget _
    let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
      (simulateQ (forward + signingOracle scheme pk sk) (adversary.main pk)).run
    let verified ← scheme.verify pk forgery.epoch forgery.message forgery.signature
    return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

noncomputable def forgeAdvantage (scheme : Scheme) (adversary : Adversary scheme) : ℝ≥0∞ :=
  Pr[= true | Rom.runtime.evalDist (gameCore scheme adversary)]

def HasHashQueryBound (scheme : Scheme) (adversary : Adversary scheme) (q : Nat) : Prop :=
  (gameCore scheme adversary).IsQueryBoundP (· matches .inr _) q

noncomputable def forgeAtMost (scheme : Scheme) (q : Nat) : ℝ≥0∞ :=
  ⨆ (adversary : Adversary scheme), ⨆ (_ : HasHashQueryBound scheme adversary q),
    forgeAdvantage scheme adversary

noncomputable def HasClassicalSecurityBits (scheme : Scheme) (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → forgeAtMost scheme q ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

end XmssSecurity
