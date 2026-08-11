import XmssSecurity.Execution

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

structure GameOutcome where
  publicKey : PublicKey
  secretKey : SecretKey
  forgery : Forgery
  signingLog : QueryLog SigningSpec
  verified : Bool

noncomputable def GameOutcome.won (outcome : GameOutcome) : Bool := by
  classical
  exact decide (SigningTranscript.Valid outcome.signingLog ∧
    ¬SigningTranscript.Contains outcome.signingLog outcome.forgery) && outcome.verified

theorem GameOutcome.won_eq_true_iff (outcome : GameOutcome) :
    outcome.won = true ↔
      SigningTranscript.Valid outcome.signingLog ∧
      ¬SigningTranscript.Contains outcome.signingLog outcome.forgery ∧
      outcome.verified = true := by
  classical
  simp [GameOutcome.won, and_assoc]

noncomputable def detailedGameCore (scheme : Scheme) (adversary : Adversary scheme) :
    OracleComp OracleWorld GameOutcome := by
  classical
  exact do
    let (publicKey, secretKey) ← scheme.keygen
    let forward :
        QueryImpl OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
      (HasQuery.toQueryImpl (spec := OracleWorld) (m := OracleComp OracleWorld)).liftTarget _
    let ((forgery, signingLog) : Forgery × QueryLog SigningSpec) ←
      (simulateQ (forward + signingOracle scheme publicKey secretKey)
        (adversary.main publicKey)).run
    let verified ← scheme.verify publicKey forgery.epoch forgery.message forgery.signature
    return ⟨publicKey, secretKey, forgery, signingLog, verified⟩

theorem gameCore_eq_map_detailedGameCore (scheme : Scheme) (adversary : Adversary scheme) :
    gameCore scheme adversary = GameOutcome.won <$> detailedGameCore scheme adversary := by
  classical
  simp [gameCore, detailedGameCore, GameOutcome.won]

noncomputable def detailedGameWithCache (scheme : Scheme) (adversary : Adversary scheme) :
    ProbComp (GameOutcome × QueryCache HashSpec) :=
  (simulateQ xmssRomImpl (detailedGameCore scheme adversary)).run ∅

theorem gameWithCache_eq_map_detailedGameWithCache
    (scheme : Scheme) (adversary : Adversary scheme) :
    gameWithCache scheme adversary =
      (fun outcome : GameOutcome × QueryCache HashSpec =>
        (outcome.1.won, outcome.2)) <$> detailedGameWithCache scheme adversary := by
  unfold gameWithCache detailedGameWithCache
  rw [gameCore_eq_map_detailedGameCore, simulateQ_map]
  rfl

theorem forgeAdvantage_eq_detailedGameWithCache
    (scheme : Scheme) (adversary : Adversary scheme) :
    forgeAdvantage scheme adversary =
      Pr[fun outcome : GameOutcome × QueryCache HashSpec => outcome.1.won = true |
        detailedGameWithCache scheme adversary] := by
  rw [forgeAdvantage_eq_gameWithCache, gameWithCache_eq_map_detailedGameWithCache,
    probEvent_map]
  rfl

end XmssSecurity
