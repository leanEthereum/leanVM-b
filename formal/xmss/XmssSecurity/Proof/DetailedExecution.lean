import XmssSecurity.Proof.Execution

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

noncomputable def detailedGameAfterKeygen (scheme : Scheme) (adversary : Adversary scheme)
    (publicKey : PublicKey) (secretKey : SecretKey) : OracleComp OracleWorld GameOutcome := by
  classical
  exact do
    let forward :
        QueryImpl OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
      (HasQuery.toQueryImpl (spec := OracleWorld) (m := OracleComp OracleWorld)).liftTarget _
    let ((forgery, signingLog) : Forgery × QueryLog SigningSpec) ←
      (simulateQ (forward + signingOracle scheme publicKey secretKey)
        (adversary.main publicKey)).run
    let verified ← scheme.verify publicKey forgery.epoch forgery.message forgery.signature
    return ⟨publicKey, secretKey, forgery, signingLog, verified⟩

noncomputable def detailedGameCore (scheme : Scheme) (adversary : Adversary scheme) :
    OracleComp OracleWorld GameOutcome := do
  let (publicKey, secretKey) ← scheme.keygen
  detailedGameAfterKeygen scheme adversary publicKey secretKey

theorem gameCore_eq_map_detailedGameCore (scheme : Scheme) (adversary : Adversary scheme) :
    gameCore scheme adversary = GameOutcome.won <$> detailedGameCore scheme adversary := by
  classical
  simp [gameCore, gameAfterKeygen, detailedGameCore, detailedGameAfterKeygen,
    GameOutcome.won]

theorem gameAfterKeygen_eq_map_detailedGameAfterKeygen
    (scheme : Scheme) (adversary : Adversary scheme)
    (publicKey : PublicKey) (secretKey : SecretKey) :
    gameAfterKeygen scheme adversary publicKey secretKey =
      GameOutcome.won <$>
        detailedGameAfterKeygen scheme adversary publicKey secretKey := by
  classical
  simp [gameAfterKeygen, detailedGameAfterKeygen, GameOutcome.won]

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

/-- Retaining the detailed outcome does not change the structural hash-query bound. -/
theorem hasHashQueryBound_iff_detailedGameCore
    (scheme : Scheme) (adversary : Adversary scheme) (q : Nat) :
    HasHashQueryBound scheme adversary q ↔
      (detailedGameCore scheme adversary).IsQueryBoundP (· matches .inr _) q := by
  unfold HasHashQueryBound
  rw [gameCore_eq_map_detailedGameCore]
  exact OracleComp.isQueryBoundP_map_iff _ _ _

/-- Retaining the detailed post-keygen outcome does not change the structural hash-query bound. -/
theorem hasPostKeygenHashQueryBound_iff_detailedGameAfterKeygen
    (scheme : Scheme) (adversary : Adversary scheme) (q : Nat) :
    HasPostKeygenHashQueryBound scheme adversary q ↔
      ∀ key ∈ support scheme.keygen,
        (detailedGameAfterKeygen scheme adversary key.1 key.2).IsQueryBoundP
          (· matches .inr _) q := by
  unfold HasPostKeygenHashQueryBound
  constructor <;> intro h key hkey
  · have hbound := h key hkey
    rw [gameAfterKeygen_eq_map_detailedGameAfterKeygen] at hbound
    exact (OracleComp.isQueryBoundP_map_iff _ _ _).mp hbound
  · rw [gameAfterKeygen_eq_map_detailedGameAfterKeygen]
    exact (OracleComp.isQueryBoundP_map_iff _ _ _).mpr (h key hkey)

end XmssSecurity
