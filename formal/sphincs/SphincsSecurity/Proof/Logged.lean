import SphincsSecurity.Proof.Game

/-!
# The adversary's own queries

The cache cannot say who asked: it holds key generation's queries, the signer's, and the adversary's
alike. Every remaining step of the reduction needs the distinction, because what has to be charged is
what the *adversary* asked. Wrapping its oracle with a log supplies it, and costs nothing: the log is
discarded, and `fst_map_run_withLogging` says the value distribution is unchanged.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

/-- The rest of the game, with the adversary's queries logged alongside the verdict. -/
noncomputable def gameRestLogged (scheme : Scheme) (adversary : Adversary) (pk : PublicKey)
    (sk : SecretKey) : OracleComp OracleWorld (Bool × QueryLog (OracleWorld + SigningSpec)) := do
  let result ← ((simulateQ ((forwardOracles + signingOracle scheme sk).withLogging)
    (adversary.main pk)).run).run
  let verified ← scheme.verify pk result.1.1.message result.1.1.signature
  return (decide (SigningTranscript.Valid result.2 ∧ ¬SigningTranscript.Contains result.2 result.1.1)
    && verified, result.1.2)

/-- Logging the adversary changes no distribution: the verdict is the first component. -/
theorem gameRest_eq_map_gameRestLogged (scheme : Scheme) (adversary : Adversary) (pk : PublicKey)
    (sk : SecretKey) :
    gameRest scheme adversary pk sk = Prod.fst <$> gameRestLogged scheme adversary pk sk := by
  simp only [gameRest, gameRestLogged, map_bind, map_pure]
  rw [← QueryImpl.fst_map_run_withLogging (forwardOracles + signingOracle scheme sk) (adversary.main pk)]
  simp [map_bind, bind_map_left]

/-- **The reduction's frame, with the adversary's queries in hand.** -/
theorem forgeAdvantage_le_logged (scheme : Scheme) (adversary : Adversary) (c : ℝ≥0∞)
    (h : ∀ keys : (PublicKey × SecretKey), ∀ cache : QueryCache HashSpec,
      (keys, cache) ∈ support ((simulateQ romImpl scheme.keygen).run ∅) →
      Pr[fun result => result.1.1 = true
        | (simulateQ romImpl (gameRestLogged scheme adversary keys.1 keys.2)).run cache] ≤ c) :
    forgeAdvantage scheme adversary ≤ c := by
  refine forgeAdvantage_le scheme adversary c fun keys cache hmem => ?_
  rw [gameRest_eq_map_gameRestLogged, simulateQ_map, StateT.run_map, probEvent_map]
  exact h keys cache hmem

end SphincsSecurity
