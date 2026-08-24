import SphincsSecurity.Proof.QueryBound

/-!
# Splitting the game at key generation

Key generation runs first and fixes every honest value, so the reduction reasons about what follows
it against a cache it can treat as given. This module factors the game accordingly: bounding the
advantage reduces to bounding, for each key generation outcome, the winning probability of the rest.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

/-- Everything the game does after key generation: run the adversary against the signing oracle,
verify what it returns, and decide whether that counts as a forgery. -/
noncomputable def gameRest (scheme : Scheme) (adversary : Adversary) (pk : PublicKey)
    (sk : SecretKey) : OracleComp OracleWorld Bool := do
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (forwardOracles + signingOracle scheme sk) (adversary.main pk)).run
  let verified ← scheme.verify pk forgery.message forgery.signature
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

theorem gameCore_eq (scheme : Scheme) (adversary : Adversary) :
    gameCore scheme adversary
      = scheme.keygen >>= fun keys => gameRest scheme adversary keys.1 keys.2 := rfl

/-- **The reduction's frame.** If the rest of the game wins with probability at most `c` from every
cache key generation can leave, the adversary's advantage is at most `c`. -/
theorem forgeAdvantage_le (scheme : Scheme) (adversary : Adversary) (c : ℝ≥0∞)
    (h : ∀ keys : (PublicKey × SecretKey), ∀ cache : QueryCache HashSpec,
      (keys, cache) ∈ support ((simulateQ romImpl scheme.keygen).run ∅) →
      Pr[fun result => result.1 = true
        | (simulateQ romImpl (gameRest scheme adversary keys.1 keys.2)).run cache] ≤ c) :
    forgeAdvantage scheme adversary ≤ c := by
  rw [forgeAdvantage, gameCore_eq, StateT.run'_eq, probOutput_map, simulateQ_bind,
    StateT.run_bind]
  refine probEvent_bind_le_of_forall_le fun keysCache hmem => ?_
  exact h keysCache.1 keysCache.2 hmem

end SphincsSecurity
