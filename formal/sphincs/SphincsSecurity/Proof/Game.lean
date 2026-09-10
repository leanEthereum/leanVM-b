import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Statement

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

end SphincsSecurity
