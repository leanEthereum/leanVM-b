import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeSimulation

/-!
# Retained verifier trace alignment

The digest and few-time recovery prefix of verification uses only stable hash domains. This module
first packages that replay fact, then connects the three concrete one-time verifier layers to the
ordinary entries produced by the probing handler.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

theorem simulateQ_probingRom_scheme_verify
    (parameter : PublicParameter) (publicKey : PublicKey)
    (message : Message) (signature : Signature) :
    simulateQ (probingRomImpl parameter)
        (scheme.verify publicKey message signature) =
      simulateQ (probingHashImpl parameter)
        (verify publicKey message signature) := by
  rw [show scheme.verify publicKey message signature =
      liftM (verify publicKey message signature : OracleComp HashSpec Bool) by rfl]
  exact QueryImpl.simulateQ_add_liftM_right _ _ _

end SphincsSecurity.Concrete.OtsProbeSimulation
