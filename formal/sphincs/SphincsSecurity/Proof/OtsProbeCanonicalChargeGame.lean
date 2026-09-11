import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.Honest
import SphincsSecurity.Proof.FtsProbeSimulation
import SphincsSecurity.Proof.RomQueryCharge
import SphincsSecurity.Proof.FewTimeSignerView
import SphincsSecurity.Proof.FewTimeWitness
import SphincsSecurity.Proof.SigningTrace
import SphincsSecurity.Proof.RootCache
import SphincsSecurity.Proof.Secrets
import SphincsSecurity.Proof.MessagePrehit
import SphincsSecurity.Proof.ForgeryClassify
import SphincsSecurity.Statement
import SphincsSecurity.Proof.EncodingCharge
import SphincsSecurity.Proof.Charge
import SphincsSecurity.Proof.EncodingSelectionCache
import SphincsSecurity.Proof.QueryBound
import SphincsSecurity.Proof.Guess
import SphincsSecurity.Proof.SecretProbe
import SphincsSecurity.Proof.OtsProbeSimulation
import SphincsSecurity.Proof.OtsProbeOrigin
import SphincsSecurity.Proof.FtsProbeSampling
import SphincsSecurity.Proof.RomQueryChargeBind

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

theorem expectedQueryCharge_map
    (charge : QueryCache HashSpec → HashInput → ℝ≥0∞)
    (computation : OracleComp OracleWorld α) (f : α → β) (cache : QueryCache HashSpec) :
    expectedQueryCharge charge (f <$> computation) cache = expectedQueryCharge charge computation cache := by
  rw [map_eq_bind_pure_comp, expectedQueryCharge_bind]
  simp only [Function.comp_apply, expectedQueryCharge_pure, mul_zero, tsum_zero, add_zero]

namespace Concrete.OtsProbeSimulation

theorem gameRest_eq_map_retained
    (adversary : Adversary) (secretKey : SecretKey) (publicKey : PublicKey) :
    gameRest scheme adversary publicKey secretKey =
      (fun result : RetainedRestResult =>
        decide (SigningTranscript.Valid result.1.2 ∧ ¬SigningTranscript.Contains result.1.2 result.1.1) && result.2) <$>
        simulateQ (expandedAdversaryImpl secretKey) (retainedGameRestComputation adversary publicKey) := by
  unfold gameRest retainedGameRestComputation
  rw [simulateQ_bind, ← simulateQ_withTraceAppend_run_eq_signingTraceComputation,
    ← forwardOracles_add_signingOracle_eq_withTraceAppend, map_bind]
  apply bind_congr
  intro result
  rcases result with ⟨forgery, log⟩
  rw [simulateQ_bind]
  have hlift : simulateQ (expandedAdversaryImpl secretKey)
      (liftOracleWorldLeft (scheme.verify publicKey forgery.message forgery.signature)) =
      scheme.verify publicKey forgery.message forgery.signature :=
    FtsProbeSimulation.simulateQ_expanded_liftOracleWorldLeft secretKey _
  rw [hlift]
  simp only [simulateQ_pure, map_bind, map_pure]

theorem expectedQueryCharge_retained_eq_gameRest
    (adversary : Adversary) (secretKey : SecretKey) (publicKey : PublicKey)
    (charge : QueryCache HashSpec → HashInput → ℝ≥0∞) (cache : QueryCache HashSpec) :
    expectedQueryCharge charge (simulateQ (expandedAdversaryImpl secretKey)
      (retainedGameRestComputation adversary publicKey)) cache =
      expectedQueryCharge charge (gameRest scheme adversary publicKey secretKey) cache := by
  rw [gameRest_eq_map_retained, expectedQueryCharge_map]

end Concrete.OtsProbeSimulation

end SphincsSecurity
