import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeFreshGuessRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

theorem resolvedContextFailureRisk_of_no_pending
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hvalid : context.Valid) (hstarts : StartTableAgrees context.state table)
    (hcovered : PendingCoveredBy [] context) :
    resolvedContextFailureRisk table context = 0 := by
  have hcoordinates : PendingCovered [] context := by
    intro entry hentry
    obtain ⟨candidate, hcandidate, _⟩ := hcovered entry hentry
    simp at hcandidate
  have hcard := hcovered.card_le
  rw [resolvedContextFailureRisk_eq_finalize_coordinates table context [] hvalid hstarts hcoordinates
    (by simp) (by simpa using lt_of_le_of_lt hcard (Fintype.card_pos : 0 < Fintype.card Digest))]
  simp [finalizeResolvedCoordinates]

end SphincsSecurity.Concrete.OtsProbeSimulation
