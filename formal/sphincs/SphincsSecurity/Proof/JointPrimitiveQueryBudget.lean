import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.RomQueryCharge
import SphincsSecurity.Proof.TerminalSampling
import SphincsSecurity.Proof.TightEncodingRefinedBound
import SphincsSecurity.Proof.TightEncodingSettledCharge

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

noncomputable def residualPrimitiveQueryCharge (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) : ℝ≥0∞ :=
  3 - TightEncoding.refinedStructuralEncodingQueryCharge secretKey cache input

noncomputable def sampledQueryCharge
    (charge : SecretKey → QueryCache HashSpec → HashInput → ℝ≥0∞)
    (adversary : Adversary) : ℝ≥0∞ :=
  ∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets] *
    expectedQueryCharge (charge (primitiveAccountingKey secrets.parameter secrets.otsSecret secrets.ftsSecret))
      (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅

theorem structural_add_residual_queryCharge (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) :
    TightEncoding.refinedStructuralEncodingQueryCharge secretKey cache input +
      residualPrimitiveQueryCharge secretKey cache input = 3 := by
  exact add_tsub_cancel_of_le
    (TightEncoding.refinedStructuralEncodingQueryCharge_le_three secretKey cache input)

end SphincsSecurity.Concrete
