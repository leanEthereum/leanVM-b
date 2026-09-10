import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeSimulation

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

noncomputable def otsHashInputCharge (parameter : PublicParameter) (input : HashInput) : ℝ≥0∞ :=
  by
    classical
    exact if ∃ position : Position, IsOtsPosition position ∧ AtPosition parameter input position then 1 else 0

noncomputable def otsOuterQueryCharge (parameter : PublicParameter) :
    (OracleWorld + SigningSpec).Domain → ℝ≥0∞
  | .inl (.inr input) => otsHashInputCharge parameter input
  | _ => 0

end SphincsSecurity.Concrete.OtsProbeSimulation
