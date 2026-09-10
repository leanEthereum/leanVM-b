import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedSampling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable

structure CanonicalQuerySelection where
  input : (OracleWorld + SigningSpec).Domain
  context : DeferredContext
  fuel : Nat
  table : OtsSecretIndex → HashOutput
  cache : SplitHashCache

noncomputable def CanonicalQuerySelection.charge
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ℝ≥0∞) :
    Option CanonicalQuerySelection → ℝ≥0∞
  | none => 0
  | some selection => charge selection.input selection.context selection.fuel selection.cache

end SphincsSecurity.Concrete.OtsProbeSimulation
