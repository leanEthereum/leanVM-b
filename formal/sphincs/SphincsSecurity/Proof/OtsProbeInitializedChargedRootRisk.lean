import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeChargedRootAdaptiveRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

noncomputable def initializedChargedRootCutObservation
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter) (target : Position)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel ordinal : Nat) (event : HashOutput × Option Digest → Prop) : ProbComp Bool := do
  let result ← runResolvedFromTable (ensuredInitialContext targets) fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)
  match result with
  | none => pure true
  | some result =>
      originalChargedRootCutObservation parameter result.value.1 target ftsSecret
        (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩)
        result.context result.remaining table result.value.2 ∅ ordinal event

end SphincsSecurity.Concrete.OtsProbeSimulation
