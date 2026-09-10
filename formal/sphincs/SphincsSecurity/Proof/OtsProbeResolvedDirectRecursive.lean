import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedSignerFinalization

/-! Erasure of the recursive work performed by one structural reveal. -/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

noncomputable def resolvedFinalizationObserve
    (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (fuel : Nat) (value : α) : ProbComp Bool :=
  finishResolvedRunIsNone (some ⟨context, fuel, value, table⟩)

end SphincsSecurity.Concrete.OtsProbeSimulation
