import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedSignerFinalization

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

theorem finishResolvedRunIsNone_value_eq
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (left : α) (right : β) :
    finishResolvedRunIsNone (some ⟨context, fuel, left, table⟩) =
      finishResolvedRunIsNone (some ⟨context, fuel, right, table⟩) := by
  unfold finishResolvedRunIsNone finishResolvedRun
  dsimp only
  split_ifs
  · simp only [map_bind]
    apply bind_congr
    intro result
    cases result <;> simp
  · simp

end SphincsSecurity.Concrete.OtsProbeSimulation
