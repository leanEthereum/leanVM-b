import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualSource

namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open InterleavedResidual (Routing)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem fixedSourceRun_bind {A B : Type} {inputs : Finset HashInput} (context : Context inputs)
    (computation : OracleComp (OracleWorld + SigningSpec) A)
    (next : A → OracleComp (OracleWorld + SigningSpec) B) (memory : Memory) :
    fixedSourceRun context (computation >>= next) memory =
      (fixedSourceRun context computation memory >>= fun result =>
        result.1.elim (pure (none, result.2)) (fun value => fixedSourceRun context (next value) result.2)) := by
  simp only [fixedSourceRun, simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind]
  apply congrArg (_ >>= ·)
  funext result
  rcases result with ⟨value, after⟩
  cases value <;> rfl

end SphincsSecurity.Concrete.RetainedResidual
