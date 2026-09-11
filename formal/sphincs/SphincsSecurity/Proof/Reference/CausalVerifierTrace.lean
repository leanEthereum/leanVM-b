import SphincsSecurity.Proof.Reference.VerifierTraceSource
import SphincsSecurity.Proof.Reference.CausalFrontierProgram

namespace SphincsSecurity.Concrete.OtsContactTrace

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] frontierRoot maskOtsPrefixes

theorem ContainsRun.mul_left {Result : Type} {f : QueryImpl HashSpec Id} {trace : Trace} {computation : OracleComp HashSpec Result}
    (h : ContainsRun f trace computation) (before : Trace) : ContainsRun f (before * trace) computation := by
  intro input hi
  exact List.mem_append_right _ (h input hi)

abbrev AdversaryTrace := ((Forgery × QueryLog SigningSpec) × SigningBoundaryTrace) × Trace

end SphincsSecurity.Concrete.OtsContactTrace
