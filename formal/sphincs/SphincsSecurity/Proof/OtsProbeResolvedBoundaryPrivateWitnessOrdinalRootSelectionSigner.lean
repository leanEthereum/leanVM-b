import SphincsSecurity.Proof.Prelude

/-!
# Swapped-root signer continuations

The concrete signer comparison is a two-stage coupling through the target-aware signer. This
module retains an arbitrary continuation after each stage, so the normalized ordinal prefix can
continue with its related canonical deferred contexts instead of projecting the signer state away.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem evalDist_bind_eq_of_relTriple_next
    (left : ProbComp α) (right : ProbComp β) (relation : α → β → Prop)
    (leftNext : α → ProbComp γ) (rightNext : β → ProbComp γ)
    (hrel : RelTriple left right relation)
    (hnext : ∀ leftValue rightValue, relation leftValue rightValue →
      evalDist (leftNext leftValue) = evalDist (rightNext rightValue)) :
    evalDist (left >>= leftNext) = evalDist (right >>= rightNext) := by
  apply evalDist_eq_of_relTriple_eqRel
  apply relTriple_bind hrel
  intro leftValue rightValue hvalue
  exact relTriple_eqRel_of_evalDist_eq (hnext leftValue rightValue hvalue)

end SphincsSecurity.Concrete.OtsProbeSimulation
