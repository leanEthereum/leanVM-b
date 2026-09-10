import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedSampling

/-!
# Private structural sample deferral through the resolved interpreter

Resolving one ensured private structural position before an arbitrary probing computation leaves
the terminal completion-failure distribution unchanged. The reveal case uses recursive resolution
commutation while retaining every pending probe through the public materialization boundary.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem DeferredCompletable.of_resolveDeferredReveal
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hcompletable : DeferredCompletable table context) (hvalid : context.Valid)
    (position : Position) (result : DeferredResolution)
    (hresult : some result ∈ support (resolveDeferredReveal table position context)) :
    DeferredCompletable table result.toDeferredContext := by
  classical
  by_cases hresolvable : ResolvableOtsPosition position
  · exact hcompletable.of_resolveDeferredPosition hvalid (by
      simpa [resolveDeferredReveal, hresolvable] using hresult)
  · exact hcompletable.of_resolveDeferredPositionValue hvalid position result (by
      simpa [resolveDeferredReveal, hresolvable] using hresult)

theorem resolveDeferredPositionValue_values_eq_of_values_eq
    (position : Position) (left right : DeferredContext)
    (leftResult rightResult : DeferredResolution)
    (hleft : some leftResult ∈ support (resolveDeferredPositionValue position left))
    (hright : some rightResult ∈ support (resolveDeferredPositionValue position right))
    (hvalues : left.values = right.values)
    (houtput : leftResult.output = rightResult.output) :
    leftResult.values = rightResult.values := by
  funext other
  by_cases heq : other = position
  · subst other
    rw [resolveDeferredPositionValue_installs position left leftResult hleft,
      resolveDeferredPositionValue_installs position right rightResult hright, houtput]
  · rw [resolveDeferredPositionValue_preserves_other position other left leftResult heq hleft,
      resolveDeferredPositionValue_preserves_other position other right rightResult heq hright,
      hvalues]

theorem clearPending_materialize_comm
    (state : LazyRevealProbe.State Coordinate) (cleared materialized : Coordinate)
    (output : HashOutput) :
    (state.clearPending cleared).materialize materialized output =
      (state.materialize materialized output).clearPending cleared := by
  rcases state with ⟨pending, values, revealed, ensured⟩
  simp [LazyRevealProbe.State.clearPending, LazyRevealProbe.State.materialize,
    LazyRevealProbe.State.pendingAway, and_comm]
  exact Finset.filter_comm (fun x : Coordinate × Digest => ¬x.1 = cleared)
    (fun x => ¬x.1 = materialized) pending

end SphincsSecurity.Concrete.OtsProbeSimulation
