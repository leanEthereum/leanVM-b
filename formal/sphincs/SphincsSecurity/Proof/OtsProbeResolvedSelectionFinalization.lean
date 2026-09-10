import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedSchedule

/-!
# Finalization equivalence through one-time layer selection

Layer selection may materialize the lower layer root before selecting a counter. This file lifts
the finalization view through those materializing computations while retaining exact public outputs
and ordinary-cache behavior.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem FinalizationViewEq.ensure
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewEq table left right) (coordinate : Coordinate) :
    FinalizationViewEq table
      { left with state := left.state.ensure coordinate }
      { right with state := right.state.ensure coordinate } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change left.ValuesConsistent
    exact hview.leftConsistent
  · change right.ValuesConsistent
    exact hview.rightConsistent
  · change StartTableAgrees left.state table
    exact hview.leftStarts
  · change StartTableAgrees right.state table
    exact hview.rightStarts
  · change resolvedCompletionValue table left = resolvedCompletionValue table right
    exact hview.valueEq
  · intro other output hvalue
    change ¬left.state.hitAt other output
    apply hview.leftClean other output
    change resolvedCompletionValue table left other = some output at hvalue
    exact hvalue
  · intro other output hvalue
    change ¬right.state.hitAt other output
    apply hview.rightClean other output
    change resolvedCompletionValue table right other = some output at hvalue
    exact hvalue
  · intro other hvalue
    change left.state.pendingAt other = right.state.pendingAt other
    apply hview.pendingEq other
    change resolvedCompletionValue table left other = none at hvalue
    exact hvalue

theorem DeferredCompletable.ensure
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hcompletable : DeferredCompletable table context) (coordinate : Coordinate) :
    DeferredCompletable table
      { context with state := context.state.ensure coordinate } := by
  rcases hcompletable with ⟨completion, hcompletion⟩
  rcases hcompletion with ⟨hstate, hprivate, hpending, htable⟩
  exact ⟨completion, ⟨hstate, hprivate, hpending, htable⟩⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
