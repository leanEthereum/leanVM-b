import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedSchedule

/-!
# Finalization equivalence for the chronological signer

This file carries the layer-schedule coupling through the delayed publication pass and the complete
signer.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem FinalizationViewEq.publish
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewEq table left right) (coordinate : Coordinate) :
    FinalizationViewEq table
      { left with state := left.state.publish coordinate }
      { right with state := right.state.publish coordinate } := by
  refine ⟨hview.leftConsistent.publish coordinate,
    hview.rightConsistent.publish coordinate, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hview.leftStarts
  · exact hview.rightStarts
  · exact hview.valueEq
  · exact hview.leftClean
  · exact hview.rightClean
  · exact hview.pendingEq

theorem DeferredCompletable.publish
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hcompletable : DeferredCompletable table context) (coordinate : Coordinate) :
    DeferredCompletable table
      { context with state := context.state.publish coordinate } := by
  rcases hcompletable with ⟨completion, hcompletion⟩
  exact ⟨completion, hcompletion⟩

noncomputable def finishResolvedRunIsNone
    (input : Option (ResolvedRunResult α)) : ProbComp Bool :=
  Option.isNone <$> finishResolvedRun input

end SphincsSecurity.Concrete.OtsProbeSimulation
