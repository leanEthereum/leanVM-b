import SphincsSecurity.Proof.OtsProbeNativeRootSwapOrdinaryCache

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

theorem runResolvedFromTable_peekPositionValues_eq_pure
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ∀ positions,
    runResolvedFromTable context fuel table
        ((peekPositionValues positions).run cache) =
      pure (some ⟨context, fuel,
        (purePeekPositionValues context.state positions, cache), table⟩)
  | [] => by
      simp [peekPositionValues, purePeekPositionValues,
        runResolvedFromTable]
  | position :: remaining => by
      rw [peekPositionValues, StateT.run_bind, runResolvedFromTable_bind,
        runResolvedFromTable_peekCoordinate]
      cases hvalue : context.state.values (.position position) with
      | none =>
          simp [purePeekPositionValues, hvalue, runResolvedFromTable]
      | some value =>
          simp only [pure_bind, Option.map_some]
          rw [StateT.run_bind, runResolvedFromTable_bind,
            runResolvedFromTable_peekPositionValues_eq_pure context fuel table cache
              remaining]
          cases htail : purePeekPositionValues context.state remaining <;>
            simp [purePeekPositionValues, hvalue, htail, runResolvedFromTable]

set_option maxRecDepth 100000 in
theorem runResolvedFromTable_peekTableInput_eq_pure
    (parameter : PublicParameter) (coordinate : Coordinate)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runResolvedFromTable context fuel table
        ((peekTableInput parameter coordinate).run cache) =
      pure (some ⟨context, fuel,
        (purePeekTableInput parameter context.state coordinate, cache), table⟩) := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      simp [peekTableInput, purePeekTableInput, runResolvedFromTable]
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          rw [peekTableInput.eq_2]
          by_cases hzero : step.val = 0
          · rw [if_pos hzero]
            rw [StateT.run_bind, runResolvedFromTable_bind,
              runResolvedFromTable_peekCoordinate]
            cases hvalue : context.state.values (.chainStart lay tree leafIdx chainIdx) <;>
              simp [purePeekTableInput, hzero, hvalue,
                runResolvedFromTable]
          · rw [if_neg hzero]
            rw [StateT.run_bind, runResolvedFromTable_bind,
              runResolvedFromTable_peekPositionValues_eq_pure]
            cases hvalues : purePeekPositionValues context.state
                (Position.chain lay tree leafIdx chainIdx step).children <;>
              simp [purePeekTableInput, hzero, hvalues,
                runResolvedFromTable]
      | leaf lay tree leafIdx =>
          simp only [peekTableInput]
          rw [StateT.run_bind, runResolvedFromTable_bind,
            runResolvedFromTable_peekPositionValues_eq_pure]
          cases hvalues : purePeekPositionValues context.state _ <;>
            simp [purePeekTableInput, hvalues, runResolvedFromTable]
      | node lay tree level nodeIdx =>
          simp only [peekTableInput]
          rw [StateT.run_bind, runResolvedFromTable_bind,
            runResolvedFromTable_peekPositionValues_eq_pure]
          cases hvalues : purePeekPositionValues context.state _ <;>
            simp [purePeekTableInput, hvalues, runResolvedFromTable]
      | ftsLeaf index tree leafIdx =>
          simp only [peekTableInput]
          rw [StateT.run_bind, runResolvedFromTable_bind,
            runResolvedFromTable_peekPositionValues_eq_pure]
          cases hvalues : purePeekPositionValues context.state _ <;>
            simp [purePeekTableInput, hvalues, runResolvedFromTable]
      | ftsNode index tree level nodeIdx =>
          simp only [peekTableInput]
          rw [StateT.run_bind, runResolvedFromTable_bind,
            runResolvedFromTable_peekPositionValues_eq_pure]
          cases hvalues : purePeekPositionValues context.state _ <;>
            simp [purePeekTableInput, hvalues, runResolvedFromTable]
      | ftsRoots index =>
          simp only [peekTableInput]
          rw [StateT.run_bind, runResolvedFromTable_bind,
            runResolvedFromTable_peekPositionValues_eq_pure]
          cases hvalues : purePeekPositionValues context.state _ <;>
            simp [purePeekTableInput, hvalues, runResolvedFromTable]

end SphincsSecurity.Concrete.OtsProbeSimulation
