import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelectionMaterialized

/-!
# Deferred selection to materialized selection

The ordinary refinement relation is generalized to two computations. This is the semantic bridge
between the real deferred planned suffix and the materialized suffix that executes the same public
plan. A private first fire on the deferred side remains an admissible stopped outcome; a
materialization-only discrepancy makes the right side doomed.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem purePeekPositionValues_eq_of_values_eq
    {left right : LazyRevealProbe.State Coordinate}
    (hvalues : left.values = right.values) : ∀ positions,
    purePeekPositionValues left positions = purePeekPositionValues right positions
  | [] => rfl
  | position :: remaining => by
      simp only [purePeekPositionValues]
      rw [hvalues]
      cases truncateHash <$> right.values (.position position) with
      | none => rfl
      | some value => rw [purePeekPositionValues_eq_of_values_eq hvalues remaining]

theorem purePeekTableInput_eq_of_values_eq
    (parameter : PublicParameter)
    {left right : LazyRevealProbe.State Coordinate}
    (hvalues : left.values = right.values) (coordinate : Coordinate) :
    purePeekTableInput parameter left coordinate =
      purePeekTableInput parameter right coordinate := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx => rfl
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          simp only [purePeekTableInput]
          by_cases hzero : step.val = 0
          · simp only [hzero, ↓reduceIte]
            rw [hvalues]
          · simp only [hzero, ↓reduceIte]
            rw [purePeekPositionValues_eq_of_values_eq hvalues]
      | leaf | node | ftsLeaf | ftsNode | ftsRoots =>
          simp only [purePeekTableInput]
          rw [purePeekPositionValues_eq_of_values_eq hvalues]

end SphincsSecurity.Concrete.OtsProbeSimulation
