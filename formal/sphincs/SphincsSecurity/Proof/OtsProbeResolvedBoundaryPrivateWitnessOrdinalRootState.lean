import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FtsProbeSimulation
import SphincsSecurity.Proof.OtsProbeSimulation

/-!
# Hidden layer-root state quotient

Two delayed-root runs may store different full outputs at one unpublished structural position while
all public lazy-state bookkeeping remains equal. This quotient isolates that one cell and is the
state-side companion of `RootEncodingCacheRel`.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

structure RootHiddenStateRel
    (target : Position) (leftOutput rightOutput : HashOutput)
    (left right : LazyRevealProbe.State Coordinate) : Prop where
  pending : left.pending = right.pending
  revealed : left.revealed = right.revealed
  ensured : left.ensured = right.ensured
  target_private : Coordinate.position target ∉ left.revealed
  left_target : left.values (.position target) = some leftOutput
  right_target : right.values (.position target) = some rightOutput
  other_values : ∀ coordinate, coordinate ≠ .position target →
    left.values coordinate = right.values coordinate

structure RootHiddenCacheRel
    (target : Position) (leftOutput rightOutput : HashOutput)
    (left right : SplitHashCache) : Prop where
  ordinary : ∀ input, left (.ordinary input) = right (.ordinary input)
  left_target : left (.hidden (.position target)) = some leftOutput
  right_target : right (.hidden (.position target)) = some rightOutput
  other_hidden : ∀ coordinate, coordinate ≠ .position target →
    left (.hidden coordinate) = right (.hidden coordinate)

theorem RootHiddenCacheRel.update_same_ordinary
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : SplitHashCache}
    (hrel : RootHiddenCacheRel target leftOutput rightOutput left right)
    (input : HashInput) (output : HashOutput) :
    RootHiddenCacheRel target leftOutput rightOutput
      (Function.update left (.ordinary input) (some output))
      (Function.update right (.ordinary input) (some output)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro other
    by_cases heq : SplitHashKey.ordinary other = .ordinary input
    · simp [heq]
    · simp [Function.update_of_ne heq, hrel.ordinary other]
  · simp [hrel.left_target]
  · simp [hrel.right_target]
  · intro coordinate hne
    simp [hrel.other_hidden coordinate hne]

def replaceHiddenRootCache
    (target : Position) (output : HashOutput) (cache : SplitHashCache) : SplitHashCache :=
  Function.update cache (.hidden (.position target)) (some output)

theorem rootHiddenCacheRel_replace
    (target : Position) (leftOutput rightOutput : HashOutput)
    (cache : SplitHashCache)
    (hleft : cache (.hidden (.position target)) = some leftOutput) :
    RootHiddenCacheRel target leftOutput rightOutput cache
      (replaceHiddenRootCache target rightOutput cache) := by
  refine ⟨?_, hleft, ?_, ?_⟩
  · intro input
    simp [replaceHiddenRootCache]
  · simp [replaceHiddenRootCache]
  · intro coordinate hne
    have hkey : SplitHashKey.hidden coordinate ≠ .hidden (.position target) := by
      intro heq
      exact hne (SplitHashKey.hidden.inj heq)
    simp [replaceHiddenRootCache, Function.update_of_ne hkey]

end SphincsSecurity.Concrete.OtsProbeSimulation
