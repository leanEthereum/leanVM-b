import SphincsSecurity.Proof.OtsProbeNativeRootEncodingHash

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

theorem runResolvedFromTable_resolveKnownInput_eq_public
    (parameter : PublicParameter) (coordinate : Coordinate) (input : HashInput)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runResolvedFromTable context fuel table ((resolveKnownInput parameter coordinate input).run cache) =
      runResolvedFromTable context fuel table ((resolvePublicKnownInput parameter context.state coordinate input).run cache) := by
  rw [resolveKnownInput, StateT.run_bind, runResolvedFromTable_bind, runResolvedFromTable_peekTableInput_eq_pure]
  simp only [pure_bind]
  rfl

theorem nativeRootRelates_resolvePublicKnownInput_of_ne
    (parameter : PublicParameter) (target : Position) (before after : HashOutput)
    (publicState : LazyRevealProbe.State Coordinate) (coordinate : Coordinate) (hne : coordinate ≠ .position target)
    (input : HashInput) :
    NativeRootRelates target before after
      (resolvePublicKnownInput parameter publicState coordinate input) (resolvePublicKnownInput parameter publicState coordinate input) := by
  unfold resolvePublicKnownInput
  cases hknown : purePeekTableInput parameter publicState coordinate with
  | none => exact nativeRootRelates_splitHashQuery_ordinary target before after input
  | some knownInput =>
      simp only
      by_cases hmatch : knownInput = input
      · rw [if_pos hmatch]
        apply (nativeRootRelates_revealCoordinateOutput_of_ne target before after coordinate hne).bind
        intro leftOutput rightOutput heq
        subst rightOutput
        apply (nativeRootRelates_publishCoordinate target before after coordinate).bind
        intro _ _ _
        apply (nativeRootRelates_modifyOrdinary target before after input leftOutput).bind
        intro _ _ _
        exact nativeRootRelates_pure target before after leftOutput
      · rw [if_neg hmatch]
        exact nativeRootRelates_splitHashQuery_ordinary target before after input

theorem relTriple_nativeRoot_resolveKnownInput_of_eq
    (parameter : PublicParameter) (target : Position) (before after : HashOutput) (coordinate : Coordinate) (input : HashInput)
    (left right : DeferredContext) (hcontext : NativeRootContextRel target before after left right)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (leftCache rightCache : SplitHashCache)
    (hcache : RootHiddenCacheRel target before after leftCache rightCache)
    (hne : coordinate ≠ .position target)
    (heq : purePeekTableInput parameter left.state coordinate = purePeekTableInput parameter right.state coordinate) :
    RelTriple
      (runResolvedFromTable left fuel table ((resolveKnownInput parameter coordinate input).run leftCache))
      (runResolvedFromTable right fuel table ((resolveKnownInput parameter coordinate input).run rightCache))
      (NativeRootSameRel target before after) := by
  rw [runResolvedFromTable_resolveKnownInput_eq_public, runResolvedFromTable_resolveKnownInput_eq_public]
  have hcomp : resolvePublicKnownInput parameter left.state coordinate input =
      resolvePublicKnownInput parameter right.state coordinate input := by
    unfold resolvePublicKnownInput
    rw [heq]
  rw [← hcomp]
  exact nativeRootRelates_resolvePublicKnownInput_of_ne parameter target before after left.state coordinate hne input
    left right hcontext fuel table leftCache rightCache hcache

def NativeRootActionSafe (parameter : PublicParameter) (target : Position) (input : HashInput)
    (left right : DeferredContext) : PlannedHashAction → Prop
  | .ordinary => True
  | .resolve coordinate =>
      (coordinate ≠ .position target ∧
        purePeekTableInput parameter left.state coordinate = purePeekTableInput parameter right.state coordinate) ∨
      (purePeekTableInput parameter left.state coordinate ≠ some input ∧
        purePeekTableInput parameter right.state coordinate ≠ some input)

theorem NativeRootActionSafe.of_values_eq
    {parameter : PublicParameter} {target : Position} {input : HashInput}
    {left right newLeft newRight : DeferredContext} {action : PlannedHashAction}
    (h : NativeRootActionSafe parameter target input left right action)
    (hleft : newLeft.state.values = left.state.values) (hright : newRight.state.values = right.state.values) :
    NativeRootActionSafe parameter target input newLeft newRight action := by
  cases action with
  | ordinary => trivial
  | resolve coordinate =>
      have hl := purePeekTableInput_eq_of_values_eq parameter hleft coordinate
      have hr := purePeekTableInput_eq_of_values_eq parameter hright coordinate
      simpa only [NativeRootActionSafe, hl, hr] using h

theorem relTriple_nativeRoot_hashAction_of_safe
    (parameter : PublicParameter) (target : Position) (before after : HashOutput) (input : HashInput) (action : PlannedHashAction)
    (left right : DeferredContext) (hcontext : NativeRootContextRel target before after left right)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (leftCache rightCache : SplitHashCache)
    (hcache : RootHiddenCacheRel target before after leftCache rightCache)
    (hsafe : NativeRootActionSafe parameter target input left right action) :
    RelTriple
      (runResolvedFromTable left fuel table
        ((match action with
          | .ordinary => splitHashQuery (.ordinary input)
          | .resolve coordinate => resolveKnownInput parameter coordinate input).run leftCache))
      (runResolvedFromTable right fuel table
        ((match action with
          | .ordinary => splitHashQuery (.ordinary input)
          | .resolve coordinate => resolveKnownInput parameter coordinate input).run rightCache))
      (NativeRootSameRel target before after) := by
  cases action with
  | ordinary =>
      exact nativeRootRelates_splitHashQuery_ordinary target before after input
        left right hcontext fuel table leftCache rightCache hcache
  | resolve coordinate =>
      rcases hsafe with ⟨hne, heq⟩ | ⟨hleft, hright⟩
      · exact relTriple_nativeRoot_resolveKnownInput_of_eq parameter target before after coordinate input
          left right hcontext fuel table leftCache rightCache hcache hne heq
      · exact relTriple_nativeRoot_resolveKnownInput_of_miss parameter target before after coordinate input
          left right hcontext fuel table leftCache rightCache hcache hleft hright

end SphincsSecurity.Concrete.OtsProbeSimulation
