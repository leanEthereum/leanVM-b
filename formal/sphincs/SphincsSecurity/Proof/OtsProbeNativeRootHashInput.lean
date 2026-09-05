import SphincsSecurity.Proof.OtsProbeNativeRootProbe

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

theorem relTriple_nativeRoot_peekTableInput_of_eq
    (parameter : PublicParameter) (target : Position) (before after : HashOutput) (coordinate : Coordinate)
    (left right : DeferredContext) (hcontext : NativeRootContextRel target before after left right)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (leftCache rightCache : SplitHashCache)
    (hcache : RootHiddenCacheRel target before after leftCache rightCache)
    (hinput : purePeekTableInput parameter left.state coordinate = purePeekTableInput parameter right.state coordinate) :
    RelTriple
      (runResolvedFromTable left fuel table ((peekTableInput parameter coordinate).run leftCache))
      (runResolvedFromTable right fuel table ((peekTableInput parameter coordinate).run rightCache))
      (NativeRootSameRel target before after) := by
  rw [runResolvedFromTable_peekTableInput_eq_pure, runResolvedFromTable_peekTableInput_eq_pure]
  exact relTriple_pure_pure ⟨hcontext, rfl, rfl, hinput, hcache⟩

theorem nativeRootRelates_peekTableInput_of_not_mem_children
    (parameter : PublicParameter) (target : Position) (before after : HashOutput)
    (position : Position) (hnot : target ∉ position.children) :
    NativeRootRelates target before after
      (peekTableInput parameter (.position position)) (peekTableInput parameter (.position position)) := by
  intro left right hcontext fuel table leftCache rightCache hcache
  exact relTriple_nativeRoot_peekTableInput_of_eq parameter target before after (.position position)
    left right hcontext fuel table leftCache rightCache hcache
    (hcontext.purePeekTableInput_eq_of_not_mem_children parameter position hnot)

theorem nativeRootRelates_revealCoordinateOutput_of_ne
    (target : Position) (before after : HashOutput) (coordinate : Coordinate)
    (hne : coordinate ≠ .position target) :
    NativeRootRelates target before after (revealCoordinateOutput coordinate) (revealCoordinateOutput coordinate) := by
  intro left right hcontext fuel table leftCache rightCache hcache
  apply relTriple_post_mono
    (relTriple_nativeRoot_revealCoordinateOutput target before after coordinate
      left right hcontext fuel table leftCache rightCache hcache)
  intro leftResult rightResult hrel
  cases leftResult with
  | none =>
      cases rightResult with
      | none => trivial
      | some rightResult => contradiction
  | some leftResult =>
      cases rightResult with
      | none => contradiction
      | some rightResult =>
          rcases hrel with ⟨hcontext, hfuel, htable, hvalue, _, hcache⟩
          exact ⟨hcontext, hfuel, htable, (by simpa [hne] using hvalue.symm), hcache⟩

theorem nativeRootRelates_modifyOrdinary
    (target : Position) (before after : HashOutput) (input : HashInput) (output : HashOutput) :
    NativeRootRelates target before after
      (modify fun cache : SplitHashCache => Function.update cache (.ordinary input) (some output))
      (modify fun cache : SplitHashCache => Function.update cache (.ordinary input) (some output)) := by
  intro left right hcontext fuel table leftCache rightCache hcache
  simp only [StateT.run_modify, runResolvedFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨hcontext, rfl, rfl, rfl, hcache.update_same_ordinary input output⟩

theorem nativeRootRelates_resolveKnownInput_of_not_mem_children
    (parameter : PublicParameter) (target : Position) (before after : HashOutput)
    (position : Position) (hnot : target ∉ position.children) (hne : position ≠ target) (input : HashInput) :
    NativeRootRelates target before after
      (resolveKnownInput parameter (.position position) input) (resolveKnownInput parameter (.position position) input) := by
  unfold resolveKnownInput
  apply (nativeRootRelates_peekTableInput_of_not_mem_children parameter target before after position hnot).bind
  intro left right heq
  subst right
  cases left with
  | none => exact nativeRootRelates_splitHashQuery_ordinary target before after input
  | some knownInput =>
      simp only
      by_cases hmatch : knownInput = input
      · rw [if_pos hmatch]
        apply (nativeRootRelates_revealCoordinateOutput_of_ne target before after (.position position) (by simpa using hne)).bind
        intro leftOutput rightOutput heq
        subst rightOutput
        apply (nativeRootRelates_publishCoordinate target before after (.position position)).bind
        intro _ _ _
        apply (nativeRootRelates_modifyOrdinary target before after input leftOutput).bind
        intro _ _ _
        exact nativeRootRelates_pure target before after leftOutput
      · rw [if_neg hmatch]
        exact nativeRootRelates_splitHashQuery_ordinary target before after input

theorem runResolvedFromTable_resolveKnownInput_of_miss
    (parameter : PublicParameter) (coordinate : Coordinate) (input : HashInput)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hmiss : purePeekTableInput parameter context.state coordinate ≠ some input) :
    runResolvedFromTable context fuel table ((resolveKnownInput parameter coordinate input).run cache) =
      runResolvedFromTable context fuel table ((splitHashQuery (.ordinary input)).run cache) := by
  rw [resolveKnownInput, StateT.run_bind, runResolvedFromTable_bind, runResolvedFromTable_peekTableInput_eq_pure]
  simp only [pure_bind]
  cases hknown : purePeekTableInput parameter context.state coordinate with
  | none => rfl
  | some knownInput =>
      have hne : knownInput ≠ input := by intro heq; exact hmiss (hknown.trans (congrArg some heq))
      simp only [if_neg hne]

theorem relTriple_nativeRoot_resolveKnownInput_of_miss
    (parameter : PublicParameter) (target : Position) (before after : HashOutput) (coordinate : Coordinate) (input : HashInput)
    (left right : DeferredContext) (hcontext : NativeRootContextRel target before after left right)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (leftCache rightCache : SplitHashCache)
    (hcache : RootHiddenCacheRel target before after leftCache rightCache)
    (hleft : purePeekTableInput parameter left.state coordinate ≠ some input)
    (hright : purePeekTableInput parameter right.state coordinate ≠ some input) :
    RelTriple
      (runResolvedFromTable left fuel table ((resolveKnownInput parameter coordinate input).run leftCache))
      (runResolvedFromTable right fuel table ((resolveKnownInput parameter coordinate input).run rightCache))
      (NativeRootSameRel target before after) := by
  rw [runResolvedFromTable_resolveKnownInput_of_miss parameter coordinate input left fuel table leftCache hleft,
    runResolvedFromTable_resolveKnownInput_of_miss parameter coordinate input right fuel table rightCache hright]
  exact nativeRootRelates_splitHashQuery_ordinary target before after input left right hcontext fuel table leftCache rightCache hcache

end SphincsSecurity.Concrete.OtsProbeSimulation
