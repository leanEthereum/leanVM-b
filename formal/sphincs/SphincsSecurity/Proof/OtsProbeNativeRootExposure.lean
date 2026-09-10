import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeRootUnsafeAction
import SphincsSecurity.Proof.OtsProbeStartHistorySupport

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem nativeRootActionSafe_target_failure_input
    (parameter : PublicParameter) (target : Position) (before after : HashOutput) (input : HashInput)
    (left right : DeferredContext) (hcontext : NativeRootContextRel target before after left right)
    (hunsafe : ¬NativeRootActionSafe parameter target input left right (.resolve (.position target))) :
    purePeekTableInput parameter left.state (.position target) = some input := by
  have hnot : target ∉ target.children := fun hmem => Nat.lt_irrefl _ (Position.depth_lt_of_mem_children hmem)
  have heq := hcontext.purePeekTableInput_eq_of_not_mem_children parameter target hnot
  by_contra hleft
  apply hunsafe
  exact Or.inr ⟨hleft, by rw [← heq]; exact hleft⟩

theorem published_of_mem_runResolved_publish_then
    (coordinate : Coordinate) (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table
      (LazyRevealProbe.publishQuery coordinate >>= next))) :
    coordinate ∈ result.context.state.revealed := by
  rw [LazyRevealProbe.publishQuery, runResolvedFromTable_publish_query_bind] at hresult
  apply revealed_subset_of_mem_runResolvedFromTable _ _ fuel table result hresult
  exact Finset.mem_insert_self _ _

theorem published_of_mem_runResolved_resolveKnownInput_of_match
    (parameter : PublicParameter) (coordinate : Coordinate) (input : HashInput)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hmatch : purePeekTableInput parameter context.state coordinate = some input)
    (result : ResolvedRunResult (HashOutput × SplitHashCache))
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table ((resolveKnownInput parameter coordinate input).run cache))) :
    coordinate ∈ result.context.state.revealed := by
  rw [runResolvedFromTable_resolveKnownInput_eq_public] at hresult
  simp only [resolvePublicKnownInput, hmatch, ↓reduceIte] at hresult
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨middle, hmiddle, htail⟩ := hresult
  cases middle with
  | none => simp at htail
  | some middle =>
      simp only [StateT.run_bind, publishCoordinate, StateT.run_liftM, bind_assoc, pure_bind] at htail
      exact published_of_mem_runResolved_publish_then coordinate _ middle.context middle.remaining middle.table result htail

theorem nativeRootHash_target_action_failure_publishes
    (parameter : PublicParameter) (target : Position) (hroot : IsLayerRoot target) (before after : HashOutput)
    (input : HashInput) (left right : DeferredContext) (hcontext : NativeRootContextRel target before after left right)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (haction : (purePlanProbingHashQuery parameter input left.state).action = .resolve (.position target))
    (hunsafe : ¬NativeRootActionSafe parameter target input left right (.resolve (.position target)))
    (result : ResolvedRunResult (HashOutput × SplitHashCache))
    (hresult : some result ∈ support (runResolvedFromTable left fuel table ((probingHashQuery parameter input).run cache))) :
    .position target ∈ result.context.state.revealed := by
  have hmatch := nativeRootActionSafe_target_failure_input parameter target before after input left right hcontext hunsafe
  have hnone : (purePlanProbingHashQuery parameter input left.state).candidate? = none := by
    obtain ⟨lay, tree, rfl⟩ := hroot
    unfold layerRootPosition at hmatch
    apply purePlanProbingHashQuery_candidate_none_of_known_node parameter input left.state lay tree _ _
      (purePeekTableInput_node_some_atPosition parameter left.state lay tree _ _ input hmatch)
    rw [hmatch]
    simp
  rw [runResolved_probingHashQuery_eq_afterPlan] at hresult
  simp only [probingHashQueryAfterPlan, executePlannedHashQuery, hnone, executeCandidate?, pure_bind, haction] at hresult
  exact published_of_mem_runResolved_resolveKnownInput_of_match parameter (.position target) input left fuel table cache hmatch result hresult

end SphincsSecurity.Concrete.OtsProbeSimulation
