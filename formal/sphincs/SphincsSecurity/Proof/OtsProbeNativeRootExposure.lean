import SphincsSecurity.Proof.OtsProbeNativeRootUnsafeAction

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

theorem nativeRootHashSafe_failure_of_hidden_result
    (parameter : PublicParameter) (target : Position) (hroot : IsLayerRoot target) (before after : HashOutput)
    (input : HashInput) (context : DeferredContext) (h : NativePositionReplaceable target before after context)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hunsafe : ¬NativeRootHashSafe parameter target before after input context)
    (result : ResolvedRunResult (HashOutput × SplitHashCache))
    (hresult : some result ∈ support (runResolvedFromTable context fuel table ((probingHashQuery parameter input).run cache)))
    (hhidden : .position target ∉ result.context.state.revealed) :
    (EncodingInputGuessesRoot parameter target (truncateHash before) input ∨
      EncodingInputGuessesRoot parameter target (truncateHash after) input) ∨
    (∃ candidate, (purePlanProbingHashQuery parameter input context.state).candidate? = some candidate ∧
      IsPrivateValueExposure target before after (.probe candidate.coordinate candidate.candidate)) ∨
      KnownHiddenStructuralRootQuery parameter input context := by
  have hinitial : .position target ∉ context.state.revealed := fun hmem =>
    hhidden (revealed_subset_of_mem_runResolvedFromTable _ context fuel table result hresult hmem)
  have hfailure := nativeRootHashSafe_failure_classify parameter target before after input context hunsafe
  rw [h.replace_self] at hfailure
  rcases hfailure with hencoding | hprobe | haction
  · apply Or.inl
    by_cases hleft : EncodingInputGuessesRoot parameter target (truncateHash before) input
    · exact Or.inl hleft
    · apply Or.inr
      by_contra hright
      exact hencoding ⟨hleft, hright⟩
  · exact Or.inr (Or.inl hprobe)
  · rcases nativeRootActionSafe_failure_exposure_or_structuralCharge parameter target hroot before after input _
      context (replaceNativePosition target after context) ⟨h, rfl⟩ hinitial haction with htarget | hstructural
    · rw [htarget] at haction
      exact False.elim (hhidden (nativeRootHash_target_action_failure_publishes parameter target hroot before after input
        context (replaceNativePosition target after context) ⟨h, rfl⟩ fuel table cache htarget haction result hresult))
    · exact Or.inr (Or.inr hstructural)

theorem nativeRootHashSafe_failure_of_hidden_continuation
    (parameter : PublicParameter) (target : Position) (hroot : IsLayerRoot target) (before after : HashOutput)
    (input : HashInput) (context : DeferredContext) (h : NativePositionReplaceable target before after context)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (next : HashOutput → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hunsafe : ¬NativeRootHashSafe parameter target before after input context)
    (result : ResolvedRunResult (α × SplitHashCache))
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table ((probingHashQuery parameter input >>= next).run cache)))
    (hhidden : .position target ∉ result.context.state.revealed) :
    (EncodingInputGuessesRoot parameter target (truncateHash before) input ∨
      EncodingInputGuessesRoot parameter target (truncateHash after) input) ∨
    (∃ candidate, (purePlanProbingHashQuery parameter input context.state).candidate? = some candidate ∧
      IsPrivateValueExposure target before after (.probe candidate.coordinate candidate.candidate)) ∨
      KnownHiddenStructuralRootQuery parameter input context := by
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨middle, hmiddle, htail⟩ := hresult
  cases middle with
  | none => simp at htail
  | some middle =>
      apply nativeRootHashSafe_failure_of_hidden_result parameter target hroot before after input context h fuel table cache
        hunsafe middle hmiddle
      intro hmem
      exact hhidden (revealed_subset_of_mem_runResolvedFromTable _ _ _ _ result htail hmem)

end SphincsSecurity.Concrete.OtsProbeSimulation
