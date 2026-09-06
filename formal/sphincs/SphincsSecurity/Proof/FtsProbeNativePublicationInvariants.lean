import SphincsSecurity.Proof.FtsProbePublicationCacheTransport

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000

theorem revealAfterNativeBody_probeFree
    (parameter : PublicParameter) (index : Index) (leaves : DigestTree → FtsLeaf)
    (bodyRun : ProbComp NativeBodyResult) :
    ProbeFree (revealAfterNativeBody parameter index leaves bodyRun) := by
  have hbody : ProbeFree (liftM (AdaptiveRevealProbe.liftProbComp (Coordinate := Coordinate) bodyRun) :
      StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) NativeBodyResult) := by
    intro cache
    rw [StateT.run_liftM, bind_pure_comp, isQueryBoundP_map_iff]
    exact AdaptiveRevealProbe.liftProbComp_isProbeBound bodyRun 0
  unfold revealAfterNativeBody
  apply hbody.bind
  intro entry
  cases entry with
  | none => exact ProbeFree.pure _
  | some entry =>
      simp only
      cases hbody : entry.value.1 with
      | none => exact ProbeFree.pure _
      | some body =>
          exact (revealSelectedFtsSecrets_probeFree parameter index leaves).bind fun _ => ProbeFree.pure _

theorem invariants_revealAfterNativeBody
    (parameter : PublicParameter) (table : Coordinate → Digest) (index : Index) (leaves : DigestTree → FtsLeaf)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) (cache finalCache : SplitHashCache)
    (bodyRun : ProbComp NativeBodyResult) (result : NativePublicationResult)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state cache) (hcached : HiddenIndexCached index cache)
    (hresult : .done false finalState (result, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel ((revealAfterNativeBody parameter index leaves bodyRun).run cache))) :
    AdaptiveRevealProbe.tableHits finalState table = false ∧
      RevealedSynced parameter table finalState finalCache ∧
        mergedCache parameter table finalCache = mergedCache parameter table cache := by
  refine ⟨tableHits_false_of_mem_runDetailed_probeFree table state finalState fuel _
    (revealAfterNativeBody_probeFree parameter index leaves bodyRun cache) hclean (result, finalCache) hresult, ?_⟩
  unfold revealAfterNativeBody at hresult
  simp only [StateT.run_bind, StateT.run_liftM, bind_assoc, pure_bind] at hresult
  rw [AdaptiveRevealProbe.runDetailed_liftProbComp_bind, mem_support_bind_iff] at hresult
  obtain ⟨entry, _, hresult⟩ := hresult
  cases entry with
  | none =>
      simp only [StateT.run_pure, AdaptiveRevealProbe.runDetailed, construct_pure, hclean,
        mem_support_pure_iff, AdaptiveRevealProbe.DetailedResult.done.injEq] at hresult
      have hstate : finalState = state := hresult.2.1
      have hcache : finalCache = cache := congrArg Prod.snd hresult.2.2
      subst finalState
      subst finalCache
      exact ⟨hsynced, rfl⟩
  | some entry =>
      cases hbody : entry.value.1 with
      | none =>
          simp only [hbody, StateT.run_pure, AdaptiveRevealProbe.runDetailed, construct_pure, hclean,
            mem_support_pure_iff, AdaptiveRevealProbe.DetailedResult.done.injEq] at hresult
          have hstate : finalState = state := hresult.2.1
          have hcache : finalCache = cache := congrArg Prod.snd hresult.2.2
          subst finalState
          subst finalCache
          exact ⟨hsynced, rfl⟩
      | some body =>
          simp only [hbody, StateT.run_map, bind_pure_comp] at hresult
          rw [AdaptiveRevealProbe.runDetailed_mapValue, support_map] at hresult
          obtain ⟨detailed, hdetailed, heq⟩ := hresult
          cases detailed with
          | stopped hit => simp [AdaptiveRevealProbe.DetailedResult.mapValue] at heq
          | done hit selectedState selected =>
              simp only [AdaptiveRevealProbe.DetailedResult.mapValue, AdaptiveRevealProbe.DetailedResult.done.injEq,
                Prod.mk.injEq] at heq
              obtain ⟨hhit, hstate, hvalue, hcache⟩ := heq
              subst hit
              subst finalState
              subst finalCache
              subst result
              have hsync := revealedSynced_of_mem_runDetailed_revealSelectedFtsSecrets parameter table index leaves
                state selectedState fuel cache selected.2 hclean hsynced hcached selected.1 hdetailed
              have hordinary := (coupledAt_revealSelectedFtsSecrets parameter table index leaves state fuel cache
                hclean hsynced hcached).mem_support_ordinary hdetailed
              simp only [StateT.run_pure, mem_support_pure_iff] at hordinary
              exact ⟨hsync, congrArg Prod.snd hordinary⟩

theorem publishedNativeCoordinate_replaceCache
    (index : Index) (leaves : DigestTree → FtsLeaf) (result : NativePublicationResult)
    (ordinary : QueryCache HashSpec) (coordinate : Coordinate) :
    PublishedNativeCoordinate index leaves (result.map (OtsProbeSimulation.replaceHistoryOrdinaryCache ordinary)) coordinate ↔
      PublishedNativeCoordinate index leaves result coordinate := by
  cases result <;> simp [PublishedNativeCoordinate, OtsProbeSimulation.replaceHistoryOrdinaryCache]

theorem revealedOnlyFrom_projectedNativePublication
    (parameter : PublicParameter) (table : Coordinate → Digest) (index : Index) (leaves : DigestTree → FtsLeaf)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) (cache finalCache : SplitHashCache)
    (bodyRun : ProbComp NativeBodyResult) (result : NativePublicationResult)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state cache) (hcached : HiddenIndexCached index cache)
    (hresult : .done false finalState (result, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel ((revealAfterNativeBody parameter index leaves bodyRun).run cache))) :
    RevealedOnlyFrom state finalState (PublishedNativeCoordinate index leaves
      (projectNativePublicationWithCache parameter table (.done false finalState (result, finalCache)))) := by
  have horigin := revealedOnlyFrom_revealAfterNativeBody parameter table index leaves state finalState fuel cache finalCache
    bodyRun result hclean hsynced hcached hresult
  intro coordinate value hvalue
  rcases horigin coordinate value hvalue with hold | hnew
  · exact Or.inl hold
  · right
    simpa only [projectNativePublicationWithCache, publishedNativeCoordinate_replaceCache] using hnew

end SphincsSecurity.Concrete.FtsProbeSimulation
