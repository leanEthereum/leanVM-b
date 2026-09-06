import SphincsSecurity.Proof.FtsProbeNativePublication

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (completePublicationEntry)

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000

def PublishedNativeCoordinate (index : Index) (leaves : DigestTree → FtsLeaf)
    (result : NativePublicationResult) (coordinate : Coordinate) : Prop :=
  ∃ entry signature, result = some entry ∧ entry.value.1 = some signature ∧ SelectedCoordinate index leaves coordinate

theorem revealedOnlyFrom_revealAfterNativeBody
    (parameter : PublicParameter) (table : Coordinate → Digest) (index : Index) (leaves : DigestTree → FtsLeaf)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) (cache finalCache : SplitHashCache)
    (bodyRun : ProbComp NativeBodyResult) (result : NativePublicationResult)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state cache) (hcached : HiddenIndexCached index cache)
    (hresult : .done false finalState (result, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel ((revealAfterNativeBody parameter index leaves bodyRun).run cache))) :
    RevealedOnlyFrom state finalState (PublishedNativeCoordinate index leaves result) := by
  unfold revealAfterNativeBody at hresult
  simp only [StateT.run_bind, StateT.run_liftM, bind_assoc, pure_bind] at hresult
  rw [AdaptiveRevealProbe.runDetailed_liftProbComp_bind, mem_support_bind_iff] at hresult
  obtain ⟨entry, _, hresult⟩ := hresult
  cases entry with
  | none =>
      simp only [StateT.run_pure, AdaptiveRevealProbe.runDetailed, construct_pure, hclean,
        mem_support_pure_iff, AdaptiveRevealProbe.DetailedResult.done.injEq] at hresult
      have hstate : finalState = state := hresult.2.1
      rw [hstate]
      exact fun _ _ h => Or.inl h
  | some entry =>
      cases hbody : entry.value.1 with
      | none =>
          simp only [hbody, StateT.run_pure, AdaptiveRevealProbe.runDetailed, construct_pure, hclean,
            mem_support_pure_iff, AdaptiveRevealProbe.DetailedResult.done.injEq] at hresult
          have hstate : finalState = state := hresult.2.1
          rw [hstate]
          exact fun _ _ h => Or.inl h
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
              have horigin := revealedOnlyFrom_revealSelectedFtsSecrets parameter table index leaves state selectedState fuel
                cache selected.2 hclean hsynced hcached selected.1 hdetailed
              intro coordinate value hrevealed
              rcases horigin coordinate value hrevealed with hold | hselected
              · exact Or.inl hold
              · exact Or.inr ⟨completePublicationEntry selected.1 entry, body.complete selected.1, rfl,
                  by simp only [completePublicationEntry, hbody, Option.map_some], hselected⟩

theorem revealedOnlyFrom_maskedNativePublication
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) (layers : Layer → Option OtsProbeSimulation.ChronologicalLayerPart)
    (context : OtsProbeSimulation.DeferredContext) (otsFuel : Nat) (history : List OtsProbeSimulation.Probe)
    (otsCache : OtsProbeSimulation.SplitHashCache) (state finalState : AdaptiveRevealProbe.State Coordinate)
    (ftsFuel : Nat) (ftsCache finalFtsCache : SplitHashCache) (result : NativePublicationResult)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache) (hcached : HiddenIndexCached index ftsCache)
    (hresult : .done false finalState (result, finalFtsCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((maskedNativePublication parameter randomness index leaves ftsPath layers context otsFuel history otsCache).run ftsCache))) :
    RevealedOnlyFrom state finalState (PublishedNativeCoordinate index leaves result) :=
  revealedOnlyFrom_revealAfterNativeBody parameter table index leaves state finalState ftsFuel ftsCache finalFtsCache
    _ result hclean hsynced hcached hresult

theorem PublishedNativeCoordinate.not_of_no_signature
    {index : Index} {leaves : DigestTree → FtsLeaf} {result : NativePublicationResult}
    (hfailed : result.bind (fun entry => entry.value.1) = none) (coordinate : Coordinate) :
    ¬PublishedNativeCoordinate index leaves result coordinate := by
  rintro ⟨entry, signature, rfl, hsignature, _⟩
  simp only [Option.bind_some, hsignature, reduceCtorEq] at hfailed

theorem RevealedOnlyFrom.no_new_reveals_of_no_signature
    {index : Index} {leaves : DigestTree → FtsLeaf} {result : NativePublicationResult}
    {state finalState : AdaptiveRevealProbe.State Coordinate}
    (horigin : RevealedOnlyFrom state finalState (PublishedNativeCoordinate index leaves result))
    (hfailed : result.bind (fun entry => entry.value.1) = none) :
    ∀ coordinate value, finalState.revealed coordinate = some value → state.revealed coordinate = some value := by
  intro coordinate value hrevealed
  exact (horigin coordinate value hrevealed).resolve_right (PublishedNativeCoordinate.not_of_no_signature hfailed coordinate)

end SphincsSecurity.Concrete.FtsProbeSimulation
