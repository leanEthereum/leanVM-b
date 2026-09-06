import SphincsSecurity.Proof.FtsProbeCappedLogCoverage
import SphincsSecurity.Proof.RetainedSigningTrace
import SphincsSecurity.Proof.FtsProbeJointRetainedRisk

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] OtsProbeSimulation.maskedPublishedTreeRoot

theorem revealedOnlyFrom_maskedJointCappedRetainedRest
    (secretKey : SecretKey) (table : Coordinate → Digest) (adversary : Adversary) (q : Nat)
    (forgery : Forgery) (log : QueryLog SigningSpec) (verified : Bool)
    (state finalState : AdaptiveRevealProbe.State Coordinate)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache)
    (entry : OtsProbeSimulation.HistoryResolvedPrefix (Option RetainedGameResult × OtsProbeSimulation.SplitHashCache))
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced secretKey.parameter table state ftsCache)
    (f : QueryImpl HashSpec Id) (hf : (mergedCache secretKey.parameter table finalCache).AgreesWithFn f)
    (hvalue : entry.value.1 = some (secretKey.root, ((forgery, log), verified)))
    (hresult : .done false finalState (some entry, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state q
        ((maskedJointComputation secretKey.parameter secretKey.root
          (Option.map (fun rest => (secretKey.root, rest)) <$>
            OtsProbeSimulation.capOuterHashQueries (retainedGameRestComputation adversary ⟨secretKey.root, secretKey.parameter⟩) q)
          context fuel history cache).run ftsCache))) :
    RevealedOnlyFrom state finalState (CoveredByLog f (mergedCache secretKey.parameter table finalCache) secretKey log) := by
  rw [retainedGameRestComputation_eq_signingTrace, OtsProbeSimulation.capOuterHashQueries_map,
    OtsProbeSimulation.capOuterHashQueries_signingTrace] at hresult
  simp only [Functor.map_map] at hresult
  apply revealedOnlyFrom_maskedJointSigningTrace_map secretKey table
    (OtsProbeSimulation.capOuterHashQueries (unloggedRetainedRestComputation adversary ⟨secretKey.root, secretKey.parameter⟩) q)
    _ log state finalState q context fuel history cache ftsCache finalCache entry _ hclean hsynced f hf _ hresult
  · rw [isQueryBoundP_map_iff]
    exact OtsProbeSimulation.isQueryBoundP_signingTraceComputation _ q (OtsProbeSimulation.capOuterHashQueries_hashBound _ q)
  · intro selected tail hproject signed hsigned
    rw [hvalue] at hproject
    cases selected with
    | none => cases hproject
    | some selected =>
        have hlog := congrArg (fun result : Option RetainedGameResult => result.map (fun value => value.2.1.2)) hproject
        have heq : tail = log := by
          simpa only [Function.comp_apply, OtsProbeSimulation.completedSigningTrace, Option.map_some,
            arrangeRetainedTrace, Option.some.injEq] using hlog
        exact heq ▸ hsigned

theorem revealedOnlyFrom_maskedJointRetained
    (secretKey : SecretKey) (table : Coordinate → Digest) (adversary : Adversary) (q : Nat)
    (forgery : Forgery) (log : QueryLog SigningSpec) (verified : Bool)
    (state finalState : AdaptiveRevealProbe.State Coordinate)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache)
    (entry : OtsProbeSimulation.HistoryResolvedPrefix (Option RetainedGameResult × OtsProbeSimulation.SplitHashCache))
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced secretKey.parameter table state ftsCache)
    (f : QueryImpl HashSpec Id) (hf : (mergedCache secretKey.parameter table finalCache).AgreesWithFn f)
    (hvalue : entry.value.1 = some (secretKey.root, ((forgery, log), verified)))
    (hresult : .done false finalState (some entry, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state q
        ((maskedJointRetained adversary secretKey.parameter q context fuel history cache).run ftsCache))) :
    RevealedOnlyFrom state finalState (CoveredByLog f (mergedCache secretKey.parameter table finalCache) secretKey log) := by
  rw [maskedJointRetained] at hresult
  rcases mem_support_bindNativeSteps_done table state finalState q _ _ context fuel history cache ftsCache finalCache
    (some entry) hclean (liftNativeBlock_probeFree _ context fuel history cache) hresult with
    ⟨hno, _⟩ | ⟨stepState, rootEntry, stepCache, hleft, htail⟩
  · cases hno
  · obtain ⟨hstate, hsynced', _⟩ := invariants_liftNativeBlock secretKey.parameter table state stepState q
      OtsProbeSimulation.maskedPublishedTreeRoot (cacheMapCommutes_native_maskedPublishedTreeRoot secretKey.parameter table)
      context fuel history cache ftsCache stepCache (some rootEntry) hsynced hleft
    have hclean' : AdaptiveRevealProbe.tableHits stepState table = false := by simpa [hstate] using hclean
    have hbound : (Option.map (fun rest => (rootEntry.value.1, rest)) <$>
        OtsProbeSimulation.capOuterHashQueries (retainedGameRestComputation adversary ⟨rootEntry.value.1, secretKey.parameter⟩) q).IsQueryBoundP
        OtsProbeSimulation.IsOuterHash q := by
      rw [isQueryBoundP_map_iff]
      exact OtsProbeSimulation.capOuterHashQueries_hashBound _ q
    have hsource := mem_support_source_of_maskedJointComputation secretKey.parameter rootEntry.value.1 table _
      stepState finalState q rootEntry.context rootEntry.remaining rootEntry.history rootEntry.value.2 stepCache finalCache entry
      hbound hclean' hsynced' htail
    rw [support_map] at hsource
    obtain ⟨selected, _, hselected⟩ := hsource
    have hroot : rootEntry.value.1 = secretKey.root := by
      rw [hvalue] at hselected
      cases selected with
      | none => cases hselected
      | some selected => exact congrArg (fun result : Option RetainedGameResult => result.map Prod.fst) hselected |> Option.some.inj
    rw [hroot] at htail
    have hcoverage := revealedOnlyFrom_maskedJointCappedRetainedRest secretKey table adversary q forgery log verified
      stepState finalState rootEntry.context rootEntry.remaining rootEntry.history rootEntry.value.2 stepCache finalCache entry
      hclean' hsynced' f hf hvalue htail
    simpa only [hstate] using hcoverage

theorem jointRetainedDetailed_revealed_covered
    (secretKey : SecretKey) (table : Coordinate → Digest) (adversary : Adversary) (q : Nat)
    (forgery : Forgery) (log : QueryLog SigningSpec) (verified : Bool)
    (finalState : AdaptiveRevealProbe.State Coordinate) (finalCache : SplitHashCache)
    (entry : OtsProbeSimulation.HistoryResolvedPrefix (Option RetainedGameResult × OtsProbeSimulation.SplitHashCache))
    (f : QueryImpl HashSpec Id) (hf : (mergedCache secretKey.parameter table finalCache).AgreesWithFn f)
    (hvalue : entry.value.1 = some (secretKey.root, ((forgery, log), verified)))
    (hresult : .done false finalState (some entry, finalCache) ∈ support
      (jointRetainedDetailed adversary secretKey.parameter table q)) :
    ∀ coordinate value, finalState.revealed coordinate = some value →
      CoveredByLog f (mergedCache secretKey.parameter table finalCache) secretKey log coordinate := by
  have hcoverage := revealedOnlyFrom_maskedJointRetained secretKey table adversary q forgery log verified
    AdaptiveRevealProbe.State.empty finalState (OtsProbeSimulation.ensuredInitialContext ∅) 0 []
    OtsProbeSimulation.emptySplitHashCache emptySplitHashCache finalCache entry
    (by simp [AdaptiveRevealProbe.tableHits, AdaptiveRevealProbe.State.empty]) (revealedSynced_empty secretKey.parameter table)
    f hf hvalue hresult
  intro coordinate value hrevealed
  rcases hcoverage coordinate value hrevealed with hold | hcovered
  · simp [AdaptiveRevealProbe.State.empty] at hold
  · exact hcovered

end SphincsSecurity.Concrete.FtsProbeSimulation
