import SphincsSecurity.Proof.FtsProbeVerifierSource
import SphincsSecurity.Proof.FtsProbeCappedPrefixSupport
import SphincsSecurity.Proof.FtsProbeRetainedLogCoverage

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] OtsProbeSimulation.maskedPublishedTreeRoot

theorem jointCappedRetainedRest_hit_revealed
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest) (adversary : Adversary) (q : Nat)
    (forgery : Forgery) (log : QueryLog SigningSpec) (verified : Bool)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache)
    (entry : OtsProbeSimulation.HistoryResolvedPrefix (Option RetainedGameResult × OtsProbeSimulation.SplitHashCache))
    (hbudget : q ≤ ftsFuel) (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache)
    (f : QueryImpl HashSpec Id) (hf : (mergedCache parameter table finalCache).AgreesWithFn f)
    (hvalue : entry.value.1 = some (root, ((forgery, log), verified)))
    (hresult : .done false finalState (some entry, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((maskedJointComputation parameter root (Option.map (fun rest => (root, rest)) <$>
          OtsProbeSimulation.capOuterHashQueries (retainedGameRestComputation adversary ⟨root, parameter⟩) q)
          context fuel history cache).run ftsCache)))
    (digest : MessageDigest) (tree : FtsTree)
    (hdigest : evalWithAnswerFn f (messageDigest parameter root forgery.message forgery.signature.randomness) = digest)
    (hadmissible : Admissible digest)
    (hsecret : forgery.signature.ftsSecret tree = table (digestIndex digest, tree, digestLeaves digest (ftsIndexOf tree))) :
    ∃ value, finalState.revealed (digestIndex digest, tree, digestLeaves digest (ftsIndexOf tree)) = some value := by
  unfold retainedGameRestComputation at hresult
  obtain ⟨pair, stepState, capFuel, stepFuel, stepContext, nativeFuel, stepHistory, nativeCache, stepCache,
      hbudget', hclean', hsynced', htail⟩ := mem_support_jointCapped_after_prefix parameter root table
    (signingTraceComputation (adversary.main ⟨root, parameter⟩)) _ (fun rest => (root, rest)) q _
    state finalState ftsFuel context fuel history cache ftsCache finalCache entry hbudget hclean hsynced hvalue hresult
  have hbound : (Option.map (fun rest => (root, rest)) <$>
      OtsProbeSimulation.capOuterHashQueries (do
        let verified ← liftOracleWorldLeft (scheme.verify ⟨root, parameter⟩ pair.1.message pair.1.signature)
        pure (pair, verified)) capFuel).IsQueryBoundP OtsProbeSimulation.IsOuterHash stepFuel := by
    rw [isQueryBoundP_map_iff]
    exact (OtsProbeSimulation.capOuterHashQueries_hashBound _ capFuel).mono hbudget'
  have hsource := mem_support_source_of_maskedJointComputation parameter root table _ stepState finalState stepFuel
    stepContext nativeFuel stepHistory nativeCache stepCache finalCache entry hbound hclean' hsynced' htail
  simp only [bind_pure_comp, OtsProbeSimulation.capOuterHashQueries_map, Functor.map_map] at hsource
  rw [support_map] at hsource
  obtain ⟨selected, _, hselected⟩ := hsource
  have hpair : pair = (forgery, log) := by
    rw [hvalue] at hselected
    cases selected with
    | none => cases hselected
    | some selected =>
        have heq := congrArg (fun result : Option RetainedGameResult => result.map (fun value => value.2.1)) hselected
        simpa only [Option.map_some, Option.some.injEq] using heq
  rw [hpair] at htail
  dsimp only at htail
  rw [liftOracleWorldLeft_scheme_verify] at htail
  exact jointCappedVerifier_hit_revealed parameter root table forgery.message forgery.signature
    (fun verdict => pure ((forgery, log), verdict)) (fun rest => (root, rest)) capFuel _ stepState finalState stepFuel
    stepContext nativeFuel stepHistory nativeCache stepCache finalCache entry hbudget' hclean' hsynced' f hf hvalue htail
    digest tree hdigest hadmissible hsecret

theorem jointRetainedDetailed_hit_revealed
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest) (adversary : Adversary) (q : Nat)
    (forgery : Forgery) (log : QueryLog SigningSpec) (verified : Bool)
    (finalState : AdaptiveRevealProbe.State Coordinate) (finalCache : SplitHashCache)
    (entry : OtsProbeSimulation.HistoryResolvedPrefix (Option RetainedGameResult × OtsProbeSimulation.SplitHashCache))
    (f : QueryImpl HashSpec Id) (hf : (mergedCache parameter table finalCache).AgreesWithFn f)
    (hvalue : entry.value.1 = some (root, ((forgery, log), verified)))
    (hresult : .done false finalState (some entry, finalCache) ∈ support (jointRetainedDetailed adversary parameter table q))
    (digest : MessageDigest) (tree : FtsTree)
    (hdigest : evalWithAnswerFn f (messageDigest parameter root forgery.message forgery.signature.randomness) = digest)
    (hadmissible : Admissible digest)
    (hsecret : forgery.signature.ftsSecret tree = table (digestIndex digest, tree, digestLeaves digest (ftsIndexOf tree))) :
    ∃ value, finalState.revealed (digestIndex digest, tree, digestLeaves digest (ftsIndexOf tree)) = some value := by
  have hclean : AdaptiveRevealProbe.tableHits (AdaptiveRevealProbe.State.empty : AdaptiveRevealProbe.State Coordinate) table = false := by
    simp [AdaptiveRevealProbe.tableHits, AdaptiveRevealProbe.State.empty]
  unfold jointRetainedDetailed maskedJointRetained at hresult
  rcases mem_support_bindNativeSteps_done table AdaptiveRevealProbe.State.empty finalState q _ _
    (OtsProbeSimulation.ensuredInitialContext ∅) 0 [] OtsProbeSimulation.emptySplitHashCache emptySplitHashCache finalCache
    (some entry) hclean (liftNativeBlock_probeFree _ _ _ _ _) hresult with
    ⟨hno, _⟩ | ⟨stepState, rootEntry, stepCache, hleft, htail⟩
  · cases hno
  · obtain ⟨hstate, hsynced', _⟩ := invariants_liftNativeBlock parameter table AdaptiveRevealProbe.State.empty stepState q
      OtsProbeSimulation.maskedPublishedTreeRoot (cacheMapCommutes_native_maskedPublishedTreeRoot parameter table)
      (OtsProbeSimulation.ensuredInitialContext ∅) 0 [] OtsProbeSimulation.emptySplitHashCache emptySplitHashCache stepCache (some rootEntry)
      (revealedSynced_empty parameter table) hleft
    have hclean' : AdaptiveRevealProbe.tableHits stepState table = false := by simpa [hstate] using hclean
    have hbound : (Option.map (fun rest => (rootEntry.value.1, rest)) <$>
        OtsProbeSimulation.capOuterHashQueries (retainedGameRestComputation adversary ⟨rootEntry.value.1, parameter⟩) q).IsQueryBoundP
        OtsProbeSimulation.IsOuterHash q := by
      rw [isQueryBoundP_map_iff]
      exact OtsProbeSimulation.capOuterHashQueries_hashBound _ q
    have hsource := mem_support_source_of_maskedJointComputation parameter rootEntry.value.1 table _ stepState finalState q
      rootEntry.context rootEntry.remaining rootEntry.history rootEntry.value.2 stepCache finalCache entry hbound hclean' hsynced' htail
    rw [support_map] at hsource
    obtain ⟨selected, _, hselected⟩ := hsource
    have hroot : rootEntry.value.1 = root := by
      rw [hvalue] at hselected
      cases selected with
      | none => cases hselected
      | some selected => exact congrArg (fun result : Option RetainedGameResult => result.map Prod.fst) hselected |> Option.some.inj
    rw [hroot] at htail
    exact jointCappedRetainedRest_hit_revealed parameter root table adversary q forgery log verified stepState finalState q
      rootEntry.context rootEntry.remaining rootEntry.history rootEntry.value.2 stepCache finalCache entry le_rfl hclean' hsynced' f hf
      hvalue htail digest tree hdigest hadmissible hsecret

end SphincsSecurity.Concrete.FtsProbeSimulation
