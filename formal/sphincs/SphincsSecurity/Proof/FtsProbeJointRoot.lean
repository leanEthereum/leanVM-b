import SphincsSecurity.Proof.FtsProbeJointExecution
import SphincsSecurity.Proof.OtsProbeOuterCapRetained

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] OtsProbeSimulation.maskedPublishedTreeRoot

theorem cacheMapCommutes_native_maskedPublishedTreeRoot
    (parameter : PublicParameter) (table : Coordinate → Digest) (ftsCache : SplitHashCache) :
    OtsProbeSimulation.CacheMapCommutes (nativeCacheProjection parameter table ftsCache)
      OtsProbeSimulation.maskedPublishedTreeRoot := by
  rw [OtsProbeSimulation.maskedPublishedTreeRoot_eq]
  apply (OtsProbeSimulation.cacheMapCommutes_maskedTreeRoot _
    (nativeCacheProjection_commutesWithHiddenUpdates parameter table ftsCache) _ _).bind
  intro root
  apply (OtsProbeSimulation.CacheMapCommutes.liftM _ _).bind
  intro _
  exact OtsProbeSimulation.CacheMapCommutes.pure _ root

noncomputable def outerCappedNativeRetained
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat) :
    StateT OtsProbeSimulation.SplitHashCache
      (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) (Option RetainedGameResult) := do
  let root ← OtsProbeSimulation.maskedPublishedTreeRoot
  simulateQ (OtsProbeSimulation.maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
    (Option.map (fun rest => (root, rest)) <$>
      OtsProbeSimulation.capOuterHashQueries (retainedGameRestComputation adversary ⟨root, parameter⟩) q)

noncomputable def maskedJointRetained
    (adversary : Adversary) (parameter : PublicParameter) (q : Nat) : NativeFtsStep (Option RetainedGameResult) :=
  bindNativeSteps (liftNativeBlock OtsProbeSimulation.maskedPublishedTreeRoot) fun root =>
    maskedJointComputation parameter root
      (Option.map (fun rest => (root, rest)) <$>
        OtsProbeSimulation.capOuterHashQueries (retainedGameRestComputation adversary ⟨root, parameter⟩) q)

theorem nativeStepRelAt_maskedJointRetained
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q : Nat)
    (state : AdaptiveRevealProbe.State Coordinate)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache) :
    NativeStepRelAt parameter table state q (maskedJointRetained adversary parameter q)
      (outerCappedNativeRetained adversary parameter (fun index tree leaf => table (index, tree, leaf)) q)
      context fuel history cache ftsCache := by
  unfold maskedJointRetained outerCappedNativeRetained
  apply nativeStepRelAt_bind_probeFree parameter table state q _ _ _ _ context fuel history cache ftsCache
    (liftNativeBlock_probeFree _ context fuel history cache)
  · exact NativeStepCoupledAt.relTriple (projectNativeStepCache_liftNativeBlock parameter table state q ftsCache _
      (cacheMapCommutes_native_maskedPublishedTreeRoot parameter table ftsCache) context fuel history cache hclean)
  · intro finalState entry finalCache hresult
    obtain ⟨hstate, hsynced', _⟩ := invariants_liftNativeBlock parameter table state finalState q
      OtsProbeSimulation.maskedPublishedTreeRoot (cacheMapCommutes_native_maskedPublishedTreeRoot parameter table)
      context fuel history cache ftsCache finalCache (some entry) hsynced hresult
    apply nativeStepRelAt_maskedJointComputation parameter entry.value.1 table _ finalState q
      entry.context entry.remaining entry.history entry.value.2 finalCache _ (by simpa [hstate] using hclean) hsynced'
    rw [isQueryBoundP_map_iff]
    exact OtsProbeSimulation.capOuterHashQueries_hashBound _ q

end SphincsSecurity.Concrete.FtsProbeSimulation
