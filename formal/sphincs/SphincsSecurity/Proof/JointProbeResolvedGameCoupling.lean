import SphincsSecurity.Proof.JointProbeResolvedExecution
import SphincsSecurity.Proof.JointProbeResolvedRetained

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] OtsProbeSimulation.maskedPublishedTreeRoot

theorem jointResolvedCoupledAt_retained
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q : Nat)
    (state : AdaptiveRevealProbe.State Coordinate)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false) (hsynced : RevealedSynced parameter table state cache.2) :
    JointResolvedCoupledAt parameter table state q (jointSourceRetained adversary parameter q)
      (outerCappedNativeRetained adversary parameter (fun index tree leaf => table (index, tree, leaf)) q)
      context fuel otsTable cache := by
  unfold jointSourceRetained outerCappedNativeRetained
  apply jointResolvedCoupledAt_bind_probeFree parameter table state q _ _ _ _ context fuel otsTable cache
    (runJointResolved_nativeBlock_probeFree _ context fuel otsTable cache)
  · exact jointResolvedCoupledAt_nativeBlock parameter table state q _
      (cacheMapCommutes_native_maskedPublishedTreeRoot parameter table) context fuel otsTable cache hclean
  · intro finalState entry hresult
    obtain ⟨hstate, hsynced', _⟩ := invariants_jointSourceNativeBlock parameter table state finalState q _
      (cacheMapCommutes_native_maskedPublishedTreeRoot parameter table) context fuel otsTable cache entry hsynced hresult
    apply jointResolvedCoupledAt_computation parameter entry.value.1 table _ finalState q
      entry.context entry.remaining entry.table entry.value.2 _ (by simpa [hstate] using hclean) hsynced'
    rw [isQueryBoundP_map_iff]
    exact OtsProbeSimulation.capOuterHashQueries_hashBound _ q

theorem relTriple_jointResolvedRetainedDetailed
    (adversary : Adversary) (parameter : PublicParameter)
    (otsTable : OtsSecretIndex → HashOutput) (table : Coordinate → Digest) (q fuel : Nat) :
    RelTriple (jointResolvedRetainedDetailed adversary parameter otsTable table q fuel)
      (OtsProbeSimulation.runResolvedFromTable (OtsProbeSimulation.ensuredInitialContext ∅) fuel otsTable
        ((outerCappedNativeRetained adversary parameter (fun index tree leaf => table (index, tree, leaf)) q).run
          OtsProbeSimulation.emptySplitHashCache)) (JointResolvedCleanRel parameter table) := by
  have h := jointResolvedCoupledAt_retained adversary parameter table q AdaptiveRevealProbe.State.empty
    (OtsProbeSimulation.ensuredInitialContext ∅) fuel otsTable (OtsProbeSimulation.emptySplitHashCache, emptySplitHashCache)
    (by simp [AdaptiveRevealProbe.tableHits, AdaptiveRevealProbe.State.empty]) (revealedSynced_empty parameter table)
  have hcache : OtsProbeSimulation.replaceOrdinaryCache OtsProbeSimulation.emptySplitHashCache ∅ =
      OtsProbeSimulation.emptySplitHashCache := by
    funext key
    cases key <;> rfl
  simpa only [JointResolvedCoupledAt, jointResolvedRetainedDetailed, mergedCache_empty, hcache] using h

theorem cleanJointResolved_eq_none_of_hit
    (result : AdaptiveRevealProbe.DetailedResult Coordinate (Option (ResolvedRunResult α))) (hhit : result.hit = true) :
    cleanJointResolved result = none := by
  cases result with
  | stopped hit => rfl
  | done hit state entry => cases hit <;> simp_all [AdaptiveRevealProbe.DetailedResult.hit, cleanJointResolved]

theorem projectJointResolvedCache_eq_none_iff
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (result : AdaptiveRevealProbe.DetailedResult Coordinate (Option (ResolvedRunResult (α × JointSourceCache)))) :
    projectJointResolvedCache parameter table result = none ↔ cleanJointResolved result = none := by
  unfold projectJointResolvedCache
  exact Option.map_eq_none_iff

theorem probEvent_outerCappedNative_none_le_jointResolved
    (adversary : Adversary) (parameter : PublicParameter)
    (otsTable : OtsSecretIndex → HashOutput) (table : Coordinate → Digest) (q fuel : Nat) :
    Pr[fun result => result = none |
      OtsProbeSimulation.runResolvedFromTable (OtsProbeSimulation.ensuredInitialContext ∅) fuel otsTable
        ((outerCappedNativeRetained adversary parameter (fun index tree leaf => table (index, tree, leaf)) q).run
          OtsProbeSimulation.emptySplitHashCache)] ≤
      Pr[fun result => cleanJointResolved result = none | jointResolvedRetainedDetailed adversary parameter otsTable table q fuel] := by
  apply probEvent_le_of_relTriple (relTriple_symm (relTriple_jointResolvedRetainedDetailed adversary parameter otsTable table q fuel))
  intro native joint hrel hnone
  rcases hrel with hhit | heq
  · exact cleanJointResolved_eq_none_of_hit joint hhit
  · exact (projectJointResolvedCache_eq_none_iff parameter table joint).mp (heq.trans hnone)

end SphincsSecurity.Concrete.FtsProbeSimulation
