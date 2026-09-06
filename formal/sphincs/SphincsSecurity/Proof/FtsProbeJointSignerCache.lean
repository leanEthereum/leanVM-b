import SphincsSecurity.Proof.FtsProbeJointSignerRandomness
import SphincsSecurity.Proof.OtsProbeNativeCacheMonotone

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] OtsProbeSimulation.maskedPublishedChronologicalSignAfterDigest

theorem mergedCache_le_maskedJointSignAfterDigest
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache)
    (entry : OtsProbeSimulation.HistoryResolvedPrefix (Option Signature × OtsProbeSimulation.SplitHashCache))
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache)
    (hresult : .done false finalState (some entry, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((maskedJointSignAfterDigest parameter randomness index leaves context fuel history cache).run ftsCache))) :
    mergedCache parameter table ftsCache ≤ mergedCache parameter table finalCache := by
  have hnative := (coupled_maskedJointSignAfterDigest parameter table randomness index leaves state ftsFuel
    context fuel history cache ftsCache hclean hsynced).mem_support_native hresult
  rw [OtsProbeSimulation.eraseProbeQueries_eq_of_probeFree _
    (OtsProbeSimulation.maskedPublishedChronologicalSignAfterDigest_probeFree parameter
      (fun index tree leaf => table (index, tree, leaf)) randomness index leaves _)] at hnative
  have hraw := OtsProbeSimulation.mem_support_of_historyPrefix _ context fuel history _ hnative
  exact OtsProbeSimulation.ordinaryCacheMonotoneSupport_maskedPublishedChronologicalSignAfterDigest parameter
    (fun index tree leaf => table (index, tree, leaf)) randomness index leaves _ _ hraw

end SphincsSecurity.Concrete.FtsProbeSimulation
