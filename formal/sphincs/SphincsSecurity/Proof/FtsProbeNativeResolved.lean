import SphincsSecurity.Proof.OtsProbeResolvedOrdinaryHash

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def NativeResolvedCoupled (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (masked : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α)
    (ordinary : OracleComp HashSpec α) : Prop :=
  ∀ (context : OtsProbeSimulation.DeferredContext) (otsFuel : Nat) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput)
      (otsCache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache),
    OtsProbeSimulation.ordinaryQueryCache otsCache = mergedCache parameter table ftsCache →
      (fun result => (projectDetailedCache parameter table result).bind
        (OtsProbeSimulation.ordinaryResolvedResult context otsFuel otsTable otsCache)) <$>
          AdaptiveRevealProbe.runDetailed table state ftsFuel (masked.run ftsCache) =
      OtsProbeSimulation.runResolvedFromTable context otsFuel otsTable
        ((simulateQ OtsProbeSimulation.ordinaryHashImpl ordinary).run otsCache)

theorem Coupled.nativeResolved
    {parameter : PublicParameter} {table : Coordinate → Digest}
    {state : AdaptiveRevealProbe.State Coordinate} {fuel : Nat}
    {masked : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α}
    {ordinary : OracleComp HashSpec α}
    (h : Coupled parameter table state fuel masked (simulateQ (randomOracle : QueryImpl HashSpec _) ordinary)) :
    NativeResolvedCoupled parameter table state fuel masked ordinary := by
  intro context otsFuel otsTable otsCache ftsCache hcache
  rw [OtsProbeSimulation.runResolved_simulateQ_ordinaryHashImpl, hcache]
  have hm := congrArg (fun computation =>
    (fun result => result.bind (OtsProbeSimulation.ordinaryResolvedResult context otsFuel otsTable otsCache)) <$> computation) (h ftsCache)
  simpa only [Functor.map_map, Function.comp_def, Option.bind_some] using hm

theorem nativeResolvedCoupled_hiddenFtsLeafHash
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) (coordinate : Coordinate)
    (hclean : AdaptiveRevealProbe.tableHits state table = false) :
    NativeResolvedCoupled parameter table state fuel (hiddenFtsLeafHash parameter coordinate)
      (ftsLeafHash parameter coordinate.1 coordinate.2.1 coordinate.2.2 (table coordinate)) :=
  (coupled_hiddenFtsLeafHash parameter table state fuel coordinate hclean).nativeResolved

theorem nativeResolvedCoupled_maskedFtsNode
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (index : Index) (tree : FtsTree) (level nodeIdx : Nat)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hlevel : level ≤ ftsTreeHeight)
    (hnodeIdx : 2 ^ level * (nodeIdx + 1) ≤ 2 ^ ftsTreeHeight) :
    NativeResolvedCoupled parameter table state fuel (maskedFtsNode parameter index tree level nodeIdx)
      (ftsNode parameter index tree (fun leafIdx => table (index, tree, leafIdx)) level nodeIdx) :=
  (coupled_maskedFtsNode parameter table state fuel index tree level nodeIdx hclean hlevel hnodeIdx).nativeResolved

theorem nativeResolvedCoupled_maskedFtsKey
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) (index : Index)
    (hclean : AdaptiveRevealProbe.tableHits state table = false) :
    NativeResolvedCoupled parameter table state fuel (maskedFtsKey parameter index)
      (ftsKey parameter index (fun tree leafIdx => table (index, tree, leafIdx))) :=
  (coupled_maskedFtsKey parameter table state fuel index hclean).nativeResolved

theorem nativeResolvedCoupled_maskedFtsOpen
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) (index : Index)
    (leaves : DigestTree → FtsLeaf)
    (hclean : AdaptiveRevealProbe.tableHits state table = false) :
    NativeResolvedCoupled parameter table state fuel (maskedFtsOpen parameter index leaves)
      (ftsOpen parameter index leaves (fun tree leafIdx => table (index, tree, leafIdx))) :=
  (coupled_maskedFtsOpen parameter table state fuel index leaves hclean).nativeResolved

end SphincsSecurity.Concrete.FtsProbeSimulation
