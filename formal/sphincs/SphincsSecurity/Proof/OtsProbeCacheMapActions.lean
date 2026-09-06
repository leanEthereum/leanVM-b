import SphincsSecurity.Proof.OtsProbeCacheMap

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem cacheMapCommutes_ensureCoordinate (rewrite : SplitHashCache → SplitHashCache) (coordinate : Coordinate) :
    CacheMapCommutes rewrite (ensureCoordinate coordinate) := by
  unfold ensureCoordinate
  exact CacheMapCommutes.liftM rewrite _

theorem cacheMapCommutes_ensureFullChain (rewrite : SplitHashCache → SplitHashCache)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    CacheMapCommutes rewrite (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  exact (cacheMapCommutes_sequenceFin rewrite _ fun _ => cacheMapCommutes_ensureCoordinate rewrite _).bind fun _ =>
    CacheMapCommutes.pure rewrite ()

theorem cacheMapCommutes_ensureChainPrefix (rewrite : SplitHashCache → SplitHashCache)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) (digit : Digit) :
    CacheMapCommutes rewrite (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  unfold ensureChainPrefix
  apply (cacheMapCommutes_sequenceFin rewrite _ fun step => by
    split
    · exact cacheMapCommutes_ensureCoordinate rewrite _
    · exact CacheMapCommutes.pure rewrite ()).bind
  intro _
  exact CacheMapCommutes.pure rewrite ()

theorem cacheMapCommutes_ensureOtsLeaf (rewrite : SplitHashCache → SplitHashCache)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    CacheMapCommutes rewrite (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  exact (cacheMapCommutes_sequenceFin rewrite _ fun chainIdx =>
    cacheMapCommutes_ensureFullChain rewrite lay tree leafIdx chainIdx).bind fun _ =>
      cacheMapCommutes_ensureCoordinate rewrite _

theorem cacheMapCommutes_ensureTreeNode (rewrite : SplitHashCache → SplitHashCache)
    (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat) :
    CacheMapCommutes rewrite (ensureTreeNode lay tree level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero => exact cacheMapCommutes_ensureOtsLeaf rewrite lay tree (leafOfNat nodeIdx)
  | succ level ih =>
      unfold ensureTreeNode
      apply (ih (2 * nodeIdx)).bind
      intro _
      apply (ih (2 * nodeIdx + 1)).bind
      intro _
      split
      · exact cacheMapCommutes_ensureCoordinate rewrite _
      · exact CacheMapCommutes.pure rewrite ()

theorem cacheMapCommutes_ensureTreePath (rewrite : SplitHashCache → SplitHashCache)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    CacheMapCommutes rewrite (ensureTreePath lay tree leafIdx) := by
  unfold ensureTreePath
  apply (cacheMapCommutes_sequenceFin rewrite _ fun level => by
    split
    · exact cacheMapCommutes_ensureTreeNode rewrite lay tree _ _
    · exact CacheMapCommutes.pure rewrite ()).bind
  intro _
  exact CacheMapCommutes.pure rewrite ()

def CommutesWithHiddenUpdates (rewrite : SplitHashCache → SplitHashCache) : Prop :=
  ∀ cache coordinate output, rewrite (Function.update cache (.hidden coordinate) (some output)) =
    Function.update (rewrite cache) (.hidden coordinate) (some output)

theorem cacheMapCommutes_revealCoordinate (rewrite : SplitHashCache → SplitHashCache)
    (hhidden : CommutesWithHiddenUpdates rewrite) (coordinate : Coordinate) :
    CacheMapCommutes rewrite (revealCoordinate coordinate) := by
  intro cache
  rw [revealCoordinate_run, revealCoordinate_run, map_bind]
  apply bind_congr
  intro output
  simp only [map_pure, hhidden cache coordinate output]

theorem cacheMapCommutes_maskedTreeRoot (rewrite : SplitHashCache → SplitHashCache)
    (hhidden : CommutesWithHiddenUpdates rewrite) (lay : Layer) (tree : TreeIndex) :
    CacheMapCommutes rewrite (maskedTreeRoot lay tree) := by
  unfold maskedTreeRoot maskedTreeNode
  apply (cacheMapCommutes_ensureTreeNode rewrite lay tree _ _).bind
  intro _
  cases layerHeight lay with
  | zero => exact cacheMapCommutes_revealCoordinate rewrite hhidden _
  | succ current =>
      simp only
      split
      · exact cacheMapCommutes_revealCoordinate rewrite hhidden _
      · exact CacheMapCommutes.pure rewrite 0

theorem cacheMapCommutes_revealPrivateLayerValues (rewrite : SplitHashCache → SplitHashCache)
    (hhidden : CommutesWithHiddenUpdates rewrite) (index : Index) (lay : Layer) (encoding : ChainIndex → Digit) :
    CacheMapCommutes rewrite (revealPrivateLayerValues index lay encoding) := by
  unfold revealPrivateLayerValues
  apply (cacheMapCommutes_sequenceFin rewrite _ fun _ => cacheMapCommutes_revealCoordinate rewrite hhidden _).bind
  intro values
  apply (cacheMapCommutes_sequenceFin rewrite _ fun level => by
    split
    · cases hlevel : level.val with
      | zero => exact cacheMapCommutes_revealCoordinate rewrite hhidden _
      | succ current =>
          simp only
          split
          · exact cacheMapCommutes_revealCoordinate rewrite hhidden _
          · exact CacheMapCommutes.pure rewrite 0
    · exact CacheMapCommutes.pure rewrite 0).bind
  intro path
  exact CacheMapCommutes.pure rewrite (values, path)

theorem CacheMapCommutes.historyPrefix
    {rewrite : SplitHashCache → SplitHashCache}
    {computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α}
    (h : CacheMapCommutes rewrite computation)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (cache : SplitHashCache) :
    runResolvedHistoryPrefix (eraseProbeQueries (computation.run (rewrite cache))) context fuel history =
      Option.map (fun (entry : HistoryResolvedPrefix (α × SplitHashCache)) =>
        { entry with value := (entry.value.1, rewrite entry.value.2) }) <$>
        runResolvedHistoryPrefix (eraseProbeQueries (computation.run cache)) context fuel history := by
  rw [h, eraseProbeQueries_map, runResolvedHistoryPrefix_map]

end SphincsSecurity.Concrete.OtsProbeSimulation
