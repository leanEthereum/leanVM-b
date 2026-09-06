import SphincsSecurity.Proof.OtsProbeCacheMapActions

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem CacheMapCommutes.modify (rewrite update : SplitHashCache → SplitHashCache)
    (hupdate : ∀ cache, rewrite (update cache) = update (rewrite cache)) :
    CacheMapCommutes rewrite (modify update : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) Unit) := by
  intro cache
  simp only [StateT.run_modify, map_pure, hupdate]

theorem cacheMapCommutes_revealCoordinateOutput (rewrite : SplitHashCache → SplitHashCache)
    (hhidden : CommutesWithHiddenUpdates rewrite) (coordinate : Coordinate) :
    CacheMapCommutes rewrite (revealCoordinateOutput coordinate) := by
  unfold revealCoordinateOutput
  apply (CacheMapCommutes.liftM rewrite _).bind
  intro output
  exact (CacheMapCommutes.modify rewrite _ (fun cache => hhidden cache coordinate output)).bind
    fun _ => CacheMapCommutes.pure rewrite output

theorem cacheMapCommutes_peekCoordinate (rewrite : SplitHashCache → SplitHashCache) (coordinate : Coordinate) :
    CacheMapCommutes rewrite (peekCoordinate coordinate) := by
  unfold peekCoordinate
  exact (CacheMapCommutes.liftM rewrite _).bind fun output => CacheMapCommutes.pure rewrite _

theorem cacheMapCommutes_peekPositionValues (rewrite : SplitHashCache → SplitHashCache) (positions : List Position) :
    CacheMapCommutes rewrite (peekPositionValues positions) := by
  induction positions with
  | nil => exact CacheMapCommutes.pure rewrite _
  | cons position remaining ih =>
      unfold peekPositionValues
      apply (cacheMapCommutes_peekCoordinate rewrite _).bind
      intro value
      cases value with
      | none => exact CacheMapCommutes.pure rewrite _
      | some value =>
          apply ih.bind
          intro values
          cases values <;> exact CacheMapCommutes.pure rewrite _

theorem cacheMapCommutes_peekTableInput (rewrite : SplitHashCache → SplitHashCache)
    (parameter : PublicParameter) (coordinate : Coordinate) :
    CacheMapCommutes rewrite (peekTableInput parameter coordinate) := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx => exact CacheMapCommutes.pure rewrite _
  | position position =>
      cases position <;> simp only [peekTableInput]
      case chain lay tree leafIdx chainIdx step =>
        split
        · apply (cacheMapCommutes_peekCoordinate rewrite _).bind
          intro value
          cases value <;> exact CacheMapCommutes.pure rewrite _
        · apply (cacheMapCommutes_peekPositionValues rewrite _).bind
          intro values
          cases values <;> exact CacheMapCommutes.pure rewrite _
      all_goals
        apply (cacheMapCommutes_peekPositionValues rewrite _).bind
        intro values
        cases values <;> exact CacheMapCommutes.pure rewrite _

theorem cacheMapCommutes_probe (rewrite : SplitHashCache → SplitHashCache) (candidate : Probe) :
    CacheMapCommutes rewrite (probe candidate) := CacheMapCommutes.liftM rewrite _

theorem cacheMapCommutes_probeFirstMissingInputCoordinate
    (rewrite : SplitHashCache → SplitHashCache) (input : HashInput) (slot : Nat) (coordinates : List Coordinate) :
    CacheMapCommutes rewrite (probeFirstMissingInputCoordinate input slot coordinates) := by
  induction coordinates generalizing slot with
  | nil => exact CacheMapCommutes.pure rewrite ()
  | cons coordinate remaining ih =>
      unfold probeFirstMissingInputCoordinate
      apply (cacheMapCommutes_peekCoordinate rewrite coordinate).bind
      intro value
      cases value with
      | none => exact cacheMapCommutes_probe rewrite _
      | some value => exact ih (slot + 1)

theorem cacheMapCommutes_prepareLeafInputProbe (rewrite : SplitHashCache → SplitHashCache)
    (input : HashInput) (candidate : Probe) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    CacheMapCommutes rewrite (prepareLeafInputProbe input candidate lay tree leafIdx) := by
  unfold prepareLeafInputProbe
  apply (cacheMapCommutes_peekCoordinate rewrite candidate.coordinate).bind
  intro value
  cases value with
  | none => exact cacheMapCommutes_probe rewrite candidate
  | some value => exact cacheMapCommutes_probeFirstMissingInputCoordinate rewrite input 0 _

theorem cacheMapCommutes_probingHashQuery
    (rewrite : SplitHashCache → SplitHashCache) (parameter : PublicParameter) (input : HashInput)
    (hresolve : ∀ coordinate, CacheMapCommutes rewrite (resolveKnownInput parameter coordinate input))
    (hordinary : CacheMapCommutes rewrite (splitHashQuery (.ordinary input))) :
    CacheMapCommutes rewrite (probingHashQuery parameter input) := by
  unfold probingHashQuery
  cases decodeProbe? parameter input with
  | some candidate =>
      cases decodePosition? parameter input with
      | none => exact (cacheMapCommutes_probe rewrite candidate).bind fun _ => hresolve candidate.outputCoordinate
      | some position =>
          cases position with
          | leaf lay tree leafIdx =>
              exact (cacheMapCommutes_prepareLeafInputProbe rewrite input candidate lay tree leafIdx).bind
                fun _ => hresolve candidate.outputCoordinate
          | chain | node | ftsLeaf | ftsNode | ftsRoots =>
              exact (cacheMapCommutes_probe rewrite candidate).bind fun _ => hresolve candidate.outputCoordinate
  | none =>
      cases decodePosition? parameter input with
      | none => exact hordinary
      | some position =>
          cases position with
          | chain lay tree leafIdx chainIdx step => exact hresolve (.position (.chain lay tree leafIdx chainIdx step))
          | leaf lay tree leafIdx => exact hresolve (.position (.leaf lay tree leafIdx))
          | node lay tree level nodeIdx =>
              exact (cacheMapCommutes_probeFirstMissingInputCoordinate rewrite input 0
                ((Position.node lay tree level nodeIdx).children.map Coordinate.position)).bind
                fun _ => hresolve (.position (.node lay tree level nodeIdx))
          | ftsLeaf | ftsNode | ftsRoots => exact hordinary

end SphincsSecurity.Concrete.OtsProbeSimulation
