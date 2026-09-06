import SphincsSecurity.Proof.OtsProbeNativePublicationCache

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem replaceOrdinaryCache_update_hidden
    (cache : SplitHashCache) (ordinary : QueryCache HashSpec) (coordinate : Coordinate) (output : HashOutput) :
    replaceOrdinaryCache (Function.update cache (.hidden coordinate) (some output)) ordinary =
      Function.update (replaceOrdinaryCache cache ordinary) (.hidden coordinate) (some output) := by
  funext key
  cases key with
  | ordinary input => simp [replaceOrdinaryCache, Function.update]
  | hidden other => simp [replaceOrdinaryCache, Function.update]

def OrdinaryCacheIndependent
    (computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ cache ordinary, computation.run (replaceOrdinaryCache cache ordinary) =
    (fun result => (result.1, replaceOrdinaryCache result.2 ordinary)) <$> computation.run cache

theorem OrdinaryCacheIndependent.pure (value : α) :
    OrdinaryCacheIndependent (pure value : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α) := by
  intro cache ordinary
  simp [StateT.run_pure]

theorem OrdinaryCacheIndependent.bind
    {left : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hleft : OrdinaryCacheIndependent left)
    (hnext : ∀ value, OrdinaryCacheIndependent (next value)) :
    OrdinaryCacheIndependent (left >>= next) := by
  intro cache ordinary
  rw [StateT.run_bind, hleft, bind_map_left, StateT.run_bind, map_bind]
  apply bind_congr
  intro result
  exact hnext result.1 result.2 ordinary

theorem ordinaryCacheIndependent_sequenceFin {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (hcomponent : ∀ index, OrdinaryCacheIndependent (computation index)) :
    OrdinaryCacheIndependent (sequenceFin computation) := by
  induction n with
  | zero =>
      simpa [sequenceFin] using OrdinaryCacheIndependent.pure Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomponent 0).bind fun head =>
        (ih (fun index : Fin n => computation index.succ)
          (fun index => hcomponent index.succ)).bind fun tail =>
            OrdinaryCacheIndependent.pure
              (Fin.cases head tail : Fin (n + 1) → alpha)

theorem ordinaryCacheIndependent_revealCoordinate (coordinate : Coordinate) :
    OrdinaryCacheIndependent (revealCoordinate coordinate) := by
  intro cache ordinary
  rw [revealCoordinate_run, revealCoordinate_run, map_bind]
  apply bind_congr
  intro output
  simp only [map_pure, replaceOrdinaryCache_update_hidden]

theorem ordinaryCacheIndependent_publishCoordinate (coordinate : Coordinate) :
    OrdinaryCacheIndependent (publishCoordinate coordinate) := by
  intro cache ordinary
  simp only [publishCoordinate, StateT.run_liftM, map_bind, map_pure]

theorem ordinaryCacheIndependent_revealPublishedCoordinate
    (coordinate : Coordinate) :
    OrdinaryCacheIndependent (revealPublishedCoordinate coordinate) := by
  unfold revealPublishedCoordinate
  exact (ordinaryCacheIndependent_revealCoordinate coordinate).bind fun _ =>
    (ordinaryCacheIndependent_publishCoordinate coordinate).bind fun _ =>
      OrdinaryCacheIndependent.pure _

theorem ordinaryCacheIndependent_revealLayerValues
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit) :
    OrdinaryCacheIndependent (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  exact (ordinaryCacheIndependent_sequenceFin _ fun chainIdx =>
    ordinaryCacheIndependent_revealPublishedCoordinate
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay)
        chainIdx (encoding chainIdx))).bind fun _ =>
      (ordinaryCacheIndependent_sequenceFin _ fun level => by
        split
        · cases hlevelValue : level.val with
          | zero => exact ordinaryCacheIndependent_revealPublishedCoordinate _
          | succ current =>
              rw [show current + 1 = Nat.succ current by omega]
              change OrdinaryCacheIndependent
                (if hlevel : current < maxLayerHeight then
                  revealPublishedCoordinate (.position (.node lay (treeIndexAt index lay)
                    ⟨current, hlevel⟩ (leafOfNat
                      (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
                else pure 0)
              by_cases hlevel : current < maxLayerHeight
              · rw [dif_pos hlevel]
                exact ordinaryCacheIndependent_revealPublishedCoordinate _
              · rw [dif_neg hlevel]
                exact OrdinaryCacheIndependent.pure 0
        · exact OrdinaryCacheIndependent.pure 0).bind fun _ =>
          OrdinaryCacheIndependent.pure _

theorem ordinaryCacheIndependent_publishSignatureBody
    (randomness : Randomness) (index : Index)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) (layers : Layer → Option ChronologicalLayerPart) :
    OrdinaryCacheIndependent (publishSignatureBody randomness index ftsPath layers) := by
  unfold publishSignatureBody
  cases traverseOption layers with
  | none => exact OrdinaryCacheIndependent.pure none
  | some parts =>
      exact (ordinaryCacheIndependent_sequenceFin _ fun lay =>
        ordinaryCacheIndependent_revealLayerValues index lay (parts lay).encoding).bind fun _ =>
          OrdinaryCacheIndependent.pure _

def replaceHistoryOrdinaryCache (ordinary : QueryCache HashSpec)
    (entry : HistoryResolvedPrefix (α × SplitHashCache)) : HistoryResolvedPrefix (α × SplitHashCache) :=
  { entry with value := (entry.value.1, replaceOrdinaryCache entry.value.2 ordinary) }

theorem OrdinaryCacheIndependent.historyPrefix
    {computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α}
    (h : OrdinaryCacheIndependent computation)
    (context : DeferredContext) (fuel : Nat) (history : List Probe)
    (cache : SplitHashCache) (ordinary : QueryCache HashSpec) :
    runResolvedHistoryPrefix (eraseProbeQueries (computation.run (replaceOrdinaryCache cache ordinary))) context fuel history =
      Option.map (replaceHistoryOrdinaryCache ordinary) <$>
        runResolvedHistoryPrefix (eraseProbeQueries (computation.run cache)) context fuel history := by
  rw [h, eraseProbeQueries_map, runResolvedHistoryPrefix_map]
  rfl

theorem completePublicationEntry_replaceHistoryOrdinaryCache
    (selected : FtsTree → Digest) (ordinary : QueryCache HashSpec)
    (entry : HistoryResolvedPrefix (Option PublishedSignatureBody × SplitHashCache)) :
    completePublicationEntry selected (replaceHistoryOrdinaryCache ordinary entry) =
      replaceHistoryOrdinaryCache ordinary (completePublicationEntry selected entry) := rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
