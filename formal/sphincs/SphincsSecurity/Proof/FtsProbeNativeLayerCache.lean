import SphincsSecurity.Proof.FtsProbeNativeCache
import SphincsSecurity.Proof.OtsProbeCacheMapActions

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem nativeCacheProjection_commutesWithHiddenUpdates
    (parameter : PublicParameter) (table : Coordinate → Digest) (ftsCache : SplitHashCache) :
    OtsProbeSimulation.CommutesWithHiddenUpdates (nativeCacheProjection parameter table ftsCache) :=
  nativeCacheProjection_update_hidden parameter table ftsCache

theorem cacheMapCommutes_native_maskedOtsSignFrom
    (parameter : PublicParameter) (table : Coordinate → Digest) (ftsCache : SplitHashCache)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) (attempts counter : Nat) :
    OtsProbeSimulation.CacheMapCommutes (nativeCacheProjection parameter table ftsCache)
      (OtsProbeSimulation.maskedOtsSignFrom parameter lay tree leafIdx message attempts counter) := by
  induction attempts generalizing counter with
  | zero => exact OtsProbeSimulation.CacheMapCommutes.pure _ none
  | succ attempts ih =>
      unfold OtsProbeSimulation.maskedOtsSignFrom
      apply (cacheMapCommutes_native_simulateQ_ordinaryHash parameter table ftsCache
        (encode parameter lay tree leafIdx message (BitVec.ofNat counterBits counter))
        (ordinaryOnly_encode parameter table lay tree leafIdx message (BitVec.ofNat counterBits counter))).bind
      intro encoded
      cases encoded with
      | none => exact ih (counter + 1)
      | some encoding =>
          apply (OtsProbeSimulation.cacheMapCommutes_sequenceFin _ _ fun chainIdx =>
            OtsProbeSimulation.cacheMapCommutes_ensureChainPrefix _ lay tree leafIdx chainIdx (encoding chainIdx)).bind
          intro _
          exact OtsProbeSimulation.CacheMapCommutes.pure _ _

theorem cacheMapCommutes_native_maskedOtsLayerAfterMessage
    (parameter : PublicParameter) (table : Coordinate → Digest) (ftsCache : SplitHashCache)
    (index : Index) (lay : Layer) (message : Digest) :
    OtsProbeSimulation.CacheMapCommutes (nativeCacheProjection parameter table ftsCache)
      (OtsProbeSimulation.maskedOtsLayerAfterMessage parameter index lay message) := by
  unfold OtsProbeSimulation.maskedOtsLayerAfterMessage OtsProbeSimulation.maskedOtsSign
  apply (cacheMapCommutes_native_maskedOtsSignFrom parameter table ftsCache lay
    (treeIndexAt index lay) (leafIndexAt index lay) message encodingAttemptLimit 0).bind
  intro result
  cases result with
  | none => exact OtsProbeSimulation.CacheMapCommutes.pure _ none
  | some result =>
      rcases result with ⟨counter, encoding⟩
      exact (OtsProbeSimulation.cacheMapCommutes_ensureTreePath _ lay (treeIndexAt index lay) (leafIndexAt index lay)).bind
        fun _ => OtsProbeSimulation.CacheMapCommutes.pure _ (some (counter, encoding))

theorem cacheMapCommutes_native_maskedChronologicalLayerAfterMessage
    (parameter : PublicParameter) (table : Coordinate → Digest) (ftsCache : SplitHashCache)
    (index : Index) (lay : Layer) (message : Digest) :
    OtsProbeSimulation.CacheMapCommutes (nativeCacheProjection parameter table ftsCache)
      (OtsProbeSimulation.maskedChronologicalLayerAfterMessage parameter index lay message) := by
  unfold OtsProbeSimulation.maskedChronologicalLayerAfterMessage
  apply (cacheMapCommutes_native_maskedOtsLayerAfterMessage parameter table ftsCache index lay message).bind
  intro result
  cases result with
  | none => exact OtsProbeSimulation.CacheMapCommutes.pure _ none
  | some result =>
      rcases result with ⟨counter, encoding⟩
      exact (OtsProbeSimulation.cacheMapCommutes_revealPrivateLayerValues _
        (nativeCacheProjection_commutesWithHiddenUpdates parameter table ftsCache) index lay encoding).bind
        fun _ => OtsProbeSimulation.CacheMapCommutes.pure _ _

theorem cacheMapCommutes_native_maskedUpperChronologicalLayer
    (parameter : PublicParameter) (table : Coordinate → Digest) (ftsCache : SplitHashCache)
    (index : Index) (lay : Fin (numLayers - 1)) :
    OtsProbeSimulation.CacheMapCommutes (nativeCacheProjection parameter table ftsCache)
      (OtsProbeSimulation.maskedUpperChronologicalLayer parameter index lay) := by
  unfold OtsProbeSimulation.maskedUpperChronologicalLayer
  apply (OtsProbeSimulation.cacheMapCommutes_maskedTreeRoot _
    (nativeCacheProjection_commutesWithHiddenUpdates parameter table ftsCache) _ _).bind
  intro message
  exact cacheMapCommutes_native_maskedChronologicalLayerAfterMessage parameter table ftsCache index _ message

theorem cacheMapCommutes_native_maskedUpperChronologicalLayers
    (parameter : PublicParameter) (table : Coordinate → Digest) (ftsCache : SplitHashCache) (index : Index) :
    OtsProbeSimulation.CacheMapCommutes (nativeCacheProjection parameter table ftsCache)
      (OtsProbeSimulation.maskedUpperChronologicalLayers parameter index) := by
  unfold OtsProbeSimulation.maskedUpperChronologicalLayers
  exact OtsProbeSimulation.cacheMapCommutes_sequenceFin _ _ fun lay =>
    cacheMapCommutes_native_maskedUpperChronologicalLayer parameter table ftsCache index lay

theorem historyPrefix_native_maskedChronologicalLayerAfterMessage
    (parameter : PublicParameter) (table : Coordinate → Digest) (ftsCache : SplitHashCache)
    (index : Index) (lay : Layer) (message : Digest) (context : OtsProbeSimulation.DeferredContext)
    (fuel : Nat) (history : List OtsProbeSimulation.Probe) (cache : OtsProbeSimulation.SplitHashCache) :
    OtsProbeSimulation.runResolvedHistoryPrefix
      (OtsProbeSimulation.eraseProbeQueries
        ((OtsProbeSimulation.maskedChronologicalLayerAfterMessage parameter index lay message).run
          (nativeCacheProjection parameter table ftsCache cache))) context fuel history =
      Option.map (fun entry => { entry with value :=
        (entry.value.1, nativeCacheProjection parameter table ftsCache entry.value.2) }) <$>
        OtsProbeSimulation.runResolvedHistoryPrefix
          (OtsProbeSimulation.eraseProbeQueries
            ((OtsProbeSimulation.maskedChronologicalLayerAfterMessage parameter index lay message).run cache)) context fuel history :=
  (cacheMapCommutes_native_maskedChronologicalLayerAfterMessage parameter table ftsCache index lay message).historyPrefix context fuel history cache

end SphincsSecurity.Concrete.FtsProbeSimulation
