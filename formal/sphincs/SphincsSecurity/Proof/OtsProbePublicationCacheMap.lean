import SphincsSecurity.Proof.OtsProbePublicationBody
import SphincsSecurity.Proof.OtsProbeCacheMapActions

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem cacheMapCommutes_revealPublishedCoordinate (rewrite : SplitHashCache → SplitHashCache)
    (hhidden : CommutesWithHiddenUpdates rewrite) (coordinate : Coordinate) :
    CacheMapCommutes rewrite (revealPublishedCoordinate coordinate) := by
  unfold revealPublishedCoordinate publishCoordinate
  exact (cacheMapCommutes_revealCoordinate rewrite hhidden coordinate).bind fun _ =>
    (CacheMapCommutes.liftM rewrite _).bind fun _ => CacheMapCommutes.pure rewrite _

theorem cacheMapCommutes_revealLayerValues (rewrite : SplitHashCache → SplitHashCache)
    (hhidden : CommutesWithHiddenUpdates rewrite)
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit) :
    CacheMapCommutes rewrite (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  apply (cacheMapCommutes_sequenceFin rewrite _ fun _ => cacheMapCommutes_revealPublishedCoordinate rewrite hhidden _).bind
  intro values
  apply (cacheMapCommutes_sequenceFin rewrite _ fun level => by
    split
    · cases hlevel : level.val with
      | zero => exact cacheMapCommutes_revealPublishedCoordinate rewrite hhidden _
      | succ current =>
          simp only
          split
          · exact cacheMapCommutes_revealPublishedCoordinate rewrite hhidden _
          · exact CacheMapCommutes.pure rewrite 0
    · exact CacheMapCommutes.pure rewrite 0).bind
  intro path
  exact CacheMapCommutes.pure rewrite (values, path)

theorem cacheMapCommutes_publishSignatureBody (rewrite : SplitHashCache → SplitHashCache)
    (hhidden : CommutesWithHiddenUpdates rewrite) (randomness : Randomness) (index : Index)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) (layers : Layer → Option ChronologicalLayerPart) :
    CacheMapCommutes rewrite (publishSignatureBody randomness index ftsPath layers) := by
  unfold publishSignatureBody
  cases traverseOption layers with
  | none => exact CacheMapCommutes.pure rewrite none
  | some parts =>
      exact (cacheMapCommutes_sequenceFin rewrite _ fun lay =>
        cacheMapCommutes_revealLayerValues rewrite hhidden index lay (parts lay).encoding).bind fun _ =>
          CacheMapCommutes.pure rewrite _

theorem replaceOrdinaryCache_commutesWithHiddenUpdates (ordinary : QueryCache HashSpec) :
    CommutesWithHiddenUpdates (fun cache => replaceOrdinaryCache cache ordinary) := by
  intro cache coordinate output
  funext key
  cases key <;> simp [replaceOrdinaryCache, Function.update]

end SphincsSecurity.Concrete.OtsProbeSimulation
