import SphincsSecurity.Proof.OtsProbePublicationBody
import SphincsSecurity.Proof.OtsProbeHistorySupport
import SphincsSecurity.Proof.OtsProbePublicCacheSupport

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem ordinaryCacheSupport_publishSignatureBody
    (randomness : Randomness) (index : Index)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) (layers : Layer → Option ChronologicalLayerPart) :
    OrdinaryCacheSupport (publishSignatureBody randomness index ftsPath layers) := by
  unfold publishSignatureBody
  cases traverseOption layers with
  | none => exact OrdinaryCacheSupport.pure none
  | some parts =>
      exact (ordinaryCacheSupport_sequenceFin _ fun lay =>
        ordinaryCacheSupport_revealLayerValues index lay (parts lay).encoding).bind fun _ =>
          OrdinaryCacheSupport.pure _

theorem publishSignatureBody_probeFree
    (randomness : Randomness) (index : Index)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) (layers : Layer → Option ChronologicalLayerPart) :
    ProbeFree (publishSignatureBody randomness index ftsPath layers) := by
  unfold publishSignatureBody
  cases traverseOption layers with
  | none => exact ProbeFree.pure none
  | some parts =>
      exact (sequenceFin_probeFree _ fun lay =>
        revealLayerValues_probeFree index lay (parts lay).encoding).bind fun _ =>
          ProbeFree.pure _

theorem historyPrefix_publishSignatureBody_ordinaryCache
    (randomness : Randomness) (index : Index)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) (layers : Layer → Option ChronologicalLayerPart)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (cache : SplitHashCache)
    (result : HistoryResolvedPrefix (Option PublishedSignatureBody × SplitHashCache))
    (hresult : some result ∈ support (runResolvedHistoryPrefix
      (eraseProbeQueries ((publishSignatureBody randomness index ftsPath layers).run cache)) context fuel history)) :
    ordinaryQueryCache result.value.2 = ordinaryQueryCache cache := by
  rw [eraseProbeQueries_eq_of_probeFree _ (publishSignatureBody_probeFree randomness index ftsPath layers cache)] at hresult
  exact ordinaryCacheSupport_publishSignatureBody randomness index ftsPath layers cache result.value
    (mem_support_of_historyPrefix _ context fuel history result hresult)

end SphincsSecurity.Concrete.OtsProbeSimulation
