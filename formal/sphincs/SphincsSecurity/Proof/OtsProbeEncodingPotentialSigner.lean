import SphincsSecurity.Proof.OtsProbeCachePotentialProjection
import SphincsSecurity.Proof.OtsProbeEncodingExhaustion

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] ResolvedCachePotentialBound
set_option backward.isDefEq.respectTransparency false

theorem resolvedCachePotentialBound_maskedOtsSignFrom_encoding
    (inputs : Finset HashInput) (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest) (attempts counter : Nat) :
    ResolvedCachePotentialBound (encodingCachePotential inputs)
      (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter) := by
  induction attempts generalizing counter with
  | zero => exact ResolvedCachePotentialBound.pure _ _
  | succ attempts ih =>
      unfold maskedOtsSignFrom
      apply (resolvedCachePotentialBound_ordinaryHash_encoding inputs _).bind
      intro selected
      cases selected with
      | none => exact ih (counter + 1)
      | some encoding =>
          apply (resolvedCachePotentialBound_sequenceFin (encodingCachePotential inputs) _ fun chainIdx =>
            resolvedCachePotentialBound_ensureChainPrefix (encodingExhaustionPotential inputs) lay tree leafIdx chainIdx (encoding chainIdx)).bind
          intro _
          exact ResolvedCachePotentialBound.pure _ _

theorem resolvedCachePotentialBound_maskedOtsSign_encoding
    (inputs : Finset HashInput) (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    ResolvedCachePotentialBound (encodingCachePotential inputs) (maskedOtsSign parameter lay tree leafIdx message) :=
  resolvedCachePotentialBound_maskedOtsSignFrom_encoding inputs parameter lay tree leafIdx message _ _

theorem resolvedCachePotentialBound_maskedOtsLayerAfterMessage_encoding
    (inputs : Finset HashInput) (parameter : PublicParameter) (index : Index) (lay : Layer) (message : Digest) :
    ResolvedCachePotentialBound (encodingCachePotential inputs) (maskedOtsLayerAfterMessage parameter index lay message) := by
  unfold maskedOtsLayerAfterMessage
  apply (resolvedCachePotentialBound_maskedOtsSign_encoding inputs parameter lay _ _ message).bind
  intro selected
  cases selected with
  | none => exact ResolvedCachePotentialBound.pure _ _
  | some selected =>
      exact (resolvedCachePotentialBound_ensureTreePath (encodingExhaustionPotential inputs) lay _ _).bind
        fun _ => ResolvedCachePotentialBound.pure _ _

theorem resolvedCachePotentialBound_chronologicalLayer_encoding
    (inputs : Finset HashInput) (parameter : PublicParameter) (index : Index) (lay : Layer) (message : Digest) :
    ResolvedCachePotentialBound (encodingCachePotential inputs) (maskedChronologicalLayerAfterMessage parameter index lay message) := by
  unfold maskedChronologicalLayerAfterMessage
  apply (resolvedCachePotentialBound_maskedOtsLayerAfterMessage_encoding inputs parameter index lay message).bind
  intro selected
  cases selected with
  | none => exact ResolvedCachePotentialBound.pure _ _
  | some selected =>
      exact (resolvedCachePotentialBound_revealPrivateLayerValues (encodingExhaustionPotential inputs) index lay selected.2).bind
        fun _ => ResolvedCachePotentialBound.pure _ _

theorem resolvedCachePotentialBound_upperLayers_encoding
    (inputs : Finset HashInput) (parameter : PublicParameter) (index : Index) :
    ResolvedCachePotentialBound (encodingCachePotential inputs) (maskedUpperChronologicalLayers parameter index) := by
  apply resolvedCachePotentialBound_sequenceFin
  intro lay
  unfold maskedUpperChronologicalLayer
  exact (resolvedCachePotentialBound_maskedTreeRoot (encodingExhaustionPotential inputs) _ _).bind
    (resolvedCachePotentialBound_chronologicalLayer_encoding inputs parameter index _)

theorem resolvedCachePotentialBound_publishSignatureBody_encoding
    (inputs : Finset HashInput) (randomness : Randomness) (index : Index)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) (layers : Layer → Option ChronologicalLayerPart) :
    ResolvedCachePotentialBound (encodingCachePotential inputs) (publishSignatureBody randomness index ftsPath layers) :=
  resolvedCachePotentialBound_of_ordinary_projection (encodingExhaustionPotential inputs) _
    (fun ordinary => cacheMapCommutes_publishSignatureBody _ (replaceOrdinaryCache_commutesWithHiddenUpdates ordinary)
      randomness index ftsPath layers)

theorem resolvedCachePotentialBound_publishedTreeRoot_encoding (inputs : Finset HashInput) :
    ResolvedCachePotentialBound (encodingCachePotential inputs) maskedPublishedTreeRoot := by
  apply resolvedCachePotentialBound_of_ordinary_projection (encodingExhaustionPotential inputs)
  intro ordinary
  unfold maskedPublishedTreeRoot
  exact (cacheMapCommutes_ensureTreeNode _ _ _ _ _).bind fun _ =>
    cacheMapCommutes_revealPublishedCoordinate _ (replaceOrdinaryCache_commutesWithHiddenUpdates ordinary) _

theorem probEvent_resolved_chronologicalLayer_encodingExhaustion_le_inv216
    (parameter : PublicParameter) (index : Index) (lay : Layer) (message : Digest)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    Pr[ResolvedAnyEncodingInputsExhausted | runResolvedFromTable context fuel table
      ((maskedChronologicalLayerAfterMessage parameter index lay message).run emptySplitHashCache)] ≤
      ((2 ^ 216 : Nat) : ENNReal)⁻¹ :=
  probEvent_resolved_anyEncodingInputsExhausted_le_inv216 _
    (fun _ _ _ => resolvedCachePotentialBound_chronologicalLayer_encoding _ parameter index lay message) context fuel table

end SphincsSecurity.Concrete.OtsProbeSimulation
