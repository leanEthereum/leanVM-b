import SphincsSecurity.Proof.OtsProbePublicationCacheTransport

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000

noncomputable def maskedChronologicalLayerAfterMessage
    (parameter : PublicParameter) (index : Index) (lay : Layer) (message : Digest) :
    StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) (Option ChronologicalLayerPart) := do
  match ← maskedOtsLayerAfterMessage parameter index lay message with
  | none => pure none
  | some (counter, encoding) => do
      let values ← revealPrivateLayerValues index lay encoding
      pure (some ⟨counter, encoding, values.1, values.2⟩)

theorem maskedChronologicalSignLayer_eq_afterMessage
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) :
    maskedChronologicalSignLayer parameter ftsSecret index lay =
      (maskedLayerMessage parameter ftsSecret index lay >>= maskedChronologicalLayerAfterMessage parameter index lay) := by
  unfold maskedChronologicalSignLayer maskedSignLayer maskedChronologicalLayerAfterMessage maskedOtsLayerAfterMessage
  simp only [bind_assoc]
  apply bind_congr
  intro message
  apply bind_congr
  intro selected
  cases selected with
  | none => simp
  | some selected => rcases selected with ⟨counter, encoding⟩; simp

noncomputable def maskedUpperChronologicalLayer
    (parameter : PublicParameter) (index : Index) (lay : Fin (numLayers - 1)) :
    StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) (Option ChronologicalLayerPart) := do
  let current : Layer := ⟨lay.val, by have := lay.isLt; norm_num [numLayers] at *; omega⟩
  let below : Layer := ⟨lay.val + 1, by have := lay.isLt; norm_num [numLayers] at *; omega⟩
  let message ← maskedTreeRoot below (treeIndexAt index below)
  maskedChronologicalLayerAfterMessage parameter index current message

noncomputable def maskedUpperChronologicalLayers (parameter : PublicParameter) (index : Index) :
    StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))
      (Fin (numLayers - 1) → Option ChronologicalLayerPart) :=
  sequenceFin (maskedUpperChronologicalLayer parameter index)

theorem maskedChronologicalSignLayers_eq_ftsBoundary
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) :
    maskedChronologicalSignLayers parameter ftsSecret index = (do
      let upper ← maskedUpperChronologicalLayers parameter index
      let root ← simulateQ ordinaryHashImpl (ftsKey parameter index (ftsSecret index))
      let bottom ← maskedChronologicalLayerAfterMessage parameter index bottomLayer root
      pure (Fin.snoc upper bottom)) := by
  unfold maskedChronologicalSignLayers maskedUpperChronologicalLayers
  simp only [numLayers, sequenceFin, bind_assoc, pure_bind]
  simp only [maskedChronologicalSignLayer_eq_afterMessage, maskedLayerMessage, numLayers, bottomLayer,
    Fin.val_zero, Fin.val_succ, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, ↓reduceDIte,
    maskedUpperChronologicalLayer, bind_assoc]
  apply bind_congr
  intro firstMessage
  apply bind_congr
  intro first
  apply bind_congr
  intro secondMessage
  apply bind_congr
  intro second
  apply bind_congr
  intro root
  apply bind_congr
  intro bottom
  congr 1
  funext lay
  fin_cases lay <;> rfl

theorem maskedPublishedChronologicalSignAfterDigest_eq_ftsBoundary
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    maskedPublishedChronologicalSignAfterDigest parameter ftsSecret randomness index leaves = (do
      let ftsPath ← simulateQ ordinaryHashImpl (ftsOpen parameter index leaves (ftsSecret index))
      let upper ← maskedUpperChronologicalLayers parameter index
      let root ← simulateQ ordinaryHashImpl (ftsKey parameter index (ftsSecret index))
      let bottom ← maskedChronologicalLayerAfterMessage parameter index bottomLayer root
      publishChronologicalSignature ftsSecret randomness index leaves ftsPath (Fin.snoc upper bottom)) := by
  unfold maskedPublishedChronologicalSignAfterDigest
  rw [maskedChronologicalSignLayers_eq_ftsBoundary]
  simp only [bind_assoc, pure_bind]

end SphincsSecurity.Concrete.OtsProbeSimulation
