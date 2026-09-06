import SphincsSecurity.Proof.HonestSettlingTrace
import SphincsSecurity.Proof.FtsProbeGame
import SphincsSecurity.Proof.EncodingCharge

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

attribute [local irreducible] instFintypePosition

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (f : QueryImpl HashSpec Id)

theorem settlingRun_treePath (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    SettlingRun parameter otsSecret ftsSecret f
      (treePath parameter lay tree (otsSecret lay tree) leafIdx) := by
  apply SettlingRun.sequenceFin
  intro level
  split_ifs with hlevel
  · apply settlingRun_treeNode parameter otsSecret ftsSecret f lay tree _ _ (by omega)
    exact FtsProbeSimulation.sibling_node_bound maxLayerHeight leafIdx.val level.val level.isLt leafIdx.isLt
  · exact SettlingRun.pure _

theorem settlingRun_ftsOpen (index : Index) (leaves : DigestTree → FtsLeaf) :
    SettlingRun parameter otsSecret ftsSecret f
      (ftsOpen parameter index leaves (ftsSecret index)) := by
  apply SettlingRun.sequenceFin
  intro tree
  apply SettlingRun.sequenceFin
  intro level
  apply settlingRun_ftsNode parameter otsSecret ftsSecret f index tree _ _ (by omega)
  exact FtsProbeSimulation.sibling_node_bound ftsTreeHeight _ level.val level.isLt (leaves (ftsIndexOf tree)).isLt

theorem settlingRun_encode (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (counter : Counter) :
    SettlingRun parameter otsSecret ftsSecret f (encode parameter lay tree leafIdx message counter) := by
  apply SettlingTrace.of_no_position
  intro input hinput position
  simp only [encode, queriedInputs_bind, queriedInputs_tweakableHash, queriedInputs_pure,
    List.append_nil, List.mem_singleton] at hinput
  subst input
  exact (show AtEncodingPosition parameter
      (tweakableHashInput parameter (.encoding lay tree leafIdx) (digestBytes message ++ counterBytes counter))
      ⟨lay, tree, leafIdx⟩ from ⟨_, rfl⟩).not_atPosition position

theorem settlingRun_otsSignFrom (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (attempts counter : Nat) :
    SettlingRun parameter otsSecret ftsSecret f
      (otsSignFrom parameter lay tree leafIdx (otsSecret lay tree leafIdx) message attempts counter) := by
  induction attempts generalizing counter with
  | zero => exact SettlingRun.pure _
  | succ attempts ih =>
      rw [otsSignFrom]
      apply (settlingRun_encode parameter otsSecret ftsSecret f lay tree leafIdx message _).bind
      split
      · apply SettlingRun.bind
        · apply SettlingRun.sequenceFin
          intro chainIdx
          exact settlingRun_chainWalk parameter otsSecret ftsSecret f lay tree leafIdx chainIdx _
        · exact SettlingRun.pure _
      · exact ih _

theorem settlingRun_layerMessage (secretKey : SecretKey) (index : Index) (lay : Layer) :
    SettlingRun secretKey.parameter secretKey.otsSecret secretKey.ftsSecret f (layerMessage secretKey index lay) := by
  unfold layerMessage
  split_ifs
  · exact settlingRun_treeRoot secretKey.parameter secretKey.otsSecret secretKey.ftsSecret f _ _
  · exact settlingRun_ftsKey secretKey.parameter secretKey.otsSecret secretKey.ftsSecret f index

theorem settlingRun_signLayer (secretKey : SecretKey) (index : Index) (lay : Layer) :
    SettlingRun secretKey.parameter secretKey.otsSecret secretKey.ftsSecret f (signLayer secretKey index lay) := by
  unfold signLayer
  apply (settlingRun_layerMessage f secretKey index lay).bind
  apply (settlingRun_otsSignFrom secretKey.parameter secretKey.otsSecret secretKey.ftsSecret f lay
    (treeIndexAt index lay) (leafIndexAt index lay) _ _ _).bind
  split
  · exact SettlingRun.pure _
  · exact (settlingRun_treePath secretKey.parameter secretKey.otsSecret secretKey.ftsSecret f lay
      (treeIndexAt index lay) (leafIndexAt index lay)).bind (SettlingRun.pure _)

theorem settlingRun_signAfterDigest (secretKey : SecretKey) (randomness : Randomness)
    (index : Index) (leaves : DigestTree → FtsLeaf) :
    SettlingRun secretKey.parameter secretKey.otsSecret secretKey.ftsSecret f
      (signAfterDigest secretKey randomness index leaves) := by
  rw [signAfterDigest]
  apply (settlingRun_ftsOpen secretKey.parameter secretKey.otsSecret secretKey.ftsSecret f index leaves).bind
  apply SettlingRun.bind
  · apply SettlingRun.sequenceFin
    intro lay
    exact settlingRun_signLayer f secretKey index lay
  · split <;> exact SettlingRun.pure _

end SphincsSecurity.Concrete
