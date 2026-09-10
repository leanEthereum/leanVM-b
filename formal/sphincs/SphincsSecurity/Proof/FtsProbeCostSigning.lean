import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FtsProbeCostActions
import SphincsSecurity.Proof.FtsProbeCostReveal

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

theorem probeCostInvariant_maskedFtsNode (parameter : PublicParameter) (index : Index)
    (tree : FtsTree) (level nodeIdx : Nat) (hlevel : level ≤ ftsTreeHeight)
    (hnodeIdx : 2 ^ level * (nodeIdx + 1) ≤ 2 ^ ftsTreeHeight) :
    ProbeCostInvariant parameter (maskedFtsNode parameter index tree level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero => exact probeCostInvariant_hiddenFtsLeafHash parameter (index, tree, ftsLeafOfNat nodeIdx)
  | succ level ih =>
      rw [maskedFtsNode]
      have hlevelChild : level ≤ ftsTreeHeight := by omega
      have hleftNode : 2 ^ level * (2 * nodeIdx + 1) ≤ 2 ^ ftsTreeHeight := by
        rw [pow_succ] at hnodeIdx
        nlinarith [Nat.two_pow_pos level]
      have hrightNode : 2 ^ level * (2 * nodeIdx + 1 + 1) ≤ 2 ^ ftsTreeHeight := by
        rw [pow_succ] at hnodeIdx
        nlinarith [Nat.two_pow_pos level]
      have hlevelSmall : level + 1 < 2 ^ 32 := by
        norm_num [ftsTreeHeight] at hlevel ⊢
        omega
      have hnodeSmall : nodeIdx < 2 ^ 32 := by
        norm_num [ftsTreeHeight] at hnodeIdx ⊢
        nlinarith [Nat.two_pow_pos (level + 1)]
      exact (ih (2 * nodeIdx) hlevelChild hleftNode).bind fun left =>
        (ih (2 * nodeIdx + 1) hlevelChild hrightNode).bind fun right =>
          probeCostInvariant_ordinaryTweakableHash parameter
            (.ftsNode index tree (level + 1) nodeIdx) (nodePayload left right) fun table =>
              isOrdinaryInput_ftsNode parameter table index tree (level + 1) nodeIdx
                (nodePayload left right) hlevelSmall hnodeSmall

theorem probeCostInvariant_maskedFtsKey (parameter : PublicParameter) (index : Index) :
    ProbeCostInvariant parameter (maskedFtsKey parameter index) := by
  unfold maskedFtsKey
  apply (probeCostInvariant_sequenceFin parameter _ fun tree =>
    probeCostInvariant_maskedFtsNode parameter index tree ftsTreeHeight 0 le_rfl (by simp)).bind
  intro roots
  exact probeCostInvariant_ordinaryTweakableHash parameter (.ftsRoots index) (ftsRootsPayload roots)
    fun table => isOrdinaryInput_ftsRoots parameter table index (ftsRootsPayload roots)

theorem probeCostInvariant_maskedFtsOpen (parameter : PublicParameter) (index : Index)
    (leaves : DigestTree → FtsLeaf) :
    ProbeCostInvariant parameter (maskedFtsOpen parameter index leaves) := by
  unfold maskedFtsOpen
  apply probeCostInvariant_sequenceFin
  intro tree
  apply probeCostInvariant_sequenceFin
  intro level
  exact probeCostInvariant_maskedFtsNode parameter index tree level.val _ level.isLt.le
    (ftsOpen_node_bound (leaves (ftsIndexOf tree)) level)

theorem probeCostInvariant_maskedLayerMessage (secretKey : SecretKey) (index : Index) (lay : Layer) :
    ProbeCostInvariant secretKey.parameter (maskedLayerMessage secretKey index lay) := by
  unfold maskedLayerMessage
  split
  · exact probeCostInvariant_simulateQ_ordinaryHashImpl secretKey.parameter _ fun table =>
      ordinaryOnly_treeRoot secretKey.parameter table _ _ _
  · exact probeCostInvariant_maskedFtsKey secretKey.parameter index

theorem probeCostInvariant_maskedSignLayer (secretKey : SecretKey) (index : Index) (lay : Layer) :
    ProbeCostInvariant secretKey.parameter (maskedSignLayer secretKey index lay) := by
  unfold maskedSignLayer
  apply (probeCostInvariant_maskedLayerMessage secretKey index lay).bind
  intro message
  apply (probeCostInvariant_simulateQ_ordinaryHashImpl secretKey.parameter _ fun table =>
    ordinaryOnly_otsSign secretKey.parameter table lay (treeIndexAt index lay)
      (leafIndexAt index lay) (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay)) message).bind
  intro result
  cases result with
  | none => exact ProbeCostInvariant.pure secretKey.parameter none
  | some result =>
      obtain ⟨counter, values⟩ := result
      apply (probeCostInvariant_simulateQ_ordinaryHashImpl secretKey.parameter _ fun table =>
        ordinaryOnly_treePath secretKey.parameter table lay (treeIndexAt index lay)
          (secretKey.otsSecret lay (treeIndexAt index lay)) (leafIndexAt index lay)
          (leafIndexAt_lt index lay)).bind
      intro path
      exact ProbeCostInvariant.pure secretKey.parameter (some (counter, values, path))

theorem probeCostInvariant_revealSelectedFtsSecrets (parameter : PublicParameter) (index : Index)
    (leaves : DigestTree → FtsLeaf) :
    ProbeCostInvariant parameter (revealSelectedFtsSecrets parameter index leaves) := by
  exact probeCostInvariant_sequenceFin parameter _ fun tree =>
    probeCostInvariant_revealFtsSecret parameter (index, tree, leaves (ftsIndexOf tree))

theorem probeCostInvariant_maskedSignAfterDigest (secretKey : SecretKey) (randomness : Randomness)
    (index : Index) (leaves : DigestTree → FtsLeaf) :
    ProbeCostInvariant secretKey.parameter (maskedSignAfterDigest secretKey randomness index leaves) := by
  unfold maskedSignAfterDigest
  apply (probeCostInvariant_maskedFtsOpen secretKey.parameter index leaves).bind
  intro ftsPath
  apply (probeCostInvariant_sequenceFin secretKey.parameter _ fun lay =>
    probeCostInvariant_maskedSignLayer secretKey index lay).bind
  intro layers
  cases traverseOption layers with
  | none => exact ProbeCostInvariant.pure secretKey.parameter none
  | some parts =>
      apply (probeCostInvariant_revealSelectedFtsSecrets secretKey.parameter index leaves).bind
      intro selected
      exact ProbeCostInvariant.pure secretKey.parameter _

theorem probeCostInvariant_maskedSignWithView (secretKey : SecretKey) (message : Message) :
    ProbeCostInvariant secretKey.parameter (maskedSignWithView secretKey message) := by
  unfold maskedSignWithView
  apply (probeCostInvariant_simulateQ_splitRomImpl secretKey.parameter _ fun table =>
    romOrdinaryOnly_signDigestLoop digestAttemptLimit secretKey table message).bind
  intro result
  cases result with
  | none => exact ProbeCostInvariant.pure secretKey.parameter (none, none)
  | some result =>
      obtain ⟨randomness, index, leaves⟩ := result
      exact (probeCostInvariant_maskedSignAfterDigest secretKey randomness index leaves).bind fun signature =>
        ProbeCostInvariant.pure secretKey.parameter (signature, some (selectedFewTimeView index leaves))

theorem probeCostInvariant_maskedSigningImpl (secretKey : SecretKey) (request : SigningSpec.Domain) :
    ProbeCostInvariant secretKey.parameter (maskedSigningImpl secretKey request) :=
  (probeCostInvariant_maskedSignWithView secretKey request).map Prod.fst

end SphincsSecurity.Concrete.FtsProbeSimulation
