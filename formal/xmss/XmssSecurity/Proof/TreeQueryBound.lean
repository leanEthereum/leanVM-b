import XmssSecurity.Proof.ConcreteQueryBound
import XmssSecurity.Proof.StatementLemmas

open OracleComp OracleSpec

namespace XmssSecurity

def TreeCovers (levels : Nat) (node : MerkleNode) (epoch : Epoch) : Prop :=
  node.val * 2 ^ levels ≤ epoch.val ∧ epoch.val < (node.val + 1) * 2 ^ levels

def TreeSubtreeValid (levels : Nat) (node : MerkleNode) : Prop :=
  (node.val + 1) * 2 ^ levels ≤ lifetime

instance (levels : Nat) (node : MerkleNode) (epoch : Epoch) :
    Decidable (TreeCovers levels node epoch) := by
  unfold TreeCovers
  infer_instance

theorem childNode_val_of_subtreeValid_succ (levels : Nat) (node : MerkleNode)
    (right : Bool) (hvalid : TreeSubtreeValid (levels + 1) node) :
    (Concrete.childNode node right).val = 2 * node.val + if right then 1 else 0 := by
  rw [Concrete.childNode, Concrete.merkleNodeOfNat]
  apply Nat.mod_eq_of_lt
  unfold TreeSubtreeValid at hvalid
  rw [pow_succ] at hvalid
  have hpow : 0 < 2 ^ levels := pow_pos (by omega) _
  split <;> nlinarith

theorem childNode_subtreeValid (levels : Nat) (node : MerkleNode)
    (right : Bool) (hvalid : TreeSubtreeValid (levels + 1) node) :
    TreeSubtreeValid levels (Concrete.childNode node right) := by
  unfold TreeSubtreeValid
  rw [childNode_val_of_subtreeValid_succ levels node right hvalid]
  unfold TreeSubtreeValid at hvalid
  rw [pow_succ] at hvalid
  have hpow : 0 < 2 ^ levels := pow_pos (by omega) _
  split <;> nlinarith

theorem treeCovers_children_sum (levels : Nat) (node : MerkleNode) (epoch : Epoch)
    (hvalid : TreeSubtreeValid (levels + 1) node) :
    (if TreeCovers levels (Concrete.childNode node false) epoch then 1 else 0) +
        (if TreeCovers levels (Concrete.childNode node true) epoch then 1 else 0) =
      if TreeCovers (levels + 1) node epoch then 1 else 0 := by
  by_cases hleft : TreeCovers levels (Concrete.childNode node false) epoch
  <;> by_cases hright : TreeCovers levels (Concrete.childNode node true) epoch
  <;> by_cases hparent : TreeCovers (levels + 1) node epoch
  <;> simp only [hleft, hright, hparent, ↓reduceIte]
  all_goals
    unfold TreeCovers at hleft hright hparent
    simp only [childNode_val_of_subtreeValid_succ levels node false hvalid,
      childNode_val_of_subtreeValid_succ levels node true hvalid,
      Bool.false_eq_true, ↓reduceIte] at hleft hright
    rw [pow_succ] at hparent
    have hpow : 0 < 2 ^ levels := pow_pos (by omega) _
    ring_nf at hleft hright hparent
    omega

theorem Concrete.treeNode_queryBound_leafAddress
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (targetEpoch : Epoch) (levels : Nat) (node : MerkleNode)
    (hlevels : levels ≤ treeHeight) (hvalid : TreeSubtreeValid levels node) :
    (Concrete.treeNode parameter secret levels node :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.leaf targetEpoch))
        (if TreeCovers levels node targetEpoch then 1 else 0) := by
  induction levels generalizing node with
  | zero =>
      rw [Concrete.treeNode_zero_eq]
      by_cases hcover : TreeCovers 0 node targetEpoch
      · have heq : node = targetEpoch := by
          apply Fin.ext
          unfold TreeCovers at hcover
          simp only [pow_zero, mul_one] at hcover
          omega
        subst targetEpoch
        simpa [hcover] using
          Concrete.leafAt_queryBound_leafAddress parameter secret node node
      · have hne : node ≠ targetEpoch := by
          intro heq
          subst targetEpoch
          apply hcover
          unfold TreeCovers
          simp
        simpa [hcover] using
          Concrete.leafAt_queryBound_zero_at_other_leaf parameter secret node
            targetEpoch hne
  | succ levels ih =>
      have hlevel : levels < treeHeight := Nat.lt_of_succ_le hlevels
      have hleftValid := childNode_subtreeValid levels node false hvalid
      have hrightValid := childNode_subtreeValid levels node true hvalid
      have hleft := ih (Concrete.childNode node false)
        (Nat.le_of_succ_le hlevels) hleftValid
      have hright := ih (Concrete.childNode node true)
        (Nat.le_of_succ_le hlevels) hrightValid
      rw [Concrete.treeNode_succ_eq]
      have hcontinuation (left : Digest) :
          (do
            let right ← Concrete.treeNode parameter secret levels
              (Concrete.childNode node true)
            Concrete.nodeHash parameter ⟨levels, hlevel⟩ node left right :
            OracleComp HashSpec Digest).IsQueryBoundP
              (AtHashAddress parameter (.leaf targetEpoch))
              (if TreeCovers levels (Concrete.childNode node true) targetEpoch then 1 else 0) := by
        refine OracleComp.isQueryBoundP_bind (m := 0) hright ?_
        intro right _
        exact Concrete.tweakableHash_queryBound_atOtherAddress parameter
          (.leaf targetEpoch) (.merkle ⟨levels, hlevel⟩ node)
          (Concrete.nodePayload left right) (by simp)
      have hall := OracleComp.isQueryBoundP_bind hleft
        (fun left _ => hcontinuation left)
      simpa only [hlevel, ↓reduceDIte, Nat.add_zero,
        treeCovers_children_sum levels node targetEpoch hvalid] using hall

theorem Concrete.rootTree_queryBound_leafAddress
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (targetEpoch : Epoch) :
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.leaf targetEpoch)) 1 := by
  have hbound := Concrete.treeNode_queryBound_leafAddress parameter secret targetEpoch
    treeHeight Concrete.rootNode le_rfl (by
      unfold TreeSubtreeValid Concrete.rootNode lifetime
      norm_num)
  have hcover : TreeCovers treeHeight Concrete.rootNode targetEpoch := by
    unfold TreeCovers Concrete.rootNode
    constructor
    · simp
    · simp [lifetime]
  simpa [hcover] using hbound

/-- A supported root-tree execution from an empty cache contains at most one input at each leaf address. -/
theorem Concrete.CacheReplay.rootTree_cache_unique_leafAddress
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (root : Digest) (cache : QueryCache HashSpec)
    (hmem : (root, cache) ∈ support
      ((simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run ∅))
    (targetEpoch : Epoch) (left right : HashInput)
    (leftOutput rightOutput : HashOutput)
    (hleftP : AtHashAddress parameter (.leaf targetEpoch) left)
    (hrightP : AtHashAddress parameter (.leaf targetEpoch) right)
    (hleft : cache left = some leftOutput)
    (hright : cache right = some rightOutput) :
    left = right := by
  exact Concrete.CacheReplay.cache_unique_of_query_bound_one
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest)
    (AtHashAddress parameter (.leaf targetEpoch)) ∅ cache root
    (Concrete.rootTree_queryBound_leafAddress parameter secret targetEpoch)
    (by simp) hmem left right leftOutput rightOutput hleftP hrightP hleft hright

theorem Concrete.treeNode_queryBound_chainAddress
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (targetEpoch : Epoch) (targetChain : ChainIndex) (targetStep : ChainStep)
    (levels : Nat) (node : MerkleNode)
    (hlevels : levels ≤ treeHeight) (hvalid : TreeSubtreeValid levels node) :
    (Concrete.treeNode parameter secret levels node :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.chain targetEpoch targetChain targetStep))
        (if TreeCovers levels node targetEpoch then 1 else 0) := by
  induction levels generalizing node with
  | zero =>
      rw [Concrete.treeNode_zero_eq]
      by_cases hcover : TreeCovers 0 node targetEpoch
      · have heq : node = targetEpoch := by
          apply Fin.ext
          unfold TreeCovers at hcover
          simp only [pow_zero, mul_one] at hcover
          omega
        subst targetEpoch
        simpa [hcover] using
          Concrete.leafAt_queryBound_chainAddress parameter secret node node
            targetChain targetStep
      · have hne : node ≠ targetEpoch := by
          intro heq
          subst targetEpoch
          apply hcover
          unfold TreeCovers
          simp
        simpa [hcover] using
          Concrete.leafAt_queryBound_zero_chainAddress_at_other_epoch parameter secret node
            targetEpoch targetChain targetStep hne
  | succ levels ih =>
      have hlevel : levels < treeHeight := Nat.lt_of_succ_le hlevels
      have hleftValid := childNode_subtreeValid levels node false hvalid
      have hrightValid := childNode_subtreeValid levels node true hvalid
      have hleft := ih (Concrete.childNode node false)
        (Nat.le_of_succ_le hlevels) hleftValid
      have hright := ih (Concrete.childNode node true)
        (Nat.le_of_succ_le hlevels) hrightValid
      rw [Concrete.treeNode_succ_eq]
      have hcontinuation (left : Digest) :
          (do
            let right ← Concrete.treeNode parameter secret levels
              (Concrete.childNode node true)
            Concrete.nodeHash parameter ⟨levels, hlevel⟩ node left right :
            OracleComp HashSpec Digest).IsQueryBoundP
              (AtHashAddress parameter (.chain targetEpoch targetChain targetStep))
              (if TreeCovers levels (Concrete.childNode node true) targetEpoch then 1 else 0) := by
        refine OracleComp.isQueryBoundP_bind (m := 0) hright ?_
        intro right _
        exact Concrete.tweakableHash_queryBound_atOtherAddress parameter
          (.chain targetEpoch targetChain targetStep) (.merkle ⟨levels, hlevel⟩ node)
          (Concrete.nodePayload left right) (by simp)
      have hall := OracleComp.isQueryBoundP_bind hleft
        (fun left _ => hcontinuation left)
      simpa only [hlevel, ↓reduceDIte, Nat.add_zero,
        treeCovers_children_sum levels node targetEpoch hvalid] using hall

theorem Concrete.rootTree_queryBound_chainAddress
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (targetEpoch : Epoch) (targetChain : ChainIndex) (targetStep : ChainStep) :
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.chain targetEpoch targetChain targetStep)) 1 := by
  have hbound := Concrete.treeNode_queryBound_chainAddress parameter secret targetEpoch
    targetChain targetStep treeHeight Concrete.rootNode le_rfl (by
      unfold TreeSubtreeValid Concrete.rootNode lifetime
      norm_num)
  have hcover : TreeCovers treeHeight Concrete.rootNode targetEpoch := by
    unfold TreeCovers Concrete.rootNode
    constructor
    · simp
    · simp [lifetime]
  simpa [hcover] using hbound

/-- A supported root-tree execution from an empty cache contains at most one input at each chain-step address. -/
theorem Concrete.CacheReplay.rootTree_cache_unique_chainAddress
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (root : Digest) (cache : QueryCache HashSpec)
    (hmem : (root, cache) ∈ support
      ((simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run ∅))
    (targetEpoch : Epoch) (targetChain : ChainIndex) (targetStep : ChainStep)
    (left right : HashInput) (leftOutput rightOutput : HashOutput)
    (hleftP : AtHashAddress parameter (.chain targetEpoch targetChain targetStep) left)
    (hrightP : AtHashAddress parameter (.chain targetEpoch targetChain targetStep) right)
    (hleft : cache left = some leftOutput)
    (hright : cache right = some rightOutput) :
    left = right := by
  exact Concrete.CacheReplay.cache_unique_of_query_bound_one
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest)
    (AtHashAddress parameter (.chain targetEpoch targetChain targetStep)) ∅ cache root
    (Concrete.rootTree_queryBound_chainAddress parameter secret targetEpoch
      targetChain targetStep)
    (by simp) hmem left right leftOutput rightOutput hleftP hrightP hleft hright

end XmssSecurity
