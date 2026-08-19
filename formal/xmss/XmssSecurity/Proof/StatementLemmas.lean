import XmssSecurity.Statement

/-!
Rewrite lemmas restating the sealed statement definitions, so proofs can unfold them without unsealing.
-/

open OracleComp OracleSpec

namespace XmssSecurity.Concrete

attribute [local semireducible] treeNode CacheReplay.treeNode sampleSecret signingRandomness

noncomputable local instance : SampleableType (Epoch → ChainIndex → Digest) :=
  SampleableType.ofFintype (Epoch → ChainIndex → Digest)

noncomputable local instance : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

@[simp]
theorem treeNode_zero_eq {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (node : MerkleNode) :
    treeNode (m := m) parameter secret 0 node =
      leafAt (m := m) parameter secret node := rfl

theorem treeNode_succ_eq {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (levels : Nat) (node : MerkleNode) :
    treeNode (m := m) parameter secret (levels + 1) node = (do
      let left ← treeNode (m := m) parameter secret levels (childNode node false)
      let right ← treeNode (m := m) parameter secret levels (childNode node true)
      if hlevel : levels < treeHeight then
        nodeHash (m := m) parameter ⟨levels, hlevel⟩ node left right
      else
        pure 0) := rfl

theorem sampleSecret_eq : sampleSecret = $ᵗ (Epoch → ChainIndex → Digest) := rfl

theorem signingRandomness_eq : signingRandomness = $ᵗ Randomness := rfl

namespace CacheReplay

@[simp]
theorem treeNode_zero_eq (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (node : MerkleNode) :
    treeNode cache parameter secret 0 node = leafAt cache parameter secret node := by
  with_unfolding_all rfl

theorem treeNode_succ_eq (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (levels : Nat) (node : MerkleNode) :
    treeNode cache parameter secret (levels + 1) node =
      if hlevel : levels < treeHeight then
        CacheView.merkleHash cache parameter ⟨levels, hlevel⟩ node
          (treeNode cache parameter secret levels (Concrete.childNode node false))
          (treeNode cache parameter secret levels (Concrete.childNode node true))
      else
        0 := by
  with_unfolding_all rfl

end CacheReplay

end XmssSecurity.Concrete
