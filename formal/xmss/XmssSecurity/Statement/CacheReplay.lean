import XmssSecurity.Statement.ConcreteKeygen
import XmssSecurity.Statement.Wots

open OracleComp OracleSpec

namespace XmssSecurity.Concrete.CacheReplay

def oneTimePublicKey (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (epoch : Epoch) : ChainIndex → Digest :=
  fun chain => Wots.walk (CacheView.chainStep cache parameter epoch chain) 0
    (chainLength - 1) (secret epoch chain)

def leafAt (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (epoch : Epoch) : Digest :=
  CacheView.leafHash cache parameter epoch
    (oneTimePublicKey cache parameter secret epoch)

def treeNode (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) : Nat → MerkleNode → Digest
  | 0, node => leafAt cache parameter secret node
  | levels + 1, node =>
      if hlevel : levels < treeHeight then
        CacheView.merkleHash cache parameter ⟨levels, hlevel⟩ node
          (treeNode cache parameter secret levels (Concrete.childNode node false))
          (treeNode cache parameter secret levels (Concrete.childNode node true))
      else
        0

@[simp]
theorem treeNode_zero_eq (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (node : MerkleNode) :
    treeNode cache parameter secret 0 node = leafAt cache parameter secret node := by
  simp only [treeNode]

theorem treeNode_succ_eq (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (levels : Nat) (node : MerkleNode) :
    treeNode cache parameter secret (levels + 1) node =
      if hlevel : levels < treeHeight then
        CacheView.merkleHash cache parameter ⟨levels, hlevel⟩ node
          (treeNode cache parameter secret levels (Concrete.childNode node false))
          (treeNode cache parameter secret levels (Concrete.childNode node true))
      else
        0 := by
  simp only [treeNode]

attribute [irreducible] treeNode

end XmssSecurity.Concrete.CacheReplay
