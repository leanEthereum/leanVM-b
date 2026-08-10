import XmssSecurity.ConcreteVerify
import VCVio.OracleComp.Constructions.SampleableType

open OracleComp OracleSpec

namespace XmssSecurity.Concrete

noncomputable local instance : SampleableType PublicParameter :=
  SampleableType.ofFintype PublicParameter

noncomputable local instance : SampleableType (Epoch → ChainIndex → Digest) :=
  SampleableType.ofFintype (Epoch → ChainIndex → Digest)

def oneTimePublicKey {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) : m (ChainIndex → Digest) :=
  sequenceFin fun chain =>
    chainWalk parameter epoch chain 0 (chainLength - 1) (secret epoch chain)

def leafAt {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) : m Digest := do
  let endpoints ← oneTimePublicKey parameter secret epoch
  leafHash parameter epoch endpoints

def merkleNodeOfNat (value : Nat) : MerkleNode :=
  ⟨value % lifetime,
    Nat.mod_lt _ (by simp [lifetime])⟩

def childNode (node : MerkleNode) (right : Bool) : MerkleNode :=
  merkleNodeOfNat (2 * node.val + if right then 1 else 0)

def treeNode {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    Nat → MerkleNode → m Digest
  | 0, node => leafAt parameter secret node
  | levels + 1, node => do
      let left ← treeNode parameter secret levels (childNode node false)
      let right ← treeNode parameter secret levels (childNode node true)
      if hlevel : levels < treeHeight then
        nodeHash parameter ⟨levels, hlevel⟩ node left right
      else
        pure 0

def rootNode : MerkleNode :=
  ⟨0, by simp [lifetime]⟩

noncomputable def keygen : OracleComp OracleWorld (PublicKey × SecretKey) := do
  let parameter ← liftM ($ᵗ PublicParameter)
  let secret ← liftM ($ᵗ (Epoch → ChainIndex → Digest))
  let root ← treeNode parameter secret treeHeight rootNode
  return (⟨root, parameter⟩, ⟨parameter, secret⟩)

attribute [irreducible] keygen

end XmssSecurity.Concrete
