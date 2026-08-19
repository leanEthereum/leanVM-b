import XmssSecurity.Statement.ConcreteKeygen
import VCVio.OracleComp.Constructions.SampleableType

open OracleComp OracleSpec

namespace XmssSecurity.Concrete

noncomputable local instance : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

noncomputable def signingRandomness : ProbComp Randomness :=
  $ᵗ Randomness

theorem signingRandomness_eq : signingRandomness = $ᵗ Randomness := rfl

attribute [irreducible] signingRandomness

def authenticationPathNode (epoch : Epoch) (level : MerkleLevel) : MerkleNode :=
  merkleNodeOfNat (Nat.xor (epoch.val / 2 ^ level.val) 1)

end XmssSecurity.Concrete
