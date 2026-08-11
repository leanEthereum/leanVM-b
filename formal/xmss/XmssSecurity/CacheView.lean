import XmssSecurity.ConcreteHash
import XmssSecurity.Execution

open OracleComp OracleSpec

namespace XmssSecurity.Concrete.CacheView

def digestAt (cache : QueryCache HashSpec) (input : HashInput) : Digest :=
  match cache input with
  | some output => truncateHash output
  | none => 0

theorem digestAt_eq_of_cache_eq_some {cache : QueryCache HashSpec} {input : HashInput}
    {output : HashOutput} (hcache : cache input = some output) :
    digestAt cache input = truncateHash output := by
  simp [digestAt, hcache]

def tweakableHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (domain : HashDomain) (payload : HashInput) : Digest :=
  digestAt cache (XmssSecurity.tweakableHashInput parameter domain payload)

def encodingInput (parameter : PublicParameter) (epoch : Epoch)
    (input : Message × Randomness) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.encoding epoch)
    (Concrete.encodingPayload input.1 input.2)

def chainInput (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position : ChainStep) (value : Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.chain epoch chain position)
    (Concrete.digestBytes value)

def leafInput (parameter : PublicParameter) (epoch : Epoch)
    (endpoints : ChainIndex → Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.leaf epoch)
    (Concrete.leafPayload endpoints)

def merkleInput (parameter : PublicParameter) (level : MerkleLevel)
    (node : MerkleNode) (left right : Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.merkle level node)
    (Concrete.nodePayload left right)

def encodingHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (epoch : Epoch) (input : Message × Randomness) : Digest :=
  digestAt cache (encodingInput parameter epoch input)

def chainStep (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (epoch : Epoch) (chain : ChainIndex) (position : Nat) (value : Digest) : Digest :=
  if hposition : position < chainLength - 1 then
    digestAt cache (chainInput parameter epoch chain ⟨position, hposition⟩ value)
  else
    0

def leafHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (epoch : Epoch) (endpoints : ChainIndex → Digest) : Digest :=
  digestAt cache (leafInput parameter epoch endpoints)

def merkleHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (level : MerkleLevel) (node : MerkleNode) (left right : Digest) : Digest :=
  digestAt cache (merkleInput parameter level node left right)

def nodeIndex (epoch : Epoch) (level : Nat) : MerkleNode :=
  ⟨epoch.val / 2 ^ (level + 1), by
    have hle := Nat.div_le_self epoch.val (2 ^ (level + 1))
    exact hle.trans_lt epoch.isLt⟩

def authenticationNodePayload (epoch : Epoch) (level : Nat)
    (current sibling : Digest) : HashInput :=
  if epoch.val.testBit level then
    Concrete.nodePayload sibling current
  else
    Concrete.nodePayload current sibling

def nodeInput (parameter : PublicParameter) (epoch : Epoch) (level : MerkleLevel)
    (current sibling : Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.merkle level (nodeIndex epoch level.val))
    (authenticationNodePayload epoch level.val current sibling)

def nodeHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (epoch : Epoch) (level : Nat) (left right : Digest) : Digest :=
  if hlevel : level < treeHeight then
    digestAt cache (nodeInput parameter epoch ⟨level, hlevel⟩ left right)
  else
    0

@[simp]
theorem chainStep_eq (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (epoch : Epoch) (chain : ChainIndex) (position : Nat) (value : Digest)
    (hposition : position < chainLength - 1) :
    chainStep cache parameter epoch chain position value =
      digestAt cache (chainInput parameter epoch chain ⟨position, hposition⟩ value) := by
  simp [chainStep, hposition]

@[simp]
theorem nodeHash_eq (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (epoch : Epoch) (level : Nat) (left right : Digest)
    (hlevel : level < treeHeight) :
    nodeHash cache parameter epoch level left right =
      digestAt cache (nodeInput parameter epoch ⟨level, hlevel⟩ left right) := by
  simp [nodeHash, hlevel]

theorem encodingInput_injective (parameter : PublicParameter) (epoch : Epoch) :
    Function.Injective (encodingInput parameter epoch) := by
  intro left right heq
  apply Concrete.encodingPayload_injective
  exact payload_eq_of_tweakableHashInput_eq parameter (.encoding epoch) heq

/-- Serialized encoding inputs are separated by epoch as well as by message and randomness. -/
theorem encodingInput_eq_iff (parameter : PublicParameter)
    (leftEpoch rightEpoch : Epoch) (left right : Message × Randomness) :
    encodingInput parameter leftEpoch left =
        encodingInput parameter rightEpoch right ↔
      leftEpoch = rightEpoch ∧ left = right := by
  constructor
  · intro heq
    have hdomain : HashDomain.encoding leftEpoch = .encoding rightEpoch :=
      domain_eq_of_tweakableHashInput_eq parameter heq
    have hepoch : leftEpoch = rightEpoch := HashDomain.encoding.inj hdomain
    subst rightEpoch
    exact ⟨rfl, encodingInput_injective parameter leftEpoch heq⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem epoch_eq_of_encodingInput_eq (parameter : PublicParameter)
    {leftEpoch rightEpoch : Epoch} {left right : Message × Randomness}
    (heq : encodingInput parameter leftEpoch left =
      encodingInput parameter rightEpoch right) :
    leftEpoch = rightEpoch :=
  (encodingInput_eq_iff parameter leftEpoch rightEpoch left right).mp heq |>.1

theorem chainInput_injective (parameter : PublicParameter) (epoch : Epoch)
    (chain : ChainIndex) (position : ChainStep) :
    Function.Injective (chainInput parameter epoch chain position) := by
  intro left right heq
  apply Concrete.digestBytes_injective
  exact payload_eq_of_tweakableHashInput_eq parameter (.chain epoch chain position) heq

theorem leafInput_injective (parameter : PublicParameter) (epoch : Epoch) :
    Function.Injective (leafInput parameter epoch) := by
  intro left right heq
  apply Concrete.leafPayload_injective
  exact payload_eq_of_tweakableHashInput_eq parameter (.leaf epoch) heq

theorem authenticationNodePayload_injective (epoch : Epoch) (level : Nat) :
    Function.Injective fun input : Digest × Digest =>
      authenticationNodePayload epoch level input.1 input.2 := by
  intro left right heq
  cases hbit : epoch.val.testBit level with
  | false =>
    simp only [authenticationNodePayload, hbit, Bool.false_eq_true, ↓reduceIte] at heq
    exact Concrete.nodePayload_injective heq
  | true =>
    simp only [authenticationNodePayload, hbit, ↓reduceIte] at heq
    have hswap : (left.2, left.1) = (right.2, right.1) :=
      Concrete.nodePayload_injective heq
    exact Prod.ext (congrArg Prod.snd hswap) (congrArg Prod.fst hswap)

theorem nodeInput_injective (parameter : PublicParameter) (epoch : Epoch)
    (level : MerkleLevel) :
    Function.Injective fun input : Digest × Digest =>
      nodeInput parameter epoch level input.1 input.2 := by
  intro left right heq
  apply authenticationNodePayload_injective epoch level.val
  exact payload_eq_of_tweakableHashInput_eq parameter
    (.merkle level (nodeIndex epoch level.val)) heq

end XmssSecurity.Concrete.CacheView
