import XmssSecurity.Scheme
import XmssSecurity.Serialization

open OracleComp

namespace XmssSecurity.Concrete

def digestBytes (value : Digest) : HashInput :=
  bytesLE 16 value

def messageBytes (message : Message) : HashInput :=
  bytesLE 32 message

def randomnessBytes (randomness : Randomness) : HashInput :=
  bytesLE 24 randomness

theorem digestBytes_injective : Function.Injective digestBytes :=
  bytesLE_injective 16

theorem messageBytes_injective : Function.Injective messageBytes :=
  bytesLE_injective 32

theorem randomnessBytes_injective : Function.Injective randomnessBytes :=
  bytesLE_injective 24

def encodingPayload (message : Message) (randomness : Randomness) : HashInput :=
  messageBytes message ++ randomnessBytes randomness ++ List.replicate 8 0

def leafPayload (endpoints : ChainIndex → Digest) : HashInput :=
  (List.ofFn endpoints).flatMap digestBytes

def nodePayload (left right : Digest) : HashInput :=
  digestBytes left ++ digestBytes right

private theorem flatMap_injective_of_eq_length {α β : Type}
    (encode : α → List β) (hinjective : Function.Injective encode)
    (encodedLength : Nat) (hlength : ∀ value, (encode value).length = encodedLength)
    {left right : List α} (hsameLength : left.length = right.length)
    (heq : left.flatMap encode = right.flatMap encode) : left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons => simp at hsameLength
  | cons head tail ih =>
      cases right with
      | nil => simp at hsameLength
      | cons rightHead rightTail =>
          simp only [List.flatMap_cons] at heq
          obtain ⟨hhead, htail⟩ := List.append_inj heq (by simp [hlength])
          congr
          · exact hinjective hhead
          · apply ih
            · simpa using Nat.succ.inj hsameLength
            · exact htail

theorem encodingPayload_injective :
    Function.Injective fun input : Message × Randomness => encodingPayload input.1 input.2 := by
  rintro ⟨leftMessage, leftRandomness⟩ ⟨rightMessage, rightRandomness⟩ heq
  have hpairs :
      messageBytes leftMessage ++ randomnessBytes leftRandomness =
        messageBytes rightMessage ++ randomnessBytes rightRandomness :=
    List.append_left_injective (List.replicate 8 0) heq
  obtain ⟨hmessage, hrandomness⟩ := List.append_inj hpairs (by simp [messageBytes])
  exact Prod.ext (messageBytes_injective hmessage) (randomnessBytes_injective hrandomness)

theorem leafPayload_injective : Function.Injective leafPayload := by
  intro left right heq
  apply List.ofFn_injective
  exact flatMap_injective_of_eq_length digestBytes digestBytes_injective 16
    (fun value => by simp [digestBytes]) (by simp) heq

theorem nodePayload_injective :
    Function.Injective fun input : Digest × Digest => nodePayload input.1 input.2 := by
  rintro ⟨leftFirst, leftSecond⟩ ⟨rightFirst, rightSecond⟩ heq
  obtain ⟨hfirst, hsecond⟩ := List.append_inj heq (by simp [digestBytes])
  exact Prod.ext (digestBytes_injective hfirst) (digestBytes_injective hsecond)

def oracleHash (input : HashInput) : OracleComp OracleWorld HashOutput :=
  liftM (OracleWorld.query (.inr input))

def tweakableHash (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) : OracleComp OracleWorld Digest := do
  let output ← oracleHash (tweakableHashInput parameter domain payload)
  return truncateHash output

def encodingHash (parameter : PublicParameter) (epoch : Epoch)
    (message : Message) (randomness : Randomness) : OracleComp OracleWorld Digest :=
  tweakableHash parameter (.encoding epoch) (encodingPayload message randomness)

def chainHash (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) : OracleComp OracleWorld Digest :=
  tweakableHash parameter (.chain epoch chain step) (digestBytes value)

def leafHash (parameter : PublicParameter) (epoch : Epoch)
    (endpoints : ChainIndex → Digest) : OracleComp OracleWorld Digest :=
  tweakableHash parameter (.leaf epoch) (leafPayload endpoints)

def nodeHash (parameter : PublicParameter) (level : MerkleLevel) (node : MerkleNode)
    (left right : Digest) : OracleComp OracleWorld Digest :=
  tweakableHash parameter (.merkle level node) (nodePayload left right)

end XmssSecurity.Concrete
