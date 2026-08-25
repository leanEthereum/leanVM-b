import SphincsSecurity.Proof.Honest

/-!
# Reading a payload's blocks

The accounting has to charge a query whose answer is what fixes an honest input one level up. What it
charges against is the block of the parent's payload that answer would have to land in, so it needs to
read a block out of an input: `slotDigest_flatMap` says the `k`-th block of a payload built from a
list of values is the `k`-th value. Nothing here is about the scheme, only about the fixed-width
encoding every payload of it uses.
-/

namespace SphincsSecurity

open OracleComp

/-- The digest a block of bytes encodes, and `0` if it encodes none. -/
noncomputable def digestOfBytes (bs : HashInput) : Digest :=
  open Classical in
  if h : ∃ value : Digest, Concrete.digestBytes value = bs then h.choose else 0

theorem digestOfBytes_digestBytes (value : Digest) :
    digestOfBytes (Concrete.digestBytes value) = value := by
  classical
  have h : ∃ candidate : Digest, Concrete.digestBytes candidate = Concrete.digestBytes value :=
    ⟨value, rfl⟩
  rw [digestOfBytes, dif_pos h]
  exact digestBytes_injective h.choose_spec

/-- What follows the tweak and the parameter in a hash input. -/
def payloadOf (input : HashInput) : HashInput := input.drop 32

theorem payloadOf_tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) : payloadOf (tweakableHashInput parameter domain payload) = payload := by
  have hlength : (tweakBytes domain ++ bytesLE 16 parameter).length = 32 := by
    simp [tweakBytes_length, bytesLE_length]
  simp only [payloadOf, tweakableHashInput]
  rw [← hlength, List.drop_left]

/-- The digest in a payload's `k`-th block. -/
noncomputable def slotDigest (k : Nat) (input : HashInput) : Digest :=
  digestOfBytes (((payloadOf input).drop (16 * k)).take 16)

theorem drop_flatMap_digestBytes (values : List Digest) (k : Nat) :
    (values.flatMap Concrete.digestBytes).drop (16 * k)
      = (values.drop k).flatMap Concrete.digestBytes := by
  induction k generalizing values with
  | zero => simp
  | succ k ih =>
      cases values with
      | nil => simp
      | cons value values =>
          rw [List.flatMap_cons, List.drop_succ_cons, ← ih values,
            show 16 * (k + 1) = (Concrete.digestBytes value).length + 16 * k by
              rw [digestBytes_length]; ring,
            List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
            Nat.add_sub_cancel_left]

/-- **Reading a block.** The `k`-th block of a payload built from a list of values is the `k`-th
value. -/
theorem slotDigest_flatMap (parameter : PublicParameter) (domain : HashDomain)
    (values : List Digest) (k : Nat) (hk : k < values.length) :
    slotDigest k (tweakableHashInput parameter domain
        (values.flatMap Concrete.digestBytes)) = values[k] := by
  rw [slotDigest, payloadOf_tweakableHashInput, drop_flatMap_digestBytes]
  have hdrop : values.drop k = values[k] :: (values.drop (k + 1)) :=
    List.drop_eq_getElem_cons hk
  rw [hdrop, List.flatMap_cons, ← digestBytes_length values[k], List.take_left,
    digestOfBytes_digestBytes]

/-- The slot occupied by a child in an honest input contains that child's honest value. -/
theorem slotDigest_honestInput_child (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) {parent child : Position}
    (hvalid : parent.Valid) (hmem : child ∈ parent.children) :
    slotDigest (parent.children.idxOf child)
        (honestInput f parameter otsSecret ftsSecret parent)
      = honestValue f parameter otsSecret ftsSecret child := by
  have hidx : parent.children.idxOf child < parent.children.length :=
    List.idxOf_lt_length_iff.mpr hmem
  rw [honestInput, honestPayload_eq_slots f parameter otsSecret ftsSecret hvalid,
    slots_eq_childValues_of_mem f parameter otsSecret ftsSecret hmem,
    slotDigest_flatMap parameter parent.domain
      (childValues f parameter otsSecret ftsSecret parent) (parent.children.idxOf child)
      (by simpa [childValues] using hidx)]
  simp [childValues, List.getElem_idxOf hidx]

end SphincsSecurity
