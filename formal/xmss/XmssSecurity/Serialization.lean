import XmssSecurity.Tweak
import Mathlib.Data.List.OfFn

namespace XmssSecurity

/-- Serialize a bit vector into a fixed number of bytes, least significant byte first. -/
def bytesLE (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * index.val) 8)

@[simp]
theorem length_bytesLE (byteCount : Nat) (value : BitVec (8 * byteCount)) :
    (bytesLE byteCount value).length = byteCount := by
  simp [bytesLE]

theorem bytesLE_injective (byteCount : Nat) : Function.Injective (bytesLE byteCount) := by
  intro left right heq
  have hbytes :
      (fun index : Fin byteCount => UInt8.ofBitVec (left.extractLsb' (8 * index.val) 8)) =
        (fun index : Fin byteCount => UInt8.ofBitVec (right.extractLsb' (8 * index.val) 8)) :=
    List.ofFn_injective heq
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  let byte : Fin byteCount := ⟨bit / 8, by omega⟩
  have hbyte := congrFun hbytes byte
  have hbyteBits := congrArg UInt8.toBitVec hbyte
  have hlocal := congrArg (fun value => value.getLsbD (bit % 8)) hbyteBits
  have hmod : bit % 8 < 8 := Nat.mod_lt bit (by omega)
  have hposition : 8 * (bit / 8) + bit % 8 = bit := by
    omega
  simpa [byte, BitVec.getLsbD_extractLsb', hmod, hposition] using hlocal

/-- The exact 16 bytes supplied by the specification as a hash tweak. -/
def tweakBytes (domain : HashDomain) : List UInt8 :=
  bytesLE 16 (hashDomainTweak domain)

theorem tweakBytes_injective : Function.Injective tweakBytes :=
  (bytesLE_injective 16).comp hashDomainTweak_injective

theorem tweakBytes_eq_iff {left right : HashDomain} :
    tweakBytes left = tweakBytes right ↔ left = right :=
  tweakBytes_injective.eq_iff

/-- The random-oracle input `tweak || parameter || message` used by every tweakable hash call. -/
def tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (message : HashInput) : HashInput :=
  tweakBytes domain ++ bytesLE 16 parameter ++ message

theorem tweakableHashInput_domain_injective (parameter : PublicParameter) (message : HashInput) :
    Function.Injective (fun domain => tweakableHashInput parameter domain message) := by
  intro left right heq
  apply tweakBytes_injective
  exact List.append_left_injective (bytesLE 16 parameter)
    (List.append_left_injective message heq)

theorem domain_eq_of_tweakableHashInput_eq (parameter : PublicParameter)
    {leftDomain rightDomain : HashDomain} {leftMessage rightMessage : HashInput}
    (heq : tweakableHashInput parameter leftDomain leftMessage =
      tweakableHashInput parameter rightDomain rightMessage) :
    leftDomain = rightDomain := by
  apply tweakBytes_injective
  have hpref := congrArg (List.take 16) heq
  simpa [tweakableHashInput, tweakBytes] using hpref

theorem payload_eq_of_tweakableHashInput_eq (parameter : PublicParameter)
    (domain : HashDomain) {left right : HashInput}
    (heq : tweakableHashInput parameter domain left =
      tweakableHashInput parameter domain right) :
    left = right := by
  exact List.append_right_injective
    (tweakBytes domain ++ bytesLE 16 parameter) heq

end XmssSecurity
