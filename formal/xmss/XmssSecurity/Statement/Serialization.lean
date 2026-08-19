import XmssSecurity.Statement.Tweak
import Mathlib.Data.List.OfFn

namespace XmssSecurity

/-- Serialize a bit vector into a fixed number of bytes, least significant byte first. -/
def bytesLE (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * index.val) 8)

/-- The exact 16 bytes supplied by the specification as a hash tweak. -/
def tweakBytes (domain : HashDomain) : List UInt8 :=
  bytesLE 16 (hashDomainTweak domain)

/-- The random-oracle input `tweak || parameter || message` used by every tweakable hash call. -/
def tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (message : HashInput) : HashInput :=
  tweakBytes domain ++ bytesLE 16 parameter ++ message

end XmssSecurity
