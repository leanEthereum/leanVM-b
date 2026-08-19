import XmssSecurity.Statement.Parameters
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

namespace XmssSecurity.TargetSum

open scoped BigOperators

def sum (x : Encoding) : Nat := ∑ i, (x i).val

def Valid (x : Encoding) : Prop := sum x = targetSum

/-- The two unused digest bits accompany the 42 three-bit digits. -/
abbrev EncodingView := Encoding × Fin 4

def digitsPerHalf : Nat := numChains / 2

/-- Offset of a three-bit digit, skipping padding bits 63 and 127. -/
def digitOffset (i : ChainIndex) : Nat :=
  winternitzBits * i.val + if i.val < digitsPerHalf then 0 else 1

def digestEncoding (digest : Digest) : Encoding :=
  fun i => (digest.extractLsb' (digitOffset i) winternitzBits).toFin

def digestPadding (digest : Digest) : Fin 4 :=
  ⟨(if digest.getLsbD 63 then 1 else 0) +
    (if digest.getLsbD 127 then 2 else 0), by
      cases digest.getLsbD 63 <;> cases digest.getLsbD 127 <;> simp⟩

/-- The concrete little-endian layout used by `IncEnc`: 21 digits, one padding bit, 21 digits, and one padding bit. -/
def digestView (digest : Digest) : EncodingView :=
  (digestEncoding digest, digestPadding digest)

def ValidView (view : EncodingView) : Prop :=
  view.2 = 0 ∧ Valid view.1

noncomputable def decodeView (view : EncodingView) : Option Encoding := by
  classical
  exact if ValidView view then some view.1 else none

noncomputable def decodeDigest (digest : Digest) : Option Encoding :=
  decodeView (digestView digest)

end XmssSecurity.TargetSum
