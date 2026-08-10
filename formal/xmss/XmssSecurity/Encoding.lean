import XmssSecurity.Parameters
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.NormNum
import ToMathlib.General

namespace XmssSecurity.TargetSum

open scoped BigOperators

def sum (x : Encoding) : Nat := ∑ i, (x i).val

def Valid (x : Encoding) : Prop := sum x = targetSum

def PointwiseLE (x y : Encoding) : Prop := ∀ i, x i ≤ y i

def Incomparable (x y : Encoding) : Prop := ¬PointwiseLE x y ∧ ¬PointwiseLE y x

def verificationWork (x : Encoding) : Nat :=
  ∑ i, (chainLength - 1 - (x i).val)

/-- The verifier's domain-separated WOTS chain positions for one encoding. -/
abbrev SuffixPosition (x : Encoding) :=
  Σ i : ChainIndex, Fin (chainLength - 1 - (x i).val)

/-- Every valid encoding makes the verifier walk exactly 99 WOTS chain edges. -/
theorem verificationWork_eq (x : Encoding) (hx : Valid x) :
    verificationWork x = verificationChainHashes := by
  unfold Valid sum at hx
  unfold verificationWork verificationChainHashes
  rw [Finset.sum_tsub_distrib Finset.univ]
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact congrArg (numChains * (chainLength - 1) - ·) hx
  · intro i _
    exact Nat.le_pred_of_lt (x i).isLt

theorem card_suffixPosition (x : Encoding) (hx : Valid x) :
    Fintype.card (SuffixPosition x) = verificationChainHashes := by
  rw [Fintype.card_sigma]
  simpa [verificationWork] using verificationWork_eq x hx

noncomputable def enumerateSuffixPositions (x : Encoding) (hx : Valid x) :
    SuffixPosition x ≃ Fin verificationChainHashes :=
  Fintype.equivFinOfCardEq (card_suffixPosition x hx)

/-- The two unused digest bits accompany the 42 three-bit digits. -/
abbrev EncodingView := Encoding × Fin 4

theorem card_digest_eq_encodingView : Fintype.card Digest = Fintype.card EncodingView := by
  norm_num [Digest, EncodingView, Encoding, ChainIndex, Digit, digestBits, numChains,
    chainLength, winternitzBits, Fintype.card_congr BitVec.equivFin.toEquiv]

/-- A security-level view of the concrete bit layout. Only its bijectivity matters to the proof. -/
noncomputable def digestView : Digest ≃ EncodingView :=
  Fintype.equivOfCardEq card_digest_eq_encodingView

def ValidView (view : EncodingView) : Prop :=
  view.2 = 0 ∧ Valid view.1

noncomputable def decodeView (view : EncodingView) : Option Encoding := by
  classical
  exact if ValidView view then some view.1 else none

noncomputable def decodeDigest (digest : Digest) : Option Encoding :=
  decodeView (digestView digest)

theorem decodeView_eq_some_iff {view : EncodingView} {x : Encoding} :
    decodeView view = some x ↔ view = (x, 0) ∧ Valid x := by
  classical
  rcases view with ⟨digits, padding⟩
  simp only [decodeView, ValidView]
  split <;> rename_i hview
  · simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · intro hdigits
      subst x
      exact ⟨⟨rfl, hview.1⟩, hview.2⟩
    · exact fun h => h.1.1
  · simp only [Prod.mk.injEq]
    constructor
    · intro heq
      cases heq
    · rintro ⟨⟨hdigits, hpadding⟩, hvalid⟩
      exfalso
      apply hview
      refine ⟨hpadding, ?_⟩
      exact hdigits.symm ▸ hvalid

theorem decodeDigest_eq_some_iff {digest : Digest} {x : Encoding} :
    decodeDigest digest = some x ↔ digestView digest = (x, 0) ∧ Valid x := by
  exact decodeView_eq_some_iff

/-- A valid target-sum encoding and zero padding determine one exact 128-bit digest. -/
theorem digest_eq_of_decodeDigest_eq_some {left right : Digest} {x : Encoding}
    (hleft : decodeDigest left = some x) (hright : decodeDigest right = some x) :
    left = right := by
  apply digestView.injective
  rw [(decodeDigest_eq_some_iff.mp hleft).1, (decodeDigest_eq_some_iff.mp hright).1]

/-- Two distinct encoding-hash inputs decoding to the same valid encoding form a target collision. -/
theorem hash_collision_of_same_decodedEncoding {α : Type} (hash : α → Digest)
    {left right : α} {x : Encoding} (hne : left ≠ right)
    (hleft : decodeDigest (hash left) = some x)
    (hright : decodeDigest (hash right) = some x) :
    left ≠ right ∧ hash left = hash right :=
  ⟨hne, digest_eq_of_decodeDigest_eq_some hleft hright⟩

theorem eq_of_pointwiseLE_of_valid {x y : Encoding} (hx : Valid x) (hy : Valid y)
    (hxy : PointwiseLE x y) : x = y := by
  by_contra hne
  have hlt : ∃ i ∈ Finset.univ, (x i).val < (y i).val := by
    by_contra h
    push Not at h
    apply hne
    funext i
    exact Fin.ext (Nat.le_antisymm (hxy i) (h i (Finset.mem_univ i)))
  have hsum : sum x < sum y := by
    apply Finset.sum_lt_sum
    · intro i _
      exact hxy i
    · exact hlt
  exact (Nat.ne_of_lt hsum) (hx.trans hy.symm)

theorem incomparable_of_valid_of_ne {x y : Encoding} (hx : Valid x) (hy : Valid y)
    (hne : x ≠ y) : Incomparable x y := by
  constructor
  · exact fun hxy => hne (eq_of_pointwiseLE_of_valid hx hy hxy)
  · exact fun hyx => hne (eq_of_pointwiseLE_of_valid hy hx hyx).symm

/-- A different valid encoding moves backward on at least one chain. -/
theorem exists_forged_lt_signed {signedEncoding forgedEncoding : Encoding}
    (hsigned : Valid signedEncoding) (hforged : Valid forgedEncoding)
    (hne : signedEncoding ≠ forgedEncoding) :
    ∃ i, forgedEncoding i < signedEncoding i := by
  have hnot := (incomparable_of_valid_of_ne hsigned hforged hne).1
  simpa only [PointwiseLE, not_forall, not_le] using hnot

end XmssSecurity.TargetSum
