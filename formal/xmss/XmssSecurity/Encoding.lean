import XmssSecurity.Parameters
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace XmssSecurity.TargetSum

open scoped BigOperators

def sum (x : Encoding) : Nat := ∑ i, (x i).val

def Valid (x : Encoding) : Prop := sum x = targetSum

def PointwiseLE (x y : Encoding) : Prop := ∀ i, x i ≤ y i

def Incomparable (x y : Encoding) : Prop := ¬PointwiseLE x y ∧ ¬PointwiseLE y x

def verificationWork (x : Encoding) : Nat :=
  ∑ i, (chainLength - 1 - (x i).val)

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
