import XmssSecurity.Parameters
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace XmssSecurity.TargetSum

open scoped BigOperators

def sum (x : Encoding) : Nat := ∑ i, (x i).val

def Valid (x : Encoding) : Prop := sum x = targetSum

def PointwiseLE (x y : Encoding) : Prop := ∀ i, x i ≤ y i

def Incomparable (x y : Encoding) : Prop := ¬PointwiseLE x y ∧ ¬PointwiseLE y x

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

end XmssSecurity.TargetSum
