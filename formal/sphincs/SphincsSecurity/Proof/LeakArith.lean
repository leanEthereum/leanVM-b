import SphincsSecurity.Proof.Prelude

/-!
# The few-time leak, arithmetically

A forgery through the few-time forest needs, for each of the `k - 1` trees it opens, some signature
at the same index that revealed that tree's leaf. Union bounding over which signatures those are and
which tree each covers gives a *finite* sum, one term per number `d` of distinct signatures involved,
`d` running only to `k - 1` because no more can be needed:

  sum over d of  C(q_s, d) * 2^(-h*d) * d^(k-1) * 2^(-a*(k-1)).

So the leak needs no tail estimate. The true value is about `2^-133.3`, this union bound gives about
`2^-122.9`, and `2^-120` is what the claim needs.

The statement below clears the denominators and replaces each binomial by `q_s^d / d!`, which loses
nothing that matters and keeps every number a product of literals and powers of two. That is
deliberate: `Nat.choose` at `q_s = 2^24` is not something the kernel can evaluate, its recursion
being on `n`, and asking it to try costs two minutes and then fails.
-/

namespace SphincsSecurity

-- the terms carry exponents past the linter's threshold; `decide` evaluates them, the elaborator need not
set_option exponentiation.threshold 400

/-- `d ! * C(n, d) ≤ n ^ d`, which is what lets the binomials go. -/
theorem factorial_mul_choose_le_pow (n d : Nat) :
    Nat.factorial d * Nat.choose n d ≤ n ^ d := by
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  exact Nat.descFactorial_le_pow n d

theorem leak_union_bound_scaled_sum :
    ∑ d ∈ Finset.Icc 1 14,
        (d + 1).ascFactorial (14 - d) * 2 ^ (24 * d) * d ^ 14 * 2 ^ (26 * (14 - d))
      ≤ Nat.factorial 14 * 2 ^ 382 := by
  decide

end SphincsSecurity
