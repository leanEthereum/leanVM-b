import SphincsSecurity.Statement

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

/-- The leak's union bound, with `14!` and the powers of two cleared through it. The multipliers are
`14! / d!`, written out so that nothing has to evaluate a factorial. -/
theorem leak_union_bound_scaled :
    87178291200 * 2 ^ (24 * 1) * 1 ^ 14 * 2 ^ (26 * 13)
      + 43589145600 * 2 ^ (24 * 2) * 2 ^ 14 * 2 ^ (26 * 12)
      + 14529715200 * 2 ^ (24 * 3) * 3 ^ 14 * 2 ^ (26 * 11)
      + 3632428800 * 2 ^ (24 * 4) * 4 ^ 14 * 2 ^ (26 * 10)
      + 726485760 * 2 ^ (24 * 5) * 5 ^ 14 * 2 ^ (26 * 9)
      + 121080960 * 2 ^ (24 * 6) * 6 ^ 14 * 2 ^ (26 * 8)
      + 17297280 * 2 ^ (24 * 7) * 7 ^ 14 * 2 ^ (26 * 7)
      + 2162160 * 2 ^ (24 * 8) * 8 ^ 14 * 2 ^ (26 * 6)
      + 240240 * 2 ^ (24 * 9) * 9 ^ 14 * 2 ^ (26 * 5)
      + 24024 * 2 ^ (24 * 10) * 10 ^ 14 * 2 ^ (26 * 4)
      + 2184 * 2 ^ (24 * 11) * 11 ^ 14 * 2 ^ (26 * 3)
      + 182 * 2 ^ (24 * 12) * 12 ^ 14 * 2 ^ (26 * 2)
      + 14 * 2 ^ (24 * 13) * 13 ^ 14 * 2 ^ 26
      + 1 * 2 ^ (24 * 14) * 14 ^ 14
    ≤ 87178291200 * 2 ^ 384 := by
  decide

end SphincsSecurity
