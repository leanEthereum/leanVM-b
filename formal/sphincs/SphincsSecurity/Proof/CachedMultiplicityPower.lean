import SphincsSecurity.Proof.MixedOccupancySigning

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def cachePowerArrival (power : Nat) (count : ENNReal) : ENNReal :=
  ∑ degree ∈ Finset.range power, (power.choose degree : ENNReal) * count ^ degree

theorem add_one_pow_eq_cachePowerArrival (power : Nat) (count : ENNReal) :
    (count + 1) ^ power = count ^ power + cachePowerArrival power count := by
  rw [add_pow, Finset.sum_range_succ]
  simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro degree _
  exact mul_comm _ _

theorem weighted_cachePowerArrival_sum (power : Nat) (counts weight : Index → ENNReal) :
    (∑ index : Index, cachePowerArrival power (counts index) * weight index) =
      ∑ degree ∈ Finset.range power, (power.choose degree : ENNReal) *
        ∑ index : Index, counts index ^ degree * weight index := by
  simp only [cachePowerArrival, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro degree _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  exact mul_assoc _ _ _

end SphincsSecurity.Concrete
