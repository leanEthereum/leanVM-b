import SphincsSecurity.Proof.DirectReuseArrival

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def pairReuseReserve (slots : Nat) (rate reuseRate target occupancy targetIncrement occupancyIncrement : ENNReal) : ENNReal :=
  target + slots * rate * occupancy + slots * reuseRate * targetIncrement +
    2 * slots.choose 2 * reuseRate * rate * occupancyIncrement

theorem pairReuseReserve_mono (slots : Nat) (rate reuseRate : ENNReal)
    {target occupancy targetIncrement occupancyIncrement target' occupancy' targetIncrement' occupancyIncrement' : ENNReal}
    (htarget : target ≤ target') (hoccupancy : occupancy ≤ occupancy')
    (htargetIncrement : targetIncrement ≤ targetIncrement') (hoccupancyIncrement : occupancyIncrement ≤ occupancyIncrement') :
    pairReuseReserve slots rate reuseRate target occupancy targetIncrement occupancyIncrement ≤
      pairReuseReserve slots rate reuseRate target' occupancy' targetIncrement' occupancyIncrement' :=
  add_le_add (add_le_add (add_le_add htarget (mul_le_mul' le_rfl hoccupancy))
    (mul_le_mul' le_rfl htargetIncrement)) (mul_le_mul' le_rfl hoccupancyIncrement)

theorem pairReuseReserve_mono_slots {first second : Nat} (hslots : first ≤ second)
    (rate reuseRate target occupancy targetIncrement occupancyIncrement : ENNReal) :
    pairReuseReserve first rate reuseRate target occupancy targetIncrement occupancyIncrement ≤
      pairReuseReserve second rate reuseRate target occupancy targetIncrement occupancyIncrement := by
  have hcast : (first : ENNReal) ≤ second := Nat.cast_le.mpr hslots
  have hchoose : (first.choose 2 : ENNReal) ≤ second.choose 2 := Nat.cast_le.mpr (Nat.choose_le_choose 2 hslots)
  exact add_le_add (add_le_add (add_le_add le_rfl (mul_le_mul' (mul_le_mul' hcast le_rfl) le_rfl))
    (mul_le_mul' (mul_le_mul' hcast le_rfl) le_rfl))
    (mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hchoose) le_rfl) le_rfl) le_rfl)

theorem pairReuseReserve_step (slots : Nat) (rate reuseRate target occupancy targetIncrement occupancyIncrement : ENNReal) :
    pairReuseReserve slots rate reuseRate (target + reuseRate * targetIncrement + rate * occupancy)
      (occupancy + reuseRate * occupancyIncrement) (targetIncrement + rate * occupancyIncrement) occupancyIncrement =
      pairReuseReserve (slots + 1) rate reuseRate target occupancy targetIncrement occupancyIncrement := by
  simp only [pairReuseReserve, Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
  ring

theorem expected_pairReuseReserve_le {α : Type} (computation : ProbComp α) (slots : Nat) (rate reuseRate : ENNReal)
    (target occupancy targetIncrement occupancyIncrement : ENNReal) (nextTarget nextOccupancy nextTargetIncrement : α → ENNReal)
    (htarget : (∑' result, Pr[= result | computation] * nextTarget result) ≤ target + reuseRate * targetIncrement + rate * occupancy)
    (hoccupancy : (∑' result, Pr[= result | computation] * nextOccupancy result) ≤ occupancy + reuseRate * occupancyIncrement)
    (hincrement : (∑' result, Pr[= result | computation] * nextTargetIncrement result) ≤ targetIncrement + rate * occupancyIncrement) :
    (∑' result, Pr[= result | computation] *
      pairReuseReserve slots rate reuseRate (nextTarget result) (nextOccupancy result) (nextTargetIncrement result) occupancyIncrement) ≤
      pairReuseReserve (slots + 1) rate reuseRate target occupancy targetIncrement occupancyIncrement := by
  calc
    _ = (∑' result, Pr[= result | computation] * nextTarget result) +
        (slots : ENNReal) * rate * (∑' result, Pr[= result | computation] * nextOccupancy result) +
        (slots : ENNReal) * reuseRate * (∑' result, Pr[= result | computation] * nextTargetIncrement result) +
        (∑' result, Pr[= result | computation]) * (2 * (slots.choose 2 : ENNReal) * reuseRate * rate * occupancyIncrement) := by
      simp only [pairReuseReserve, mul_add]
      simp_rw [mul_left_comm (Pr[= _ | computation])]
      simp only [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
      ring
    _ ≤ pairReuseReserve slots rate reuseRate
        (∑' result, Pr[= result | computation] * nextTarget result)
        (∑' result, Pr[= result | computation] * nextOccupancy result)
        (∑' result, Pr[= result | computation] * nextTargetIncrement result) occupancyIncrement :=
      add_le_add le_rfl (mul_le_of_le_one_left' tsum_probOutput_le_one)
    _ ≤ pairReuseReserve slots rate reuseRate (target + reuseRate * targetIncrement + rate * occupancy)
        (occupancy + reuseRate * occupancyIncrement) (targetIncrement + rate * occupancyIncrement) occupancyIncrement :=
      pairReuseReserve_mono slots rate reuseRate htarget hoccupancy hincrement le_rfl
    _ = _ := pairReuseReserve_step slots rate reuseRate target occupancy targetIncrement occupancyIncrement

end SphincsSecurity.Concrete
