import SphincsSecurity.Proof.PairReuseReserve

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def linearReuseReserve (slots : Nat) (rate reuseRate target occupancy targetIncrement : ENNReal) : ENNReal :=
  target + slots * rate * occupancy + slots * reuseRate * targetIncrement

theorem linearReuseReserve_mono (slots : Nat) (rate reuseRate : ENNReal)
    {target occupancy targetIncrement target' occupancy' targetIncrement' : ENNReal}
    (htarget : target ≤ target') (hoccupancy : occupancy ≤ occupancy') (hincrement : targetIncrement ≤ targetIncrement') :
    linearReuseReserve slots rate reuseRate target occupancy targetIncrement ≤
      linearReuseReserve slots rate reuseRate target' occupancy' targetIncrement' :=
  add_le_add (add_le_add htarget (mul_le_mul' le_rfl hoccupancy)) (mul_le_mul' le_rfl hincrement)

theorem linearReuseReserve_mono_slots {first second : Nat} (hslots : first ≤ second)
    (rate reuseRate target occupancy targetIncrement : ENNReal) :
    linearReuseReserve first rate reuseRate target occupancy targetIncrement ≤
      linearReuseReserve second rate reuseRate target occupancy targetIncrement := by
  have hcast : (first : ENNReal) ≤ second := Nat.cast_le.mpr hslots
  exact add_le_add (add_le_add le_rfl (mul_le_mul' (mul_le_mul' hcast le_rfl) le_rfl))
    (mul_le_mul' (mul_le_mul' hcast le_rfl) le_rfl)

theorem linearReuseReserve_step (slots : Nat) (rate reuseRate target occupancy targetIncrement occupancyIncrement : ENNReal) :
    linearReuseReserve slots rate reuseRate (target + reuseRate * targetIncrement + rate * occupancy)
      (occupancy + reuseRate * occupancyIncrement) (targetIncrement + rate * occupancyIncrement) =
      linearReuseReserve (slots + 1) rate reuseRate target occupancy targetIncrement +
        2 * slots * reuseRate * rate * occupancyIncrement := by
  simp only [linearReuseReserve, Nat.cast_add, Nat.cast_one]
  ring

theorem expected_linearReuseReserve_le {α : Type} (computation : ProbComp α) (slots : Nat) (rate reuseRate : ENNReal)
    (target occupancy targetIncrement occupancyIncrement : ENNReal) (nextTarget nextOccupancy nextTargetIncrement : α → ENNReal)
    (htarget : (∑' result, Pr[= result | computation] * nextTarget result) ≤ target + reuseRate * targetIncrement + rate * occupancy)
    (hoccupancy : (∑' result, Pr[= result | computation] * nextOccupancy result) ≤ occupancy + reuseRate * occupancyIncrement)
    (hincrement : (∑' result, Pr[= result | computation] * nextTargetIncrement result) ≤ targetIncrement + rate * occupancyIncrement) :
    (∑' result, Pr[= result | computation] *
      linearReuseReserve slots rate reuseRate (nextTarget result) (nextOccupancy result) (nextTargetIncrement result)) ≤
      linearReuseReserve (slots + 1) rate reuseRate target occupancy targetIncrement +
        2 * slots * reuseRate * rate * occupancyIncrement := by
  calc
    _ = linearReuseReserve slots rate reuseRate
        (∑' result, Pr[= result | computation] * nextTarget result)
        (∑' result, Pr[= result | computation] * nextOccupancy result)
        (∑' result, Pr[= result | computation] * nextTargetIncrement result) := by
      simp only [linearReuseReserve, mul_add]
      simp_rw [mul_left_comm (Pr[= _ | computation])]
      simp only [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    _ ≤ linearReuseReserve slots rate reuseRate (target + reuseRate * targetIncrement + rate * occupancy)
        (occupancy + reuseRate * occupancyIncrement) (targetIncrement + rate * occupancyIncrement) :=
      linearReuseReserve_mono slots rate reuseRate htarget hoccupancy hincrement
    _ = _ := linearReuseReserve_step slots rate reuseRate target occupancy targetIncrement occupancyIncrement

end SphincsSecurity.Concrete
