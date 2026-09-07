import SphincsSecurity.Proof.CacheGrowthCharge

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def cacheCapacity (q : Nat) (cache : QueryCache HashSpec) : ENNReal :=
  (q : ENNReal) - QueryCache.enncard cache

theorem cacheCapacity_add_growth (q : Nat) (before after : QueryCache HashSpec)
    (hcache : before ≤ after) (hcap : QueryCache.enncard after ≤ q) :
    cacheCapacity q after + (QueryCache.enncard after - QueryCache.enncard before) = cacheCapacity q before := by
  have hle := QueryCache.enncard_mono hcache
  have hfinite : QueryCache.enncard before ≠ ∞ := ne_top_of_le_ne_top (by finiteness) (hle.trans hcap)
  apply (ENNReal.add_right_inj hfinite).mp
  unfold cacheCapacity
  calc
    _ = ((q : ENNReal) - QueryCache.enncard after) +
        (QueryCache.enncard before + (QueryCache.enncard after - QueryCache.enncard before)) := by ac_rfl
    _ = (q : ENNReal) := by rw [add_tsub_cancel_of_le hle, tsub_add_cancel_of_le hcap]
    _ = _ := (add_tsub_cancel_of_le (hle.trans hcap)).symm

theorem cacheCapacity_reserve_le (q : Nat) (before after : QueryCache HashSpec)
    (hcache : before ≤ after) (hcap : QueryCache.enncard after ≤ q)
    (lower weight : ENNReal) (hweight : lower ≤ weight) :
    (QueryCache.enncard after - QueryCache.enncard before) * lower + cacheCapacity q after * weight ≤
      cacheCapacity q before * weight := by
  apply (add_le_add (mul_le_mul' le_rfl hweight) le_rfl).trans_eq
  rw [← add_mul, add_comm, cacheCapacity_add_growth q before after hcache hcap]

theorem expected_cacheCapacity_reserve_le {α : Type} (computation : ProbComp α)
    (q : Nat) (before : QueryCache HashSpec) (after : α → QueryCache HashSpec)
    (lower : ENNReal) (weight : α → ENNReal)
    (hcache : ∀ result ∈ support computation, before ≤ after result)
    (hcap : ∀ result ∈ support computation, QueryCache.enncard (after result) ≤ q)
    (hweight : ∀ result ∈ support computation, lower ≤ weight result) :
    (∑' result, Pr[= result | computation] * (QueryCache.enncard (after result) - QueryCache.enncard before)) * lower +
      (∑' result, Pr[= result | computation] * (cacheCapacity q (after result) * weight result)) ≤
        cacheCapacity q before * ∑' result, Pr[= result | computation] * weight result := by
  rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  calc
    _ ≤ ∑' result, Pr[= result | computation] * (cacheCapacity q before * weight result) := by
      apply ENNReal.tsum_le_tsum
      intro result
      rw [mul_assoc, ← mul_add]
      by_cases hresult : result ∈ support computation
      · exact mul_le_mul' le_rfl (cacheCapacity_reserve_le q before (after result)
          (hcache result hresult) (hcap result hresult) lower (weight result) (hweight result hresult))
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ = _ := by
      simp_rw [mul_left_comm (Pr[= _ | _])]
      rw [ENNReal.tsum_mul_left]

end SphincsSecurity.Concrete
