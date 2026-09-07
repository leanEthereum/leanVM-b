import SphincsSecurity.Proof.CacheCapacity

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def cacheSlotCount (q : Nat) (cache : QueryCache HashSpec) : Nat :=
  q - {input | cache input ≠ none}.ncard

theorem cacheSlotCount_cast (q : Nat) (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    (cacheSlotCount q cache : ENNReal) = cacheCapacity q cache := by
  rw [cacheSlotCount, ENNReal.natCast_sub, hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
  rfl

theorem cachedInputs_ncard_cacheQuery_of_fresh (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (input : HashInput) (output : HashOutput) (hfresh : cache input = none) :
    {other | (cache.cacheQuery input output) other ≠ none}.ncard = {other | cache other ≠ none}.ncard + 1 := by
  have hcast : ({other | (cache.cacheQuery input output) other ≠ none}.ncard : ENNReal) =
      (({other | cache other ≠ none}.ncard + 1 : Nat) : ENNReal) := by
    rw [(finite_cacheQuery hfinite input output).cachedInputs_ncard_toENNReal_eq_enncard, Nat.cast_add,
      hfinite.cachedInputs_ncard_toENNReal_eq_enncard, Nat.cast_one, enncard_cacheQuery_of_fresh cache input output hfresh]
  exact_mod_cast hcast

theorem cacheSlotCount_cacheQuery_succ (q : Nat) (cache : QueryCache HashSpec)
    (input : HashInput) (output : HashOutput) (hfresh : cache input = none)
    (hcap : QueryCache.enncard cache + 1 ≤ q) :
    cacheSlotCount q cache = cacheSlotCount q (cache.cacheQuery input output) + 1 := by
  have hfinite := Finite.of_enncard_le (le_self_add.trans hcap)
  have hcount : {other | cache other ≠ none}.ncard + 1 ≤ q := by
    have hcast := hcap
    rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard] at hcast
    exact_mod_cast hcast
  simp only [cacheSlotCount, cachedInputs_ncard_cacheQuery_of_fresh cache hfinite input output hfresh]
  omega

end SphincsSecurity.Concrete
