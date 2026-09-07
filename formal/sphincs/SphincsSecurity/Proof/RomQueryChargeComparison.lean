import SphincsSecurity.Proof.RomQueryChargeBind

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

theorem expectedQueryCharge_lift_unif_eq_zero
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (computation : OracleComp unifSpec α) (cache : QueryCache HashSpec) :
    expectedQueryCharge charge (liftM computation : OracleComp OracleWorld α) cache = 0 := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind query next ih =>
      rw [liftM_bind]
      change expectedQueryCharge charge
        ((liftM (OracleWorld.query (.inl query)) : OracleComp OracleWorld _) >>= fun answer => liftM (next answer)) cache = 0
      rw [expectedQueryCharge_query_bind]
      simp only [hashQueryCharge, Sum.elim_inl, ih, mul_zero, tsum_zero, zero_add]

theorem expectedQueryCharge_bind_le_bind
    (first second : QueryCache HashSpec → HashInput → ENNReal)
    (computation : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β)
    (cache : QueryCache HashSpec)
    (hleft : expectedQueryCharge first computation cache ≤ expectedQueryCharge second computation cache)
    (hright : ∀ result ∈ support ((simulateQ romImpl computation).run cache),
      expectedQueryCharge first (next result.1) result.2 ≤ expectedQueryCharge second (next result.1) result.2) :
    expectedQueryCharge first (computation >>= next) cache ≤ expectedQueryCharge second (computation >>= next) cache := by
  rw [expectedQueryCharge_bind, expectedQueryCharge_bind]
  apply add_le_add hleft
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ support ((simulateQ romImpl computation).run cache)
  · exact mul_le_mul' le_rfl (hright result hr)
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

theorem expectedQueryCharge_lift_sequenceFin_le {n : Nat}
    (first second : QueryCache HashSpec → HashInput → ENNReal)
    (computation : Fin n → OracleComp HashSpec α)
    (h : ∀ i cache, expectedQueryCharge first (liftM (computation i) : OracleComp OracleWorld α) cache ≤
      expectedQueryCharge second (liftM (computation i) : OracleComp OracleWorld α) cache)
    (cache : QueryCache HashSpec) :
    expectedQueryCharge first (liftM (Concrete.sequenceFin computation) : OracleComp OracleWorld _) cache ≤
      expectedQueryCharge second (liftM (Concrete.sequenceFin computation) : OracleComp OracleWorld _) cache := by
  induction n generalizing cache with
  | zero => simp [Concrete.sequenceFin]
  | succ n ih =>
      rw [Concrete.sequenceFin, liftM_bind]
      apply expectedQueryCharge_bind_le_bind _ _ _ _ _ (h 0 cache)
      intro result _
      rw [liftM_bind]
      apply expectedQueryCharge_bind_le_bind _ _ _ _ _ (ih (fun i => computation i.succ) (fun i => h i.succ) result.2)
      intros
      simp

end SphincsSecurity
