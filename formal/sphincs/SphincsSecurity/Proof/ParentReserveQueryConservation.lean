import SphincsSecurity.Proof.ParentReserveConservation
import SphincsSecurity.Proof.RomQueryCharge

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition parentReserve parentReserveCharge releasedParentReserve
set_option backward.isDefEq.respectTransparency false

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
  (eligible : Position → Prop)

theorem releasedParentReserve_refl (cache : QueryCache HashSpec) :
    releasedParentReserve parameter otsSecret ftsSecret eligible cache cache = 0 := by
  simp only [releasedParentReserve, releasedParentReserveAt, not_and_self, and_false, if_false, Finset.sum_const_zero]

noncomputable def freshParentReserveCharge (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  if cache input = none then (parentReserveCharge parameter otsSecret ftsSecret eligible cache input : ENNReal) else 0

noncomputable def releasedParentQueryCharge (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  ∑' result, Pr[= result | (randomOracle input).run cache] *
    (releasedParentReserve parameter otsSecret ftsSecret eligible cache result.2 : ENNReal)

theorem randomOracle_parentReserve_add_released
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) :
    (∑' result, Pr[= result | (randomOracle input).run cache] * (parentReserve parameter otsSecret ftsSecret eligible result.2 : ENNReal)) +
      releasedParentQueryCharge parameter otsSecret ftsSecret eligible cache input =
      (parentReserve parameter otsSecret ftsSecret eligible cache : ENNReal) + freshParentReserveCharge parameter otsSecret ftsSecret eligible cache input := by
  rw [releasedParentQueryCharge, ← ENNReal.tsum_add]
  simp_rw [← mul_add, ← Nat.cast_add]
  by_cases hfresh : cache input = none
  · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul,
      freshParentReserveCharge, if_pos hfresh]
    simp_rw [parentReserve_cacheQuery_add_released_eq parameter otsSecret ftsSecret eligible hfinite hfresh]
    rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul, Nat.cast_add]
  · obtain ⟨answer, ha⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [randomOracle, QueryImpl.withCaching_run_some _ ha, tsum_probOutput_pure_mul,
      freshParentReserveCharge, if_neg hfresh, releasedParentReserve_refl, Nat.add_zero, add_zero]

theorem romImpl_parentReserve_add_released
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (query : OracleWorld.Domain) :
    (∑' result, Pr[= result | (romImpl query).run cache] * (parentReserve parameter otsSecret ftsSecret eligible result.2 : ENNReal)) +
      hashQueryCharge (releasedParentQueryCharge parameter otsSecret ftsSecret eligible) cache query =
      (parentReserve parameter otsSecret ftsSecret eligible cache : ENNReal) +
        hashQueryCharge (freshParentReserveCharge parameter otsSecret ftsSecret eligible) cache query := by
  cases query with
  | inl sample =>
      have hu : (romImpl (.inl sample)).run cache =
          (fun output => (output, cache)) <$> (liftM (unifSpec.query sample) : ProbComp _) := rfl
      rw [hu, tsum_probOutput_map_mul]
      dsimp only
      rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
      simp only [hashQueryCharge, Sum.elim_inl]
  | inr input => exact randomOracle_parentReserve_add_released parameter otsSecret ftsSecret eligible cache hfinite input

theorem expected_parentReserve_add_released_eq_queryCharge
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    (∑' result, Pr[= result | (simulateQ romImpl computation).run cache] * (parentReserve parameter otsSecret ftsSecret eligible result.2 : ENNReal)) +
      expectedQueryCharge (releasedParentQueryCharge parameter otsSecret ftsSecret eligible) computation cache =
      (parentReserve parameter otsSecret ftsSecret eligible cache : ENNReal) +
        expectedQueryCharge (freshParentReserveCharge parameter otsSecret ftsSecret eligible) computation cache := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp [simulateQ_pure]
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul,
        expectedQueryCharge_query_bind, expectedQueryCharge_query_bind]
      calc
        _ = (∑' result, Pr[= result | (romImpl query).run cache] *
            ((∑' final, Pr[= final | (simulateQ romImpl (next result.1)).run result.2] *
                (parentReserve parameter otsSecret ftsSecret eligible final.2 : ENNReal)) +
              expectedQueryCharge (releasedParentQueryCharge parameter otsSecret ftsSecret eligible) (next result.1) result.2)) +
            hashQueryCharge (releasedParentQueryCharge parameter otsSecret ftsSecret eligible) cache query := by
          simp only [mul_add, ENNReal.tsum_add]
          ac_rfl
        _ = (∑' result, Pr[= result | (romImpl query).run cache] *
            ((parentReserve parameter otsSecret ftsSecret eligible result.2 : ENNReal) +
              expectedQueryCharge (freshParentReserveCharge parameter otsSecret ftsSecret eligible) (next result.1) result.2)) +
            hashQueryCharge (releasedParentQueryCharge parameter otsSecret ftsSecret eligible) cache query := by
          congr 1
          apply tsum_congr
          intro result
          by_cases hr : result ∈ support ((romImpl query).run cache)
          · rw [ih result.1 result.2 (finite_of_mem_support_romImpl hfinite hr)]
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
        _ = _ := by
          simp only [mul_add, ENNReal.tsum_add]
          rw [add_right_comm, romImpl_parentReserve_add_released parameter otsSecret ftsSecret eligible cache hfinite query, add_assoc]

end SphincsSecurity
