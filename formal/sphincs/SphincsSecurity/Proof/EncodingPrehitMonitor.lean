import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.EncodingSelectionLift
import SphincsSecurity.Proof.FirstBad
import SphincsSecurity.Proof.RomQueryCharge
import SphincsSecurity.Proof.TightEncodingPrehitCharge
import SphincsSecurity.Proof.TightEncodingSelectionLift

namespace SphincsSecurity.Concrete.TightEncoding

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable

noncomputable def encodingPrehitQuery (secretKey : SecretKey) (cache : QueryCache HashSpec) :
    (query : OracleWorld.Domain) → OracleWorld.Range query → Bool
  | .inl _, _ => false
  | .inr input, answer => decide (cache input = none ∧ EncodingMessagePrehit cache secretKey input answer)

noncomputable def runEncodingPrehitMonitor (secretKey : SecretKey)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hit : Bool) :
    ProbComp ((α × QueryCache HashSpec) × Bool) :=
  OracleComp.construct
    (C := fun _ => QueryCache HashSpec → Bool → ProbComp ((α × QueryCache HashSpec) × Bool))
    (fun value cache hit => pure ((value, cache), hit))
    (fun query _ next cache hit => do
      let result ← (romImpl query).run cache
      next result.1 result.2 (hit || encodingPrehitQuery secretKey cache query result.1))
    computation cache hit

noncomputable def encodingPrehitMonitorPotential (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (hit : Bool) : ℝ≥0∞ :=
  if hit then 1 else encodingSelectionAdaptivePotential cache secretKey

theorem runEncodingPrehitMonitor_project (secretKey : SecretKey)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hit : Bool) :
    Prod.fst <$> runEncodingPrehitMonitor secretKey computation cache hit =
      (simulateQ romImpl computation).run cache := by
  induction computation using OracleComp.inductionOn generalizing cache hit with
  | pure value => simp [runEncodingPrehitMonitor, simulateQ_pure]
  | query_bind query next ih =>
      rw [runEncodingPrehitMonitor, OracleComp.construct_query_bind, map_bind,
        simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact bind_congr fun result => ih result.1 result.2 _

theorem expected_encodingPrehitMonitorPotential_query_le
    (secretKey : SecretKey) (query : OracleWorld.Domain) (cache : QueryCache HashSpec)
    (hit : Bool) (hfinite : Finite cache) :
    (∑' result, Pr[= result | (romImpl query).run cache] *
      encodingPrehitMonitorPotential secretKey result.2 (hit || encodingPrehitQuery secretKey cache query result.1)) ≤
    encodingPrehitMonitorPotential secretKey cache hit +
      hashQueryCharge (fun cache input => refinedStructuralEncodingQueryCharge secretKey cache input *
        (Fintype.card Digest : ℝ≥0∞)⁻¹) cache query := by
  cases hit with
  | true =>
      simp only [Bool.true_or, encodingPrehitMonitorPotential, ↓reduceIte, mul_one,
        romImpl_query_mass]
      exact le_self_add
  | false =>
      cases query with
      | inl input =>
          have hquery : (romImpl (.inl input)).run cache =
              (fun answer => (answer, cache)) <$> (liftM (unifSpec.query input) : ProbComp _) := rfl
          simp only [encodingPrehitQuery, encodingPrehitMonitorPotential, Bool.false_or,
            Bool.false_eq_true, ↓reduceIte, hashQueryCharge, Sum.elim_inl, add_zero]
          rw [hquery]
          change (∑' result : Fin (input + 1) × QueryCache HashSpec,
            Pr[= result | (fun answer : Fin (input + 1) => (answer, cache)) <$>
              (liftM (unifSpec.query input) : ProbComp (Fin (input + 1)))] *
                encodingSelectionAdaptivePotential result.2 secretKey) ≤ _
          rw [tsum_probOutput_map_mul]
          dsimp only
          rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
      | inr input =>
          change (∑' result, Pr[= result | (randomOracle input).run cache] *
            encodingPrehitMonitorPotential secretKey result.2 (false || encodingPrehitQuery secretKey cache (.inr input) result.1)) ≤ _
          by_cases hfresh : cache input = none
          · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
            simp only [encodingPrehitMonitorPotential, encodingPrehitQuery, hfresh, true_and,
              Bool.false_or, decide_eq_true_eq, Bool.false_eq_true, ↓reduceIte,
              hashQueryCharge, Sum.elim_inr]
            simp_rw [encodingSelectionAdaptivePotential_eq (finite_cacheQuery hfinite input _)]
            rw [encodingSelectionAdaptivePotential_eq hfinite]
            exact uniform_encodingPrehit_or_potential_le_refined_charge hfinite hfresh
          · obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hfresh
            rw [randomOracle, QueryImpl.withCaching_run_some _ hanswer]
            simp [encodingPrehitMonitorPotential, encodingPrehitQuery, hfresh]

theorem expected_runEncodingPrehitMonitor_potential_le_queryCharge
    (secretKey : SecretKey) (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hit : Bool) (hfinite : Finite cache) :
    (∑' result, Pr[= result | runEncodingPrehitMonitor secretKey computation cache hit] *
      encodingPrehitMonitorPotential secretKey result.1.2 result.2) ≤
    encodingPrehitMonitorPotential secretKey cache hit +
      expectedQueryCharge (refinedStructuralEncodingQueryCharge secretKey) computation cache *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  rw [← expectedQueryCharge_mul]
  let charge := fun cache input => refinedStructuralEncodingQueryCharge secretKey cache input *
    (Fintype.card Digest : ℝ≥0∞)⁻¹
  change _ ≤ _ + expectedQueryCharge charge computation cache
  induction computation using OracleComp.inductionOn generalizing cache hit with
  | pure value =>
      simp only [runEncodingPrehitMonitor, OracleComp.construct_pure,
        tsum_probOutput_pure_mul, expectedQueryCharge_pure, add_zero, le_refl]
  | query_bind query next ih =>
      rw [runEncodingPrehitMonitor, OracleComp.construct_query_bind, tsum_probOutput_bind_mul,
        expectedQueryCharge_query_bind]
      calc
        _ ≤ ∑' result, Pr[= result | (romImpl query).run cache] *
            (encodingPrehitMonitorPotential secretKey result.2
              (hit || encodingPrehitQuery secretKey cache query result.1) +
              expectedQueryCharge charge (next result.1) result.2) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hresult : result ∈ support ((romImpl query).run cache)
          · exact mul_le_mul' le_rfl
              (ih result.1 result.2 _ (finite_of_mem_support_romImpl hfinite hresult))
          · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
        _ = (∑' result, Pr[= result | (romImpl query).run cache] *
            encodingPrehitMonitorPotential secretKey result.2
              (hit || encodingPrehitQuery secretKey cache query result.1)) +
            ∑' result, Pr[= result | (romImpl query).run cache] *
              expectedQueryCharge charge (next result.1) result.2 := by
          simp_rw [mul_add, ENNReal.tsum_add]
        _ ≤ (encodingPrehitMonitorPotential secretKey cache hit + hashQueryCharge charge cache query) +
            ∑' result, Pr[= result | (romImpl query).run cache] *
              expectedQueryCharge charge (next result.1) result.2 :=
          add_le_add (expected_encodingPrehitMonitorPotential_query_le secretKey query cache hit hfinite) le_rfl
        _ = _ := by rw [add_assoc]

theorem finite_of_mem_runEncodingPrehitMonitor
    (secretKey : SecretKey) (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hit : Bool) (hfinite : Finite cache)
    (result : (α × QueryCache HashSpec) × Bool)
    (hresult : result ∈ support (runEncodingPrehitMonitor secretKey computation cache hit)) :
    Finite result.1.2 := by
  have hproject : result.1 ∈ support ((simulateQ romImpl computation).run cache) := by
    rw [← runEncodingPrehitMonitor_project secretKey computation cache hit, support_map]
    exact ⟨result, hresult, rfl⟩
  exact finite_cache_of_mem_support computation cache result.1.1 result.1.2 hproject hfinite

theorem probEvent_prehit_or_bad_or_encodingBad_le_queryCharge
    (secretKey : SecretKey) (computation : OracleComp OracleWorld α) :
    Pr[fun result => result.2 = true ∨
      Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret result.1.2 ∨
      EncodingBad result.1.2 secretKey | runEncodingPrehitMonitor secretKey computation ∅ false] ≤
    expectedQueryCharge (refinedStructuralEncodingQueryCharge secretKey) computation ∅ *
      (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  apply le_trans _ ((expected_runEncodingPrehitMonitor_potential_le_queryCharge
    secretKey computation ∅ false finite_empty).trans_eq (by
      simp [encodingPrehitMonitorPotential]))
  rw [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hevent : result.2 = true ∨
      Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret result.1.2 ∨
      EncodingBad result.1.2 secretKey
  · rw [if_pos hevent]
    by_cases hresult : result ∈ support (runEncodingPrehitMonitor secretKey computation ∅ false)
    · have hpotential : encodingPrehitMonitorPotential secretKey result.1.2 result.2 = 1 := by
        by_cases hhit : result.2 = true
        · simp [encodingPrehitMonitorPotential, hhit]
        · have hbad := hevent.resolve_left hhit
          have hfinite := finite_of_mem_runEncodingPrehitMonitor secretKey computation ∅ false finite_empty result hresult
          rw [encodingPrehitMonitorPotential, if_neg hhit, encodingSelectionAdaptivePotential_eq hfinite,
            encodingSelectionTotalPotential_eq_one_of_bad_or_encodingBad hfinite hbad]
      rw [hpotential, mul_one]
    · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]
  · rw [if_neg hevent]
    exact bot_le

end SphincsSecurity.Concrete.TightEncoding
