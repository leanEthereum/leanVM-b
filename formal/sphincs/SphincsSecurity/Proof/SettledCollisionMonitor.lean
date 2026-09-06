import SphincsSecurity.Proof.SettledCollisionQuery

namespace SphincsSecurity.Concrete.SettledCollision

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable

structure History where
  unsettled : Finset HashInput
  hit : Bool

def initialHistory : History := ⟨∅, false⟩

noncomputable def queryHit (secretKey : SecretKey) (cache : QueryCache HashSpec) :
    (query : OracleWorld.Domain) → OracleWorld.Range query → Bool
  | .inl _, _ => false
  | .inr input, answer => decide (Collision secretKey cache input answer)

noncomputable def advance (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (history : History) (query : OracleWorld.Domain) (answer : OracleWorld.Range query) : History where
  unsettled := match query with
    | .inl _ => history.unsettled
    | .inr input => if cache input = none ∧ ¬ SettledInput secretKey cache input
        then insert input history.unsettled else history.unsettled
  hit := history.hit || queryHit secretKey cache query answer

noncomputable def runMonitor (secretKey : SecretKey)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (history : History) :
    ProbComp ((α × QueryCache HashSpec) × History) :=
  OracleComp.construct
    (C := fun _ => QueryCache HashSpec → History → ProbComp ((α × QueryCache HashSpec) × History))
    (fun value cache history => pure ((value, cache), history))
    (fun query _ next cache history => do
      let result ← (romImpl query).run cache
      next result.1 result.2 (advance secretKey cache history query result.1))
    computation cache history

def hitPotential (history : History) : ℝ≥0∞ := if history.hit then 1 else 0

theorem runMonitor_project (secretKey : SecretKey)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (history : History) :
    Prod.fst <$> runMonitor secretKey computation cache history =
      (simulateQ romImpl computation).run cache := by
  induction computation using OracleComp.inductionOn generalizing cache history with
  | pure value => simp [runMonitor, simulateQ_pure]
  | query_bind query next ih =>
      rw [runMonitor, OracleComp.construct_query_bind, map_bind,
        simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact bind_congr fun result => ih result.1 result.2 _

theorem expected_advance_hit_le (secretKey : SecretKey) (query : OracleWorld.Domain)
    (cache : QueryCache HashSpec) (history : History) :
    (∑' result, Pr[= result | (romImpl query).run cache] *
      hitPotential (advance secretKey cache history query result.1)) ≤
    hitPotential history + hashQueryCharge (fun cache input =>
      queryCharge secretKey cache input * (Fintype.card Digest : ℝ≥0∞)⁻¹) cache query := by
  by_cases hhit : history.hit = true
  · simp only [hitPotential, advance, hhit, Bool.true_or, ↓reduceIte, mul_one,
      romImpl_query_mass]
    exact le_self_add
  · cases query with
    | inl input => simp [hitPotential, advance, queryHit, hhit]
    | inr input =>
        change (∑' result, Pr[= result | (randomOracle input).run cache] *
          hitPotential (advance secretKey cache history (.inr input) result.1)) ≤ _
        by_cases hfresh : cache input = none
        · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
          simp only [hitPotential, advance, queryHit, Bool.or_eq_true, hhit, Bool.false_eq_true, false_or,
            decide_eq_true_eq, ↓reduceIte, zero_add, hashQueryCharge, Sum.elim_inr]
          simpa only [mul_ite, mul_one, mul_zero, probEvent_eq_tsum_ite,
            uniformSampleImpl, probOutput_uniformSample] using
            probEvent_collision_le_charge secretKey cache input
        · obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hfresh
          rw [randomOracle, QueryImpl.withCaching_run_some _ hanswer]
          simp [hitPotential, advance, queryHit, Collision, hfresh, hhit]

theorem expected_runMonitor_hit_le (secretKey : SecretKey)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (history : History) :
    (∑' result, Pr[= result | runMonitor secretKey computation cache history] *
      hitPotential result.2) ≤ hitPotential history +
      expectedQueryCharge (queryCharge secretKey) computation cache * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  rw [← expectedQueryCharge_mul]
  let charge := fun cache input => queryCharge secretKey cache input * (Fintype.card Digest : ℝ≥0∞)⁻¹
  change _ ≤ _ + expectedQueryCharge charge computation cache
  induction computation using OracleComp.inductionOn generalizing cache history with
  | pure value =>
      simp only [runMonitor, OracleComp.construct_pure, tsum_probOutput_pure_mul,
        expectedQueryCharge_pure, add_zero, le_refl]
  | query_bind query next ih =>
      rw [runMonitor, OracleComp.construct_query_bind, tsum_probOutput_bind_mul,
        expectedQueryCharge_query_bind]
      calc
        _ ≤ ∑' result, Pr[= result | (romImpl query).run cache] *
            (hitPotential (advance secretKey cache history query result.1) +
              expectedQueryCharge charge (next result.1) result.2) :=
          ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (ih result.1 result.2 _)
        _ = (∑' result, Pr[= result | (romImpl query).run cache] *
            hitPotential (advance secretKey cache history query result.1)) +
            ∑' result, Pr[= result | (romImpl query).run cache] *
              expectedQueryCharge charge (next result.1) result.2 := by
          simp_rw [mul_add, ENNReal.tsum_add]
        _ ≤ (hitPotential history + hashQueryCharge charge cache query) +
            ∑' result, Pr[= result | (romImpl query).run cache] *
              expectedQueryCharge charge (next result.1) result.2 :=
          add_le_add (expected_advance_hit_le secretKey query cache history) le_rfl
        _ = _ := by rw [add_assoc]

theorem probEvent_runMonitor_hit_le_queryCharge (secretKey : SecretKey)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    Pr[fun result => result.2.hit = true | runMonitor secretKey computation cache initialHistory] ≤
      expectedQueryCharge (queryCharge secretKey) computation cache * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  simpa only [hitPotential, initialHistory, Bool.false_eq_true, ↓reduceIte, zero_add,
    mul_ite, mul_one, mul_zero, ← probEvent_eq_tsum_ite] using
    expected_runMonitor_hit_le secretKey computation cache initialHistory

theorem probEvent_runMonitor_hit_le_queryBound (secretKey : SecretKey)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (q : Nat) (hq : computation.IsQueryBoundP (· matches Sum.inr _) q) :
    Pr[fun result => result.2.hit = true | runMonitor secretKey computation cache initialHistory] ≤
      (q : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  apply (probEvent_runMonitor_hit_le_queryCharge secretKey computation cache).trans
  apply mul_le_mul' _ le_rfl
  simpa only [one_mul] using expectedQueryCharge_le_queryBound (queryCharge secretKey) 1
    (queryCharge_le_one secretKey) computation q hq cache

end SphincsSecurity.Concrete.SettledCollision
