import SphincsSecurity.Proof.EncodingSelectionPotential
import SphincsSecurity.Proof.CacheSize

/-!
# Adaptive conditional encoding risk

The complete one-query inequality lifts through an arbitrary computation handled by the lazy
random oracle. Only fresh hash queries spend one unit of the query budget.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

set_option maxRecDepth 100000

/-- The total encoding potential, extended harmlessly to caches not known to be finite. All caches
reachable from the empty lazy random oracle cache are finite. -/
noncomputable def encodingSelectionAdaptivePotential
    (cache : QueryCache HashSpec) (secretKey : SecretKey) : ℝ≥0∞ :=
  open Classical in
    if hfinite : Finite cache then
      encodingSelectionTotalPotential cache hfinite secretKey
    else 0

theorem encodingSelectionAdaptivePotential_eq
    {cache : QueryCache HashSpec} (hfinite : Finite cache) (secretKey : SecretKey) :
    encodingSelectionAdaptivePotential cache secretKey =
      encodingSelectionTotalPotential cache hfinite secretKey := by
  rw [encodingSelectionAdaptivePotential, dif_pos hfinite]

@[simp] theorem encodingSelectionAdaptivePotential_empty (secretKey : SecretKey) :
    encodingSelectionAdaptivePotential ∅ secretKey = 0 := by
  rw [encodingSelectionAdaptivePotential_eq finite_empty]
  exact encodingSelectionTotalPotential_empty secretKey

theorem uniform_encodingSelectionAdaptivePotential_cacheQuery_sum_le
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput}
    (huncached : cache input = none) :
    (∑' answer : HashOutput,
      Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        encodingSelectionAdaptivePotential (cache.cacheQuery input answer) secretKey) ≤
      encodingSelectionAdaptivePotential cache secretKey +
        44 * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  simp_rw [encodingSelectionAdaptivePotential_eq
    (finite_cacheQuery hfinite input _)]
  rw [encodingSelectionAdaptivePotential_eq hfinite]
  exact uniform_encodingSelectionTotalPotential_cacheQuery_sum_le hfinite huncached

theorem expected_encodingSelectionAdaptivePotential_simulateQ_le
    {alpha : Type} (computation : OracleComp OracleWorld alpha) :
    ∀ (q : Nat), computation.IsQueryBoundP (· matches Sum.inr _) q →
      ∀ (cache : QueryCache HashSpec), Finite cache → ∀ secretKey : SecretKey,
        (∑' result,
          Pr[= result | (simulateQ romImpl computation).run cache] *
            encodingSelectionAdaptivePotential result.2 secretKey) ≤
          encodingSelectionAdaptivePotential cache secretKey +
            (44 * q : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro q _ cache _ secretKey
      simp [simulateQ_pure]
  | query_bind query next ih =>
      intro q hq cache hfinite secretKey
      rw [isQueryBoundP_query_bind_iff] at hq
      obtain ⟨hcan, hcont⟩ := hq
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      cases query with
      | inl input =>
          simp only [Bool.false_eq_true, if_false] at hcont
          have hrun : ((romImpl (Sum.inl input)).run cache
                >>= fun result => (simulateQ romImpl (next result.1)).run result.2) =
              (liftM (unifSpec.query input) : ProbComp _) >>= fun answer =>
                (simulateQ romImpl (next answer)).run cache := by
            simp [romImpl, unifFwdImpl, QueryImpl.liftTarget, HasQuery.toQueryImpl,
              StateT.run_monadLift, map_eq_bind_pure_comp, bind_assoc]
          rw [hrun, tsum_probOutput_bind_mul]
          calc
            _ ≤ ∑' answer,
                Pr[= answer | (liftM (unifSpec.query input) : ProbComp _)] *
                  (encodingSelectionAdaptivePotential cache secretKey +
                    (44 * q : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹) := by
              apply ENNReal.tsum_le_tsum
              intro answer
              exact mul_le_mul' le_rfl (ih answer q (hcont answer) cache hfinite secretKey)
            _ = _ := by
              rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
      | inr input =>
          simp only [if_true] at hcont
          have hq1 : 0 < q := by simpa using hcan
          obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
          simp only [Nat.add_sub_cancel] at hcont
          simp only [Nat.cast_add, Nat.cast_one]
          by_cases huncached : cache input = none
          · have hrun : ((romImpl (Sum.inr input)).run cache
                  >>= fun result => (simulateQ romImpl (next result.1)).run result.2) =
                ($ᵗ HashOutput : ProbComp HashOutput) >>= fun answer =>
                  (simulateQ romImpl (next answer)).run
                    (cache.cacheQuery input answer) := by
              have hro : (romImpl (Sum.inr input)).run cache =
                  ((uniformSampleImpl.withCaching : QueryImpl HashSpec _) input).run cache := rfl
              rw [hro, QueryImpl.withCaching_run_none _ huncached]
              simp [map_eq_bind_pure_comp, bind_assoc, uniformSampleImpl]
            rw [hrun, tsum_probOutput_bind_mul]
            calc
              _ ≤ ∑' answer : HashOutput,
                  Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                    (encodingSelectionAdaptivePotential (cache.cacheQuery input answer) secretKey +
                      (44 * q' : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹) := by
                apply ENNReal.tsum_le_tsum
                intro answer
                exact mul_le_mul' le_rfl
                  (ih answer q' (hcont answer) (cache.cacheQuery input answer)
                    (finite_cacheQuery hfinite input answer) secretKey)
              _ = (∑' answer : HashOutput,
                    Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                      encodingSelectionAdaptivePotential (cache.cacheQuery input answer) secretKey) +
                    (44 * q' : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
                simp_rw [mul_add]
                rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
                  tsum_probOutput_of_liftM_PMF, one_mul]
              _ ≤ (encodingSelectionAdaptivePotential cache secretKey +
                    44 * (Fintype.card Digest : ℝ≥0∞)⁻¹) +
                  (44 * q' : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ :=
                add_le_add
                  (uniform_encodingSelectionAdaptivePotential_cacheQuery_sum_le
                    hfinite huncached) le_rfl
              _ = encodingSelectionAdaptivePotential cache secretKey +
                    44 * ((q' : ℝ≥0∞) + 1) *
                      (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
                ring
          · obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp huncached
            have hrun : ((romImpl (Sum.inr input)).run cache
                  >>= fun result => (simulateQ romImpl (next result.1)).run result.2) =
                (simulateQ romImpl (next answer)).run cache := by
              have hro : (romImpl (Sum.inr input)).run cache =
                  ((uniformSampleImpl.withCaching : QueryImpl HashSpec _) input).run cache := rfl
              rw [hro, QueryImpl.withCaching_run_some _ hanswer]
              simp
            rw [hrun]
            exact (ih answer q' (hcont answer) cache hfinite secretKey).trans (by
              gcongr
              norm_num)

theorem probEvent_clean_encodingBad_simulateQ_le
    {alpha : Type} (computation : OracleComp OracleWorld alpha)
    (q : Nat) (hq : computation.IsQueryBoundP (· matches Sum.inr _) q)
    (secretKey : SecretKey) :
    Pr[fun result =>
        ¬Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret result.2 ∧
          EncodingBad result.2 secretKey |
      (simulateQ romImpl computation).run ∅] ≤
      (44 * q : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  classical
  rw [probEvent_eq_tsum_ite]
  calc
    _ ≤ ∑' result,
        Pr[= result | (simulateQ romImpl computation).run ∅] *
          encodingSelectionAdaptivePotential result.2 secretKey := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hevent :
          ¬Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret result.2 ∧
            EncodingBad result.2 secretKey
      · rw [if_pos hevent]
        by_cases hresult : result ∈ support ((simulateQ romImpl computation).run ∅)
        · have hfinite : Finite result.2 := Finite.of_enncard_le
            (simulateQ_romImpl_enncard_le_queryBound computation q hq result hresult)
          rw [encodingSelectionAdaptivePotential_eq hfinite,
            encodingSelectionTotalPotential_eq_one_of_clean_of_encodingBad
              hfinite hevent.1 hevent.2, mul_one]
        · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]
      · rw [if_neg hevent]
        exact bot_le
    _ ≤ encodingSelectionAdaptivePotential ∅ secretKey +
          (44 * q : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ :=
      expected_encodingSelectionAdaptivePotential_simulateQ_le computation q hq ∅
        finite_empty secretKey
    _ = _ := by simp

end SphincsSecurity.Concrete
