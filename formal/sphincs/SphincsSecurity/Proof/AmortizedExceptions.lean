import SphincsSecurity.Proof.Amortized

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

noncomputable def queryException
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (cache : QueryCache HashSpec) : (query : OracleWorld.Domain) → OracleWorld.Range query → Bool
  | .inl _, _ => false
  | .inr input, answer => by
      classical
      exact decide (cache input = none ∧ exception cache input answer)

noncomputable def runExceptionMonitor
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hit : Bool) :
    ProbComp ((α × QueryCache HashSpec) × Bool) :=
  OracleComp.construct
    (C := fun _ => QueryCache HashSpec → Bool → ProbComp ((α × QueryCache HashSpec) × Bool))
    (fun value cache hit => pure ((value, cache), hit))
    (fun query _ next cache hit => do
      let result ← (romImpl query).run cache
      next result.1 result.2 (hit || queryException exception cache query result.1))
    computation cache hit

theorem runExceptionMonitor_project
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hit : Bool) :
    Prod.fst <$> runExceptionMonitor exception computation cache hit = (simulateQ romImpl computation).run cache := by
  induction computation using OracleComp.inductionOn generalizing cache hit with
  | pure value => simp [runExceptionMonitor, simulateQ_pure]
  | query_bind query next ih =>
      rw [runExceptionMonitor, OracleComp.construct_query_bind, map_bind,
        simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact bind_congr fun result => ih result.1 result.2 _

theorem runExceptionMonitor_true
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    runExceptionMonitor exception computation cache true =
      (fun result => (result, true)) <$> (simulateQ romImpl computation).run cache := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp [runExceptionMonitor, simulateQ_pure]
  | query_bind query next ih =>
      rw [runExceptionMonitor, OracleComp.construct_query_bind, simulateQ_bind,
        simulateQ_spec_query, StateT.run_bind, map_bind]
      simp only [Bool.true_or]
      exact bind_congr fun result => ih result.1 result.2

theorem probEvent_bad_without_exception_le_amortized
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    {Bad Inv : QueryCache HashSpec → Prop} {potential : QueryCache HashSpec → Nat} {c : Nat} {ε : ℝ≥0∞}
    (hstep : ∀ target : Digest,
      Pr[fun answer => truncateHash answer = target | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ ε)
    (hinv : ∀ (cache : QueryCache HashSpec) (input : HashInput) (answer : HashOutput), Inv cache →
      Inv (cache.cacheQuery input answer))
    (hamortized : ∀ cache : QueryCache HashSpec, Inv cache → ¬ Bad cache → ∀ input : HashInput,
      cache input = none → ∃ targets : Finset Digest, targets.card ≤ potential cache + c ∧
        ∀ answer : HashOutput, ¬ exception cache input answer → truncateHash answer ∉ targets →
          ¬ Bad (cache.cacheQuery input answer) ∧
            potential (cache.cacheQuery input answer) + targets.card ≤ potential cache + c)
    (computation : OracleComp OracleWorld α) :
    ∀ q : Nat, computation.IsQueryBoundP (· matches Sum.inr _) q →
      ∀ cache : QueryCache HashSpec, Inv cache → ¬ Bad cache →
        Pr[fun result => Bad result.1.2 ∧ result.2 = false |
          runExceptionMonitor exception computation cache false] ≤
            ((c * q + potential cache : Nat) : ℝ≥0∞) * ε := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro q _ cache _ hclean
      simp [runExceptionMonitor, hclean]
  | query_bind query next ih =>
      intro q hq cache hinvCache hclean
      rw [isQueryBoundP_query_bind_iff] at hq
      obtain ⟨hcan, hcont⟩ := hq
      rw [runExceptionMonitor, OracleComp.construct_query_bind]
      simp only [Bool.false_or]
      change Pr[fun result => Bad result.1.2 ∧ result.2 = false |
        (romImpl query).run cache >>= fun result =>
          runExceptionMonitor exception (next result.1) result.2
            (queryException exception cache query result.1)] ≤ _
      cases query with
      | inl input =>
          simp only [Bool.false_eq_true, if_false] at hcont
          have hrun : ((romImpl (Sum.inl input)).run cache >>= fun result =>
              runExceptionMonitor exception (next result.1) result.2
                (queryException exception cache (.inl input) result.1)) =
              (liftM (unifSpec.query input) : ProbComp _) >>= fun answer =>
                runExceptionMonitor exception (next answer) cache false := by
            simp [romImpl, unifFwdImpl, QueryImpl.liftTarget, HasQuery.toQueryImpl,
              StateT.run_monadLift, map_eq_bind_pure_comp, bind_assoc, queryException]
          rw [hrun]
          exact probEvent_bind_le_of_forall_le fun answer _ =>
            ih answer q (hcont answer) cache hinvCache hclean
      | inr input =>
          simp only [if_true] at hcont
          have hq1 : 0 < q := by simpa using hcan
          obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
          simp only [Nat.add_sub_cancel] at hcont
          by_cases hfresh : cache input = none
          · obtain ⟨targets, hcard, htargets⟩ := hamortized cache hinvCache hclean input hfresh
            have hrun : ((romImpl (Sum.inr input)).run cache >>= fun result =>
                runExceptionMonitor exception (next result.1) result.2
                  (queryException exception cache (.inr input) result.1)) =
                ($ᵗ HashOutput : ProbComp HashOutput) >>= fun answer =>
                  runExceptionMonitor exception (next answer) (cache.cacheQuery input answer)
                    (decide (exception cache input answer)) := by
              have hro : (romImpl (Sum.inr input)).run cache =
                  ((uniformSampleImpl.withCaching : QueryImpl HashSpec _) input).run cache := rfl
              rw [hro, QueryImpl.withCaching_run_none _ hfresh]
              simp [map_eq_bind_pure_comp, bind_assoc, uniformSampleImpl, queryException, hfresh]
            rw [hrun]
            refine le_trans (probEvent_bind_le_add_of_forall_le
              (bad := fun answer => truncateHash answer ∈ targets)
              (c := ((c * q' + (potential cache + c - targets.card) : Nat) : ℝ≥0∞) * ε) ?_) ?_
            · intro answer hgood
              by_cases hexception : exception cache input answer
              · simp [hexception, runExceptionMonitor_true, probEvent_map, Function.comp_def]
              · simp only [hexception, decide_false]
                obtain ⟨hbad, hpotential⟩ := htargets answer hexception hgood
                exact le_trans (ih answer q' (hcont answer) _ (hinv cache input answer hinvCache) hbad)
                  (mul_le_mul_left (Nat.cast_le.mpr (by omega)) ε)
            · calc
                Pr[fun answer => truncateHash answer ∈ targets | ($ᵗ HashOutput : ProbComp HashOutput)] +
                    ((c * q' + (potential cache + c - targets.card) : Nat) : ℝ≥0∞) * ε ≤
                    (targets.card : ℝ≥0∞) * ε +
                      ((c * q' + (potential cache + c - targets.card) : Nat) : ℝ≥0∞) * ε :=
                  add_le_add (probEvent_mem_targets_le hstep targets) le_rfl
                _ = ((targets.card + (c * q' + (potential cache + c - targets.card)) : Nat) : ℝ≥0∞) * ε := by
                  push_cast
                  ring
                _ ≤ _ := mul_le_mul_left (Nat.cast_le.mpr (by rw [Nat.mul_succ]; omega)) ε
          · obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hfresh
            have hrun : ((romImpl (Sum.inr input)).run cache >>= fun result =>
                runExceptionMonitor exception (next result.1) result.2
                  (queryException exception cache (.inr input) result.1)) =
                runExceptionMonitor exception (next answer) cache false := by
              have hro : (romImpl (Sum.inr input)).run cache =
                  ((uniformSampleImpl.withCaching : QueryImpl HashSpec _) input).run cache := rfl
              rw [hro, QueryImpl.withCaching_run_some _ hanswer]
              simp [queryException, hfresh]
            rw [hrun]
            exact le_trans (ih answer q' (hcont answer) cache hinvCache hclean)
              (mul_le_mul_left (Nat.cast_le.mpr (by
                have : c * q' ≤ c * (q' + 1) := Nat.mul_le_mul_left c (by omega)
                omega)) ε)

theorem probEvent_le_bad_without_exception_add_residual
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (Bad : QueryCache HashSpec → Prop) (event : α × QueryCache HashSpec → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    Pr[event | (simulateQ romImpl computation).run cache] ≤
      Pr[fun result => Bad result.1.2 ∧ result.2 = false |
        runExceptionMonitor exception computation cache false] +
      Pr[fun result => event result.1 ∧ (result.2 = true ∨ ¬ Bad result.1.2) |
        runExceptionMonitor exception computation cache false] := by
  classical
  rw [← runExceptionMonitor_project exception computation cache false, probEvent_map]
  apply le_trans _ (probEvent_or_le _ _ _)
  apply probEvent_mono
  intro result _ hevent
  by_cases hbad : Bad result.1.2
  · cases result.2
    · exact Or.inl ⟨hbad, rfl⟩
    · exact Or.inr ⟨hevent, Or.inl rfl⟩
  · exact Or.inr ⟨hevent, Or.inr hbad⟩

theorem probEvent_bad_le_amortized_add_exception
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    {Bad Inv : QueryCache HashSpec → Prop} {potential : QueryCache HashSpec → Nat} {c : Nat} {ε : ℝ≥0∞}
    (hstep : ∀ target : Digest,
      Pr[fun answer => truncateHash answer = target | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ ε)
    (hinv : ∀ (cache : QueryCache HashSpec) (input : HashInput) (answer : HashOutput), Inv cache →
      Inv (cache.cacheQuery input answer))
    (hamortized : ∀ cache : QueryCache HashSpec, Inv cache → ¬ Bad cache → ∀ input : HashInput,
      cache input = none → ∃ targets : Finset Digest, targets.card ≤ potential cache + c ∧
        ∀ answer : HashOutput, ¬ exception cache input answer → truncateHash answer ∉ targets →
          ¬ Bad (cache.cacheQuery input answer) ∧
            potential (cache.cacheQuery input answer) + targets.card ≤ potential cache + c)
    (computation : OracleComp OracleWorld α) (q : Nat)
    (hq : computation.IsQueryBoundP (· matches Sum.inr _) q)
    (cache : QueryCache HashSpec) (hinvCache : Inv cache) (hclean : ¬ Bad cache) :
    Pr[fun result => Bad result.2 | (simulateQ romImpl computation).run cache] ≤
      ((c * q + potential cache : Nat) : ℝ≥0∞) * ε +
        Pr[fun result => result.2 = true | runExceptionMonitor exception computation cache false] := by
  rw [← runExceptionMonitor_project exception computation cache false, probEvent_map]
  apply le_trans _ (add_le_add
    (probEvent_bad_without_exception_le_amortized exception hstep hinv hamortized computation q hq cache hinvCache hclean) le_rfl)
  apply le_trans _ (probEvent_or_le _ _ _)
  apply probEvent_mono
  intro result _ hbad
  cases result.2
  · exact Or.inl ⟨hbad, rfl⟩
  · exact Or.inr rfl

end SphincsSecurity
