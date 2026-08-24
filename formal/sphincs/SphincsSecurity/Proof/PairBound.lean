import SphincsSecurity.Proof.QueryBound

/-!
# Charging a collision to the pair, not to the step

The extraction produces a *pair*: an input the adversary supplied and the honest input at the same
position, whose answers agree after truncation. Domain separation makes the partner unique, so the
pairs number at most `q`, and the bound is `q * eps`.

Charging `eps` per step, as `probEvent_cacheHit_le` does, is the wrong accounting here. When the
honest input is queried second, its fresh answer has to miss every value already queried at that
tweak, which costs `m * eps` at that one step. What is true is that the `m` pairs it settles were
each opened by an earlier query, so the run's total charge is still one `eps` per query. The
invariant below carries that: a budget of `q` for queries yet to come, plus one unit for every pair
already opened and not yet settled.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

variable (partner : HashInput → HashInput)

/-- The cache holds a pair: a non-honest input and its honest partner, agreeing after truncation. -/
def PairHit (cache : QueryCache HashSpec) : Prop :=
  ∃ x ax ay, cache x = some ax ∧ cache (partner x) = some ay ∧ x ≠ partner x
    ∧ truncateHash ax = truncateHash ay

/-- The pairs already opened and not yet settled: cached inputs, other than honest ones, whose
partner is still uncached. -/
noncomputable def pending (domain : Finset HashInput) (cache : QueryCache HashSpec) :
    Finset HashInput :=
  open Classical in
  domain.filter fun x => cache x ≠ none ∧ cache (partner x) = none ∧ x ≠ partner x

theorem pending_subset (domain : Finset HashInput) (cache : QueryCache HashSpec) :
    pending partner domain cache ⊆ domain := by
  classical
  exact Finset.filter_subset _ _

/-- One fresh answer misses a finite set of targets, at `eps` each. -/
theorem probEvent_exists_truncate_le {ε : ℝ≥0∞} {value : HashInput → Digest}
    (hstep : ∀ target : Digest,
      Pr[fun answer => truncateHash answer = target | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ ε)
    (targets : Finset HashInput) :
    Pr[fun answer => ∃ x ∈ targets, truncateHash answer = value x
      | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ (targets.card : ℝ≥0∞) * ε := by
  classical
  induction targets using Finset.induction with
  | empty => simp
  | insert a targets hnotMem ih =>
      calc Pr[fun answer => ∃ x ∈ insert a targets, truncateHash answer = value x
              | ($ᵗ HashOutput : ProbComp HashOutput)]
          = Pr[fun answer => truncateHash answer = value a
                ∨ ∃ x ∈ targets, truncateHash answer = value x
              | ($ᵗ HashOutput : ProbComp HashOutput)] := by
            simp only [Finset.mem_insert, exists_eq_or_imp]
        _ ≤ Pr[fun answer => truncateHash answer = value a | ($ᵗ HashOutput : ProbComp HashOutput)]
              + Pr[fun answer => ∃ x ∈ targets, truncateHash answer = value x
                  | ($ᵗ HashOutput : ProbComp HashOutput)] := probEvent_or_le _ _ _
        _ ≤ ε + (targets.card : ℝ≥0∞) * ε := add_le_add (hstep _) ih
        _ = ((insert a targets).card : ℝ≥0∞) * ε := by
            rw [Finset.card_insert_of_notMem hnotMem]
            push_cast
            ring

/-! ### How one fresh query changes the pending set

Three cases, and the idempotence of `partner` is what separates them: an honest input is its own
partner, so it can settle pairs but never open one, and a non-honest input can open one but never
settle any. -/

section Pending

variable {domain : Finset HashInput} {cache : QueryCache HashSpec} {input : HashInput}
  {answer : HashOutput}

/-- An honest input settles the pairs pointing at it and opens none. -/
theorem pending_cacheQuery_of_self (hidem : ∀ x, partner (partner x) = partner x)
    (huncached : cache input = none) (hself : partner input = input) :
    pending partner (insert input domain) (cache.cacheQuery input answer)
      = open Classical in (pending partner domain cache).filter fun x => partner x ≠ input := by
  classical
  ext y
  simp only [pending, Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hmem, hy, hpartner, hne⟩
    have hyne : y ≠ input := by
      intro heq
      subst heq
      exact hne hself.symm
    have hpartnerNe : partner y ≠ input := by
      intro heq
      rw [heq, QueryCache.cacheQuery_self] at hpartner
      simp at hpartner
    refine ⟨⟨hmem.resolve_left hyne, ?_, ?_, hne⟩, hpartnerNe⟩
    · rwa [QueryCache.cacheQuery_of_ne _ _ hyne] at hy
    · rwa [QueryCache.cacheQuery_of_ne _ _ hpartnerNe] at hpartner
  · rintro ⟨⟨hmem, hy, hpartner, hne⟩, hpartnerNe⟩
    have hyne : y ≠ input := by
      intro heq
      subst heq
      exact hy huncached
    exact ⟨Or.inr hmem, by rwa [QueryCache.cacheQuery_of_ne _ _ hyne],
      by rwa [QueryCache.cacheQuery_of_ne _ _ hpartnerNe], hne⟩

/-- A non-honest input whose partner is uncached opens exactly one pair. -/
theorem pending_cacheQuery_of_partner_uncached (hidem : ∀ x, partner (partner x) = partner x)
    (huncached : cache input = none) (hne : partner input ≠ input)
    (hpartnerUncached : cache (partner input) = none) :
    pending partner (insert input domain) (cache.cacheQuery input answer)
      = insert input (pending partner domain cache) := by
  classical
  have hnoSettle : ∀ y, partner y ≠ input := by
    intro y heq
    exact hne (by rw [← heq, hidem])
  ext y
  simp only [pending, Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hmem, hy, hpartner, hyne⟩
    by_cases hyeq : y = input
    · exact Or.inl hyeq
    · refine Or.inr ⟨hmem.resolve_left hyeq, ?_, ?_, hyne⟩
      · rwa [QueryCache.cacheQuery_of_ne _ _ hyeq] at hy
      · rwa [QueryCache.cacheQuery_of_ne _ _ (hnoSettle y)] at hpartner
  · rintro (heq | ⟨hmem, hy, hpartner, hyne⟩)
    · subst heq
      exact ⟨Or.inl rfl, by simp [QueryCache.cacheQuery_self],
        by rwa [QueryCache.cacheQuery_of_ne _ _ (hnoSettle y)], Ne.symm hne⟩
    · have hyeq : y ≠ input := fun heq => hy (heq ▸ huncached)
      exact ⟨Or.inr hmem, by rwa [QueryCache.cacheQuery_of_ne _ _ hyeq],
        by rwa [QueryCache.cacheQuery_of_ne _ _ (hnoSettle y)], hyne⟩

/-- A non-honest input whose partner is already cached changes nothing. -/
theorem pending_cacheQuery_of_partner_cached (hidem : ∀ x, partner (partner x) = partner x)
    (huncached : cache input = none) (hne : partner input ≠ input)
    (hpartnerCached : cache (partner input) ≠ none) :
    pending partner (insert input domain) (cache.cacheQuery input answer)
      = pending partner domain cache := by
  classical
  have hnoSettle : ∀ y, partner y ≠ input := by
    intro y heq
    exact hne (by rw [← heq, hidem])
  ext y
  simp only [pending, Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hmem, hy, hpartner, hyne⟩
    have hyne' : y ≠ input := by
      intro heq
      subst heq
      rw [QueryCache.cacheQuery_of_ne _ _ (hnoSettle y)] at hpartner
      exact hpartnerCached hpartner
    refine ⟨hmem.resolve_left hyne', ?_, ?_, hyne⟩
    · rwa [QueryCache.cacheQuery_of_ne _ _ hyne'] at hy
    · rwa [QueryCache.cacheQuery_of_ne _ _ (hnoSettle y)] at hpartner
  · rintro ⟨hmem, hy, hpartner, hyne⟩
    have hyne' : y ≠ input := by
      intro heq
      subst heq
      exact hy huncached
    exact ⟨Or.inr hmem, by rwa [QueryCache.cacheQuery_of_ne _ _ hyne'],
      by rwa [QueryCache.cacheQuery_of_ne _ _ (hnoSettle y)], hyne⟩

end Pending

end SphincsSecurity
