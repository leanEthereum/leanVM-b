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
theorem pending_cacheQuery_of_self
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

/-- A fresh answer keeps the cache clean when it misses the pairs this query would settle: the ones
pointing at it if it is honest, and its own partner's value if it is not. -/
theorem not_pairHit_cacheQuery
    (huncached : cache input = none) (hclean : ¬ PairHit partner cache)
    (hsettle : ∀ x ax, cache x = some ax → partner x = input → x ≠ input →
      truncateHash answer ≠ truncateHash ax)
    (hopen : ∀ ay, cache (partner input) = some ay → partner input ≠ input →
      truncateHash answer ≠ truncateHash ay) :
    ¬ PairHit partner (cache.cacheQuery input answer) := by
  classical
  rintro ⟨x, ax, ay, hx, hpartner, hne, hcollide⟩
  by_cases hxeq : x = input
  · subst hxeq
    rw [QueryCache.cacheQuery_self] at hx
    have hax : ax = answer := (Option.some.inj hx).symm
    subst hax
    rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hne)] at hpartner
    exact hopen ay hpartner (Ne.symm hne) hcollide
  · rw [QueryCache.cacheQuery_of_ne _ _ hxeq] at hx
    by_cases hpeq : partner x = input
    · rw [hpeq, QueryCache.cacheQuery_self] at hpartner
      have hay : ay = answer := (Option.some.inj hpartner).symm
      subst hay
      exact hsettle x ax hx hpeq hxeq hcollide.symm
    · rw [QueryCache.cacheQuery_of_ne _ _ hpeq] at hpartner
      exact hclean ⟨x, ax, ay, hx, hpartner, hne, hcollide⟩

end Pending

/-- **The pair bound.** A computation making at most `q` hash queries leaves a cache holding a
collided pair with probability at most `q * eps`, the pairs being at most one per query. -/
theorem probEvent_pairHit_le {ε : ℝ≥0∞}
    (hstep : ∀ target : Digest,
      Pr[fun answer => truncateHash answer = target | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ ε)
    (hidem : ∀ x, partner (partner x) = partner x)
    {α : Type} (oa : OracleComp OracleWorld α) :
    ∀ (q : Nat), oa.IsQueryBoundP (· matches Sum.inr _) q →
      ∀ (cache : QueryCache HashSpec) (domain : Finset HashInput),
        (∀ x, cache x ≠ none → x ∈ domain) → ¬ PairHit partner cache →
        Pr[fun result => PairHit partner result.2 | (simulateQ romImpl oa).run cache]
          ≤ ((q : ℝ≥0∞) + ((pending partner domain cache).card : ℝ≥0∞)) * ε := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro q _ cache domain _ hclean
      simp [hclean]
  | query_bind t k ih =>
      intro q hq cache domain hdomain hclean
      rw [isQueryBoundP_query_bind_iff] at hq
      obtain ⟨hcan, hcont⟩ := hq
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      cases t with
      | inl i =>
          simp only [Bool.false_eq_true, if_false] at hcont
          have hrun : ((romImpl (Sum.inl i)).run cache
                >>= fun p => (simulateQ romImpl (k p.1)).run p.2)
              = (liftM (unifSpec.query i) : ProbComp _)
                  >>= fun u => (simulateQ romImpl (k u)).run cache := by
            simp [romImpl, unifFwdImpl, QueryImpl.liftTarget, HasQuery.toQueryImpl,
              StateT.run_monadLift, map_eq_bind_pure_comp, bind_assoc]
          rw [hrun]
          exact probEvent_bind_le_of_forall_le fun u _ =>
            ih u q (hcont u) cache domain hdomain hclean
      | inr input =>
          simp only [if_true] at hcont
          have hq1 : 0 < q := by simpa using hcan
          obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
          simp only [Nat.add_sub_cancel] at hcont
          have hmono : ∀ n : Nat, ((n : ℝ≥0∞) + ((pending partner domain cache).card : ℝ≥0∞)) * ε
              ≤ (((q' + 1 : Nat) : ℝ≥0∞) + ((pending partner domain cache).card : ℝ≥0∞)) * ε
              → True := fun _ _ => trivial
          by_cases hcached : cache input = none
          · have hrun : ((romImpl (Sum.inr input)).run cache
                  >>= fun p => (simulateQ romImpl (k p.1)).run p.2)
                = ($ᵗ HashOutput : ProbComp HashOutput) >>= fun answer =>
                    (simulateQ romImpl (k answer)).run (cache.cacheQuery input answer) := by
              have hro : (romImpl (Sum.inr input)).run cache
                  = ((uniformSampleImpl.withCaching : QueryImpl HashSpec _) input).run cache := rfl
              rw [hro, QueryImpl.withCaching_run_none _ hcached]
              simp [map_eq_bind_pure_comp, bind_assoc, uniformSampleImpl]
            rw [hrun]
            have hdomain' : ∀ answer : HashOutput, ∀ x,
                (cache.cacheQuery input answer) x ≠ none → x ∈ insert input domain := by
              intro answer x hx
              by_cases hxeq : x = input
              · exact hxeq ▸ Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem
                  (hdomain x (by rwa [QueryCache.cacheQuery_of_ne _ _ hxeq] at hx))
            by_cases hself : partner input = input
            · -- an honest input settles the pairs pointing at it
              set settled := (pending partner domain cache).filter fun x => partner x = input
                with hsettledDef
              have hsub : settled ⊆ pending partner domain cache := Finset.filter_subset _ _
              have hcards : settled.card ≤ (pending partner domain cache).card :=
                Finset.card_le_card hsub
              refine le_trans (probEvent_bind_le_add_of_forall_le
                (bad := fun answer => ∃ x ∈ settled,
                  truncateHash answer = truncateHash ((cache x).getD 0))
                (c := ((q' : ℝ≥0∞)
                  + (((pending partner domain cache).card - settled.card : Nat) : ℝ≥0∞)) * ε)
                ?_) ?_
              · intro answer hgood
                have hclean' : ¬ PairHit partner (cache.cacheQuery input answer) := by
                  refine not_pairHit_cacheQuery partner hcached hclean ?_ ?_
                  · intro x ax hx hpx hxne hcollide
                    refine hgood ⟨x, ?_, ?_⟩
                    · rw [hsettledDef]
                      simp only [Finset.mem_filter, pending, Finset.mem_filter]
                      exact ⟨⟨hdomain x (by rw [hx]; simp), by rw [hx]; simp,
                        by rwa [hpx], fun heq => hxne (heq.trans hpx)⟩, hpx⟩
                    · rw [hx]
                      simpa using hcollide
                  · intro ay hay hne
                    exact absurd hself hne
                have hpending' : pending partner (insert input domain)
                      (cache.cacheQuery input answer)
                    = pending partner domain cache \ settled := by
                  rw [pending_cacheQuery_of_self partner hcached hself, hsettledDef]
                  ext y
                  simp only [Finset.mem_filter, Finset.mem_sdiff]
                  tauto
                refine le_trans (ih answer q' (hcont answer) _ (insert input domain)
                  (hdomain' answer) hclean') ?_
                rw [hpending', Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
              · have hbad : Pr[fun answer => ∃ x ∈ settled,
                      truncateHash answer = truncateHash ((cache x).getD 0)
                    | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ (settled.card : ℝ≥0∞) * ε :=
                  probEvent_exists_truncate_le hstep settled
                calc Pr[fun answer => ∃ x ∈ settled,
                        truncateHash answer = truncateHash ((cache x).getD 0)
                      | ($ᵗ HashOutput : ProbComp HashOutput)]
                      + ((q' : ℝ≥0∞)
                        + (((pending partner domain cache).card - settled.card : Nat) : ℝ≥0∞)) * ε
                    ≤ (settled.card : ℝ≥0∞) * ε
                      + ((q' : ℝ≥0∞)
                        + (((pending partner domain cache).card - settled.card : Nat) : ℝ≥0∞)) * ε :=
                      add_le_add hbad le_rfl
                  _ = ((settled.card + (q' + ((pending partner domain cache).card
                        - settled.card)) : Nat) : ℝ≥0∞) * ε := by push_cast; ring
                  _ = (((q' + (pending partner domain cache).card : Nat) : ℝ≥0∞)) * ε := by
                      congr 2
                      omega
                  _ ≤ (((q' + 1 : Nat) : ℝ≥0∞)
                        + ((pending partner domain cache).card : ℝ≥0∞)) * ε := by
                      gcongr
                      push_cast
                      exact add_le_add (le_add_right le_rfl) le_rfl
            · by_cases hpartnerCached : cache (partner input) = none
              · -- a non-honest input with an uncached partner opens one pair and settles none
                have hbound : ∀ answer : HashOutput,
                    Pr[fun result => PairHit partner result.2
                      | (simulateQ romImpl (k answer)).run (cache.cacheQuery input answer)]
                      ≤ ((q' : ℝ≥0∞)
                        + (((pending partner domain cache).card + 1 : Nat) : ℝ≥0∞)) * ε := by
                  intro answer
                  refine le_trans (ih answer q' (hcont answer) _ (insert input domain)
                    (hdomain' answer) (not_pairHit_cacheQuery partner hcached hclean
                      (fun x ax hx hpx hxne => absurd (by rw [← hpx, hidem]) hself)
                      (fun ay hay _ => absurd hay (by rw [hpartnerCached]; simp))))
                    (le_of_eq ?_)
                  rw [pending_cacheQuery_of_partner_uncached partner hidem hcached hself
                    hpartnerCached, Finset.card_insert_of_notMem (by
                      simp only [pending, Finset.mem_filter]
                      exact fun hmem => hmem.2.1 hcached)]
                refine le_trans (probEvent_bind_le_of_forall_le fun answer _ => hbound answer)
                  (le_of_eq ?_)
                push_cast
                ring
              · -- a non-honest input with a cached partner settles its own pair
                obtain ⟨ay, hay⟩ := Option.ne_none_iff_exists'.mp hpartnerCached
                refine le_trans (probEvent_bind_le_add_of_forall_le
                  (bad := fun answer => truncateHash answer = truncateHash ay)
                  (c := ((q' : ℝ≥0∞) + ((pending partner domain cache).card : ℝ≥0∞)) * ε) ?_) ?_
                · intro answer hgood
                  refine le_trans (ih answer q' (hcont answer) _ (insert input domain)
                    (hdomain' answer) (not_pairHit_cacheQuery partner hcached hclean
                      (fun x ax hx hpx hxne => absurd (by rw [← hpx, hidem]) hself)
                      (fun ay' hay' _ => by rw [hay] at hay'; exact (Option.some.inj hay') ▸ hgood)))
                    (le_of_eq (by
                      rw [pending_cacheQuery_of_partner_cached partner hidem hcached hself
                        hpartnerCached]))
                · calc Pr[fun answer => truncateHash answer = truncateHash ay
                        | ($ᵗ HashOutput : ProbComp HashOutput)]
                        + ((q' : ℝ≥0∞) + ((pending partner domain cache).card : ℝ≥0∞)) * ε
                      ≤ ε + ((q' : ℝ≥0∞) + ((pending partner domain cache).card : ℝ≥0∞)) * ε :=
                        add_le_add (hstep _) le_rfl
                    _ = (((q' + 1 : Nat) : ℝ≥0∞)
                          + ((pending partner domain cache).card : ℝ≥0∞)) * ε := by
                        push_cast
                        ring
          · obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hcached
            have hrun : ((romImpl (Sum.inr input)).run cache
                  >>= fun p => (simulateQ romImpl (k p.1)).run p.2)
                = (simulateQ romImpl (k answer)).run cache := by
              have hro : (romImpl (Sum.inr input)).run cache
                  = ((uniformSampleImpl.withCaching : QueryImpl HashSpec _) input).run cache := rfl
              rw [hro, QueryImpl.withCaching_run_some _ hanswer]
              simp
            rw [hrun]
            refine le_trans (ih answer q' (hcont answer) cache domain hdomain hclean) ?_
            gcongr
            omega

end SphincsSecurity
