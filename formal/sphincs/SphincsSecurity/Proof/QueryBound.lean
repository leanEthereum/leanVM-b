import SphincsSecurity.Proof.Guess

/-!
# Charging one query at a time

The tool every strategy's bound instantiates: if an event needs some oracle answer to satisfy a
predicate fixed at its input, and one fresh answer satisfies it with probability at most `eps`, then
a computation making at most `q` hash queries produces such an answer with probability at most
`q * eps`.

The cache is what the statement talks about, since it is the random oracle's own state: a hit is an
entry whose answer satisfies the predicate at its input. A repeated query cannot add a hit, so
counting every query rather than every distinct one only weakens the bound.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

/-- A bound on a bind bounds each continuation. VCVio composes bounds, `n` then `m` giving `n + m`;
what the reduction needs is the other direction, to bound what runs after key generation by what
bounds the whole game. -/
theorem isQueryBoundP_of_bind {α β : Type} {oa : OracleComp OracleWorld α}
    {k : α → OracleComp OracleWorld β} {q : Nat}
    (h : IsQueryBoundP (oa >>= k) (· matches Sum.inr _) q) :
    ∀ x ∈ support oa, IsQueryBoundP (k x) (· matches Sum.inr _) q := by
  induction oa using OracleComp.inductionOn generalizing q with
  | pure x =>
      intro x' hx'
      simp only [support_pure, Set.mem_singleton_iff] at hx'
      subst hx'
      simpa using h
  | query_bind t mx ih =>
      intro x hx
      rw [bind_assoc, isQueryBoundP_query_bind_iff] at h
      obtain ⟨u, hu⟩ := (mem_support_bind_iff _ _ _).mp hx
      exact (ih u (h.2 u) x hu.2).mono (by split_ifs <;> omega)

/-- A query bound on a bind bounds its left-hand computation. -/
theorem IsQueryBoundP.of_bind_left {ι : Type} {spec : OracleSpec ι}
    {α β : Type} {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {p : ι → Prop} [DecidablePred p] {n : Nat}
    (h : IsQueryBoundP (oa >>= ob) p n) : IsQueryBoundP oa p n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure _ => trivial
  | query_bind input continuation ih =>
      rw [bind_assoc, isQueryBoundP_query_bind_iff] at h
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨h.1, fun output => ih output (h.2 output)⟩

/-- A predicate query bound controls the matching entries of every logging trace. -/
theorem queryLog_countQ_le_of_mem_support_run_simulateQ
    {ι : Type} {spec : OracleSpec.{0, 0} ι}
    [spec.DecidableEq] [IsUniformSpec spec] {α : Type}
    {oa : OracleComp spec α} {p : ι → Prop} [DecidablePred p] {n : Nat}
    (hbound : IsQueryBoundP oa p n)
    {z : α × QueryLog spec}
    (hz : z ∈ support ((simulateQ loggingOracle oa).run)) :
    z.2.countQ p ≤ n := by
  induction oa using OracleComp.inductionOn generalizing n z with
  | pure x =>
      simp only [simulateQ_pure] at hz
      subst hz
      simp [QueryLog.countQ]
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      obtain ⟨hcan, hrest⟩ := hbound
      rw [run_simulateQ_loggingOracle_query_bind, support_bind] at hz
      simp only [Set.mem_iUnion, support_map] at hz
      obtain ⟨u, _, z', hz', rfl⟩ := hz
      have htail := ih u (hrest u) hz'
      by_cases ht : p t
      · have hn : 0 < n := by simpa [ht] using hcan
        simp only [ht, if_true] at htail
        change z'.2.countQ p ≤ n - 1 at htail
        rw [QueryLog.countQ] at htail
        simp only [QueryLog.countQ, QueryLog.getQ_cons, ht, if_true, List.length_cons]
        omega
      · simpa [QueryLog.countQ, QueryLog.getQ_cons, ht] using htail

/-- The cache holds an answer satisfying `P` at its input. -/
def CacheHit (P : HashInput → HashOutput → Prop) (cache : QueryCache HashSpec) : Prop :=
  ∃ input answer, cache input = some answer ∧ P input answer

/-- Caching a fresh answer adds a hit exactly when that answer is one. The freshness matters: an
answer written over an existing entry could remove a hit instead, and the run only ever caches what
it did not find. -/
theorem cacheHit_cacheQuery_iff (P : HashInput → HashOutput → Prop)
    (cache : QueryCache HashSpec) (input : HashInput) (answer : HashOutput)
    (huncached : cache input = none) :
    CacheHit P (cache.cacheQuery input answer) ↔ P input answer ∨ CacheHit P cache := by
  classical
  constructor
  · rintro ⟨input', answer', hlookup, hP⟩
    by_cases hsame : input' = input
    · subst hsame
      rw [QueryCache.cacheQuery_self] at hlookup
      have hanswer := Option.some.inj hlookup
      subst hanswer
      exact Or.inl hP
    · exact Or.inr ⟨input', answer', by rwa [QueryCache.cacheQuery_of_ne _ _ hsame] at hlookup, hP⟩
  · rintro (hP | ⟨input', answer', hlookup, hP'⟩)
    · exact ⟨input, answer, QueryCache.cacheQuery_self _ _ _, hP⟩
    · have hsame : input' ≠ input := by
        intro heq
        rw [heq, huncached] at hlookup
        simp at hlookup
      exact ⟨input', answer', by rwa [QueryCache.cacheQuery_of_ne _ _ hsame], hP'⟩

/-- Split a bind on an exceptional set: outside it every branch is bounded, inside it anything can
happen, so the whole bind costs the exception plus the bound. -/
theorem probEvent_bind_le_add_of_forall_le {α β : Type} {mx : ProbComp α} {f : α → ProbComp β}
    {E : β → Prop} {bad : α → Prop} {c : ℝ≥0∞} (h : ∀ x, ¬ bad x → Pr[E | f x] ≤ c) :
    Pr[E | mx >>= f] ≤ Pr[bad | mx] + c := by
  classical
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  calc ∑' x, Pr[= x | mx] * Pr[E | f x]
      ≤ ∑' x, (Pr[= x | mx] * (if bad x then 1 else 0) + Pr[= x | mx] * c) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hbad : bad x
        · simp only [hbad, if_true]
          exact le_add_right (mul_le_mul' le_rfl probEvent_le_one)
        · simp only [hbad, if_false]
          exact le_add_left (mul_le_mul' le_rfl (h x hbad))
    _ = (∑' x, Pr[= x | mx] * (if bad x then 1 else 0)) + ∑' x, Pr[= x | mx] * c :=
        ENNReal.tsum_add
    _ ≤ (∑' x, if bad x then Pr[= x | mx] else 0) + c := by
        refine add_le_add (ENNReal.tsum_le_tsum fun x => ?_) ?_
        · by_cases hbad : bad x <;> simp [hbad]
        · rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left zero_le tsum_probOutput_le_one

theorem probEvent_cacheHit_le {P : HashInput → HashOutput → Prop} {ε : ℝ≥0∞}
    (hstep : ∀ input, Pr[fun answer => P input answer | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ ε)
    {α : Type} (oa : OracleComp OracleWorld α) :
    ∀ (q : Nat), oa.IsQueryBoundP (· matches Sum.inr _) q →
      ∀ (cache : QueryCache HashSpec), ¬ CacheHit P cache →
        Pr[fun result => CacheHit P result.2 | (simulateQ romImpl oa).run cache] ≤ q * ε := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro q _ cache hclean
      simp [hclean]
  | query_bind t k ih =>
      intro q hq cache hclean
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
          exact probEvent_bind_le_of_forall_le fun u _ => ih u q (hcont u) cache hclean
      | inr input =>
          simp only [if_true] at hcont
          have hq1 : 0 < q := by simpa using hcan
          obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
          simp only [Nat.add_sub_cancel] at hcont
          have hshrink : (q' : ℝ≥0∞) * ε + ε = ((q' + 1 : Nat) : ℝ≥0∞) * ε := by
            push_cast
            ring
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
            refine le_trans (probEvent_bind_le_add_of_forall_le
              (bad := fun answer => P input answer) (c := (q' : ℝ≥0∞) * ε) ?_) ?_
            · intro answer hanswer
              refine ih answer q' (hcont answer) _ ?_
              rw [cacheHit_cacheQuery_iff P cache input answer hcached]
              exact fun hhit => hhit.elim hanswer hclean
            · calc Pr[fun answer => P input answer | ($ᵗ HashOutput : ProbComp HashOutput)]
                    + (q' : ℝ≥0∞) * ε
                  ≤ ε + (q' : ℝ≥0∞) * ε := add_le_add (hstep input) le_rfl
                _ = ((q' + 1 : Nat) : ℝ≥0∞) * ε := by rw [add_comm]; exact hshrink
          · obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hcached
            have hrun : ((romImpl (Sum.inr input)).run cache
                  >>= fun p => (simulateQ romImpl (k p.1)).run p.2)
                = (simulateQ romImpl (k answer)).run cache := by
              have hro : (romImpl (Sum.inr input)).run cache
                  = ((uniformSampleImpl.withCaching : QueryImpl HashSpec _) input).run cache := rfl
              rw [hro, QueryImpl.withCaching_run_some _ hanswer]
              simp
            rw [hrun]
            refine le_trans (ih answer q' (hcont answer) cache hclean) ?_
            exact mul_le_mul_left (by exact_mod_cast Nat.le_succ q') ε

/-- **The union bound, at the digest length.** A computation making at most `q` hash queries lands
an answer on its target with probability at most `q * 2^-n`, whatever target each input is assigned.
Every strategy the specification accounts for is an instance: domain separation fixes which position
a query bears on, so the target is a function of the input alone. -/
theorem probEvent_cacheHit_target_le {α : Type} (target : HashInput → Digest)
    (oa : OracleComp OracleWorld α) (q : Nat)
    (hq : oa.IsQueryBoundP (· matches Sum.inr _) q) (cache : QueryCache HashSpec)
    (hclean : ¬ CacheHit (fun input answer => truncateHash answer = target input) cache) :
    Pr[fun result => CacheHit (fun input answer => truncateHash answer = target input) result.2
      | (simulateQ romImpl oa).run cache] ≤ q * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  refine probEvent_cacheHit_le (fun input => ?_) oa q hq cache hclean
  rw [← probOutput_map]
  exact probOutput_truncateHash_le (target input)

end SphincsSecurity
