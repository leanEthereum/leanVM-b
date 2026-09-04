import SphincsSecurity.Proof.QueryBound

/-!
# The accounting, once and for all

Every per-query charge in the development has the same shape: a bad event on the random oracle's
cache, and a potential on caches that pays for the charges a query cannot pay for itself. A fresh
answer is dangerous only if it lands in a finite set of digests, and what that set costs is funded
by the potential the earlier queries built up, plus a constant per query.

That is ordinary amortized analysis, and it is the only probabilistic argument the reduction needs:
`probEvent_bad_le_amortized` takes the bad event, the potential and the constant, and returns
`(c * q + potential) * eps`. Everything else about a strategy, the hits it has to produce and how
many targets each fresh answer faces, is deterministic bookkeeping in the hypothesis.

The constant matters, since a factor `c` is `log2 c` bits off the claim: the honest value a query has
to hit may itself be undetermined when the query is made, and then the charge falls on the answer
that determines it, one per slot of the payload it lands in. That is what `c` pays for, and the
widest payload in the instance is the `v = 42` chain endpoints of a leaf.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

/-- One fresh answer lands in a finite set of digests with probability at most `|targets| * eps`. -/
theorem probEvent_mem_targets_le {ε : ℝ≥0∞}
    (hstep : ∀ target : Digest,
      Pr[fun answer => truncateHash answer = target | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ ε)
    (targets : Finset Digest) :
    Pr[fun answer => truncateHash answer ∈ targets | ($ᵗ HashOutput : ProbComp HashOutput)]
      ≤ (targets.card : ℝ≥0∞) * ε := by
  classical
  induction targets using Finset.induction with
  | empty => simp
  | insert a targets hnotMem ih =>
      calc Pr[fun answer => truncateHash answer ∈ insert a targets
              | ($ᵗ HashOutput : ProbComp HashOutput)]
          = Pr[fun answer => truncateHash answer = a ∨ truncateHash answer ∈ targets
              | ($ᵗ HashOutput : ProbComp HashOutput)] := by
            simp only [Finset.mem_insert]
        _ ≤ Pr[fun answer => truncateHash answer = a | ($ᵗ HashOutput : ProbComp HashOutput)]
              + Pr[fun answer => truncateHash answer ∈ targets
                  | ($ᵗ HashOutput : ProbComp HashOutput)] := probEvent_or_le _ _ _
        _ ≤ ε + (targets.card : ℝ≥0∞) * ε := add_le_add (hstep a) ih
        _ = ((insert a targets).card : ℝ≥0∞) * ε := by
            rw [Finset.card_insert_of_notMem hnotMem]
            push_cast
            ring

/-- **The accounting.** A computation making at most `q` hash queries leaves a bad cache with
probability at most `(c * q + potential) * eps`, whenever each fresh answer on an uncached input is
dangerous only inside a finite set of digests whose size the potential pays for, up to `c` per
query. -/
theorem probEvent_bad_le_amortized {Bad Inv : QueryCache HashSpec → Prop}
    {potential : QueryCache HashSpec → Nat} {c : Nat} {ε : ℝ≥0∞}
    (hstep : ∀ target : Digest,
      Pr[fun answer => truncateHash answer = target | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ ε)
    (hinv : ∀ (cache : QueryCache HashSpec) (input : HashInput) (answer : HashOutput), Inv cache →
      Inv (cache.cacheQuery input answer))
    (hamortized : ∀ cache : QueryCache HashSpec, Inv cache → ¬ Bad cache → ∀ input : HashInput,
      cache input = none → ∃ targets : Finset Digest, targets.card ≤ potential cache + c
        ∧ ∀ answer : HashOutput, truncateHash answer ∉ targets →
          ¬ Bad (cache.cacheQuery input answer)
            ∧ potential (cache.cacheQuery input answer) + targets.card ≤ potential cache + c)
    {α : Type} (oa : OracleComp OracleWorld α) :
    ∀ (q : Nat), oa.IsQueryBoundP (· matches Sum.inr _) q →
      ∀ cache : QueryCache HashSpec, Inv cache → ¬ Bad cache →
        Pr[fun result => Bad result.2 | (simulateQ romImpl oa).run cache]
          ≤ ((c * q + potential cache : Nat) : ℝ≥0∞) * ε := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro q _ cache _ hclean
      simp [hclean]
  | query_bind t k ih =>
      intro q hq cache hinvCache hclean
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
            ih u q (hcont u) cache hinvCache hclean
      | inr input =>
          simp only [if_true] at hcont
          have hq1 : 0 < q := by simpa using hcan
          obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
          simp only [Nat.add_sub_cancel] at hcont
          by_cases hcached : cache input = none
          · obtain ⟨targets, hcard, htargets⟩ := hamortized cache hinvCache hclean input hcached
            have hrun : ((romImpl (Sum.inr input)).run cache
                  >>= fun p => (simulateQ romImpl (k p.1)).run p.2)
                = ($ᵗ HashOutput : ProbComp HashOutput) >>= fun answer =>
                    (simulateQ romImpl (k answer)).run (cache.cacheQuery input answer) := by
              have hro : (romImpl (Sum.inr input)).run cache
                  = ((uniformSampleImpl.withCaching : QueryImpl HashSpec _) input).run cache := rfl
              rw [hro, QueryImpl.withCaching_run_none _ hcached]
              simp [map_eq_bind_pure_comp, bind_assoc, uniformSampleImpl]
            rw [hrun]
            refine le_trans (probEvent_bind_le_add_of_forall_le
              (bad := fun answer => truncateHash answer ∈ targets)
              (c := ((c * q' + (potential cache + c - targets.card) : Nat) : ℝ≥0∞) * ε) ?_) ?_
            · intro answer hgood
              obtain ⟨hbad, hpotential⟩ := htargets answer hgood
              exact le_trans (ih answer q' (hcont answer) _ (hinv cache input answer hinvCache) hbad)
                (mul_le_mul_left (Nat.cast_le.mpr (by omega)) ε)
            · calc Pr[fun answer => truncateHash answer ∈ targets
                      | ($ᵗ HashOutput : ProbComp HashOutput)]
                    + ((c * q' + (potential cache + c - targets.card) : Nat) : ℝ≥0∞) * ε
                  ≤ (targets.card : ℝ≥0∞) * ε
                      + ((c * q' + (potential cache + c - targets.card) : Nat) : ℝ≥0∞) * ε :=
                    add_le_add (probEvent_mem_targets_le hstep targets) le_rfl
                _ = ((targets.card + (c * q' + (potential cache + c - targets.card)) : Nat)
                      : ℝ≥0∞) * ε := by push_cast; ring
                _ ≤ ((c * (q' + 1) + potential cache : Nat) : ℝ≥0∞) * ε :=
                    mul_le_mul_left (Nat.cast_le.mpr (by rw [Nat.mul_succ]; omega)) ε
          · obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hcached
            have hrun : ((romImpl (Sum.inr input)).run cache
                  >>= fun p => (simulateQ romImpl (k p.1)).run p.2)
                = (simulateQ romImpl (k answer)).run cache := by
              have hro : (romImpl (Sum.inr input)).run cache
                  = ((uniformSampleImpl.withCaching : QueryImpl HashSpec _) input).run cache := rfl
              rw [hro, QueryImpl.withCaching_run_some _ hanswer]
              simp
            rw [hrun]
            exact le_trans (ih answer q' (hcont answer) cache hinvCache hclean)
              (mul_le_mul_left (Nat.cast_le.mpr (by
                have : c * q' ≤ c * (q' + 1) := Nat.mul_le_mul_left c (by omega)
                omega)) ε)

end SphincsSecurity
