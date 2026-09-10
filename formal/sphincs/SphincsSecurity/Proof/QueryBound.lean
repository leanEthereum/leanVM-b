import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Statement

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

end SphincsSecurity
