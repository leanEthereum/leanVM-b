import SphincsSecurity.Proof.FirstExceptionMonitor

namespace SphincsSecurity

open OracleComp OracleSpec

def worldHashQueryCost : OracleWorld.Domain → Nat
  | .inl _ => 0
  | .inr _ => 1

inductive ExceptionFreePrefix {α : Type}
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) :
    OracleComp OracleWorld α → QueryCache HashSpec → Nat →
      OracleComp OracleWorld α → QueryCache HashSpec → Prop where
  | refl (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
      ExceptionFreePrefix exception computation cache 0 computation cache
  | step (query : OracleWorld.Domain) (next : OracleWorld.Range query → OracleComp OracleWorld α)
      (cache : QueryCache HashSpec) (response : OracleWorld.Range query × QueryCache HashSpec)
      (spent : Nat) (suffix : OracleComp OracleWorld α) (suffixCache : QueryCache HashSpec)
      (hsupport : response ∈ support ((romImpl query).run cache))
      (hclean : queryException exception cache query response.1 = false)
      (htail : ExceptionFreePrefix exception (next response.1) response.2 spent suffix suffixCache) :
      ExceptionFreePrefix exception (OracleSpec.query query >>= next) cache
        (worldHashQueryCost query + spent) suffix suffixCache

theorem ExceptionFreePrefix.cache_le
    {exception : QueryCache HashSpec → HashInput → HashOutput → Prop}
    {computation suffix : OracleComp OracleWorld α} {cache suffixCache : QueryCache HashSpec} {spent : Nat}
    (h : ExceptionFreePrefix exception computation cache spent suffix suffixCache) : cache ≤ suffixCache := by
  induction h with
  | refl => exact le_rfl
  | step query next cache response spent suffix suffixCache hsupport hclean htail ih =>
      exact (simulateQ_romImpl_cache_le (OracleSpec.query query) cache response
        (by simpa only [simulateQ_spec_query] using hsupport)).trans ih

theorem ExceptionFreePrefix.queryBudget
    {exception : QueryCache HashSpec → HashInput → HashOutput → Prop}
    {computation suffix : OracleComp OracleWorld α} {cache suffixCache : QueryCache HashSpec} {spent : Nat}
    (h : ExceptionFreePrefix exception computation cache spent suffix suffixCache)
    (q : Nat) (hq : computation.IsQueryBoundP (· matches Sum.inr _) q) :
    ∃ remaining, spent + remaining = q ∧ suffix.IsQueryBoundP (· matches Sum.inr _) remaining := by
  induction h generalizing q with
  | refl computation cache => exact ⟨q, by omega, hq⟩
  | step query next cache response spent suffix suffixCache hsupport hclean htail ih =>
      rw [isQueryBoundP_query_bind_iff] at hq
      obtain ⟨hcan, hnext⟩ := hq
      obtain ⟨remaining, hremaining, hbound⟩ := ih _ (hnext response.1)
      refine ⟨remaining, ?_, hbound⟩
      cases query <;> simp_all [worldHashQueryCost]
      omega

theorem recordQueryException_eq_none_of_no_exception
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (cache : QueryCache HashSpec) (query : OracleWorld.Domain) (answer : OracleWorld.Range query)
    (hclean : queryException exception cache query answer = false) :
    recordQueryException exception cache query answer = none := by
  cases query with
  | inl sample => rfl
  | inr input => simp [recordQueryException, hclean]

theorem firstExceptionRecord_split
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp OracleWorld α) (initialCache : QueryCache HashSpec)
    (result : α × QueryCache HashSpec) (record : ExceptionRecord)
    (hresult : (result, some record) ∈ support (runFirstException exception computation initialCache none)) :
    ∃ spent, ∃ next : HashOutput → OracleComp OracleWorld α,
      ExceptionFreePrefix exception computation initialCache spent
        ((liftM (OracleWorld.query (.inr record.input)) : OracleComp OracleWorld HashOutput) >>= next) record.cache ∧
      record.cache record.input = none ∧ exception record.cache record.input record.answer ∧
      result ∈ support ((simulateQ romImpl (next record.answer)).run
        (record.cache.cacheQuery record.input record.answer)) := by
  classical
  induction computation using OracleComp.inductionOn generalizing initialCache with
  | pure value =>
      simp [runFirstException] at hresult
  | query_bind query next ih =>
      rw [runFirstException, OracleComp.construct_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨response, hresponse, hrest⟩ := hresult
      change (result, some record) ∈ support (runFirstException exception (next response.1) response.2
        (retainFirstException exception none initialCache query response.1)) at hrest
      simp only [retainFirstException] at hrest
      by_cases hfire : queryException exception initialCache query response.1 = true
      · cases query with
        | inl sample => simp [queryException] at hfire
        | inr input =>
            have hstep : initialCache input = none ∧ exception initialCache input response.1 := by
              simpa only [queryException, decide_eq_true_eq] using hfire
            rw [recordQueryException, if_pos hfire, runFirstException_some, support_map] at hrest
            obtain ⟨output, houtput, heq⟩ := hrest
            simp only [Prod.mk.injEq, Option.some.injEq] at heq
            obtain ⟨rfl, hrecord⟩ := heq
            subst record
            have hcache : response.2 = initialCache.cacheQuery input response.1 := by
              change response ∈ support ((randomOracle input).run initialCache) at hresponse
              rw [randomOracle, QueryImpl.withCaching_run_none _ hstep.1, support_map] at hresponse
              obtain ⟨answer, _, rfl⟩ := hresponse
              rfl
            exact ⟨0, next, .refl _ _, hstep.1, hstep.2, hcache ▸ houtput⟩
      · have hclean : queryException exception initialCache query response.1 = false := by
          cases h : queryException exception initialCache query response.1 <;> simp_all
        rw [recordQueryException_eq_none_of_no_exception exception initialCache query response.1 hclean] at hrest
        obtain ⟨spent, suffix, hprefix, hfresh, hexception, hsuffix⟩ := ih response.1 response.2 hrest
        exact ⟨_, suffix, .step query next initialCache response spent _ record.cache hresponse hclean hprefix,
          hfresh, hexception, hsuffix⟩

set_option backward.isDefEq.respectTransparency false in
theorem firstExceptionRecord_split_queryBudget
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp OracleWorld α) (initialCache : QueryCache HashSpec)
    (result : α × QueryCache HashSpec) (record : ExceptionRecord)
    (hresult : (result, some record) ∈ support (runFirstException exception computation initialCache none))
    (q : Nat) (hq : computation.IsQueryBoundP (· matches Sum.inr _) q) :
    ∃ spent remaining, ∃ next : HashOutput → OracleComp OracleWorld α,
      spent + 1 + remaining = q ∧
      ExceptionFreePrefix exception computation initialCache spent
        ((liftM (OracleWorld.query (.inr record.input)) : OracleComp OracleWorld HashOutput) >>= next) record.cache ∧
      record.cache record.input = none ∧ exception record.cache record.input record.answer ∧
      (next record.answer).IsQueryBoundP (· matches Sum.inr _) remaining ∧
      result ∈ support ((simulateQ romImpl (next record.answer)).run
        (record.cache.cacheQuery record.input record.answer)) := by
  obtain ⟨spent, next, hprefix, hfresh, hexception, hsuffix⟩ :=
    firstExceptionRecord_split exception computation initialCache result record hresult
  obtain ⟨suffixBudget, hbudget, hbound⟩ := hprefix.queryBudget q hq
  rw [isQueryBoundP_query_bind_iff] at hbound
  obtain ⟨hcan, hnext⟩ := hbound
  have hpositive : 0 < suffixBudget := by simpa using hcan
  refine ⟨spent, suffixBudget - 1, next, ?_, hprefix, hfresh, hexception, ?_, hsuffix⟩
  · omega
  · simpa using hnext record.answer

end SphincsSecurity
