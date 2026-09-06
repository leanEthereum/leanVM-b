import SphincsSecurity.Proof.FirstExceptionPrefix
import SphincsSecurity.Proof.FirstParentSettlementGame

namespace SphincsSecurity

open OracleComp OracleSpec

theorem queryException_cleanParent_eq
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (cache : QueryCache HashSpec) (hclean : ¬ Bad parameter otsSecret ftsSecret cache)
    (query : OracleWorld.Domain) (answer : OracleWorld.Range query) :
    queryException (CleanParentSettlement parameter otsSecret ftsSecret) cache query answer =
      queryException (ParentSettlement parameter otsSecret ftsSecret) cache query answer := by
  cases query <;> simp [queryException, CleanParentSettlement, hclean]

theorem ExceptionFreePrefix.cleanParent_to_parent
    {parameter : PublicParameter}
    {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {computation suffix : OracleComp OracleWorld α} {cache suffixCache : QueryCache HashSpec} {spent : Nat}
    (h : ExceptionFreePrefix (CleanParentSettlement parameter otsSecret ftsSecret)
      computation cache spent suffix suffixCache)
    (hclean : ¬ Bad parameter otsSecret ftsSecret suffixCache) :
    ExceptionFreePrefix (ParentSettlement parameter otsSecret ftsSecret)
      computation cache spent suffix suffixCache := by
  induction h with
  | refl => exact .refl _ _
  | step query next cache response spent suffix suffixCache hsupport hnoException htail ih =>
      have hquery : cache ≤ response.2 := simulateQ_romImpl_cache_le (OracleSpec.query query) cache response
        (by simpa only [simulateQ_spec_query] using hsupport)
      have hbefore : ¬ Bad parameter otsSecret ftsSecret cache :=
        fun hbad => hclean (Bad.mono parameter otsSecret ftsSecret (hquery.trans htail.cache_le) hbad)
      rw [queryException_cleanParent_eq parameter otsSecret ftsSecret cache hbefore query response.1] at hnoException
      exact .step query next cache response spent suffix suffixCache hsupport hnoException (ih hclean)

namespace Concrete

theorem sampledFirstParentSettlementGame_record_clean (adversary : Adversary)
    {result : SampledSecrets × ((Bool × QueryCache HashSpec) × Option ExceptionRecord)}
    (hresult : result ∈ support (sampledFirstParentSettlementGame adversary))
    {record : ExceptionRecord} (hrecord : record ∈ result.2.2) :
    ¬ Bad result.1.parameter result.1.otsSecret result.1.ftsSecret record.cache :=
  (sampledFirstParentSettlementGame_record_valid adversary hresult hrecord).2.2.1.1

set_option backward.isDefEq.respectTransparency false in
theorem sampledFirstParentSettlementGame_record_split
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    {result : SampledSecrets × ((Bool × QueryCache HashSpec) × Option ExceptionRecord)}
    (hresult : result ∈ support (sampledFirstParentSettlementGame adversary))
    {record : ExceptionRecord} (hrecord : record ∈ result.2.2) :
    ∃ spent remaining, ∃ next : HashOutput → OracleComp OracleWorld Bool,
      spent + 1 + remaining = q ∧
      ExceptionFreePrefix (ParentSettlement result.1.parameter result.1.otsSecret result.1.ftsSecret)
        (gameAfterSecrets adversary result.1.parameter result.1.otsSecret result.1.ftsSecret) ∅ spent
        ((liftM (OracleWorld.query (.inr record.input)) : OracleComp OracleWorld HashOutput) >>= next) record.cache ∧
      record.cache record.input = none ∧
      ¬ Bad result.1.parameter result.1.otsSecret result.1.ftsSecret record.cache ∧
      ParentSettlement result.1.parameter result.1.otsSecret result.1.ftsSecret record.cache record.input record.answer ∧
      (next record.answer).IsQueryBoundP (· matches Sum.inr _) remaining ∧
      result.2.1 ∈ support ((simulateQ romImpl (next record.answer)).run
        (record.cache.cacheQuery record.input record.answer)) := by
  obtain ⟨hsecrets, hrun⟩ := sampledFirstParentSettlementGame_support adversary hresult
  obtain ⟨hparameter, hots, hfts⟩ := result.1.support_components hsecrets
  have hbound := isQueryBoundP_gameAfterSecrets adversary q hq hparameter hots hfts
  change result.2.2 = some record at hrecord
  have hrun' : (result.2.1, some record) ∈ support
      (runFirstException (CleanParentSettlement result.1.parameter result.1.otsSecret result.1.ftsSecret)
        (gameAfterSecrets adversary result.1.parameter result.1.otsSecret result.1.ftsSecret) ∅ none) := by
    simpa only [← hrecord] using hrun
  obtain ⟨spent, remaining, next, hbudget, hprefix, hfresh, hexception, hnext, hsuffix⟩ :=
    firstExceptionRecord_split_queryBudget _ _ _ _ record hrun' q hbound
  exact ⟨spent, remaining, next, hbudget, hprefix.cleanParent_to_parent hexception.1,
    hfresh, hexception.1, hexception.2, hnext, hsuffix⟩

end Concrete
end SphincsSecurity
