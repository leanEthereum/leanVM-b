import SphincsSecurity.Proof.FirstExceptionMonitor
import SphincsSecurity.Proof.HashQueryCut

namespace SphincsSecurity

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

theorem firstExceptionRecord_hash_cut
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp HashSpec α) (initialCache : QueryCache HashSpec)
    (result : α × QueryCache HashSpec) (record : ExceptionRecord)
    (hresult : (result, some record) ∈ support
      (runFirstException exception (liftM computation) initialCache none)) :
    ∃ ordinal, ∃ next : HashOutput → OracleComp HashSpec α,
      (HashQueryCut.query record.input next, record.cache) ∈ support
        ((simulateQ (randomOracle : QueryImpl HashSpec _) (hashQueryCutAt computation ordinal)).run initialCache) := by
  induction computation using OracleComp.inductionOn generalizing initialCache with
  | pure value => simp [runFirstException] at hresult
  | query_bind input next ih =>
      change (result, some record) ∈ support (runFirstException exception
        ((liftM (OracleWorld.query (.inr input)) : OracleComp OracleWorld HashOutput) >>=
          fun answer => liftM (next answer)) initialCache none) at hresult
      rw [runFirstException, OracleComp.construct_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨response, hresponse, htail⟩ := hresult
      have hquery : response ∈ support ((randomOracle input).run initialCache) := hresponse
      by_cases hfire : queryException exception initialCache (.inr input) response.1 = true
      · have hsaved : retainFirstException exception none initialCache (.inr input) response.1 =
            some ⟨initialCache, input, response.1⟩ := by
          simp [retainFirstException, recordQueryException, hfire]
        change (result, some record) ∈ support (runFirstException exception (liftM (next response.1)) response.2
          (retainFirstException exception none initialCache (.inr input) response.1)) at htail
        rw [hsaved, runFirstException_some, support_map] at htail
        obtain ⟨output, _, heq⟩ := htail
        have hrecord : record = ⟨initialCache, input, response.1⟩ := by
          exact Option.some.inj (congrArg Prod.snd heq).symm
        subst record
        refine ⟨0, next, ?_⟩
        simp [hashQueryCutAt]
      · have hsaved : retainFirstException exception none initialCache (.inr input) response.1 = none := by
          simp [retainFirstException, recordQueryException, hfire]
        change (result, some record) ∈ support (runFirstException exception (liftM (next response.1)) response.2
          (retainFirstException exception none initialCache (.inr input) response.1)) at htail
        rw [hsaved] at htail
        obtain ⟨ordinal, continuation, hcut⟩ := ih response.1 response.2 htail
        refine ⟨ordinal + 1, continuation, ?_⟩
        rw [hashQueryCutAt, OracleComp.construct_query_bind]
        change (HashQueryCut.query record.input continuation, record.cache) ∈ support
          ((randomOracle input).run initialCache >>= fun response =>
            (simulateQ (randomOracle : QueryImpl HashSpec _)
              (hashQueryCutAt (next response.1) ordinal)).run response.2)
        rw [mem_support_bind_iff]
        exact ⟨response, hquery, hcut⟩

end SphincsSecurity
