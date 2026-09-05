import SphincsSecurity.Proof.EncodingPrehitComposition

namespace SphincsSecurity.Concrete.TightEncoding

open OracleComp OracleSpec

theorem mem_support_simulateQ_of_mem_runEncodingPrehitMonitor
    (secretKey : SecretKey) (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hit : Bool) (result : (α × QueryCache HashSpec) × Bool)
    (hresult : result ∈ support (runEncodingPrehitMonitor secretKey computation cache hit)) :
    result.1 ∈ support ((simulateQ romImpl computation).run cache) := by
  rw [← runEncodingPrehitMonitor_project secretKey computation cache hit, support_map]
  exact ⟨result, hresult, rfl⟩

theorem cache_le_of_mem_runEncodingPrehitMonitor
    (secretKey : SecretKey) (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hit : Bool) (result : (α × QueryCache HashSpec) × Bool)
    (hresult : result ∈ support (runEncodingPrehitMonitor secretKey computation cache hit)) :
    cache ≤ result.1.2 :=
  simulateQ_romImpl_cache_le computation cache result.1
    (mem_support_simulateQ_of_mem_runEncodingPrehitMonitor secretKey computation cache hit result hresult)

theorem runEncodingPrehitMonitor_hit_of_mem_support (secretKey : SecretKey)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (result : (α × QueryCache HashSpec) × Bool)
    (hresult : result ∈ support (runEncodingPrehitMonitor secretKey computation cache true)) :
    result.2 = true := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      simpa only [runEncodingPrehitMonitor_pure, support_pure, Set.mem_singleton_iff] using
        congrArg Prod.snd (show result = ((value, cache), true) by
          simpa only [runEncodingPrehitMonitor_pure, support_pure, Set.mem_singleton_iff] using hresult)
  | query_bind query next ih =>
      rw [runEncodingPrehitMonitor, OracleComp.construct_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨response, _, hresult⟩ := hresult
      simp only [Bool.true_or] at hresult
      exact ih response.1 response.2 hresult

theorem runEncodingPrehitMonitor_initial_false_of_mem_support
    (secretKey : SecretKey) (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hit : Bool) (result : α × QueryCache HashSpec)
    (hresult : (result, false) ∈ support (runEncodingPrehitMonitor secretKey computation cache hit)) :
    hit = false := by
  cases hit with
  | false => rfl
  | true =>
      exact Bool.noConfusion (runEncodingPrehitMonitor_hit_of_mem_support secretKey computation cache (result, false) hresult)

theorem mem_support_runEncodingPrehitMonitor_bind_false_iff
    (secretKey : SecretKey) (computation : OracleComp OracleWorld α)
    (next : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec)
    (result : β × QueryCache HashSpec) :
    (result, false) ∈ support (runEncodingPrehitMonitor secretKey (computation >>= next) cache false) ↔
      ∃ middle : α × QueryCache HashSpec,
        (middle, false) ∈ support (runEncodingPrehitMonitor secretKey computation cache false) ∧
        (result, false) ∈ support (runEncodingPrehitMonitor secretKey (next middle.1) middle.2 false) := by
  rw [runEncodingPrehitMonitor_bind, mem_support_bind_iff]
  constructor
  · rintro ⟨⟨middle, hit⟩, hmiddle, hresult⟩
    have hfalse := runEncodingPrehitMonitor_initial_false_of_mem_support secretKey (next middle.1) middle.2 hit result hresult
    subst hit
    exact ⟨middle, hmiddle, hresult⟩
  · rintro ⟨middle, hmiddle, hresult⟩
    exact ⟨(middle, false), hmiddle, hresult⟩

theorem mem_support_runEncodingPrehitMonitor_query_bind_false_iff
    (secretKey : SecretKey) (query : OracleWorld.Domain)
    (next : OracleWorld.Range query → OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (result : α × QueryCache HashSpec) :
    (result, false) ∈ support (runEncodingPrehitMonitor secretKey (OracleWorld.query query >>= next) cache false) ↔
      ∃ response : OracleWorld.Range query × QueryCache HashSpec,
        response ∈ support ((romImpl query).run cache) ∧
        encodingPrehitQuery secretKey cache query response.1 = false ∧
        (result, false) ∈ support (runEncodingPrehitMonitor secretKey (next response.1) response.2 false) := by
  rw [runEncodingPrehitMonitor, OracleComp.construct_query_bind, mem_support_bind_iff]
  simp only [Bool.false_or]
  constructor
  · rintro ⟨response, hresponse, hresult⟩
    have hfalse := runEncodingPrehitMonitor_initial_false_of_mem_support secretKey (next response.1) response.2
      (encodingPrehitQuery secretKey cache query response.1) result hresult
    exact ⟨response, hresponse, hfalse, hfalse ▸ hresult⟩
  · rintro ⟨response, hresponse, hfalse, hresult⟩
    exact ⟨response, hresponse, hfalse.symm ▸ hresult⟩

theorem not_encodingMessagePrehit_of_mem_support_query_false
    (secretKey : SecretKey) (input : HashInput) (answer : HashOutput)
    (cache finalCache : QueryCache HashSpec) (hit : Bool) (hfresh : cache input = none)
    (hresult : ((answer, finalCache), false) ∈ support
      (runEncodingPrehitMonitor secretKey (OracleWorld.query (.inr input)) cache hit)) :
    ¬ EncodingMessagePrehit cache secretKey input answer := by
  rw [runEncodingPrehitMonitor_query, support_map] at hresult
  obtain ⟨response, _, heq⟩ := hresult
  obtain ⟨rfl, hflag⟩ := Prod.mk.inj heq
  have hfalse := (Bool.or_eq_false_iff.mp hflag).2
  simpa [encodingPrehitQuery, hfresh] using hfalse

end SphincsSecurity.Concrete.TightEncoding
