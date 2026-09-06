import SphincsSecurity.Proof.FirstExceptionMonitor

namespace SphincsSecurity

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

def PreservesExceptionRecord
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp OracleWorld α) : Prop :=
  ∀ (cache : QueryCache HashSpec) (saved : Option ExceptionRecord),
    runFirstException exception computation cache saved =
      (fun result => (result, saved)) <$> (simulateQ romImpl computation).run cache

theorem PreservesExceptionRecord.pure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (value : α) :
    PreservesExceptionRecord exception (pure value) := by
  intro cache saved
  simp [runFirstException, simulateQ_pure]

theorem PreservesExceptionRecord.bind
    {exception : QueryCache HashSpec → HashInput → HashOutput → Prop}
    {computation : OracleComp OracleWorld α} {next : α → OracleComp OracleWorld β}
    (hleft : PreservesExceptionRecord exception computation)
    (hright : ∀ value, PreservesExceptionRecord exception (next value)) :
    PreservesExceptionRecord exception (computation >>= next) := by
  intro cache saved
  rw [runFirstException_bind, hleft cache saved, bind_map_left, simulateQ_bind, StateT.run_bind, map_bind]
  exact bind_congr fun result => hright result.1 result.2 saved

theorem PreservesExceptionRecord.query
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (query : OracleWorld.Domain)
    (h : ∀ cache answer, queryException exception cache query answer = false) :
    PreservesExceptionRecord exception (OracleSpec.query query) := by
  intro cache saved
  change ((romImpl query).run cache >>= fun result =>
      Pure.pure ((result.1, result.2), retainFirstException exception saved cache query result.1)) = _
  rw [simulateQ_spec_query, map_eq_bind_pure_comp]
  apply bind_congr
  intro result
  have hsaved : retainFirstException exception saved cache query result.1 = saved := by
    cases saved with
    | some record => rfl
    | none =>
        cases query with
        | inl sample => rfl
        | inr input => simp [retainFirstException, recordQueryException, h]
  simp only [hsaved, Function.comp_def]

theorem PreservesExceptionRecord.lift_prob
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (computation : ProbComp α) :
    PreservesExceptionRecord exception (liftM computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact PreservesExceptionRecord.pure exception value
  | query_bind input next ih =>
      change PreservesExceptionRecord exception
        ((liftM (OracleWorld.query (.inl input)) : OracleComp OracleWorld _) >>= fun value => liftM (next value))
      exact (PreservesExceptionRecord.query exception (.inl input) (by intros; rfl)).bind ih

theorem runFirstException_map
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp OracleWorld α) (project : α → β)
    (cache : QueryCache HashSpec) (saved : Option ExceptionRecord) :
    runFirstException exception (project <$> computation) cache saved =
      (fun result => ((project result.1.1, result.1.2), result.2)) <$>
        runFirstException exception computation cache saved := by
  rw [map_eq_bind_pure_comp, runFirstException_bind]
  simp only [Function.comp_def, runFirstException, OracleComp.construct_pure, map_eq_bind_pure_comp]

theorem firstExceptionRecord_query_cache
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (query : OracleWorld.Domain) (cache : QueryCache HashSpec)
    (result : OracleWorld.Range query × QueryCache HashSpec) (record : ExceptionRecord)
    (hresult : (result, some record) ∈ support
      (runFirstException exception (OracleSpec.query query) cache none)) : record.cache = cache := by
  change (result, some record) ∈ support ((romImpl query).run cache >>= fun response =>
    pure (response, retainFirstException exception none cache query response.1)) at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨response, _, heq⟩ := hresult
  simp only [mem_support_pure_iff] at heq
  have hsaved := congrArg Prod.snd heq
  cases query with
  | inl sample => simp [retainFirstException, recordQueryException] at hsaved
  | inr input =>
      by_cases hfire : queryException exception cache (.inr input) response.1 = true
      · have hrecord : record = ⟨cache, input, response.1⟩ := by
          simpa [retainFirstException, recordQueryException, hfire] using hsaved
        rw [hrecord]
      · simp [retainFirstException, recordQueryException, hfire] at hsaved

end SphincsSecurity
