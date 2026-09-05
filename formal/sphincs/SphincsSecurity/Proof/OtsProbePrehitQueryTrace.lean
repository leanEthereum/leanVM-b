import SphincsSecurity.Proof.OtsProbeSelectedRootPrehit

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

structure PrehitQuerySnapshot where
  input : (OracleWorld + SigningSpec).Domain
  state : ViewedFullTraceState × Bool

def PrehitQuerySnapshot.actual (entry : PrehitQuerySnapshot) : ActualQuerySelection :=
  ⟨entry.input, entry.state.1.cache⟩

noncomputable def runPrehitQueryTrace (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ViewedFullTraceState × Bool →
      ProbComp ((α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot) :=
  OracleComp.construct (fun value state => pure ((value, state), []))
    (fun input _ next state => do
      let result ← (encodingPrehitViewedAdversaryImpl accountingKey secretKey input).run state
      let tail ← next result.1 result.2
      pure (tail.1, (⟨input, state⟩ : PrehitQuerySnapshot) :: tail.2)) computation

theorem runPrehitQueryTrace_query_bind (accountingKey secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (state : ViewedFullTraceState × Bool) :
    runPrehitQueryTrace accountingKey secretKey (OracleSpec.query input >>= next) state = (do
      let result ← (encodingPrehitViewedAdversaryImpl accountingKey secretKey input).run state
      let tail ← runPrehitQueryTrace accountingKey secretKey (next result.1) result.2
      pure (tail.1, (⟨input, state⟩ : PrehitQuerySnapshot) :: tail.2)) := rfl

theorem runPrehitQueryTrace_projection (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × Bool) :
    Prod.fst <$> runPrehitQueryTrace accountingKey secretKey computation state =
      (simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey) computation).run state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp [runPrehitQueryTrace]
  | query_bind input next ih =>
      rw [runPrehitQueryTrace_query_bind]
      simp only [map_bind, map_pure, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      apply bind_congr
      intro result
      simpa only [map_eq_bind_pure_comp, Function.comp_def] using ih result.1 result.2

theorem mem_support_prehitRun_of_trace (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × Bool)
    (result : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot)
    (hrun : result ∈ support (runPrehitQueryTrace accountingKey secretKey computation state)) :
    result.1 ∈ support
      ((simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey) computation).run state) := by
  rw [← runPrehitQueryTrace_projection, support_map]
  exact ⟨result, hrun, rfl⟩

set_option maxRecDepth 100000 in
theorem queryCut_support_of_mem_prehitQueryTrace
    (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × Bool)
    (result : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot)
    (hrun : result ∈ support (runPrehitQueryTrace accountingKey secretKey computation state))
    (entry : PrehitQuerySnapshot) (hentry : entry ∈ result.2) :
    ∃ ordinal : Nat, ∃ cut : OuterQueryCut α,
      cut.input? = some entry.input ∧
      (cut, entry.state) ∈ support
        ((simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey)
          (outerQueryCutAt computation ordinal)).run state) := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [runPrehitQueryTrace, OracleComp.construct_pure, mem_support_pure_iff] at hrun
      subst result
      simp at hentry
  | query_bind input next ih =>
      rw [runPrehitQueryTrace_query_bind, mem_support_bind_iff] at hrun
      obtain ⟨step, hstep, hrun⟩ := hrun
      rw [mem_support_bind_iff] at hrun
      obtain ⟨tail, htail, hresult⟩ := hrun
      simp only [mem_support_pure_iff] at hresult
      subst result
      rcases List.mem_cons.mp hentry with heq | htailEntry
      · subst entry
        refine ⟨0, .query input next, rfl, ?_⟩
        simp [outerQueryCutAt]
      · obtain ⟨ordinal, cut, hinput, hcut⟩ := ih step.1 step.2 tail htail htailEntry
        refine ⟨ordinal + 1, cut, hinput, ?_⟩
        rw [outerQueryCutAt, OracleComp.construct_query_bind]
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
        exact ⟨step, hstep, hcut⟩

set_option maxRecDepth 100000 in
theorem prehitQueryTrace_entry_false_of_final_false
    (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × Bool)
    (result : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot)
    (hrun : result ∈ support (runPrehitQueryTrace accountingKey secretKey computation state))
    (hfinal : result.1.2.2 = false) (entry : PrehitQuerySnapshot) (hentry : entry ∈ result.2) :
    entry.state.2 = false := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [runPrehitQueryTrace, OracleComp.construct_pure, mem_support_pure_iff] at hrun
      subst result
      simp at hentry
  | query_bind input next ih =>
      have hproject := mem_support_prehitRun_of_trace accountingKey secretKey _ state result hrun
      rw [runPrehitQueryTrace_query_bind, mem_support_bind_iff] at hrun
      obtain ⟨step, hstep, hrun⟩ := hrun
      rw [mem_support_bind_iff] at hrun
      obtain ⟨tail, htail, hresult⟩ := hrun
      simp only [mem_support_pure_iff] at hresult
      subst result
      rcases List.mem_cons.mp hentry with heq | htailEntry
      · subst entry
        exact encodingPrehitViewedAdversaryImpl_initial_false_of_mem_support accountingKey secretKey
          (OracleSpec.query input >>= next) state.1 tail.1.2.1 state.2 tail.1.1 (by
            dsimp only at hfinal
            simpa only [← hfinal] using hproject)
      · exact ih step.1 step.2 tail htail hfinal htailEntry

end SphincsSecurity.Concrete.OtsProbeSimulation
