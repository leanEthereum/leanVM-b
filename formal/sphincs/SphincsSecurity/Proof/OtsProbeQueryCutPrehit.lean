import SphincsSecurity.Proof.OuterQueryCut
import SphincsSecurity.Proof.OtsProbeEncodingPrehitViewed

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem encodingPrehitViewedAdversaryImpl_cache_projection
    (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × Bool) :
    (fun result => (result.1, result.2.1.cache)) <$>
      (simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey) computation).run state =
      (simulateQ (unloggedMappedAdversaryImpl secretKey) computation).run state.1.cache := by
  calc
    _ = (fun result : α × ViewedFullTraceState => (result.1, result.2.cache)) <$>
        (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey) computation).run state.1 := by
      rw [← encodingPrehitViewedAdversaryImpl_projection accountingKey secretKey computation state]
      simp only [Functor.map_map]
      rfl
    _ = Prod.map id Prod.fst <$>
        (simulateQ (fullTracedMappedAdversaryImpl secretKey) computation).run state.1.base := by
      rw [← viewedFullTracedMappedAdversaryImpl_projection secretKey computation state.1]
      simp only [Functor.map_map]
      rfl
    _ = _ := _root_.OracleComp.extendState_run_proj_eq (unloggedMappedAdversaryImpl secretKey)
      fullAdversaryTraceUpdate computation state.1.cache state.1.trace

def actualSelectionOfPrehitCut (result : OuterQueryCut α × (ViewedFullTraceState × Bool)) :
    Option ActualQuerySelection :=
  result.1.input?.map (fun input => ⟨input, result.2.1.cache⟩)

theorem actualSelectionOfPrehitCut_projection
    (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (ordinal : Nat)
    (state : ViewedFullTraceState × Bool) :
    actualSelectionOfPrehitCut <$>
      (simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey)
        (outerQueryCutAt computation ordinal)).run state =
      actualQuerySelection secretKey computation ordinal state.1.cache := by
  rw [actualQuerySelection_eq_cut_projection,
    ← encodingPrehitViewedAdversaryImpl_cache_projection accountingKey secretKey
      (outerQueryCutAt computation ordinal) state]
  simp only [Functor.map_map]
  rfl

theorem encodingPrehitViewedAdversaryImpl_initial_false_of_mem_support
    (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState finalState : ViewedFullTraceState) (hit : Bool) (value : α)
    (hrun : (value, (finalState, false)) ∈ support
      ((simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey) computation).run (initialState, hit))) :
    hit = false := by
  obtain ⟨log, hmonitor, _⟩ := encodingPrehitViewedAdversaryImpl_support_monitor accountingKey secretKey
    computation (initialState, hit) (value, (finalState, false)) hrun
  exact TightEncoding.runEncodingPrehitMonitor_initial_false_of_mem_support accountingKey _
    initialState.cache hit _ hmonitor

theorem mem_support_prehit_cut_resume_false_iff
    (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (ordinal : Nat)
    (initialState finalState : ViewedFullTraceState) (value : α) :
    (value, (finalState, false)) ∈ support
      ((simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey) computation).run (initialState, false)) ↔
      ∃ cut : OuterQueryCut α, ∃ middleState : ViewedFullTraceState,
        (cut, (middleState, false)) ∈ support
          ((simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey)
            (outerQueryCutAt computation ordinal)).run (initialState, false)) ∧
        (value, (finalState, false)) ∈ support
          ((simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey) cut.resume).run (middleState, false)) := by
  rw [mem_support_run_cut_resume_iff]
  constructor
  · rintro ⟨cut, ⟨middleState, hit⟩, hprefix, hsuffix⟩
    have hfalse := encodingPrehitViewedAdversaryImpl_initial_false_of_mem_support accountingKey secretKey
      cut.resume middleState finalState hit value hsuffix
    subst hit
    exact ⟨cut, middleState, hprefix, hsuffix⟩
  · rintro ⟨cut, middleState, hprefix, hsuffix⟩
    exact ⟨cut, (middleState, false), hprefix, hsuffix⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
