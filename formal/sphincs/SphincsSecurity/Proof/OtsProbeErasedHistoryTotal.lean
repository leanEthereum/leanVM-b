import SphincsSecurity.Proof.OtsProbeErasedRun
import SphincsSecurity.Proof.OtsProbeCanonicalStopping

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem none_not_mem_historyPrefix_of_probeFree
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe 0)
    (hconsistent : context.ValuesConsistent) (hpending : context.state.pending = ∅) :
    none ∉ support (runResolvedHistoryPrefix computation context fuel []) := by
  intro hnone
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value => simp [runResolvedHistoryPrefix] at hnone
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [runResolvedHistoryPrefix_query_bind] at hnone
      have hnext output : (next output).IsQueryBoundP LazyRevealProbe.IsProbe 0 := by
        simpa using hbound.2 output
      cases input with
      | probe coordinate digest => simpa [LazyRevealProbe.IsProbe] using hbound.1
      | uniform n =>
          simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, mem_support_bind_iff] at hnone
          obtain ⟨output, _, htail⟩ := hnone
          exact ih output context fuel (hnext output) hconsistent hpending htail
      | hashOutput =>
          simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, mem_support_bind_iff] at hnone
          obtain ⟨output, _, htail⟩ := hnone
          exact ih output context fuel (hnext output) hconsistent hpending htail
      | ensure coordinate =>
          exact ih () { context with state := context.state.ensure coordinate } fuel (hnext ()) hconsistent hpending hnone
      | publish coordinate =>
          exact ih () { context with state := context.state.publish coordinate } fuel (hnext ()) hconsistent hpending hnone
      | peek coordinate =>
          exact ih (context.state.values coordinate) context fuel (hnext _) hconsistent hpending hnone
      | reveal coordinate =>
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, OtsSecretIndex.coordinate] at hnone
              have hhit output : ¬context.state.hitAt (.chainStart lay tree leafIdx chainIdx) output := by
                simp [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt, hpending]
              cases hknown : context.state.values (.chainStart lay tree leafIdx chainIdx) with
              | some output =>
                  simp only [hknown, if_neg (hhit output)] at hnone
                  exact ih output _ fuel (hnext output)
                    (valuesConsistent_materialize_chainStart context ⟨lay, tree, leafIdx, chainIdx⟩ output hconsistent)
                    (by simp [LazyRevealProbe.State.materialize, LazyRevealProbe.State.pendingAway, hpending]) hnone
              | none =>
                  rw [hknown] at hnone
                  simp only [ChainStartHistoryOutputHit, List.not_mem_nil, false_and, exists_false, if_false,
                    mem_support_bind_iff] at hnone
                  obtain ⟨output, _, htail⟩ := hnone
                  exact ih output _ fuel (hnext output)
                    (valuesConsistent_materialize_chainStart context ⟨lay, tree, leafIdx, chainIdx⟩ output hconsistent)
                    (by simp only [LazyRevealProbe.State.materialize, LazyRevealProbe.State.pendingAway, hpending, Finset.filter_empty]) htail
          | position position =>
              simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, mem_support_bind_iff] at hnone
              obtain ⟨option, hoption, htail⟩ := hnone
              cases option with
              | none =>
                  apply none_not_mem_resolveDeferredReveal_of_no_pending (startTableAvoidingPending context) position context _ _ hoption
                  · exact ⟨hconsistent, by simp [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt, hpending]⟩
                  · intro entry hentry
                    simp [hpending] at hentry
              | some resolved =>
                  exact ih resolved.output _ fuel (hnext resolved.output)
                    (hconsistent.materializeResolvedPosition_of (startTableAvoidingPending context) position resolved hoption)
                    (by simp [materializeResolvedPosition, LazyRevealProbe.State.materialize, LazyRevealProbe.State.pendingAway, hpending]) htail

theorem erasedHistoryPrefix_some_invariants
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (entry : HistoryResolvedPrefix α)
    (hconsistent : context.ValuesConsistent) (hpending : context.state.pending = ∅)
    (hentry : some entry ∈ support (runResolvedHistoryPrefix (eraseProbeQueries computation) context 0 [])) :
    entry.context.ValuesConsistent ∧ entry.context.state.pending = ∅ ∧ entry.history = [] := by
  have hhistory := historyPrefix_history_eq_of_probeFree _ context 0 [] entry (eraseProbeQueries_probeFree _) hentry
  have hcovered := (historyPrefix_invariant_of_mem _ context 0 0 [] entry
    (by intro candidate hcandidate; simp [hpending] at hcandidate) (eraseProbeQueries_probeFree _) hentry).1
  rw [hhistory] at hcovered
  refine ⟨valuesConsistent_of_mem_historyPrefix _ context 0 [] entry hconsistent hentry, ?_, hhistory⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro candidate hcandidate
  simpa using hcovered candidate hcandidate

end SphincsSecurity.Concrete.OtsProbeSimulation
