import XmssSecurity.CappedGlobalCausalInstalledStrategyExperiment

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

def globalObservedTraceReveals
    (trace : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :
    List (GlobalChainValueIndex × Digest) :=
  trace.filterMap fun action =>
    match action with
    | .probe _ _ => none
    | .reveal index value => some (index, value)

theorem mem_globalObservedTraceReveals_iff
    (trace : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (reveal : GlobalChainValueIndex × Digest) :
    reveal ∈ globalObservedTraceReveals trace ↔
      RevealProbeOracleSimulation.ObservedAction.reveal reveal.1 reveal.2 ∈
        trace := by
  unfold globalObservedTraceReveals
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨action, haction, heq⟩
    cases action with
    | probe index target => simp at heq
    | reveal index value =>
        simp only [Option.some.injEq] at heq
        subst reveal
        exact haction
  · intro haction
    exact ⟨RevealProbeOracleSimulation.ObservedAction.reveal
      reveal.1 reveal.2, haction, rfl⟩

def GlobalCausalTraceHitsAvoidingReveals
    (q : Nat)
    (result : (GlobalChainValueIndex → Digest) ×
      ((List Bool → GlobalChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) : Prop :=
  IndexedHiddenValue.readMany result.1 q result.2.1 = true ∧
    IndexedHiddenValue.AvoidsReveals
      (globalObservedTraceReveals result.2.2) result.2.1

theorem runObserved_globalStrategyProbeTrace_eq_true_of_readMany_of_hidden
    (table : GlobalChainValueIndex → Digest)
    (state : AdaptiveRevealMonitor.State GlobalChainValueIndex)
    (q : Nat) (strategy : List Bool → GlobalChainValueIndex × Digest)
    (hhit : IndexedHiddenValue.readMany table q strategy = true)
    (hhidden : ∀ history, state.revealed (strategy history).1 = none) :
    RevealProbeOracleSimulation.runObserved table state
      (globalStrategyProbeTrace q strategy) = true := by
  unfold globalStrategyProbeTrace
  rw [RevealProbeOracleSimulation.runObserved_probeTrace]
  · simp only [RevealProbeOracleSimulation.tableHits, decide_eq_true_eq]
    rw [IndexedHiddenValue.readMany_true_iff] at hhit
    obtain ⟨round, hround, hvalue⟩ := hhit
    let probe := strategy (List.replicate round false)
    refine ⟨probe.1, ?_⟩
    rw [hvalue]
    apply RevealProbeOracleSimulation.mem_pending_installProbes_of_mem
    exact List.mem_map.mpr ⟨round, List.mem_range.mpr hround, rfl⟩
  · intro probe hprobe
    obtain ⟨round, _hround, rfl⟩ := List.mem_map.mp hprobe
    exact hhidden (List.replicate round false)

theorem runObserved_globalActionTrace_append_strategyProbeTrace_from_state
    (table : GlobalChainValueIndex → Digest)
    (state : AdaptiveRevealMonitor.State GlobalChainValueIndex)
    (trace : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (q : Nat) (strategy : List Bool → GlobalChainValueIndex × Digest)
    (hhidden : ∀ history, state.revealed (strategy history).1 = none)
    (havoid : IndexedHiddenValue.AvoidsReveals
      (globalObservedTraceReveals trace) strategy)
    (hhit : IndexedHiddenValue.readMany table q strategy = true) :
    RevealProbeOracleSimulation.runObserved table state
      (trace ++ globalStrategyProbeTrace q strategy) = true := by
  induction trace generalizing state with
  | nil =>
      simpa using
        runObserved_globalStrategyProbeTrace_eq_true_of_readMany_of_hidden
          table state q strategy hhit hhidden
  | cons action trace ih =>
      cases action with
      | probe index target =>
          have havoidRest : IndexedHiddenValue.AvoidsReveals
              (globalObservedTraceReveals trace) strategy := by
            simpa [globalObservedTraceReveals] using havoid
          simp only [List.cons_append,
            RevealProbeOracleSimulation.runObserved]
          cases hrevealed : state.revealed index with
          | some value => exact ih state hhidden havoidRest
          | none =>
              apply ih (state.addPending index target)
              · simpa [AdaptiveRevealMonitor.State.addPending] using hhidden
              · exact havoidRest
      | reveal index value =>
          have havoidRest : IndexedHiddenValue.AvoidsReveals
              (globalObservedTraceReveals trace) strategy := by
            intro history hmem
            apply havoid history
            change (strategy history).1 ∈
              index :: (globalObservedTraceReveals trace).map Prod.fst
            exact List.mem_cons_of_mem index hmem
          have hne : ∀ history, (strategy history).1 ≠ index := by
            intro history heq
            apply havoid history
            simp [globalObservedTraceReveals, heq]
          simp only [List.cons_append,
            RevealProbeOracleSimulation.runObserved]
          cases hrevealed : state.revealed index with
          | some previous => exact ih state hhidden havoidRest
          | none =>
              by_cases hearly : table index ∈ state.pending index
              · simp [hearly]
              · rw [if_neg hearly]
                apply ih (state.install index (table index))
                · intro history
                  simpa [AdaptiveRevealMonitor.State.install,
                    Function.update_of_ne (hne history)] using hhidden history
                · exact havoidRest

theorem runObserved_globalActionTrace_append_strategyProbeTrace
    (table : GlobalChainValueIndex → Digest)
    (trace : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (q : Nat) (strategy : List Bool → GlobalChainValueIndex × Digest)
    (havoid : IndexedHiddenValue.AvoidsReveals
      (globalObservedTraceReveals trace) strategy)
    (hhit : IndexedHiddenValue.readMany table q strategy = true) :
    RevealProbeOracleSimulation.runObserved table
      AdaptiveRevealMonitor.State.empty
      (trace ++ globalStrategyProbeTrace q strategy) = true := by
  apply runObserved_globalActionTrace_append_strategyProbeTrace_from_state
  · simp [AdaptiveRevealMonitor.State.empty]
  · exact havoid
  · exact hhit

theorem globalCausalTraceHitsAvoidingReveals_implies_observedHit
    (q : Nat)
    (result : (GlobalChainValueIndex → Digest) ×
      ((List Bool → GlobalChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (hhit : GlobalCausalTraceHitsAvoidingReveals q result) :
    RevealProbeOracleSimulation.ObservedHit
      (appendGlobalStrategyProbeTrace q result) := by
  exact runObserved_globalActionTrace_append_strategyProbeTrace
    result.1 result.2.2 q result.2.1 hhit.2 hhit.1

theorem globalCausalTraceHit_probability_le_lazyObservedHit
    (q : Nat) (adversary : Adversary Concrete.cappedScheme) :
    Pr[GlobalCausalTraceHitsAvoidingReveals q |
        globalCausalLazyStrategyViewExperiment adversary] ≤
      Pr[RevealProbeOracleSimulation.ObservedHit |
        globalCausalLazyCompiledStrategyExperiment q adversary] := by
  calc
    Pr[GlobalCausalTraceHitsAvoidingReveals q |
        globalCausalLazyStrategyViewExperiment adversary] ≤
        Pr[fun result => RevealProbeOracleSimulation.ObservedHit
          (appendGlobalStrategyProbeTrace q result) |
          globalCausalLazyStrategyViewExperiment adversary] := by
      apply probEvent_mono
      intro result _hresult hhit
      exact globalCausalTraceHitsAvoidingReveals_implies_observedHit
        q result hhit
    _ = Pr[RevealProbeOracleSimulation.ObservedHit |
          globalCausalLazyCompiledStrategyExperiment q adversary] := by
      rw [globalCausalLazyCompiledStrategyExperiment_eq_map_view,
        probEvent_map]
      rfl

end XmssSecurity.CappedChain
