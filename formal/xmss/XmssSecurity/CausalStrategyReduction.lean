import XmssSecurity.CausalInstalledStrategyExperiment
import XmssSecurity.CausalKeygenGameCoupling
import XmssSecurity.CausalRevealCoverageGame

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

set_option maxRecDepth 100000

def observedProbeResult
    (q : Nat) (view : IndexedHiddenValue.RevealProbeView ChainValueIndex) :
    (ChainValueIndex → Digest) ×
      (Unit × RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  (view.table, ((),
    (RevealProbeOracleSimulation.strategyProbes q view.strategy).map fun probe =>
      RevealProbeOracleSimulation.ObservedAction.probe probe.1 probe.2))

def revealTrace
    (reveals : List (ChainValueIndex × Digest)) :
    RevealProbeOracleSimulation.ActionTrace ChainValueIndex :=
  reveals.map fun reveal =>
    RevealProbeOracleSimulation.ObservedAction.reveal reveal.1 reveal.2

def observedTraceReveals
    (trace : RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :
    List (ChainValueIndex × Digest) :=
  trace.filterMap fun action =>
    match action with
    | .probe _ _ => none
    | .reveal index value => some (index, value)

theorem mem_observedTraceReveals_iff
    (trace : RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (reveal : ChainValueIndex × Digest) :
    reveal ∈ observedTraceReveals trace ↔
      RevealProbeOracleSimulation.ObservedAction.reveal reveal.1 reveal.2 ∈
        trace := by
  unfold observedTraceReveals
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

theorem avoids_observedTraceReveals_of_covered
    (covered : Set ChainValueIndex)
    (trace : RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (strategy : List Bool → ChainValueIndex × Digest)
    (htrace : CausalTraceRevealsCovered covered trace)
    (hstrategy : ∀ history, (strategy history).1 ∉ covered) :
    IndexedHiddenValue.AvoidsReveals
      (observedTraceReveals trace) strategy := by
  intro history hmem
  apply hstrategy history
  rw [List.mem_map] at hmem
  obtain ⟨reveal, hreveal, heq⟩ := hmem
  have hindex : reveal.1 ∈ covered := htrace reveal.1 reveal.2
    ((mem_observedTraceReveals_iff trace reveal).mp hreveal)
  simpa [heq] using hindex

theorem avoids_observedTraceReveals_of_returnedCovered
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex)
    (trace : RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (strategy : List Bool → ChainValueIndex × Digest)
    (htrace : CausalTraceRevealsCovered
      (ReturnedChainValueCovered finalCache secretKey log chain) trace)
    (hstrategy : IndexedHiddenValue.AvoidsReveals
      (returnedChainValueReveals keygenCache finalCache secretKey log chain)
        strategy) :
    IndexedHiddenValue.AvoidsReveals
      (observedTraceReveals trace) strategy := by
  apply avoids_observedTraceReveals_of_covered
    (ReturnedChainValueCovered finalCache secretKey log chain) trace strategy
      htrace
  intro history hmem
  exact hstrategy history (returnedChainValueCovered_mem_reveals
    keygenCache finalCache secretKey log chain (strategy history).1 hmem)

theorem lazyCausalStrategyResult_avoids_observedTraceReveals
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × CausalHashState)
    (chain : ChainIndex)
    (execution : ((((Forgery × Bool) × AttackerActionTrace) ×
      CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hinitial : ∀ index,
      keyResult.2.finishKeygen.revealed index = none)
    (hexecution : execution ∈ support
      (causalLazyDetailedGameAfterKeygen adversary keyResult.1.1
        keyResult.1.2 chain keyResult.2.finishKeygen))
    (hstrategy : IndexedHiddenValue.AvoidsReveals
      (actionTracedRevealProbeView chain
        (causalDetailedResult keyResult execution.1)).reveals
      (lazyCausalStrategyResult chain keyResult execution).1) :
    IndexedHiddenValue.AvoidsReveals
      (observedTraceReveals execution.2)
      (lazyCausalStrategyResult chain keyResult execution).1 := by
  have hcovered :=
    causalLazyDetailedGameAfterKeygen_support_returnedCovered
      adversary keyResult.1.1 keyResult.1.2 chain
        keyResult.2.finishKeygen hinitial execution hexecution
  apply avoids_observedTraceReveals_of_returnedCovered
    keyResult.2.cache execution.1.2.cache keyResult.1.2
      execution.1.1.2.toSigningLog chain execution.2
      (lazyCausalStrategyResult chain keyResult execution).1
  · exact hcovered.2
  · simpa [lazyCausalStrategyResult, actionTracedRevealProbeView,
      causalDetailedResult, actionTraceOutcome] using hstrategy

def CausalTraceHitsAvoidingReveals
    (q : Nat)
    (result : (ChainValueIndex → Digest) ×
      ((List Bool → ChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) : Prop :=
  IndexedHiddenValue.readMany result.1 q result.2.1 = true ∧
    IndexedHiddenValue.AvoidsReveals
      (observedTraceReveals result.2.2) result.2.1

theorem runObserved_strategyProbeTrace_eq_true_of_readMany_of_hidden
    (table : ChainValueIndex → Digest)
    (state : AdaptiveRevealMonitor.State ChainValueIndex)
    (q : Nat) (strategy : List Bool → ChainValueIndex × Digest)
    (hhit : IndexedHiddenValue.readMany table q strategy = true)
    (hhidden : ∀ history, state.revealed (strategy history).1 = none) :
    RevealProbeOracleSimulation.runObserved table state
      (strategyProbeTrace q strategy) = true := by
  unfold strategyProbeTrace
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

theorem runObserved_revealTrace_append_strategyProbeTrace_from_state
    (table : ChainValueIndex → Digest)
    (state : AdaptiveRevealMonitor.State ChainValueIndex)
    (reveals : List (ChainValueIndex × Digest))
    (q : Nat) (strategy : List Bool → ChainValueIndex × Digest)
    (hpending : ∀ index, state.pending index = ∅)
    (hhidden : ∀ history, state.revealed (strategy history).1 = none)
    (havoid : IndexedHiddenValue.AvoidsReveals reveals strategy)
    (hhit : IndexedHiddenValue.readMany table q strategy = true) :
    RevealProbeOracleSimulation.runObserved table state
      (revealTrace reveals ++ strategyProbeTrace q strategy) = true := by
  induction reveals generalizing state with
  | nil =>
      simpa [revealTrace] using
        runObserved_strategyProbeTrace_eq_true_of_readMany_of_hidden
          table state q strategy hhit hhidden
  | cons reveal reveals ih =>
      have havoidRest : IndexedHiddenValue.AvoidsReveals reveals strategy := by
        intro history hmem
        exact havoid history (by simp [hmem])
      simp only [revealTrace, List.map_cons, List.cons_append,
        RevealProbeOracleSimulation.runObserved]
      cases hrevealed : state.revealed reveal.1 with
      | some value =>
          exact ih state hpending hhidden havoidRest
      | none =>
          have hnotPending : table reveal.1 ∉ state.pending reveal.1 := by
            rw [hpending reveal.1]
            simp
          rw [if_neg hnotPending]
          apply ih (state.install reveal.1 (table reveal.1))
          · intro index
            by_cases heq : index = reveal.1
            · subst index
              simp [AdaptiveRevealMonitor.State.install]
            · simpa [AdaptiveRevealMonitor.State.install,
                Function.update_of_ne heq] using hpending index
          · intro history
            have hne : (strategy history).1 ≠ reveal.1 := by
              intro heq
              apply havoid history
              simp [heq]
            simpa [AdaptiveRevealMonitor.State.install,
              Function.update_of_ne hne] using hhidden history
          · exact havoidRest

theorem runObserved_revealTrace_append_strategyProbeTrace
    (view : IndexedHiddenValue.RevealProbeView ChainValueIndex)
    (q : Nat)
    (hhit : IndexedHiddenValue.RevealProbeView.HitsAvoidingReveals q view) :
    RevealProbeOracleSimulation.runObserved view.table
      AdaptiveRevealMonitor.State.empty
      (revealTrace view.reveals ++ strategyProbeTrace q view.strategy) = true := by
  apply runObserved_revealTrace_append_strategyProbeTrace_from_state
  · simp [AdaptiveRevealMonitor.State.empty]
  · simp [AdaptiveRevealMonitor.State.empty]
  · exact hhit.2
  · exact hhit.1

theorem runObserved_actionTrace_append_strategyProbeTrace_from_state
    (table : ChainValueIndex → Digest)
    (state : AdaptiveRevealMonitor.State ChainValueIndex)
    (trace : RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (q : Nat) (strategy : List Bool → ChainValueIndex × Digest)
    (hhidden : ∀ history, state.revealed (strategy history).1 = none)
    (havoid : IndexedHiddenValue.AvoidsReveals
      (observedTraceReveals trace) strategy)
    (hhit : IndexedHiddenValue.readMany table q strategy = true) :
    RevealProbeOracleSimulation.runObserved table state
      (trace ++ strategyProbeTrace q strategy) = true := by
  induction trace generalizing state with
  | nil =>
      simpa using
        runObserved_strategyProbeTrace_eq_true_of_readMany_of_hidden
          table state q strategy hhit hhidden
  | cons action trace ih =>
      cases action with
      | probe index target =>
          have havoidRest : IndexedHiddenValue.AvoidsReveals
              (observedTraceReveals trace) strategy := by
            simpa [observedTraceReveals] using havoid
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
              (observedTraceReveals trace) strategy := by
            intro history hmem
            apply havoid history
            change (strategy history).1 ∈
              index :: (observedTraceReveals trace).map Prod.fst
            exact List.mem_cons_of_mem index hmem
          have hne : ∀ history, (strategy history).1 ≠ index := by
            intro history heq
            apply havoid history
            simp [observedTraceReveals, heq]
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

theorem runObserved_actionTrace_append_strategyProbeTrace
    (table : ChainValueIndex → Digest)
    (trace : RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (q : Nat) (strategy : List Bool → ChainValueIndex × Digest)
    (havoid : IndexedHiddenValue.AvoidsReveals
      (observedTraceReveals trace) strategy)
    (hhit : IndexedHiddenValue.readMany table q strategy = true) :
    RevealProbeOracleSimulation.runObserved table
      AdaptiveRevealMonitor.State.empty
      (trace ++ strategyProbeTrace q strategy) = true := by
  apply runObserved_actionTrace_append_strategyProbeTrace_from_state
  · simp [AdaptiveRevealMonitor.State.empty]
  · exact havoid
  · exact hhit

theorem causalTraceHitsAvoidingReveals_implies_observedHit
    (q : Nat)
    (result : (ChainValueIndex → Digest) ×
      ((List Bool → ChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hhit : CausalTraceHitsAvoidingReveals q result) :
    RevealProbeOracleSimulation.ObservedHit
      (appendStrategyProbeTrace q result) := by
  exact runObserved_actionTrace_append_strategyProbeTrace
    result.1 result.2.2 q result.2.1 hhit.2 hhit.1

theorem causalTraceHit_probability_le_lazyObservedHit
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (chain : ChainIndex) :
    Pr[CausalTraceHitsAvoidingReveals q |
        causalLazyStrategyViewExperiment adversary chain] ≤
      Pr[RevealProbeOracleSimulation.ObservedHit |
        causalLazyCompiledStrategyExperiment q adversary chain] := by
  calc
    Pr[CausalTraceHitsAvoidingReveals q |
        causalLazyStrategyViewExperiment adversary chain] ≤
        Pr[fun result => RevealProbeOracleSimulation.ObservedHit
          (appendStrategyProbeTrace q result) |
          causalLazyStrategyViewExperiment adversary chain] := by
      apply probEvent_mono
      intro result _hresult hhit
      exact causalTraceHitsAvoidingReveals_implies_observedHit q result hhit
    _ = Pr[RevealProbeOracleSimulation.ObservedHit |
          causalLazyCompiledStrategyExperiment q adversary chain] := by
      rw [causalLazyCompiledStrategyExperiment_eq_map_view, probEvent_map]
      rfl

noncomputable def chronologicallyWarmedObservedProbeExperiment
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (chain : ChainIndex) :
    ProbComp ((ChainValueIndex → Digest) ×
      (Unit × RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) :=
  observedProbeResult q <$>
    chronologicallyWarmedRevealProbeViewExperiment adversary chain

theorem evalDist_actionTracedObservedProbeViewExperiment_eq_warmed
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (chain : ChainIndex) :
    evalDist (actionTracedObservedProbeViewExperiment q adversary chain) =
      evalDist (chronologicallyWarmedObservedProbeExperiment
        q adversary chain) := by
  calc
    evalDist (actionTracedObservedProbeViewExperiment q adversary chain) =
        evalDist (observedProbeResult q <$>
          (actionTracedRevealProbeView chain <$>
            detailedGameWithKeygenCacheAndActionTrace adversary)) := by
      unfold actionTracedObservedProbeViewExperiment observedProbeResult
      simp [Functor.map_map]
    _ = evalDist (observedProbeResult q <$>
          chronologicallyWarmedRevealProbeViewExperiment adversary chain) := by
      rw [evalDist_map, evalDist_actionTracedRevealProbeView_eq_warmed,
        ← evalDist_map]
    _ = evalDist (chronologicallyWarmedObservedProbeExperiment
          q adversary chain) := rfl

theorem actionTracedChainProbeHit_probability_le_warmedObservedHit
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (chain : ChainIndex) :
    Pr[ActionTracedChainProbeHit q chain |
        detailedGameWithKeygenCacheAndActionTrace adversary] ≤
      Pr[RevealProbeOracleSimulation.ObservedHit |
        chronologicallyWarmedObservedProbeExperiment
          q adversary chain] := by
  calc
    _ ≤ Pr[ActionTracedObservedProbeHit q chain |
          detailedGameWithKeygenCacheAndActionTrace adversary] :=
      actionTracedChainProbeHit_probability_le_observedProbeHit
        q adversary chain
    _ = Pr[RevealProbeOracleSimulation.ObservedHit |
          actionTracedObservedProbeViewExperiment q adversary chain] := by
      rw [actionTracedObservedProbeViewExperiment, probEvent_map]
      rfl
    _ = _ := probEvent_congr' (fun _ _ => Iff.rfl)
      (evalDist_actionTracedObservedProbeViewExperiment_eq_warmed
        q adversary chain)

theorem causalStrategyProgram_observedHit_probability_eq_lazy
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (chain : ChainIndex) :
    Pr[RevealProbeOracleSimulation.ObservedHit |
        RevealProbeOracleSimulation.eagerExperiment
          (RevealProbeOracleSimulation.compileStrategyProbes q
            (causalStrategyProgram adversary chain))] =
      Pr[RevealProbeOracleSimulation.ObservedHit |
        causalLazyCompiledStrategyExperiment q adversary chain] := by
  exact probEvent_congr' (fun _ _ => Iff.rfl)
    (evalDist_eagerExperiment_compile_causalStrategyProgram_eq_lazy
      q adversary chain)

def WarmedActionTracedChainProbeHit
    (q : Nat) (chain : ChainIndex) (result : FixedChainActionTracedResult) : Prop :=
  ActionTracedChainProbeHit q chain (eraseFixedChainKeygenView result)

theorem actionTracedChainProbeHit_probability_eq_warmed
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (chain : ChainIndex) :
    Pr[ActionTracedChainProbeHit q chain |
        detailedGameWithKeygenCacheAndActionTrace adversary] =
      Pr[WarmedActionTracedChainProbeHit q chain |
        chronologicallyWarmedDetailedGame adversary chain] := by
  calc
    Pr[ActionTracedChainProbeHit q chain |
        detailedGameWithKeygenCacheAndActionTrace adversary] =
        Pr[ActionTracedChainProbeHit q chain |
          eraseFixedChainKeygenView <$>
            chronologicallyWarmedDetailedGame adversary chain] :=
      probEvent_congr' (fun _ _ => Iff.rfl)
        (evalDist_originalActionTracedGame_eq_erase_warmed adversary chain)
    _ = Pr[WarmedActionTracedChainProbeHit q chain |
          chronologicallyWarmedDetailedGame adversary chain] := by
      rw [probEvent_map]
      rfl

theorem actionTracedChainProbeHit_probability_le_warmedRevealProbeHit
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (chain : ChainIndex) :
    Pr[ActionTracedChainProbeHit q chain |
        detailedGameWithKeygenCacheAndActionTrace adversary] ≤
      Pr[IndexedHiddenValue.RevealProbeView.HitsAvoidingReveals q |
        chronologicallyWarmedRevealProbeViewExperiment adversary chain] := by
  calc
    Pr[ActionTracedChainProbeHit q chain |
        detailedGameWithKeygenCacheAndActionTrace adversary] ≤
        Pr[IndexedHiddenValue.RevealProbeView.HitsAvoidingReveals q |
          actionTracedRevealProbeView chain <$>
            detailedGameWithKeygenCacheAndActionTrace adversary] :=
      actionTracedChainProbeHit_probability_le_revealProbeView
        q adversary chain
    _ = Pr[IndexedHiddenValue.RevealProbeView.HitsAvoidingReveals q |
          chronologicallyWarmedRevealProbeViewExperiment adversary chain] :=
      probEvent_congr' (fun _ _ => Iff.rfl)
        (evalDist_actionTracedRevealProbeView_eq_warmed adversary chain)

/-- The remaining causal reduction obligation is exactly the comparison between the real traced game and the fully lazy simulator. -/
theorem hasActionTracedCausalStrategyReduction_of_lazy_probability
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (chain : ChainIndex)
    (hprobability :
      Pr[ActionTracedChainProbeHit q chain |
          detailedGameWithKeygenCacheAndActionTrace adversary] ≤
        Pr[RevealProbeOracleSimulation.ObservedHit |
          causalLazyCompiledStrategyExperiment q adversary chain]) :
    HasActionTracedCausalStrategyReduction q adversary chain := by
  refine ⟨causalStrategyProgram adversary chain,
    causalStrategyProgram_isProbeQueryBoundP adversary chain, ?_⟩
  rw [causalStrategyProgram_observedHit_probability_eq_lazy]
  exact hprobability

theorem hasActionTracedCausalStrategyReduction_of_warmed_probability
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (chain : ChainIndex)
    (hwarmed :
      Pr[WarmedActionTracedChainProbeHit q chain |
          chronologicallyWarmedDetailedGame adversary chain] ≤
        Pr[RevealProbeOracleSimulation.ObservedHit |
          causalLazyCompiledStrategyExperiment q adversary chain]) :
    HasActionTracedCausalStrategyReduction q adversary chain := by
  apply hasActionTracedCausalStrategyReduction_of_lazy_probability
  rw [actionTracedChainProbeHit_probability_eq_warmed q adversary chain]
  exact hwarmed

theorem hasActionTracedCausalStrategyReduction_of_warmed_view_probability
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (chain : ChainIndex)
    (hwarmed :
      Pr[IndexedHiddenValue.RevealProbeView.HitsAvoidingReveals q |
          chronologicallyWarmedRevealProbeViewExperiment adversary chain] ≤
        Pr[RevealProbeOracleSimulation.ObservedHit |
          causalLazyCompiledStrategyExperiment q adversary chain]) :
    HasActionTracedCausalStrategyReduction q adversary chain := by
  apply hasActionTracedCausalStrategyReduction_of_lazy_probability
  exact (actionTracedChainProbeHit_probability_le_warmedRevealProbeHit
    q adversary chain).trans hwarmed

theorem hasActionTracedCausalStrategyReduction_of_programmed_view_probability
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (chain : ChainIndex)
    (hprogrammed :
      Pr[IndexedHiddenValue.RevealProbeView.HitsAvoidingReveals q |
          programmedWarmedRevealProbeViewExperiment adversary chain] ≤
        Pr[RevealProbeOracleSimulation.ObservedHit |
          causalLazyCompiledStrategyExperiment q adversary chain]) :
    HasActionTracedCausalStrategyReduction q adversary chain := by
  apply hasActionTracedCausalStrategyReduction_of_warmed_view_probability
  rw [chronologicallyWarmedRevealProbeHit_probability_eq_programmed]
  exact hprogrammed

theorem hasActionTracedCausalStrategyReduction_of_programmed_causal_trace_probability
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (chain : ChainIndex)
    (hprogrammed :
      Pr[IndexedHiddenValue.RevealProbeView.HitsAvoidingReveals q |
          programmedWarmedRevealProbeViewExperiment adversary chain] ≤
        Pr[CausalTraceHitsAvoidingReveals q |
          causalLazyStrategyViewExperiment adversary chain]) :
    HasActionTracedCausalStrategyReduction q adversary chain := by
  apply hasActionTracedCausalStrategyReduction_of_programmed_view_probability
  exact hprogrammed.trans
    (causalTraceHit_probability_le_lazyObservedHit q adversary chain)

end XmssSecurity
