import XmssSecurity.CausalDirectLazyGame
import XmssSecurity.CausalViewCoupling

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

noncomputable local instance directFinalReductionSampleableChainTable :
    SampleableType (ChainValueIndex → Digest) :=
  SampleableType.ofFintype (ChainValueIndex → Digest)

namespace RevealProbeOracleSimulation

theorem runObserved_eq_true_of_tableHits
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (table : Index → Digest) (state : AdaptiveRevealMonitor.State Index)
    (trace : ActionTrace Index)
    (hhit : tableHits state table = true) :
    runObserved table state trace = true := by
  unfold tableHits at hhit
  simp only [decide_eq_true_eq] at hhit
  obtain ⟨index, hindex⟩ := hhit
  induction trace generalizing state index with
  | nil =>
      simp only [runObserved]
      unfold tableHits
      simp only [decide_eq_true_eq]
      exact ⟨index, hindex⟩
  | cons action trace ih =>
      cases action with
      | probe probeIndex target =>
          cases hrevealed : state.revealed probeIndex with
          | none =>
              rw [runObserved, hrevealed]
              apply ih (state.addPending probeIndex target) index
              by_cases heq : index = probeIndex
              · subst index
                simp [AdaptiveRevealMonitor.State.addPending, hindex]
              · simpa [AdaptiveRevealMonitor.State.addPending,
                  Function.update_of_ne heq] using hindex
          | some value =>
              rw [runObserved, hrevealed]
              exact ih state index hindex
      | reveal revealIndex value =>
          cases hrevealed : state.revealed revealIndex with
          | some revealedValue =>
              rw [runObserved, hrevealed]
              exact ih state index hindex
          | none =>
              rw [runObserved, hrevealed]
              by_cases hcontains : table revealIndex ∈ state.pending revealIndex
              · simp [hcontains]
              · rw [if_neg hcontains]
                apply ih (state.install revealIndex (table revealIndex)) index
                by_cases heq : index = revealIndex
                · subst index
                  exact False.elim (hcontains hindex)
                · simpa [AdaptiveRevealMonitor.State.install,
                    Function.update_of_ne heq] using hindex

theorem runObserved_append_eq_true
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (table : Index → Digest) (state : AdaptiveRevealMonitor.State Index)
    (trace suffix : ActionTrace Index)
    (hhit : runObserved table state trace = true) :
    runObserved table state (trace ++ suffix) = true := by
  induction trace generalizing state with
  | nil =>
      exact runObserved_eq_true_of_tableHits table state suffix hhit
  | cons action trace ih =>
      cases action with
      | probe index target =>
          cases hrevealed : state.revealed index with
          | none =>
              rw [runObserved, hrevealed] at hhit
              rw [List.cons_append, runObserved, hrevealed]
              exact ih (state.addPending index target) hhit
          | some value =>
              rw [runObserved, hrevealed] at hhit
              rw [List.cons_append, runObserved, hrevealed]
              exact ih state hhit
      | reveal index value =>
          cases hrevealed : state.revealed index with
          | some revealedValue =>
              rw [runObserved, hrevealed] at hhit
              rw [List.cons_append, runObserved, hrevealed]
              exact ih state hhit
          | none =>
              rw [runObserved, hrevealed] at hhit
              rw [List.cons_append, runObserved, hrevealed]
              by_cases hcontains : table index ∈ state.pending index
              · simp [hcontains]
              · rw [if_neg hcontains] at hhit ⊢
                exact ih (state.install index (table index)) hhit

end RevealProbeOracleSimulation

set_option maxRecDepth 1000000 in
theorem evalDist_actualFixedChainKeygen_uniformTable_eq_withBase
    (chain : ChainIndex) :
    𝒟[do
      let keyView ← actualFixedChainKeygen chain
      let table ← $ᵗ (ChainValueIndex → Digest)
      pure (keyView, table)] =
    𝒟[do
      let keyView ← actualFixedChainKeygen chain
      let table ← uniformChainValueTable chain
      pure (keyView, table)] := by
  apply evalDist_bind_congr
  intro keyView _hkeyView
  unfold uniformChainValueTable
  simpa [map_eq_bind_pure_comp] using
    congrArg (fun distribution =>
        (fun table => (keyView, table)) <$> distribution)
      (Concrete.evalDist_sampledAllEpochChainValueTableOnly_eq_uniform
        0 chain).symm

set_option maxRecDepth 1000000 in
theorem relTriple_programmedWarmedFixedChainKeygen_fullUniform
    (chain : ChainIndex) :
    RelTriple
      (programmedWarmedFixedChainKeygen chain)
      (do
        let keyView ← actualFixedChainKeygen chain
        let table ← $ᵗ (ChainValueIndex → Digest)
        pure (keyView, table))
      (ProgrammedActualKeygenFullRelation chain) := by
  exact relTriple_of_evalDist_eq_right
    (evalDist_actualFixedChainKeygen_uniformTable_eq_withBase chain).symm
      (relTriple_programmedWarmedFixedChainKeygen_withBase_full chain)

end XmssSecurity
