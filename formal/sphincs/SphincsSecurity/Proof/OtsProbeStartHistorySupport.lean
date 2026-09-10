import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedSampling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
theorem revealed_subset_of_mem_runResolvedFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (result : ResolvedRunResult α)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table computation)) :
    context.state.revealed ⊆ result.context.state.revealed := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runResolvedFromTable] at hresult
      subst result
      exact Finset.Subset.rfl
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runResolvedFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output context fuel htail
      | hashOutput =>
          rw [runResolvedFromTable_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output context fuel htail
      | ensure coordinate =>
          rw [runResolvedFromTable_ensure_query_bind] at hresult
          exact ih () { context with state := context.state.ensure coordinate } fuel hresult
      | probe coordinate digest =>
          cases fuel with
          | zero => simp [runResolvedFromTable_probe_query_bind] at hresult
          | succ remaining =>
              rw [runResolvedFromTable_probe_query_bind] at hresult
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · exact ih () context remaining (by simpa only [hrevealed, ↓reduceIte] using hresult)
              · exact ih () { context with state := context.state.addPending coordinate digest } remaining
                  (by simpa only [hrevealed, ↓reduceIte] using hresult)
      | peek coordinate =>
          rw [runResolvedFromTable_peek_query_bind] at hresult
          exact ih (context.state.values coordinate) context fuel hresult
      | publish coordinate =>
          rw [runResolvedFromTable_publish_query_bind] at hresult
          exact (Finset.subset_insert coordinate context.state.revealed).trans
            (ih () { context with state := context.state.publish coordinate } fuel hresult)
      | reveal coordinate =>
          rw [runResolvedFromTable_reveal_query_bind] at hresult
          cases coordinate <;> rw [mem_support_bind_iff] at hresult
          all_goals
            obtain ⟨option, _hresolve, htail⟩ := hresult
            cases option with
            | none => simp at htail
            | some resolved =>
                have hmono := ih resolved.output _ fuel htail
                exact hmono

end SphincsSecurity.Concrete.OtsProbeSimulation
