import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedComputedInvariant

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

set_option maxRecDepth 100000 in
theorem DeferredComputationsClosed.of_mem_runResolved
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (result : ResolvedRunResult α) (hclosed : DeferredComputationsClosed context)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table computation)) :
    DeferredComputationsClosed result.context := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runResolvedFromTable] at hresult
      subst result
      exact hclosed
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runResolvedFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output context fuel hclosed hrest
      | hashOutput =>
          rw [runResolvedFromTable_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output context fuel hclosed hrest
      | ensure coordinate =>
          rw [runResolvedFromTable_ensure_query_bind] at hresult
          exact ih () { context with state := context.state.ensure coordinate } fuel
            (hclosed.of_positionValue_eq (fun _ => rfl)) hresult
      | probe coordinate candidate =>
          rw [runResolvedFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · exact ih () context remaining hclosed (by simpa [hrevealed] using hresult)
              · exact ih () { context with state := context.state.addPending coordinate candidate }
                  remaining (hclosed.of_positionValue_eq (fun _ => rfl)) (by simpa [hrevealed] using hresult)
      | peek coordinate =>
          rw [runResolvedFromTable_peek_query_bind] at hresult
          exact ih (context.state.values coordinate) context fuel hclosed hresult
      | publish coordinate =>
          rw [runResolvedFromTable_publish_query_bind] at hresult
          exact ih () { context with state := context.state.publish coordinate } fuel
            (hclosed.of_positionValue_eq (fun _ => rfl)) hresult
      | reveal coordinate =>
          rw [runResolvedFromTable_reveal_query_bind] at hresult
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
              simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hresult
              obtain ⟨resolvedOption, hresolved, hrest⟩ := hresult
              cases resolvedOption with
              | none => simp at hrest
              | some resolved =>
                  have hresolvedEq : resolveDeferredChainStart table index context = some resolved := by
                    simpa [index] using hresolved.symm
                  exact ih resolved.output (materializeResolvedChainStart context index resolved) fuel
                    (hclosed.of_positionValue_eq (congrFun
                      (materializeResolvedChainStart_positionValue_eq table index context resolved hresolvedEq)))
                    (by simpa [index, OtsSecretIndex.coordinate, materializeResolvedChainStart] using hrest)
          | position position =>
              rw [mem_support_bind_iff] at hresult
              obtain ⟨resolvedOption, hresolved, hrest⟩ := hresult
              cases resolvedOption with
              | none => simp at hrest
              | some resolved =>
                  have hresolvedClosed := hclosed.of_resolveReveal table position context resolved hresolved
                  have hstate := resolveDeferredReveal_preserves_state_values table position context resolved hresolved
                  have hvalue := resolveDeferredReveal_resolves table position context resolved hresolved
                  exact ih resolved.output (materializeResolvedPosition context position resolved) fuel
                    (hresolvedClosed.of_positionValue_eq (congrFun
                      (materializeResolvedPosition_positionValue_eq context position resolved hstate hvalue)))
                    (by simpa [materializeResolvedPosition] using hrest)

end SphincsSecurity.Concrete.OtsProbeSimulation
