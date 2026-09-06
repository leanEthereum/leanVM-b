import SphincsSecurity.Proof.OtsProbeHistoryPrefix

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

theorem mem_support_of_historyPrefix
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (result : HistoryResolvedPrefix α)
    (hresult : some result ∈ support (runResolvedHistoryPrefix computation context fuel history)) :
    result.value ∈ support computation := by
  induction computation using OracleComp.inductionOn generalizing context fuel history with
  | pure value =>
      simp only [runResolvedHistoryPrefix, OracleComp.construct_pure, mem_support_pure_iff, Option.some.injEq] at hresult
      subst result
      simp
  | query_bind input next ih =>
      rw [runResolvedHistoryPrefix_query_bind] at hresult
      rw [mem_support_bind_iff]
      have finish (output : (LazyRevealProbe.World Coordinate).Range input)
          (context : DeferredContext) (fuel : Nat) (history : List Probe)
          (htail : some result ∈ support (runResolvedHistoryPrefix (next output) context fuel history)) :
          ∃ output, output ∈ support (liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) ∧
            result.value ∈ support (next output) :=
        ⟨output, OracleComp.mem_support_query input output, ih output context fuel history htail⟩
      cases input with
      | uniform n =>
          simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact finish output context fuel history htail
      | hashOutput =>
          simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact finish output context fuel history htail
      | ensure coordinate =>
          exact finish () { context with state := context.state.ensure coordinate } fuel history hresult
      | peek coordinate =>
          exact finish (context.state.values coordinate) context fuel history hresult
      | publish coordinate =>
          exact finish () { context with state := context.state.publish coordinate } fuel history hresult
      | probe coordinate digest =>
          cases fuel with
          | zero => simp [historyAdaptiveQueryStep] at hresult
          | succ remaining =>
              simp only [historyAdaptiveQueryStep] at hresult
              split_ifs at hresult with hrevealed
              · exact finish () context remaining history hresult
              · exact finish () { context with state := context.state.addPending coordinate digest }
                  remaining (history ++ [⟨coordinate, digest⟩]) hresult
      | reveal coordinate =>
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, OtsSecretIndex.coordinate] at hresult
              cases hknown : context.state.values (.chainStart lay tree leafIdx chainIdx) with
              | some output =>
                  rw [hknown] at hresult
                  dsimp only at hresult
                  split_ifs at hresult with hhit
                  · simp at hresult
                  · exact finish output
                      { context with state := context.state.materialize (.chainStart lay tree leafIdx chainIdx) output }
                      fuel history hresult
              | none =>
                  rw [hknown] at hresult
                  dsimp only at hresult
                  rw [mem_support_bind_iff] at hresult
                  obtain ⟨output, _houtput, htail⟩ := hresult
                  split_ifs at htail with hhit
                  · simp at htail
                  · exact finish output
                      { context with state := context.state.materialize (.chainStart lay tree leafIdx chainIdx) output }
                      fuel history htail
          | position position =>
              simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, mem_support_bind_iff] at hresult
              obtain ⟨option, _hoption, htail⟩ := hresult
              cases option with
              | none => simp at htail
              | some resolved =>
                  exact finish resolved.output
                    { state := context.state.materialize (.position position) resolved.output, values := resolved.values }
                    fuel history htail

end SphincsSecurity.Concrete.OtsProbeSimulation
