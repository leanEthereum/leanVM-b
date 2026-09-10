import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedPrivateSampling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option maxRecDepth 100000 in
theorem evalDist_finishResolvedRunIsNone_eq_of_finalizationContextEq
    (table : OtsSecretIndex → HashOutput) (left right : DeferredContext)
    (fuel : Nat) (value : α)
    (hcontext : FinalizationContextEq table (some left) (some right)) :
    evalDist (finishResolvedRunIsNone
        (some (ResolvedRunResult.mk left fuel value table))) =
      evalDist (finishResolvedRunIsNone
        (some (ResolvedRunResult.mk right fuel value table))) := by
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  have hrightCompletable : DeferredCompletable table right := by
    rcases hleftCompletable with ⟨completion, hcompletion⟩
    exact ⟨completion, (hview.deferredCompletion_iff completion).mp hcompletion⟩
  rw [finishResolvedRunIsNone_some_eq_finalize _ hleftCompletable,
    finishResolvedRunIsNone_some_eq_finalize _ hrightCompletable]
  exact evalDist_map_isNone_finalizeResolvedCoordinates_congr_covered table
    left.state.coordinates.toList right.state.coordinates.toList left right hview
    left.state.coordinates.nodup_toList right.state.coordinates.nodup_toList
    (pendingCovered_coordinates_toList left) (pendingCovered_coordinates_toList right)

set_option maxRecDepth 100000 in
theorem ensuredLE_of_mem_runResolvedFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (result : ResolvedRunResult α)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table computation)) :
    LazyRevealProbe.EnsuredLE context.state result.context.state := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runResolvedFromTable] at hresult
      subst result
      exact LazyRevealProbe.EnsuredLE.refl context.state
  | query_bind query next ih =>
      cases query with
      | uniform n =>
          rw [runResolvedFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output context fuel hrest
      | hashOutput =>
          rw [runResolvedFromTable_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output context fuel hrest
      | ensure coordinate =>
          rw [runResolvedFromTable_ensure_query_bind] at hresult
          exact (LazyRevealProbe.ensuredLE_ensure context.state coordinate).trans
            (ih () { context with state := context.state.ensure coordinate } fuel hresult)
      | probe coordinate candidate =>
          rw [runResolvedFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · exact ih () context remaining (by simpa [hrevealed] using hresult)
              · exact (LazyRevealProbe.ensuredLE_addPending context.state coordinate
                    candidate).trans
                  (ih () { context with state := context.state.addPending coordinate candidate }
                    remaining (by simpa [hrevealed] using hresult))
      | peek coordinate =>
          rw [runResolvedFromTable_peek_query_bind] at hresult
          exact ih (context.state.values coordinate) context fuel hresult
      | publish coordinate =>
          rw [runResolvedFromTable_publish_query_bind] at hresult
          exact (LazyRevealProbe.ensuredLE_publish context.state coordinate).trans
            (ih () { context with state := context.state.publish coordinate } fuel hresult)
      | reveal coordinate =>
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              rw [runResolvedFromTable_reveal_query_bind, mem_support_bind_iff] at hresult
              obtain ⟨resolvedOption, _hresolved, hrest⟩ := hresult
              cases resolvedOption with
              | none => simp at hrest
              | some resolved =>
                  exact (LazyRevealProbe.ensuredLE_materialize context.state
                        (.chainStart lay tree leafIdx chainIdx) resolved.output).trans
                    (ih resolved.output
                      { state := context.state.materialize
                          (.chainStart lay tree leafIdx chainIdx) resolved.output
                        values := resolved.values }
                      fuel hrest)
          | position position =>
              rw [runResolvedFromTable_reveal_query_bind, mem_support_bind_iff] at hresult
              obtain ⟨resolvedOption, _hresolved, hrest⟩ := hresult
              cases resolvedOption with
              | none => simp at hrest
              | some resolved =>
                  exact (LazyRevealProbe.ensuredLE_materialize context.state
                        (.position position) resolved.output).trans
                    (ih resolved.output
                      { state := context.state.materialize (.position position)
                          resolved.output
                        values := resolved.values }
                      fuel hrest)

attribute [local irreducible] ensureFullChain ensureOtsLeaf

end SphincsSecurity.Concrete.OtsProbeSimulation
