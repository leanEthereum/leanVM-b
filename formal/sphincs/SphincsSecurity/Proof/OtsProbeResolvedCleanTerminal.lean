import SphincsSecurity.Proof.OtsProbeResolvedAdaptiveEndpoint

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

def cleanDeferredContext (state : LazyRevealProbe.State Coordinate) : DeferredContext :=
  { state := state, values := emptyDeferredStructuralValues }

noncomputable def finishCleanRunIsNone :
    Option (CleanRunResult α) → ProbComp Bool := fun result =>
  Option.isNone <$> finishCleanRunFromTable result

set_option maxRecDepth 100000 in
theorem evalDist_finishResolvedRunIsNone_eq_finishCleanRunIsNone
    (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (state : LazyRevealProbe.State Coordinate)
    (fuel : Nat) (value : α)
    (hcontext : FinalizationContextEq table (some context)
      (some (cleanDeferredContext state))) :
    evalDist (finishResolvedRunIsNone
        (some (ResolvedRunResult.mk context fuel value table))) =
      evalDist (finishCleanRunIsNone
        (some (CleanRunResult.mk state fuel value table))) := by
  have hcleanCompletable : DeferredCompletable table (cleanDeferredContext state) := by
    rcases hcontext.2.2.2 with ⟨completion, hcompletion⟩
    exact ⟨completion, (hcontext.1.deferredCompletion_iff completion).mp hcompletion⟩
  have hprojection := finishResolvedRun_empty_projects_to_clean state fuel value table
    (by simpa [cleanDeferredContext] using hcleanCompletable)
  change projectResolvedRunResult <$>
      finishResolvedRun
        (some (ResolvedRunResult.mk (cleanDeferredContext state) fuel value table)) =
    finishCleanRunFromTable
      (some (CleanRunResult.mk state fuel value table)) at hprojection
  calc
    _ = evalDist (finishResolvedRunIsNone
          (some (ResolvedRunResult.mk (cleanDeferredContext state) fuel value table))) :=
      evalDist_finishResolvedRunIsNone_eq_of_finalizationContextEq table context
        (cleanDeferredContext state) fuel value hcontext
    _ = evalDist (Option.isNone <$>
          (projectResolvedRunResult <$>
            finishResolvedRun
              (some (ResolvedRunResult.mk (cleanDeferredContext state) fuel value table)))) := by
      unfold finishResolvedRunIsNone
      apply congrArg evalDist
      rw [Functor.map_map]
      congr 1
      funext result
      cases result <;> rfl
    _ = evalDist (Option.isNone <$>
          finishCleanRunFromTable
            (some (CleanRunResult.mk state fuel value table))) := by
      rw [hprojection]
    _ = _ := rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
