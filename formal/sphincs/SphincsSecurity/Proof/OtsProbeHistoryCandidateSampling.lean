import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeHashRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

theorem afterCandidateContext_values (context : DeferredContext) (candidate : Option Probe) :
    (afterCandidateContext context candidate).state.values = context.state.values := by
  cases candidate with
  | none => rfl
  | some candidate =>
      unfold afterCandidateContext
      dsimp only
      split_ifs <;> rfl

theorem evalDist_runResolved_observe_of_not_completable
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (failure : ProbComp β) (observe : Option (ResolvedRunResult α) → ProbComp β)
    (hnone : evalDist (observe none) = evalDist failure)
    (hobserve : ∀ result, result.context.ValuesConsistent → StartTableAgrees result.context.state result.table →
      ¬DeferredCompletable result.table result.context →
      evalDist (observe (some result)) = evalDist failure)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hdoomed : ¬DeferredCompletable table context) :
    evalDist (runResolvedFromTable context fuel table computation >>= observe) = evalDist failure := by
  calc
    _ = evalDist (runResolvedFromTable context fuel table computation >>= fun _ => failure) := by
      apply evalDist_bind_congr
      intro option hoption
      cases option with
      | none => exact hnone
      | some result =>
          have hcore := resolvedCore_of_mem_runResolvedFromTable computation context fuel table result
            hconsistent hstarts hoption
          apply hobserve result hcore.2.1 (hcore.1 ▸ hcore.2.2)
          rw [hcore.1]
          exact not_deferredCompletable_of_mem_runResolvedFromTable computation context fuel table result
            hconsistent hstarts hoption hdoomed
    _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails _ (by simp [runResolvedFromTable]) failure

end SphincsSecurity.Concrete.OtsProbeSimulation
