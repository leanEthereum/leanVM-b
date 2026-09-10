import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbePrivateValueProbeCounting

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def resolvedContinuationCharge
    (charge : LazyRevealProbe.Query Coordinate → ENNReal)
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β) : Option (ResolvedRunResult α) → ENNReal
  | none => 0
  | some result => expectedResolvedQueryCharge charge (next result.value) result.context result.remaining result.table

theorem expectedResolvedQueryCharge_bind
    (charge : LazyRevealProbe.Query Coordinate → ENNReal)
    (left : OracleComp (LazyRevealProbe.World Coordinate) α) (next : α → OracleComp (LazyRevealProbe.World Coordinate) β)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    expectedResolvedQueryCharge charge (left >>= next) context fuel table =
      expectedResolvedQueryCharge charge left context fuel table +
        ∑' result, Pr[= result | runResolvedFromTable context fuel table left] * resolvedContinuationCharge charge next result := by
  induction left using OracleComp.inductionOn generalizing context fuel table with
  | pure value => simp [expectedResolvedQueryCharge, runResolvedFromTable, resolvedContinuationCharge]
  | query_bind input continuation ih =>
      rw [bind_assoc, expectedResolvedQueryCharge_query_bind, expectedResolvedQueryCharge_query_bind,
        runResolvedFromTable_bind, tsum_probOutput_bind_mul, add_assoc, ← ENNReal.tsum_add]
      congr 1
      apply tsum_congr
      intro result
      cases result with
      | none => simp [resolvedContinuationCharge]
      | some result =>
          dsimp only
          rw [ih, mul_add, ← ENNReal.tsum_mul_left]

end SphincsSecurity.Concrete.OtsProbeSimulation
