import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbePrivateValueLiveProbeCounting

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expectedLiveResolvedQueryCharge_le_raw
    (charge : LazyRevealProbe.Query Coordinate → ENNReal) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    expectedLiveResolvedQueryCharge charge computation context fuel table ≤ expectedResolvedQueryCharge charge computation context fuel table := by
  induction computation using OracleComp.inductionOn generalizing context fuel table with
  | pure value => rfl
  | query_bind input next ih =>
      rw [expectedLiveResolvedQueryCharge_query_bind, expectedResolvedQueryCharge_query_bind]
      by_cases hcomplete : DeferredCompletable table context
      · rw [if_pos hcomplete]
        apply add_le_add le_rfl
        apply ENNReal.tsum_le_tsum
        intro result
        cases result with
        | none => rfl
        | some result => exact mul_le_mul' le_rfl (ih result.value result.context result.remaining result.table)
      · simp [hcomplete]

noncomputable def liveResolvedContinuationCharge
    (charge : LazyRevealProbe.Query Coordinate → ENNReal)
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β) : Option (ResolvedRunResult α) → ENNReal
  | none => 0
  | some result => expectedLiveResolvedQueryCharge charge (next result.value) result.context result.remaining result.table

theorem expectedLiveResolvedQueryCharge_bind
    (charge : LazyRevealProbe.Query Coordinate → ENNReal)
    (left : OracleComp (LazyRevealProbe.World Coordinate) α) (next : α → OracleComp (LazyRevealProbe.World Coordinate) β)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    expectedLiveResolvedQueryCharge charge (left >>= next) context fuel table =
      expectedLiveResolvedQueryCharge charge left context fuel table +
        ∑' result, Pr[= result | runResolvedFromTable context fuel table left] * liveResolvedContinuationCharge charge next result := by
  induction left using OracleComp.inductionOn generalizing context fuel table with
  | pure value => simp [expectedLiveResolvedQueryCharge, runResolvedFromTable, liveResolvedContinuationCharge]
  | query_bind input continuation ih =>
      by_cases hcomplete : DeferredCompletable table context
      · rw [bind_assoc, expectedLiveResolvedQueryCharge_query_bind, expectedLiveResolvedQueryCharge_query_bind,
          if_pos hcomplete, if_pos hcomplete, runResolvedFromTable_bind, tsum_probOutput_bind_mul, add_assoc, ← ENNReal.tsum_add]
        congr 1
        apply tsum_congr
        intro result
        by_cases hresult : result ∈ support (runResolvedFromTable context fuel table (liftM (OracleSpec.query input)))
        · cases result with
          | none => simp [liveResolvedContinuationCharge]
          | some result =>
              have hcore := resolvedCore_of_mem_runResolvedFromTable (liftM (OracleSpec.query input)) context fuel table result hconsistent hstarts hresult
              dsimp only
              rw [ih result.value result.context result.remaining result.table hcore.2.1 (hcore.1 ▸ hcore.2.2), mul_add, ← ENNReal.tsum_mul_left]
        · simp [probOutput_eq_zero_of_not_mem_support hresult]
      · rw [expectedLiveResolvedQueryCharge_eq_zero_of_not_completable charge _ context fuel table hcomplete,
          expectedLiveResolvedQueryCharge_eq_zero_of_not_completable charge _ context fuel table hcomplete, zero_add]
        symm
        apply ENNReal.tsum_eq_zero.mpr
        intro result
        by_cases hresult : result ∈ support (runResolvedFromTable context fuel table
            ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= continuation))
        · cases result with
          | none => simp [liveResolvedContinuationCharge]
          | some result =>
              have hcore := resolvedCore_of_mem_runResolvedFromTable _ context fuel table result hconsistent hstarts hresult
              have hdoomed := not_deferredCompletable_of_mem_runResolvedFromTable _ context fuel table result hconsistent hstarts hresult hcomplete
              simp only [liveResolvedContinuationCharge, hcore.1,
                expectedLiveResolvedQueryCharge_eq_zero_of_not_completable charge _ _ _ _ hdoomed, mul_zero]
        · simp [probOutput_eq_zero_of_not_mem_support hresult]

end SphincsSecurity.Concrete.OtsProbeSimulation
