import SphincsSecurity.Proof.OtsProbeStartAllowanceCounting

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem liveStartProbeAllowance_eq_zero_of_not_completable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hcomplete : ¬DeferredCompletable table context) :
    liveStartProbeAllowance computation context fuel table = 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next _ => rw [liveStartProbeAllowance_query_bind, if_neg hcomplete]

noncomputable def startContinuationAllowance
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β) : Option (ResolvedRunResult α) → ENNReal
  | none => 0
  | some result => liveStartProbeAllowance (next result.value) result.context result.remaining result.table

theorem liveStartProbeAllowance_bind
    (left : OracleComp (LazyRevealProbe.World Coordinate) α) (next : α → OracleComp (LazyRevealProbe.World Coordinate) β)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    liveStartProbeAllowance (left >>= next) context fuel table =
      liveStartProbeAllowance left context fuel table +
        ∑' result, Pr[= result | runResolvedFromTable context fuel table left] * startContinuationAllowance next result := by
  induction left using OracleComp.inductionOn generalizing context fuel table with
  | pure value => simp [liveStartProbeAllowance, runResolvedFromTable, startContinuationAllowance]
  | query_bind input continuation ih =>
      by_cases hcomplete : DeferredCompletable table context
      · rw [bind_assoc, liveStartProbeAllowance_query_bind, liveStartProbeAllowance_query_bind,
          if_pos hcomplete, if_pos hcomplete, runResolvedFromTable_bind, tsum_probOutput_bind_mul, add_assoc, ← ENNReal.tsum_add]
        congr 1
        apply tsum_congr
        intro result
        by_cases hresult : result ∈ support (runResolvedFromTable context fuel table (liftM (OracleSpec.query input)))
        · cases result with
          | none => simp [startContinuationAllowance]
          | some result =>
              have hcore := resolvedCore_of_mem_runResolvedFromTable (liftM (OracleSpec.query input)) context fuel table result hconsistent hstarts hresult
              dsimp only
              rw [ih result.value result.context result.remaining result.table hcore.2.1 (hcore.1 ▸ hcore.2.2), mul_add, ← ENNReal.tsum_mul_left]
        · simp [probOutput_eq_zero_of_not_mem_support hresult]
      · rw [liveStartProbeAllowance_eq_zero_of_not_completable _ context fuel table hcomplete,
          liveStartProbeAllowance_eq_zero_of_not_completable _ context fuel table hcomplete, zero_add]
        symm
        apply ENNReal.tsum_eq_zero.mpr
        intro result
        by_cases hresult : result ∈ support (runResolvedFromTable context fuel table
            ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= continuation))
        · cases result with
          | none => simp [startContinuationAllowance]
          | some result =>
              have hcore := resolvedCore_of_mem_runResolvedFromTable _ context fuel table result hconsistent hstarts hresult
              have hdoomed := not_deferredCompletable_of_mem_runResolvedFromTable _ context fuel table result hconsistent hstarts hresult hcomplete
              simp only [startContinuationAllowance, hcore.1,
                liveStartProbeAllowance_eq_zero_of_not_completable _ _ _ _ hdoomed, mul_zero]
        · simp [probOutput_eq_zero_of_not_mem_support hresult]

end SphincsSecurity.Concrete.OtsProbeSimulation
