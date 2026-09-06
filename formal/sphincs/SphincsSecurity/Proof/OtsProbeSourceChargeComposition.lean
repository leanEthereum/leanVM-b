import SphincsSecurity.Proof.OtsProbeSourceAllowanceComponents

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem liveSourceCharge_eq_zero_of_not_completable
    (charge : (OtsSecretIndex → HashOutput) → DeferredContext → LazyRevealProbe.Query Coordinate → ENNReal) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hcomplete : ¬DeferredCompletable table context) :
    liveSourceCharge charge computation context fuel table = 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next _ => rw [liveSourceCharge_query_bind, if_neg hcomplete]

noncomputable def sourceContinuationCharge
    (charge : (OtsSecretIndex → HashOutput) → DeferredContext → LazyRevealProbe.Query Coordinate → ENNReal)
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β) : Option (ResolvedRunResult α) → ENNReal
  | none => 0
  | some result => liveSourceCharge charge (next result.value) result.context result.remaining result.table

theorem liveSourceCharge_bind
    (charge : (OtsSecretIndex → HashOutput) → DeferredContext → LazyRevealProbe.Query Coordinate → ENNReal)
    (left : OracleComp (LazyRevealProbe.World Coordinate) α) (next : α → OracleComp (LazyRevealProbe.World Coordinate) β)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    liveSourceCharge charge (left >>= next) context fuel table =
      liveSourceCharge charge left context fuel table +
        ∑' result, Pr[= result | runResolvedFromTable context fuel table left] * sourceContinuationCharge charge next result := by
  induction left using OracleComp.inductionOn generalizing context fuel table with
  | pure value => simp [liveSourceCharge, runResolvedFromTable, sourceContinuationCharge]
  | query_bind input continuation ih =>
      by_cases hcomplete : DeferredCompletable table context
      · rw [bind_assoc, liveSourceCharge_query_bind, liveSourceCharge_query_bind,
          if_pos hcomplete, if_pos hcomplete, runResolvedFromTable_bind, tsum_probOutput_bind_mul, add_assoc, ← ENNReal.tsum_add]
        congr 1
        apply tsum_congr
        intro result
        by_cases hresult : result ∈ support (runResolvedFromTable context fuel table (liftM (OracleSpec.query input)))
        · cases result with
          | none => simp [sourceContinuationCharge]
          | some result =>
              have hcore := resolvedCore_of_mem_runResolvedFromTable (liftM (OracleSpec.query input)) context fuel table result hconsistent hstarts hresult
              dsimp only
              rw [ih result.value result.context result.remaining result.table hcore.2.1 (hcore.1 ▸ hcore.2.2), mul_add, ← ENNReal.tsum_mul_left]
        · simp [probOutput_eq_zero_of_not_mem_support hresult]
      · rw [liveSourceCharge_eq_zero_of_not_completable charge _ context fuel table hcomplete,
          liveSourceCharge_eq_zero_of_not_completable charge _ context fuel table hcomplete, zero_add]
        symm
        apply ENNReal.tsum_eq_zero.mpr
        intro result
        by_cases hresult : result ∈ support (runResolvedFromTable context fuel table
            ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= continuation))
        · cases result with
          | none => simp [sourceContinuationCharge]
          | some result =>
              have hcore := resolvedCore_of_mem_runResolvedFromTable _ context fuel table result hconsistent hstarts hresult
              have hdoomed := not_deferredCompletable_of_mem_runResolvedFromTable _ context fuel table result hconsistent hstarts hresult hcomplete
              simp only [sourceContinuationCharge, hcore.1,
                liveSourceCharge_eq_zero_of_not_completable charge _ _ _ _ hdoomed, mul_zero]
        · simp [probOutput_eq_zero_of_not_mem_support hresult]

theorem liveSourceCharge_map
    (charge : (OtsSecretIndex → HashOutput) → DeferredContext → LazyRevealProbe.Query Coordinate → ENNReal)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (f : α → β)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    liveSourceCharge charge (f <$> computation) context fuel table = liveSourceCharge charge computation context fuel table := by
  rw [map_eq_bind_pure_comp, liveSourceCharge_bind charge computation _ context fuel table hconsistent hstarts]
  calc
    _ = liveSourceCharge charge computation context fuel table + 0 := by
      congr 1
      apply ENNReal.tsum_eq_zero.mpr
      intro result
      cases result <;> simp [sourceContinuationCharge, liveSourceCharge]
    _ = _ := add_zero _

end SphincsSecurity.Concrete.OtsProbeSimulation
