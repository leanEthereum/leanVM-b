import SphincsSecurity.Proof.OtsProbePrivateMissingAllowance

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem privateLiveMissingProbeAllowance_eq_zero_of_not_completable
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hcomplete : ¬DeferredCompletable table context) :
    privateLiveMissingProbeAllowance target computation context fuel table = 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next _ => rw [privateLiveMissingProbeAllowance_query_bind, if_neg hcomplete]

noncomputable def privateMissingContinuationAllowance
    (target : Position)
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β) : Option (ResolvedRunResult α) → ENNReal
  | none => 0
  | some result => privateLiveMissingProbeAllowance target (next result.value) result.context result.remaining result.table

theorem privateLiveMissingProbeAllowance_bind
    (target : Position)
    (left : OracleComp (LazyRevealProbe.World Coordinate) α) (next : α → OracleComp (LazyRevealProbe.World Coordinate) β)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    privateLiveMissingProbeAllowance target (left >>= next) context fuel table =
      privateLiveMissingProbeAllowance target left context fuel table +
        ∑' result, Pr[= result | runResolvedFromTable context fuel table left] * privateMissingContinuationAllowance target next result := by
  induction left using OracleComp.inductionOn generalizing context fuel table with
  | pure value => simp [privateLiveMissingProbeAllowance, runResolvedFromTable, privateMissingContinuationAllowance]
  | query_bind input continuation ih =>
      by_cases hcomplete : DeferredCompletable table context
      · rw [bind_assoc, privateLiveMissingProbeAllowance_query_bind, privateLiveMissingProbeAllowance_query_bind,
          if_pos hcomplete, if_pos hcomplete, runResolvedFromTable_bind, tsum_probOutput_bind_mul, add_assoc, ← ENNReal.tsum_add]
        congr 1
        apply tsum_congr
        intro result
        by_cases hresult : result ∈ support (runResolvedFromTable context fuel table (liftM (OracleSpec.query input)))
        · cases result with
          | none => simp [privateMissingContinuationAllowance]
          | some result =>
              have hcore := resolvedCore_of_mem_runResolvedFromTable (liftM (OracleSpec.query input)) context fuel table result hconsistent hstarts hresult
              dsimp only
              rw [ih result.value result.context result.remaining result.table hcore.2.1 (hcore.1 ▸ hcore.2.2), mul_add, ← ENNReal.tsum_mul_left]
        · simp [probOutput_eq_zero_of_not_mem_support hresult]
      · rw [privateLiveMissingProbeAllowance_eq_zero_of_not_completable target _ context fuel table hcomplete,
          privateLiveMissingProbeAllowance_eq_zero_of_not_completable target _ context fuel table hcomplete, zero_add]
        symm
        apply ENNReal.tsum_eq_zero.mpr
        intro result
        by_cases hresult : result ∈ support (runResolvedFromTable context fuel table
            ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= continuation))
        · cases result with
          | none => simp [privateMissingContinuationAllowance]
          | some result =>
              have hcore := resolvedCore_of_mem_runResolvedFromTable _ context fuel table result hconsistent hstarts hresult
              have hdoomed := not_deferredCompletable_of_mem_runResolvedFromTable _ context fuel table result hconsistent hstarts hresult hcomplete
              simp only [privateMissingContinuationAllowance, hcore.1,
                privateLiveMissingProbeAllowance_eq_zero_of_not_completable target _ _ _ _ hdoomed, mul_zero]
        · simp [probOutput_eq_zero_of_not_mem_support hresult]

end SphincsSecurity.Concrete.OtsProbeSimulation
