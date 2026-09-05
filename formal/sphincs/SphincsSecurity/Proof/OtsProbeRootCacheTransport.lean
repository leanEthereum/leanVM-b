import SphincsSecurity.Proof.OtsProbeRootCache
import SphincsSecurity.Proof.OtsProbeSelectionHistory

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

set_option maxRecDepth 100000 in
theorem positionValue_old_or_materialized_of_done_direct
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (result : ResolvedRunResult α)
    (hresult : DirectWitnessResult.done result ∈ support
      (runDirectResolvedWitnessFromTable context fuel table computation))
    (position : Position) (output : HashOutput)
    (hvalue : result.context.positionValue position = some output) :
    context.positionValue position = some output ∨ result.context.state.values (.position position) = some output := by
  have hdetailed : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table computation) := by
    rw [← map_erase_runDirectResolvedWitnessFromTable computation context fuel table, support_map]
    exact ⟨DirectWitnessResult.done result, hresult, rfl⟩
  cases hfinalState : result.context.state.values (.position position) with
  | some finalOutput =>
      right
      simpa only [DeferredContext.positionValue, hfinalState] using hvalue
  | none =>
      left
      have hfinalPrivate : result.context.values position = some output := by
        simpa only [DeferredContext.positionValue, hfinalState] using hvalue
      cases hstate : context.state.values (.position position) with
      | some initialOutput =>
          have hpreserved := valuesLE_of_done_runDirectResolvedDetailedFromTable
            computation context fuel table result hdetailed (.position position) initialOutput hstate
          rw [hfinalState] at hpreserved
          contradiction
      | none =>
          cases hprivate : context.values position with
          | none =>
              have hmissing := auxiliaryPositionValue_none_of_done_runDirectResolvedWitnessFromTable
                position computation context fuel table result hstate hprivate hresult hfinalState
              rw [hfinalPrivate] at hmissing
              contradiction
          | some initialOutput =>
              have hpreserved := privateValuesLE_of_done_runDirectResolvedDetailedFromTable
                computation context fuel table result hdetailed position initialOutput hprivate
              have heq : initialOutput = output := Option.some.inj (hpreserved.symm.trans hfinalPrivate)
              simp only [DeferredContext.positionValue, hstate, hprivate, heq]

theorem RootValuesCached.of_done_direct
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {initialCache finalCache : QueryCache HashSpec}
    (hclosed : RootValuesCached parameter table context initialCache) (hle : initialCache ≤ finalCache)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (fuel : Nat)
    (result : ResolvedRunResult α)
    (hresult : DirectWitnessResult.done result ∈ support
      (runDirectResolvedWitnessFromTable context fuel table computation))
    (hvisible : VisibleResolvedComputationsCached parameter table result.context finalCache) :
    RootValuesCached parameter table result.context finalCache :=
  hclosed.of_materialized_or_previous hle hvisible
    (fun lay tree output hvalue => positionValue_old_or_materialized_of_done_direct
      computation context fuel table result hresult (layerRootPosition lay tree) output hvalue)

theorem RootValuesCached.of_done_direct_canonicalized
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {initialCache finalCache : QueryCache HashSpec}
    (hclosed : RootValuesCached parameter table context initialCache) (hle : initialCache ≤ finalCache)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (fuel : Nat)
    (result : ResolvedRunResult α)
    (hresult : DirectWitnessResult.done result ∈ support
      (runDirectResolvedWitnessFromTable context fuel table computation))
    (hvisible : VisibleResolvedComputationsCached parameter table result.context finalCache)
    (hconsistent : result.context.ValuesConsistent) :
    RootValuesCached parameter table (canonicalizeMaterializedValues table result.context) finalCache :=
  (hclosed.of_done_direct hle computation fuel result hresult hvisible).canonicalize hconsistent

theorem RootValuesCached.of_positionValue_eq
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {left right : DeferredContext} {cache : QueryCache HashSpec}
    (hclosed : RootValuesCached parameter table left cache)
    (hvalues : ∀ position, right.positionValue position = left.positionValue position) :
    RootValuesCached parameter table right cache := by
  intro lay tree output hvalue
  exact hclosed lay tree output ((hvalues _).symm.trans hvalue)

theorem RootValuesCached.materialized_shadow
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {cache : QueryCache HashSpec}
    (hclosed : RootValuesCached parameter table context cache) :
    RootValuesCached parameter table (materializedDeferredContext context) cache := by
  apply hclosed.of_positionValue_eq
  intro position
  cases hstate : context.state.values (.position position) <;>
    cases hprivate : context.values position <;>
    simp [materializedDeferredContext, directDeferredContext, directDeferredValues,
      materializedDeferredState, DeferredContext.positionValue, hstate, hprivate]

theorem RootValuesCached.of_canonicalSelectionPreserved
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {left : PrivateOrdinalSelection} {right : PermissivePrivateOrdinalSelection}
    {cache : QueryCache HashSpec}
    (hclosed : RootValuesCached parameter table left.context cache)
    (hrelation : CanonicalSelectionPreserved (some left) (some right)) :
    RootValuesCached parameter table (directDeferredContext right.state) cache := by
  apply hclosed.materialized_shadow.of_positionValue_eq
  intro position
  simp only [materializedDeferredContext, directDeferredContext, directDeferredValues,
    DeferredContext.positionValue]
  rw [← hrelation.2.1.values]

end SphincsSecurity.Concrete.OtsProbeSimulation
