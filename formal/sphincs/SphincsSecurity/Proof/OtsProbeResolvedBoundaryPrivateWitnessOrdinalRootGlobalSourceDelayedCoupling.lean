import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveNormalizedSignerStrong
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveProduction

/-!
# Delayed source permissive coupling

A completed deferred execution is coupled to the same computation in the permissive materialized
interpreter. Stopped deferred executions impose no obligation. This is the local action rule used by
the delayed-root selector bridge.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def DirectWitnessPermissiveRunRel :
    DirectWitnessResult α → Option (CleanRunResult α) → Prop
  | .done left, some right =>
      left.value = right.value ∧
        left.remaining = right.remaining ∧
        left.table = right.table ∧
        left.context.state.revealed = right.state.revealed ∧
        (materializedDeferredState left.context).values = right.state.values
  | .done _, none => False
  | _, _ => True

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedWitness_runPermissiveFromTable
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hcouples : DirectWitnessFinalizationMaterializedCouples table computation) :
    RelTriple
      (runDirectResolvedWitnessFromTable context fuel table (computation.run cache))
      (runPermissiveFromTable (materializedDeferredState context) fuel table
        (computation.run cache))
      DirectWitnessPermissiveRunRel := by
  let materialized := materializedDeferredContext context
  have hcontext : FinalizationContextEq table (some context) (some materialized) :=
    finalizationContextEq_materializedDeferredContext hvalid hcompletable
  have hstrong := hcouples context materialized fuel fuel cache cache hcontext rfl rfl rfl (by
    simp [materialized, materializedDeferredContext, directDeferredContext])
  have hstrength : RelTriple
      (runDirectResolvedWitnessFromTable context fuel table (computation.run cache))
      (runDirectResolvedDetailedFromTable materialized fuel table (computation.run cache))
      (fun left right ↦ DirectWitnessPermissiveRunRel left
        (projectDirectDetailedClean right)) := by
    apply relTriple_post_mono hstrong
    intro left right hrelation
    cases left with
    | stoppedFuel => trivial
    | stoppedOrdinary => trivial
    | stoppedPrivate witness => trivial
    | done left =>
        cases right with
        | stopped reason =>
            simp [DirectWitnessFinalizationMaterializedRunEq] at hrelation
        | done right =>
            rcases hrelation with
              ⟨hvalue, _hcontext, hremaining, _hrightRemaining, htable, _hrightTable,
                hcache, hrevealed, hmaterialized, _hle, _hright⟩
            exact ⟨Prod.ext hvalue hcache, hremaining.trans _hrightRemaining.symm,
              htable.trans _hrightTable.symm, hrevealed, hmaterialized⟩
  have hproject : RelTriple
      (runDirectResolvedWitnessFromTable context fuel table (computation.run cache))
      (projectDirectDetailedClean <$>
        runDirectResolvedDetailedFromTable materialized fuel table (computation.run cache))
      DirectWitnessPermissiveRunRel := by
    have hmapped := relTriple_map (R := DirectWitnessPermissiveRunRel)
      (f := id) (g := projectDirectDetailedClean) hstrength
    rw [id_map] at hmapped
    exact hmapped
  have hprojectEq :
      projectDirectDetailedClean <$>
          runDirectResolvedDetailedFromTable materialized fuel table (computation.run cache) =
        runCleanFromTable (materializedDeferredState context) fuel table
          (computation.run cache) := by
    simpa [materialized, materializedDeferredContext] using
      (map_projectDirectDetailedClean_run_eq_clean (computation.run cache)
        (materializedDeferredState context) fuel table)
  have hclean : RelTriple
      (runDirectResolvedWitnessFromTable context fuel table (computation.run cache))
      (runCleanFromTable (materializedDeferredState context) fuel table
        (computation.run cache))
      DirectWitnessPermissiveRunRel :=
    relTriple_of_evalDist_eq_right (congrArg evalDist hprojectEq) hproject
  have hpermissive := relTriple_runCleanFromTable_runPermissiveFromTable
    (computation.run cache) (materializedDeferredState context) fuel table
  have hglued := SphincsSecurity.relTriple_trans_exists hclean hpermissive
  apply relTriple_post_mono hglued
  intro left right hrelation
  obtain ⟨middle, hleft, hright⟩ := hrelation
  cases left with
  | stoppedFuel => trivial
  | stoppedOrdinary => trivial
  | stoppedPrivate witness => trivial
  | done left =>
      cases middle with
      | none => exact False.elim hleft
      | some middle =>
          cases right with
          | none =>
              simp only [CleanPermissiveRel] at hright
              cases hright
          | some right =>
              have heq : right = middle := by
                exact Option.some.inj (by simpa [CleanPermissiveRel] using hright)
              subst right
              exact hleft

end SphincsSecurity.Concrete.OtsProbeSimulation
