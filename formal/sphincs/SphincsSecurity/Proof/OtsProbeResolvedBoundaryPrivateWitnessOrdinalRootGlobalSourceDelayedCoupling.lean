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

def DirectWitnessRejected
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α) : Prop :=
  let canonical := canonicalizeMaterializedValues table result.context
  PrivateStructuralHit canonical ∨
    ¬PublishedValues result.context.state ∨
    ¬DeferredCompletable table canonical

def DirectWitnessPermissiveRunRel
    (table : OtsSecretIndex → HashOutput) :
    DirectWitnessResult α → Option (CleanRunResult α) → Prop
  | .done left, right =>
      DirectWitnessRejected table left ∨
        ∃ clean, right = some clean ∧
          left.value = clean.value ∧
          left.remaining = clean.remaining ∧
          left.table = table ∧
          clean.table = table ∧
          left.context.state.revealed = clean.state.revealed ∧
          (materializedDeferredState left.context).values = clean.state.values ∧
          ChainState.ValidFor (fun _ ↦ True) left.context.state ∧
          FinalizationContextEq table (some left.context)
            (some (directDeferredContext clean.state))
  | _, _ => True

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedWitness_runCleanFromTable
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hchainValid : ChainState.ValidFor (fun _ ↦ True) context.state)
    (hpreserves : PreservesChainValid (fun _ ↦ True) computation)
    (hcouples : DirectWitnessFinalizationMaterializedCouples table computation) :
    RelTriple
      (runDirectResolvedWitnessFromTable context fuel table (computation.run cache))
      (runCleanFromTable (materializedDeferredState context) fuel table
        (computation.run cache))
      (DirectWitnessPermissiveRunRel table) := by
  let materialized := materializedDeferredContext context
  have hcontext : FinalizationContextEq table (some context) (some materialized) :=
    finalizationContextEq_materializedDeferredContext hvalid hcompletable
  have hstrong := hcouples context materialized fuel fuel cache cache hcontext rfl rfl rfl (by
    simp [materialized, materializedDeferredContext, directDeferredContext])
  have hstrongSupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hstrong
      (fun result => match result with
        | .done resolved => ChainState.ValidFor (fun _ ↦ True) resolved.context.state
        | _ => True) (by
        intro result hresult
        cases result with
        | stoppedFuel => trivial
        | stoppedOrdinary => trivial
        | stoppedPrivate witness => trivial
        | done resolved =>
            have hdetailed : DirectDetailedResult.done resolved ∈ support
                (runDirectResolvedDetailedFromTable context fuel table
                  (computation.run cache)) := by
              rw [← map_erase_runDirectResolvedWitnessFromTable
                (computation.run cache) context fuel table, support_map]
              exact ⟨.done resolved, hresult, rfl⟩
            have hdirect : some resolved ∈ support
                (runDirectResolvedFromTable context fuel table (computation.run cache)) :=
              mem_support_runDirectResolvedFromTable_of_done_detailed
                (computation.run cache) context fuel table resolved hdetailed
            exact chainValid_of_mem_runDirectResolvedFromTable (fun _ ↦ True) computation
              context fuel table cache resolved hpreserves hchainValid hdirect)
  have hstrength : RelTriple
      (runDirectResolvedWitnessFromTable context fuel table (computation.run cache))
      (runDirectResolvedDetailedFromTable materialized fuel table (computation.run cache))
      (fun left right ↦ DirectWitnessPermissiveRunRel table left
        (projectDirectDetailedClean right)) := by
    apply relTriple_post_mono hstrongSupported
    intro left right hrelation
    rcases hrelation with ⟨hrelation, hleftChainValid⟩
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
            let clean : CleanRunResult (α × SplitHashCache) :=
              ⟨right.context.state, right.remaining, right.value, right.table⟩
            refine Or.inr ⟨clean, rfl, Prod.ext hvalue hcache,
              hremaining.trans _hrightRemaining.symm,
              htable, _hrightTable, hrevealed, hmaterialized, hleftChainValid, ?_⟩
            rw [_hright] at _hcontext
            exact _hcontext
  have hproject : RelTriple
      (runDirectResolvedWitnessFromTable context fuel table (computation.run cache))
      (projectDirectDetailedClean <$>
        runDirectResolvedDetailedFromTable materialized fuel table (computation.run cache))
      (DirectWitnessPermissiveRunRel table) := by
    have hmapped := relTriple_map (R := DirectWitnessPermissiveRunRel table)
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
  exact relTriple_of_evalDist_eq_right (congrArg evalDist hprojectEq) hproject

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedWitness_runPermissiveFromTable
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hchainValid : ChainState.ValidFor (fun _ ↦ True) context.state)
    (hpreserves : PreservesChainValid (fun _ ↦ True) computation)
    (hcouples : DirectWitnessFinalizationMaterializedCouples table computation) :
    RelTriple
      (runDirectResolvedWitnessFromTable context fuel table (computation.run cache))
      (runPermissiveFromTable (materializedDeferredState context) fuel table
        (computation.run cache))
      (DirectWitnessPermissiveRunRel table) := by
  have hclean := relTriple_runDirectResolvedWitness_runCleanFromTable computation context fuel table
    cache hvalid hcompletable hchainValid hpreserves hcouples
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
      | none =>
          exact Or.inl (by
            rcases hleft with hreject | ⟨clean, hnone, _⟩
            · exact hreject
            · cases hnone)
      | some middle =>
          cases right with
          | none =>
              simp only [CleanPermissiveRel] at hright
              cases hright
          | some right =>
              have heq : right = middle := by
                exact Option.some.inj (by simpa [CleanPermissiveRel] using hright)
              subst right
              rcases hleft with hreject | ⟨clean, hclean, hfields⟩
              · exact Or.inl hreject
              · exact Or.inr ⟨clean, hclean, hfields⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
