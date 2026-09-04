import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAwareExperiment

/-!
# Root-aware failure-retaining experiment

The exact shared-prefix outcome is lifted through the public root samplers and projected to the
root-aware optional selector. Its match event therefore inherits the production-weighted one-guess
bound without discarding the explicit failure marker needed by the joint stopped coupling.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option linter.constructorNameAsVariable false
attribute [local irreducible] maskedPublishedTreeRoot

noncomputable def sampledHighMaterializedRootAwareOutcomeAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    ProbComp (Digest × Digest × MaterializedSelectionOutcome) := do
  let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
  let leftRoot ← ($ᵗ Digest : ProbComp Digest)
  let rightRoot ← ($ᵗ Digest : ProbComp Digest)
  let output := fun root => rootOutputOfParts root high
  let context : DeferredContext := directDeferredContext rootResult.state
  let rootContext :=
    { context with values := context.values.install target (output leftRoot) }
  let outcome ← materializedActualRootAwareOrdinalSelectionOutcome ordinal parameter
    rootResult.value.1 target leftRoot rightRoot ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
    (materializedDeferredState rootContext) rootResult.remaining rootResult.table
    (rootInstalledCache target output rootResult.value.2 leftRoot)
  pure (leftRoot, rightRoot, outcome)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_sampledHigh_materializedRootAwareOutcome_optional
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    RelTriple
      (sampledHighMaterializedRootAwareOutcomeAfterRootResult ordinal adversary parameter
        ftsSecret target rootResult)
      (sampledHighMaterializedRootAwareSelectionAfterRootResult ordinal adversary parameter
        ftsSecret target rootResult)
      (fun left right =>
        left.1 = right.1 ∧ left.2.1 = right.2.1 ∧
          MaterializedOutcomeOptionRel target left.1 left.2.2 right.2.2) := by
  unfold sampledHighMaterializedRootAwareOutcomeAfterRootResult
    sampledHighMaterializedRootAwareSelectionAfterRootResult
  apply relTriple_bind (relTriple_refl ($ᵗ RootOutputHigh : ProbComp RootOutputHigh))
  intro leftHigh rightHigh hhigh
  subst rightHigh
  apply relTriple_bind (relTriple_refl ($ᵗ Digest : ProbComp Digest))
  intro leftRoot rightRoot hroot
  subst rightRoot
  apply relTriple_bind (relTriple_refl ($ᵗ Digest : ProbComp Digest))
  intro leftComparison rightComparison hcomparison
  subst rightComparison
  apply relTriple_bind
    (relTriple_materializedActualRootAwareOutcome_optionalSelection ordinal parameter
      rootResult.value.1 target leftRoot leftComparison ftsSecret
      (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
      (materializedDeferredState
        { directDeferredContext rootResult.state with
          values := (directDeferredContext rootResult.state).values.install target
            (rootOutputOfParts leftRoot leftHigh) })
      rootResult.remaining rootResult.table
      (rootInstalledCache target (fun root => rootOutputOfParts root leftHigh)
        rootResult.value.2 leftRoot))
  intro leftOutcome rightSelection hselection
  exact relTriple_pure_pure ⟨rfl, rfl, hselection⟩

noncomputable def materializedRootAwareOrdinalOutcomeExperimentAfterTable
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    ProbComp (Digest × Digest × MaterializedSelectionOutcome) := do
  let rootResult ← runCleanFromTable
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
    (maskedPublishedTreeRoot.run emptySplitHashCache)
  match rootResult with
  | none => pure (0, 0, .failed)
  | some result =>
      sampledHighMaterializedRootAwareOutcomeAfterRootResult ordinal adversary parameter
        ftsSecret target result

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_materializedRootAwareOrdinalOutcome_optional
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    RelTriple
      (materializedRootAwareOrdinalOutcomeExperimentAfterTable ordinal adversary parameter
        ftsSecret target fuel table)
      (materializedRootAwareOrdinalMatchExperimentAfterTable ordinal adversary parameter
        ftsSecret target fuel table)
      (fun left right =>
        left.1 = right.1 ∧ left.2.1 = right.2.1 ∧
          MaterializedOutcomeOptionRel target left.1 left.2.2 right.2.2) := by
  unfold materializedRootAwareOrdinalOutcomeExperimentAfterTable
    materializedRootAwareOrdinalMatchExperimentAfterTable
  apply relTriple_bind (relTriple_refl
    (runCleanFromTable (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)))
  intro leftResult rightResult hresult
  subst rightResult
  cases leftResult with
  | none =>
      exact relTriple_pure_pure ⟨rfl, rfl, fun hmatch => False.elim hmatch⟩
  | some result =>
      exact relTriple_sampledHigh_materializedRootAwareOutcome_optional ordinal adversary
        parameter ftsSecret target result

theorem probEvent_materializedRootAwareOrdinalOutcome_match_le
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    Pr[fun result => result.2.2.Matches target result.1 |
        materializedRootAwareOrdinalOutcomeExperimentAfterTable ordinal adversary parameter
          ftsSecret target fuel table] ≤
      Pr[fun result => materializedOrdinalSelectionAt target result.2 |
          materializedRootAwareOrdinalProductionExperimentAfterTable ordinal adversary parameter
            ftsSecret target fuel table] *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ ≤ Pr[fun result => materializedOrdinalSelectionMatches target result.1 result.2.2 |
          materializedRootAwareOrdinalMatchExperimentAfterTable ordinal adversary parameter
            ftsSecret target fuel table] := by
      apply probEvent_le_of_relTriple
        (relTriple_materializedRootAwareOrdinalOutcome_optional ordinal adversary parameter
          ftsSecret target fuel table)
      intro left right hrelation hmatch
      rw [← hrelation.1]
      exact hrelation.2.2 hmatch
    _ ≤ _ := probEvent_materializedRootAwareOrdinalMatchExperimentAfterTable_le_mul ordinal
      adversary parameter ftsSecret target hroot hparent fuel table

end SphincsSecurity.Concrete.OtsProbeSimulation
