import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelectionInitial

/-!
# Root-selection boundary

The failure-retaining materialized prefix is averaged over the same top-root result and root-output
parts as the exchangeable optional prefix. Its selected branch projects to that optional prefix,
while its failure branch remains explicit for the shared clean-finalization charge.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

noncomputable def materializedRootSelectionOutcomeAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (high : RootOutputHigh)
    (rootResult : CleanRunResult (Digest × SplitHashCache))
    (leftRoot rightRoot : Digest) : ProbComp MaterializedSelectionOutcome :=
  let output := fun root => rootOutputOfParts root high
  let context : DeferredContext := directDeferredContext rootResult.state
  let rootContext :=
    { context with values := context.values.install target (output leftRoot) }
  materializedActualRootAvoidingOrdinalSelectionOutcome ordinal parameter rootResult.value.1 target
    leftRoot rightRoot ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
    (materializedDeferredState rootContext) rootResult.remaining rootResult.table
    (rootInstalledCache target output rootResult.value.2 leftRoot)

theorem relTriple_materializedRootSelectionOutcomeAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (high : RootOutputHigh)
    (rootResult : CleanRunResult (Digest × SplitHashCache))
    (leftRoot rightRoot : Digest) :
    RelTriple
      (materializedRootSelectionOutcomeAfterRootResult ordinal adversary parameter ftsSecret
        target high rootResult leftRoot rightRoot)
      (materializedRootSelectionAfterRootResult ordinal adversary parameter ftsSecret target high
        rootResult leftRoot rightRoot)
      (MaterializedOutcomeOptionRel target leftRoot) := by
  unfold materializedRootSelectionOutcomeAfterRootResult
    materializedRootSelectionAfterRootResult
  exact relTriple_materializedActualOutcome_optionalSelection ordinal parameter rootResult.value.1
    target leftRoot rightRoot ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
    (materializedDeferredState
      { directDeferredContext rootResult.state with
        values := (directDeferredContext rootResult.state).values.install target
          (rootOutputOfParts leftRoot high) })
    rootResult.remaining rootResult.table
    (rootInstalledCache target (fun root => rootOutputOfParts root high) rootResult.value.2 leftRoot)

noncomputable def sampledHighMaterializedRootSelectionOutcomeAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    ProbComp (Digest × Digest × MaterializedSelectionOutcome) := do
  let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
  let leftRoot ← ($ᵗ Digest : ProbComp Digest)
  let rightRoot ← ($ᵗ Digest : ProbComp Digest)
  let outcome ← materializedRootSelectionOutcomeAfterRootResult ordinal adversary parameter
    ftsSecret target high rootResult leftRoot rightRoot
  pure (leftRoot, rightRoot, outcome)

set_option maxRecDepth 100000 in
theorem relTriple_sampledHigh_materializedRootSelectionOutcomeAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    RelTriple
      (sampledHighMaterializedRootSelectionOutcomeAfterRootResult ordinal adversary parameter
        ftsSecret target rootResult)
      (sampledHighMaterializedRootSelectionAfterRootResult ordinal adversary parameter ftsSecret
        target rootResult)
      (fun left right =>
        left.1 = right.1 ∧ left.2.1 = right.2.1 ∧
          MaterializedOutcomeOptionRel target left.1 left.2.2 right.2.2) := by
  unfold sampledHighMaterializedRootSelectionOutcomeAfterRootResult
    sampledHighMaterializedRootSelectionAfterRootResult
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
    (relTriple_materializedRootSelectionOutcomeAfterRootResult ordinal adversary parameter
      ftsSecret target leftHigh rootResult leftRoot leftComparison)
  intro leftOutcome rightSelection hselection
  exact relTriple_pure_pure ⟨rfl, rfl, hselection⟩

theorem probEvent_sampledHigh_materializedRootSelectionOutcome_match_le
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    Pr[fun result => result.2.2.Matches target result.1 |
        sampledHighMaterializedRootSelectionOutcomeAfterRootResult ordinal adversary parameter
          ftsSecret target rootResult] ≤
      Pr[fun result => materializedOrdinalSelectionMatches target result.1 result.2.2 |
        sampledHighMaterializedRootSelectionAfterRootResult ordinal adversary parameter ftsSecret
          target rootResult] := by
  apply probEvent_le_of_relTriple
    (relTriple_sampledHigh_materializedRootSelectionOutcomeAfterRootResult ordinal adversary
      parameter ftsSecret target rootResult)
  intro left right hrel hmatch
  rw [← hrel.1]
  exact hrel.2.2 hmatch

noncomputable def materializedRootOrdinalOutcomeExperimentAfterTable
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
      sampledHighMaterializedRootSelectionOutcomeAfterRootResult ordinal adversary parameter
        ftsSecret target result

set_option maxRecDepth 100000 in
theorem relTriple_materializedRootOrdinalOutcomeExperimentAfterTable
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    RelTriple
      (materializedRootOrdinalOutcomeExperimentAfterTable ordinal adversary parameter ftsSecret
        target fuel table)
      (materializedRootOrdinalMatchExperimentAfterTable ordinal adversary parameter ftsSecret
        target fuel table)
      (fun left right =>
        left.1 = right.1 ∧ left.2.1 = right.2.1 ∧
          MaterializedOutcomeOptionRel target left.1 left.2.2 right.2.2) := by
  unfold materializedRootOrdinalOutcomeExperimentAfterTable
    materializedRootOrdinalMatchExperimentAfterTable
  apply relTriple_bind (relTriple_refl
    (runCleanFromTable
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
      (maskedPublishedTreeRoot.run emptySplitHashCache)))
  intro leftRootResult rightRootResult hrootResult
  subst rightRootResult
  cases leftRootResult with
  | none =>
      exact relTriple_pure_pure ⟨rfl, rfl, fun hmatch => False.elim hmatch⟩
  | some result =>
      exact relTriple_sampledHigh_materializedRootSelectionOutcomeAfterRootResult ordinal
        adversary parameter ftsSecret target result

theorem probEvent_materializedRootOrdinalOutcome_match_le
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    Pr[fun result => result.2.2.Matches target result.1 |
        materializedRootOrdinalOutcomeExperimentAfterTable ordinal adversary parameter ftsSecret
          target fuel table] ≤
      Pr[fun result => materializedOrdinalSelectionAt target result.2 |
          materializedRootOrdinalProductionExperimentAfterTable ordinal adversary parameter
            ftsSecret target fuel table] *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ ≤ Pr[fun result => materializedOrdinalSelectionMatches target result.1 result.2.2 |
          materializedRootOrdinalMatchExperimentAfterTable ordinal adversary parameter ftsSecret
            target fuel table] := by
      apply probEvent_le_of_relTriple
        (relTriple_materializedRootOrdinalOutcomeExperimentAfterTable ordinal adversary parameter
          ftsSecret target fuel table)
      intro left right hrel hmatch
      rw [← hrel.1]
      exact hrel.2.2 hmatch
    _ ≤ _ := probEvent_materializedRootOrdinalMatchExperimentAfterTable_le_mul ordinal
      adversary parameter ftsSecret target hroot hparent fuel table

end SphincsSecurity.Concrete.OtsProbeSimulation
