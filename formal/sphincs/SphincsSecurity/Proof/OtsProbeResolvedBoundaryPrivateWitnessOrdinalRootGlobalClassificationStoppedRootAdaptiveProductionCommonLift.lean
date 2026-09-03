import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveProductionCommon

/-!
# Detailed common production lift

The target-specific clean production selector is dominated by an unrevealed position fiber of the
detailed permissive selector. Its explicit low and high output sampler is then normalized to the
ordinary deferred position resolver.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot

noncomputable def sampledHighInstalledPermissiveDetailedSelectionAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    ProbComp (Digest × Option PermissivePrivateOrdinalSelection) := do
  let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
  let leftRoot ← ($ᵗ Digest : ProbComp Digest)
  let output := fun root => rootOutputOfParts root high
  let context : DeferredContext := directDeferredContext rootResult.state
  let rootContext :=
    { context with values := context.values.install target (output leftRoot) }
  let selection ← permissiveDetailedRootAwareOrdinalSelection ordinal parameter
    rootResult.value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
    (materializedDeferredState rootContext) rootResult.remaining rootResult.table
    (rootInstalledCache target output rootResult.value.2 leftRoot)
  pure (leftRoot, selection)

noncomputable def resolvedInstalledPermissiveDetailedSelectionAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    ProbComp (Digest × Option PermissivePrivateOrdinalSelection) := do
  let resolved ← resolveDeferredPositionValue target
    (directDeferredContext rootResult.state)
  match resolved with
  | none => pure (0, none)
  | some resolved =>
      let selection ← permissiveDetailedRootAwareOrdinalSelection ordinal parameter
        rootResult.value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
        (materializedDeferredState resolved.toDeferredContext) rootResult.remaining
        rootResult.table
        (replaceHiddenRootCache target resolved.output rootResult.value.2)
      pure (truncateHash resolved.output, selection)

theorem relTriple_sampledHigh_materializedRootAwareProduction_installedPermissiveDetailed
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (rootResult : CleanRunResult (Digest × SplitHashCache))
    (hunrevealed : Coordinate.position target ∉ rootResult.state.revealed) :
    RelTriple
      (sampledHighMaterializedRootAwareSelectionProductionAfterRootResult ordinal adversary
        parameter ftsSecret target rootResult)
      (sampledHighInstalledPermissiveDetailedSelectionAfterRootResult ordinal adversary parameter
        ftsSecret target rootResult)
      (fun left right => left.1 = right.1 ∧
        MaterializedPermissiveDetailedSelectionRel target left.2 right.2) := by
  unfold sampledHighMaterializedRootAwareSelectionProductionAfterRootResult
    sampledHighInstalledPermissiveDetailedSelectionAfterRootResult
  apply relTriple_bind (relTriple_refl ($ᵗ RootOutputHigh : ProbComp RootOutputHigh))
  intro leftHigh rightHigh hhigh
  subst rightHigh
  apply relTriple_bind (relTriple_refl ($ᵗ Digest : ProbComp Digest))
  intro leftRoot rightRoot hrootEq
  subst rightRoot
  let output := fun root => rootOutputOfParts root leftHigh
  let context : DeferredContext := directDeferredContext rootResult.state
  let rootContext :=
    { context with values := context.values.install target (output leftRoot) }
  have hrootUnrevealed : Coordinate.position target ∉
      (materializedDeferredState rootContext).revealed := by
    change Coordinate.position target ∉ rootResult.state.revealed
    exact hunrevealed
  apply relTriple_bind
    (relTriple_materializedRootAware_permissiveDetailedRootAwareOrdinalSelection ordinal parameter
      rootResult.value.1 target hroot leftRoot leftRoot ftsSecret
      (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
      (materializedDeferredState rootContext) rootResult.remaining rootResult.table
      (rootInstalledCache target output rootResult.value.2 leftRoot) hrootUnrevealed)
  intro leftSelection rightSelection hselection
  exact relTriple_pure_pure ⟨rfl, hselection⟩

theorem probEvent_materializedRootAwareProduction_le_installedPermissiveDetailed
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (rootResult : CleanRunResult (Digest × SplitHashCache))
    (hunrevealed : Coordinate.position target ∉ rootResult.state.revealed) :
    Pr[fun result => materializedOrdinalSelectionAt target result.2 |
        sampledHighMaterializedRootAwareSelectionProductionAfterRootResult ordinal adversary
          parameter ftsSecret target rootResult] ≤
      Pr[fun result =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? result.2 = some target |
        sampledHighInstalledPermissiveDetailedSelectionAfterRootResult ordinal adversary
          parameter ftsSecret target rootResult] := by
  apply probEvent_le_of_relTriple
    (relTriple_sampledHigh_materializedRootAwareProduction_installedPermissiveDetailed ordinal
      adversary parameter ftsSecret target hroot rootResult hunrevealed)
  intro left right hrelation hleft
  exact hrelation.2 hleft

set_option maxRecDepth 100000 in
theorem evalDist_sampledHighInstalledPermissiveDetailed_eq_resolved
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache))
    (hstate : rootResult.state.values (.position target) = none)
    (hpending : rootResult.state.pending = ∅) :
    evalDist
        (sampledHighInstalledPermissiveDetailedSelectionAfterRootResult ordinal adversary
          parameter ftsSecret target rootResult) =
      evalDist
        (resolvedInstalledPermissiveDetailedSelectionAfterRootResult ordinal adversary
          parameter ftsSecret target rootResult) := by
  unfold resolvedInstalledPermissiveDetailedSelectionAfterRootResult
  rw [resolveDeferredPositionValue_fresh target (directDeferredContext rootResult.state)]
  · have hhit : ∀ output, ¬rootResult.state.hitAt (.position target) output := by
      intro output
      simp [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt, hpending]
    simp only [directDeferredContext, hhit, ↓reduceIte]
    have hclear : rootResult.state.clearPending (.position target) = rootResult.state := by
      rcases hrootState : rootResult.state with ⟨pending, values, revealed, ensured⟩
      simp only [LazyRevealProbe.State.clearPending]
      have hp : pending = ∅ := by simpa only [hrootState] using hpending
      simp [LazyRevealProbe.State.pendingAway, hp]
    rw [hclear]
    unfold sampledHighInstalledPermissiveDetailedSelectionAfterRootResult rootInstalledCache
    let parts : ProbComp HashOutput := do
      let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
      let root ← ($ᵗ Digest : ProbComp Digest)
      pure (rootOutputOfParts root high)
    have hparts : evalDist parts = evalDist LazyRevealProbe.sampleHashOutput := by
      calc
        _ = evalDist (do
              let root ← ($ᵗ Digest : ProbComp Digest)
              let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
              pure (rootOutputOfParts root high)) := by
            exact OracleComp.DeferredSampling.evalDist_bind_comm
              ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
              ($ᵗ Digest : ProbComp Digest)
              (fun high root => pure (rootOutputOfParts root high))
        _ = _ := evalDist_sample_rootOutputOfParts
    let continuation := fun output : HashOutput => do
      let selection ← permissiveDetailedRootAwareOrdinalSelection ordinal parameter
        rootResult.value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
        (materializedDeferredState
          { state := rootResult.state
            values := (directDeferredValues rootResult.state).install target output })
        rootResult.remaining rootResult.table
        (replaceHiddenRootCache target output rootResult.value.2)
      pure (truncateHash output, selection)
    calc
      _ = evalDist (parts >>= continuation) := by
        simp [parts, continuation, directDeferredContext, bind_assoc]
      _ = evalDist (LazyRevealProbe.sampleHashOutput >>= continuation) := by
        exact evalDist_bind_eq_of_evalDist_eq hparts continuation
      _ = _ := by rfl
  · simpa [directDeferredContext] using hstate
  · simpa [directDeferredContext, directDeferredValues] using hstate

theorem probEvent_materializedRootAwareProduction_le_resolvedPermissiveDetailed_afterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (rootResult : CleanRunResult (Digest × SplitHashCache))
    (hresult : some rootResult ∈ support
      (runCleanFromTable
        (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
        (maskedPublishedTreeRoot.run emptySplitHashCache))) :
    Pr[fun result => materializedOrdinalSelectionAt target result.2 |
        sampledHighMaterializedRootAwareSelectionProductionAfterRootResult ordinal adversary
          parameter ftsSecret target rootResult] ≤
      Pr[fun result =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? result.2 = some target |
        resolvedInstalledPermissiveDetailedSelectionAfterRootResult ordinal adversary parameter
          ftsSecret target rootResult] := by
  have habsent := target_absent_of_mem_runCleanFromTable_maskedPublishedTreeRoot target hroot
    hparent fuel table rootResult hresult
  have hpending := pending_eq_empty_of_mem_runCleanFromTable_maskedPublishedTreeRoot fuel table
    rootResult hresult
  calc
    _ ≤ Pr[fun result =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? result.2 = some target |
        sampledHighInstalledPermissiveDetailedSelectionAfterRootResult ordinal adversary
          parameter ftsSecret target rootResult] :=
      probEvent_materializedRootAwareProduction_le_installedPermissiveDetailed ordinal adversary
        parameter ftsSecret target hroot rootResult habsent.2
    _ = _ := by
      apply OracleComp.probEvent_congr' (fun _ _ => Iff.rfl)
      exact evalDist_sampledHighInstalledPermissiveDetailed_eq_resolved ordinal adversary parameter
        ftsSecret target rootResult habsent.1 hpending

noncomputable def resolvedInstalledPermissiveDetailedSelectionExperimentAfterTable
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    ProbComp (Digest × Option PermissivePrivateOrdinalSelection) := do
  let rootResult ← runCleanFromTable
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
    (maskedPublishedTreeRoot.run emptySplitHashCache)
  match rootResult with
  | none => pure (0, none)
  | some result =>
      resolvedInstalledPermissiveDetailedSelectionAfterRootResult ordinal adversary parameter
        ftsSecret target result

theorem probEvent_materializedRootAwareProduction_le_resolvedPermissiveDetailed
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    Pr[fun result => materializedOrdinalSelectionAt target result.2 |
        materializedRootAwareOrdinalProductionExperimentAfterTable ordinal adversary parameter
          ftsSecret target fuel table] ≤
      Pr[fun result =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? result.2 = some target |
        resolvedInstalledPermissiveDetailedSelectionExperimentAfterTable ordinal adversary
          parameter ftsSecret target fuel table] := by
  unfold materializedRootAwareOrdinalProductionExperimentAfterTable
    resolvedInstalledPermissiveDetailedSelectionExperimentAfterTable
  apply probEvent_bind_le_bind_of_forall_le
  intro rootResult hresult
  cases rootResult with
  | none => simp [materializedOrdinalSelectionAt,
      permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?]
  | some rootResult =>
      exact
        probEvent_materializedRootAwareProduction_le_resolvedPermissiveDetailed_afterRootResult
          ordinal adversary parameter ftsSecret target hroot hparent fuel table rootResult hresult

end SphincsSecurity.Concrete.OtsProbeSimulation
