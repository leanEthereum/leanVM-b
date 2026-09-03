import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSourceDelayedSelectionSampling
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelectionInitial

/-!
# Delayed source root production

The older materialized root selector has exactly the delayed source hash schedule: it records the root-aware candidate and executes only the source public action. This module reuses its root-swap bound and connects its production marginal to the delayed permissive selector.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option linter.constructorNameAsVariable false
attribute [local irreducible] maskedPublishedTreeRoot

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_materializedRoot_permissiveDelayedOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hunrevealed : Coordinate.position target ∉ state.revealed) :
    RelTriple
      (materializedActualRootAvoidingOrdinalSelection ordinal parameter publicRoot target
        leftRoot rightRoot ftsSecret computation candidates state fuel table cache)
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter publicRoot ftsSecret
        computation candidates state fuel table cache)
      (MaterializedPermissiveDetailedSelectionRel target) := by
  induction computation using OracleComp.inductionOn generalizing candidates state fuel cache with
  | pure value =>
      simp only [materializedActualRootAvoidingOrdinalSelection,
        materializedRootAvoidingOrdinalSelection,
        delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_pure]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_selected_materializedPermissiveDetailedSelection target hroot
          (candidates.get ⟨ordinal, hselected⟩) state candidates hunrevealed
      · simp only [hselected, ↓reduceDIte]
        apply relTriple_pure_pure
        simp [MaterializedPermissiveDetailedSelectionRel, materializedOrdinalSelectionAt]
  | query_bind query next ih =>
      rw [materializedActualRootAvoidingOrdinalSelection,
        materializedRootAvoidingOrdinalSelection, OracleComp.construct_query_bind,
        delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_selected_materializedPermissiveDetailedSelection target hroot
          (candidates.get ⟨ordinal, hselected⟩) state candidates hunrevealed
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                let leftObserve : LazyRevealProbe.State Coordinate → Nat → Fin (n + 1) →
                    SplitHashCache → List Probe → ProbComp (Option Probe) :=
                  fun nextState remaining output nextCache laterCandidates =>
                    materializedActualRootAvoidingOrdinalSelection ordinal parameter
                      publicRoot target leftRoot rightRoot ftsSecret (next output) laterCandidates
                      nextState remaining table nextCache
                let rightObserve : LazyRevealProbe.State Coordinate → Nat → Fin (n + 1) →
                    SplitHashCache → List Probe →
                      ProbComp (Option PermissivePrivateOrdinalSelection) :=
                  fun nextState remaining output nextCache laterCandidates =>
                    delayedPermissiveDetailedOrdinalSelection ordinal parameter publicRoot
                      ftsSecret (next output) laterCandidates nextState remaining table nextCache
                apply relTriple_bind
                  (relTriple_runCleanFromTable_runPermissiveFromTable
                    ((splitUniformImpl n).run cache) state fuel table)
                intro leftResult rightResult hresult
                apply relTriple_finishMaterializedPermissiveDetailedSelection target leftObserve
                  rightObserve candidates leftResult rightResult hresult
                intro result hnextUnrevealed
                simpa [leftObserve, rightObserve] using
                  ih result.value.1 candidates result.state result.remaining result.value.2
                    hnextUnrevealed
            | inr input =>
                simp only
                let publicContext := materializedCanonicalContext table state
                let plan := purePlanProbingHashQuery parameter input publicContext.state
                let candidate? := rootAwareCandidateForPlan? parameter input plan
                let nextCandidates := appendPlannedCandidate candidates candidate?
                have hnextCandidates :
                    permissiveRootAwareCandidates parameter input table state candidates =
                      nextCandidates := by
                  rfl
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hleftSelected : ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state))).length := by
                    simpa [publicContext, plan, candidate?, nextCandidates] using hnextSelected
                  have hrightSelected : ordinal <
                      (permissiveRootAwareCandidates parameter input table state candidates).length :=
                    by simpa [hnextCandidates] using hnextSelected
                  simp only [hleftSelected, hrightSelected, ↓reduceDIte]
                  exact relTriple_pure_selected_materializedPermissiveDetailedSelection target
                    hroot (nextCandidates.get ⟨ordinal, hnextSelected⟩) state nextCandidates
                    hunrevealed
                · have hleftSelected : ¬ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state))).length := by
                    simpa [publicContext, plan, candidate?, nextCandidates] using hnextSelected
                  have hrightSelected : ¬ordinal <
                      (permissiveRootAwareCandidates parameter input table state candidates).length :=
                    by simpa [hnextCandidates] using hnextSelected
                  simp only [hleftSelected, hrightSelected, ↓reduceDIte]
                  by_cases hsafe : RootAwareCandidateAvoidsRoots target leftRoot rightRoot candidate?
                  · have hsafeActual : RootAwareCandidateAvoidsRoots target leftRoot rightRoot
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [publicContext, plan, candidate?] using hsafe
                    simp only [hsafeActual, ↓reduceIte]
                    let leftObserve : LazyRevealProbe.State Coordinate → Nat → HashOutput →
                        SplitHashCache → List Probe → ProbComp (Option Probe) :=
                      fun nextState remaining output nextCache laterCandidates =>
                        materializedActualRootAvoidingOrdinalSelection ordinal parameter
                          publicRoot target leftRoot rightRoot ftsSecret (next output)
                          laterCandidates nextState remaining table nextCache
                    let rightObserve : LazyRevealProbe.State Coordinate → Nat → HashOutput →
                        SplitHashCache → List Probe →
                          ProbComp (Option PermissivePrivateOrdinalSelection) :=
                      fun nextState remaining output nextCache laterCandidates =>
                        delayedPermissiveDetailedOrdinalSelection ordinal parameter publicRoot
                          ftsSecret (next output) laterCandidates nextState remaining table nextCache
                    let inner :=
                      (probingHashQueryAfterPublicPlan parameter input publicContext.state plan).run
                        cache
                    have hrightAction :
                        delayedPermissivePublicAction parameter input table state cache = inner := by
                      rfl
                    rw [hrightAction]
                    apply relTriple_bind
                      (relTriple_runCleanFromTable_runPermissiveFromTable inner state fuel table)
                    intro leftResult rightResult hresult
                    apply relTriple_finishMaterializedPermissiveDetailedSelection target
                      leftObserve rightObserve nextCandidates leftResult rightResult hresult
                    intro result hnextUnrevealed
                    simpa [leftObserve, rightObserve] using
                      ih result.value.1 nextCandidates result.state result.remaining result.value.2
                        hnextUnrevealed
                  · have hsafeActual : ¬RootAwareCandidateAvoidsRoots target leftRoot rightRoot
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [publicContext, plan, candidate?] using hsafe
                    simp only [hsafeActual, ↓reduceIte]
                    exact relTriple_none_any_materializedPermissiveDetailedSelection target _
        | inr message =>
            let leftObserve : LazyRevealProbe.State Coordinate → Nat → Option Signature →
                SplitHashCache → List Probe → ProbComp (Option Probe) :=
              fun nextState remaining output nextCache laterCandidates =>
                materializedActualRootAvoidingOrdinalSelection ordinal parameter publicRoot
                  target leftRoot rightRoot ftsSecret (next output) laterCandidates nextState
                  remaining table nextCache
            let rightObserve : LazyRevealProbe.State Coordinate → Nat → Option Signature →
                SplitHashCache → List Probe →
                  ProbComp (Option PermissivePrivateOrdinalSelection) :=
              fun nextState remaining output nextCache laterCandidates =>
                delayedPermissiveDetailedOrdinalSelection ordinal parameter publicRoot ftsSecret
                  (next output) laterCandidates nextState remaining table nextCache
            apply relTriple_bind
              (relTriple_runCleanFromTable_runPermissiveFromTable
                ((maskedSign parameter publicRoot ftsSecret message).run cache) state fuel table)
            intro leftResult rightResult hresult
            apply relTriple_finishMaterializedPermissiveDetailedSelection target leftObserve
              rightObserve candidates leftResult rightResult hresult
            intro result hnextUnrevealed
            simpa [leftObserve, rightObserve] using
              ih result.value.1 candidates result.state result.remaining result.value.2
                hnextUnrevealed

noncomputable def sampledHighInstalledDelayedSelectionAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    ProbComp (Digest × Option PermissivePrivateOrdinalSelection) := do
  let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
  let leftRoot ← ($ᵗ Digest : ProbComp Digest)
  let output := fun root => rootOutputOfParts root high
  let selection ← delayedPermissiveDetailedOrdinalSelection ordinal parameter
    rootResult.value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
    (preloadPositionValue target (output leftRoot) rootResult.state) rootResult.remaining
    rootResult.table
    (rootInstalledCache target output rootResult.value.2 leftRoot)
  pure (leftRoot, selection)

theorem relTriple_sampledHigh_materializedRootProduction_installedDelayed
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (rootResult : CleanRunResult (Digest × SplitHashCache))
    (hvalue : rootResult.state.values (.position target) = none)
    (hunrevealed : Coordinate.position target ∉ rootResult.state.revealed) :
    RelTriple
      (sampledHighMaterializedRootSelectionProductionAfterRootResult ordinal adversary
        parameter ftsSecret target rootResult)
      (sampledHighInstalledDelayedSelectionAfterRootResult ordinal adversary parameter
        ftsSecret target rootResult)
      (fun left right => left.1 = right.1 ∧
        MaterializedPermissiveDetailedSelectionRel target left.2 right.2) := by
  unfold sampledHighMaterializedRootSelectionProductionAfterRootResult
    sampledHighInstalledDelayedSelectionAfterRootResult
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
  have hbase :=
    (relTriple_materializedRoot_permissiveDelayedOrdinalSelection ordinal parameter
      rootResult.value.1 target hroot leftRoot leftRoot ftsSecret
      (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
      (materializedDeferredState rootContext) rootResult.remaining rootResult.table
      (rootInstalledCache target output rootResult.value.2 leftRoot) hrootUnrevealed)
  have hstate : PermissiveStateRel (materializedDeferredState rootContext)
      (preloadPositionValue target (output leftRoot) rootResult.state) := by
    constructor
    · funext coordinate
      cases coordinate with
      | chainStart => rfl
      | position position =>
          by_cases heq : position = target
          · subst position
            simp [rootContext, context, DeferredContext.positionValue, directDeferredContext,
              DeferredStructuralValues.install, hvalue]
          · have hcoordinate : Coordinate.position position ≠ Coordinate.position target := by
              simpa using heq
            simp only [rootContext, context, materializedDeferredState_position,
              DeferredContext.positionValue, directDeferredContext,
              DeferredStructuralValues.install, Function.update_of_ne heq,
              preloadPositionValue_values_of_ne target (output leftRoot) rootResult.state
                (.position position) hcoordinate]
            unfold directDeferredValues
            cases rootResult.state.values (.position position) <;> rfl
    · rfl
  have htransport :=
    relTriple_delayedPermissiveDetailedOrdinalSelection_of_stateRel ordinal parameter
      rootResult.value.1 ftsSecret
      (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) [] []
      (materializedDeferredState rootContext)
      (preloadPositionValue target (output leftRoot) rootResult.state)
      rootResult.remaining rootResult.table
      (rootInstalledCache target output rootResult.value.2 leftRoot) rfl hstate
  have hglued := SphincsSecurity.relTriple_trans_exists hbase htransport
  have hcombined : RelTriple
      (materializedActualRootAvoidingOrdinalSelection ordinal parameter rootResult.value.1 target
        leftRoot leftRoot ftsSecret
        (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
        (materializedDeferredState rootContext) rootResult.remaining rootResult.table
        (rootInstalledCache target output rootResult.value.2 leftRoot))
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter rootResult.value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
        (preloadPositionValue target (output leftRoot) rootResult.state) rootResult.remaining
        rootResult.table (rootInstalledCache target output rootResult.value.2 leftRoot))
      (MaterializedPermissiveDetailedSelectionRel target) := by
    apply relTriple_post_mono hglued
    intro left right hrelation
    obtain ⟨middle, hleft, hright⟩ := hrelation
    intro hselected
    have hmiddle := hleft hselected
    exact hright.positionFiber_eq.symm.trans hmiddle
  apply relTriple_bind hcombined
  intro leftSelection rightSelection hselection
  exact relTriple_pure_pure ⟨rfl, hselection⟩

theorem probEvent_materializedRootProduction_le_sampledHighInstalledDelayed
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (rootResult : CleanRunResult (Digest × SplitHashCache))
    (hvalue : rootResult.state.values (.position target) = none)
    (hunrevealed : Coordinate.position target ∉ rootResult.state.revealed) :
    Pr[fun result => materializedOrdinalSelectionAt target result.2 |
        sampledHighMaterializedRootSelectionProductionAfterRootResult ordinal adversary
          parameter ftsSecret target rootResult] ≤
      Pr[fun result =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? result.2 = some target |
        sampledHighInstalledDelayedSelectionAfterRootResult ordinal adversary parameter
          ftsSecret target rootResult] := by
  apply probEvent_le_of_relTriple
    (relTriple_sampledHigh_materializedRootProduction_installedDelayed ordinal adversary
      parameter ftsSecret target hroot rootResult hvalue hunrevealed)
  intro left right hrelation hleft
  exact hrelation.2 hleft

theorem evalDist_sampledHighInstalledDelayed_snd_eq_installed
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    evalDist
        (Prod.snd <$>
          sampledHighInstalledDelayedSelectionAfterRootResult ordinal adversary parameter
            ftsSecret target rootResult) =
      evalDist
        (installedDelayedPermissiveDetailedSelectionAfterRootResult ordinal adversary parameter
          ftsSecret target rootResult) := by
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
  let continuation := fun output : HashOutput =>
    delayedPermissiveDetailedOrdinalSelection ordinal parameter rootResult.value.1 ftsSecret
      (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
      (preloadPositionValue target output rootResult.state) rootResult.remaining rootResult.table
      (replaceHiddenRootCache target output rootResult.value.2)
  calc
    _ = evalDist (parts >>= continuation) := by
      simp [sampledHighInstalledDelayedSelectionAfterRootResult, parts, continuation,
        rootInstalledCache, bind_assoc, map_eq_bind_pure_comp]
    _ = evalDist (LazyRevealProbe.sampleHashOutput >>= continuation) :=
      evalDist_bind_eq_of_evalDist_eq hparts continuation
    _ = _ := by
      rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem probEvent_materializedRootProduction_le_installedDelayed
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    Pr[fun result => materializedOrdinalSelectionAt target result.2 |
        materializedRootOrdinalProductionExperimentAfterTable ordinal adversary parameter
          ftsSecret target fuel table] ≤
      Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        installedDelayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary
          parameter ftsSecret target fuel table] := by
  unfold materializedRootOrdinalProductionExperimentAfterTable
    installedDelayedPermissiveDetailedSelectionExperimentAfterTable
  apply probEvent_bind_le_bind_of_forall_le
  intro rootResult hresult
  cases rootResult with
  | none =>
      simp [materializedOrdinalSelectionAt,
        permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?]
  | some rootResult =>
      have habsent := target_absent_of_mem_runCleanFromTable_maskedPublishedTreeRoot target hroot
        hparent fuel table rootResult hresult
      calc
        _ ≤ Pr[fun result =>
              permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? result.2 = some target |
            sampledHighInstalledDelayedSelectionAfterRootResult ordinal adversary parameter
              ftsSecret target rootResult] :=
          probEvent_materializedRootProduction_le_sampledHighInstalledDelayed ordinal adversary
            parameter ftsSecret target hroot rootResult habsent.1 habsent.2
        _ = Pr[fun selection =>
              permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
            Prod.snd <$> sampledHighInstalledDelayedSelectionAfterRootResult ordinal adversary
              parameter ftsSecret target rootResult] := by
          rw [probEvent_map]
          rfl
        _ = _ := by
          apply OracleComp.probEvent_congr' (fun _ _ => Iff.rfl)
          exact evalDist_sampledHighInstalledDelayed_snd_eq_installed ordinal adversary parameter
            ftsSecret target rootResult

set_option maxRecDepth 100000 in
theorem probEvent_materializedRootOrdinalMatch_le_common_mul
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    Pr[fun result => materializedOrdinalSelectionMatches target result.1 result.2.2 |
        materializedRootOrdinalMatchExperimentAfterTable ordinal adversary parameter ftsSecret
          target fuel table] ≤
      Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
          ftsSecret fuel table] * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ ≤ Pr[fun result => materializedOrdinalSelectionAt target result.2 |
          materializedRootOrdinalProductionExperimentAfterTable ordinal adversary parameter
            ftsSecret target fuel table] * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
      probEvent_materializedRootOrdinalMatchExperimentAfterTable_le_mul ordinal adversary
        parameter ftsSecret target hroot hparent fuel table
    _ ≤ Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        installedDelayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary
          parameter ftsSecret target fuel table] * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
      gcongr
      exact probEvent_materializedRootProduction_le_installedDelayed ordinal adversary parameter
        ftsSecret target hroot hparent fuel table
    _ ≤ _ := by
      gcongr
      exact probEvent_installedDelayedSelection_fiber_le_common ordinal adversary parameter
        ftsSecret target hroot hparent fuel table

end SphincsSecurity.Concrete.OtsProbeSimulation
