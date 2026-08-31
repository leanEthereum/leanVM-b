import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelectionOutcomeProbability

/-!
# Comparison-root guard weakening

Removing the comparison-root stop from the materialized optional prefix cannot destroy a selected
match. The resulting reference run depends on the actual root but not on the independently sampled
comparison root.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def MaterializedOptionMatchRel
    (target : Position) (root : Digest) : Option Probe → Option Probe → Prop :=
  fun left right =>
    materializedOrdinalSelectionMatches target root left →
      materializedOrdinalSelectionMatches target root right

theorem relTriple_none_any_materializedOptionMatch
    (target : Position) (root : Digest) (right : ProbComp (Option Probe)) :
    RelTriple (pure none : ProbComp (Option Probe)) right
      (MaterializedOptionMatchRel target root) := by
  have hbase := relTriple_true (pure none : ProbComp (Option Probe)) right
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun selection => selection = none) (by
        intro selection hselection
        simpa using hselection)
  apply relTriple_post_mono hsupported
  intro leftSelection rightSelection hrelation hmatch
  rw [hrelation.2] at hmatch
  exact False.elim hmatch

theorem relTriple_finishMaterializedSelection_weaken
    (target : Position) (matchRoot : Digest)
    (leftObserve rightObserve : LazyRevealProbe.State Coordinate → Nat → α →
      SplitHashCache → List Probe → ProbComp (Option Probe))
    (candidates : List Probe) (result : Option (CleanRunResult (α × SplitHashCache)))
    (hnext : ∀ resolved : CleanRunResult (α × SplitHashCache),
      RelTriple
        (leftObserve resolved.state resolved.remaining resolved.value.1 resolved.value.2 candidates)
        (rightObserve resolved.state resolved.remaining resolved.value.1 resolved.value.2 candidates)
        (MaterializedOptionMatchRel target matchRoot)) :
    RelTriple
      (finishMaterializedPrivateOrdinalSelection leftObserve candidates result)
      (finishMaterializedPrivateOrdinalSelection rightObserve candidates result)
      (MaterializedOptionMatchRel target matchRoot) := by
  cases result with
  | none => exact relTriple_none_any_materializedOptionMatch target matchRoot _
  | some resolved =>
      unfold finishMaterializedPrivateOrdinalSelection
      exact hnext resolved

theorem rootAwareCandidateAvoidsRoots_actual
    (target : Position) (leftRoot rightRoot : Digest) (candidate? : Option Probe)
    (havoid : RootAwareCandidateAvoidsRoots target leftRoot rightRoot candidate?) :
    RootAwareCandidateAvoidsRoots target leftRoot leftRoot candidate? := by
  cases candidate? with
  | none => simp [RootAwareCandidateAvoidsRoots]
  | some candidate =>
      rw [rootAwareCandidateAvoidsRoots_iff] at havoid ⊢
      exact ⟨havoid.1, havoid.1⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_materializedRootAvoidingOrdinalSelection_weaken_comparison
    (ordinal : Nat) (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot matchRoot : Digest)
    (signer : Message → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    RelTriple
      (materializedRootAvoidingOrdinalSelection ordinal parameter target leftRoot rightRoot signer
        computation candidates state fuel table cache)
      (materializedRootAvoidingOrdinalSelection ordinal parameter target leftRoot leftRoot signer
        computation candidates state fuel table cache)
      (MaterializedOptionMatchRel target matchRoot) := by
  induction computation using OracleComp.inductionOn generalizing candidates state fuel cache with
  | pure value =>
      simp only [materializedRootAvoidingOrdinalSelection, OracleComp.construct_pure]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure (fun hmatch => hmatch)
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure (fun hmatch => hmatch)
  | query_bind query next ih =>
      rw [materializedRootAvoidingOrdinalSelection, OracleComp.construct_query_bind,
        materializedRootAvoidingOrdinalSelection, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure (fun hmatch => hmatch)
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                let leftObserve : LazyRevealProbe.State Coordinate → Nat → Fin (n + 1) →
                    SplitHashCache → List Probe → ProbComp (Option Probe) :=
                  fun nextState remaining output nextCache laterCandidates =>
                    materializedRootAvoidingOrdinalSelection ordinal parameter target leftRoot
                      rightRoot signer (next output) laterCandidates nextState remaining table
                      nextCache
                let rightObserve : LazyRevealProbe.State Coordinate → Nat → Fin (n + 1) →
                    SplitHashCache → List Probe → ProbComp (Option Probe) :=
                  fun nextState remaining output nextCache laterCandidates =>
                    materializedRootAvoidingOrdinalSelection ordinal parameter target leftRoot
                      leftRoot signer (next output) laterCandidates nextState remaining table
                      nextCache
                apply relTriple_bind
                  (relTriple_refl
                    (runCleanFromTable state fuel table ((splitUniformImpl n).run cache)))
                intro leftResult rightResult hresult
                subst rightResult
                apply relTriple_finishMaterializedSelection_weaken target matchRoot
                  (continueMaterializedPrivateOrdinalSelection target leftObserve)
                  (continueMaterializedPrivateOrdinalSelection target rightObserve)
                  candidates leftResult
                intro resolved
                unfold continueMaterializedPrivateOrdinalSelection
                by_cases hrevealed : Coordinate.position target ∈ resolved.state.revealed
                · simp [hrevealed, MaterializedOptionMatchRel,
                    materializedOrdinalSelectionMatches]
                · simpa [hrevealed, leftObserve, rightObserve] using
                    ih resolved.value.1 candidates resolved.state resolved.remaining
                      resolved.value.2
            | inr input =>
                let publicContext := materializedCanonicalContext table state
                let plan := purePlanProbingHashQuery parameter input publicContext.state
                let candidate? := rootAwareCandidateForPlan? parameter input plan
                let nextCandidates := appendPlannedCandidate candidates candidate?
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hactual : ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state))).length := by
                    simpa [publicContext, plan, candidate?, nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  exact relTriple_pure_pure (fun hmatch => hmatch)
                · have hactual : ¬ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state))).length := by
                    simpa [publicContext, plan, candidate?, nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  by_cases hsafe : RootAwareCandidateAvoidsRoots target leftRoot rightRoot candidate?
                  · have hsafeActual : RootAwareCandidateAvoidsRoots target leftRoot rightRoot
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [publicContext, plan, candidate?] using hsafe
                    have hleftSafe := rootAwareCandidateAvoidsRoots_actual target leftRoot rightRoot
                      candidate? hsafe
                    have hleftSafeActual : RootAwareCandidateAvoidsRoots target leftRoot leftRoot
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [publicContext, plan, candidate?] using hleftSafe
                    simp only [hsafeActual, hleftSafeActual, ↓reduceIte]
                    let leftObserve : LazyRevealProbe.State Coordinate → Nat → HashOutput →
                        SplitHashCache → List Probe → ProbComp (Option Probe) :=
                      fun nextState remaining output nextCache laterCandidates =>
                        materializedRootAvoidingOrdinalSelection ordinal parameter target leftRoot
                          rightRoot signer (next output) laterCandidates nextState remaining table
                          nextCache
                    let rightObserve : LazyRevealProbe.State Coordinate → Nat → HashOutput →
                        SplitHashCache → List Probe → ProbComp (Option Probe) :=
                      fun nextState remaining output nextCache laterCandidates =>
                        materializedRootAvoidingOrdinalSelection ordinal parameter target leftRoot
                          leftRoot signer (next output) laterCandidates nextState remaining table
                          nextCache
                    apply relTriple_bind
                      (relTriple_refl
                        (runCleanFromTable state fuel table
                          ((probingHashQueryAfterPublicPlan parameter input publicContext.state plan).run
                            cache)))
                    intro leftResult rightResult hresult
                    subst rightResult
                    apply relTriple_finishMaterializedSelection_weaken target matchRoot
                      (continueMaterializedPrivateOrdinalSelection target leftObserve)
                      (continueMaterializedPrivateOrdinalSelection target rightObserve)
                      nextCandidates leftResult
                    intro resolved
                    unfold continueMaterializedPrivateOrdinalSelection
                    by_cases hrevealed : Coordinate.position target ∈ resolved.state.revealed
                    · simp [hrevealed, MaterializedOptionMatchRel,
                        materializedOrdinalSelectionMatches]
                    · simpa [hrevealed, leftObserve, rightObserve] using
                        ih resolved.value.1 nextCandidates resolved.state resolved.remaining
                          resolved.value.2
                  · have hsafeActual : ¬RootAwareCandidateAvoidsRoots target leftRoot rightRoot
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [publicContext, plan, candidate?] using hsafe
                    simp only [hsafeActual, ↓reduceIte]
                    exact relTriple_none_any_materializedOptionMatch target matchRoot _
        | inr message =>
            let leftObserve : LazyRevealProbe.State Coordinate → Nat → Option Signature →
                SplitHashCache → List Probe → ProbComp (Option Probe) :=
              fun nextState remaining output nextCache laterCandidates =>
                materializedRootAvoidingOrdinalSelection ordinal parameter target leftRoot
                  rightRoot signer (next output) laterCandidates nextState remaining table nextCache
            let rightObserve : LazyRevealProbe.State Coordinate → Nat → Option Signature →
                SplitHashCache → List Probe → ProbComp (Option Probe) :=
              fun nextState remaining output nextCache laterCandidates =>
                materializedRootAvoidingOrdinalSelection ordinal parameter target leftRoot leftRoot
                  signer (next output) laterCandidates nextState remaining table nextCache
            apply relTriple_bind
              (relTriple_refl (runCleanFromTable state fuel table ((signer message).run cache)))
            intro leftResult rightResult hresult
            subst rightResult
            apply relTriple_finishMaterializedSelection_weaken target matchRoot
              (continueMaterializedPrivateOrdinalSelection target leftObserve)
              (continueMaterializedPrivateOrdinalSelection target rightObserve)
              candidates leftResult
            intro resolved
            unfold continueMaterializedPrivateOrdinalSelection
            by_cases hrevealed : Coordinate.position target ∈ resolved.state.revealed
            · simp [hrevealed, MaterializedOptionMatchRel,
                materializedOrdinalSelectionMatches]
            · simpa [hrevealed, leftObserve, rightObserve] using
                ih resolved.value.1 candidates resolved.state resolved.remaining resolved.value.2

theorem probEvent_materializedRootAvoidingOrdinalSelection_match_le_actual_guard
    (ordinal : Nat) (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot matchRoot : Digest)
    (signer : Message → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    Pr[materializedOrdinalSelectionMatches target matchRoot |
        materializedRootAvoidingOrdinalSelection ordinal parameter target leftRoot rightRoot signer
          computation candidates state fuel table cache] ≤
      Pr[materializedOrdinalSelectionMatches target matchRoot |
        materializedRootAvoidingOrdinalSelection ordinal parameter target leftRoot leftRoot signer
          computation candidates state fuel table cache] :=
  probEvent_le_of_relTriple
    (relTriple_materializedRootAvoidingOrdinalSelection_weaken_comparison ordinal parameter target
      leftRoot rightRoot matchRoot signer computation candidates state fuel table cache)
    (fun _ _ hrelation => hrelation)

def selectedProbeDigest : Option Probe → Digest
  | none => 0
  | some candidate => candidate.candidate

def materializedOrdinalSelectionAt
    (target : Position) : Option Probe → Prop
  | none => False
  | some candidate => candidate.coordinate = .position target

theorem materializedOrdinalSelectionMatches_root_eq_selectedProbeDigest
    {target : Position} {root : Digest} {selection : Option Probe}
    (hmatch : materializedOrdinalSelectionMatches target root selection) :
    root = selectedProbeDigest selection := by
  cases selection with
  | none => exact False.elim hmatch
  | some candidate =>
      unfold materializedOrdinalSelectionMatches at hmatch
      subst candidate
      rfl

theorem materializedOrdinalSelectionAt_of_matches
    {target : Position} {root : Digest} {selection : Option Probe}
    (hmatch : materializedOrdinalSelectionMatches target root selection) :
    materializedOrdinalSelectionAt target selection := by
  cases selection with
  | none => exact False.elim hmatch
  | some candidate =>
      unfold materializedOrdinalSelectionMatches at hmatch
      subst candidate
      rfl

set_option maxRecDepth 100000 in
theorem probEvent_sampledComparisonRoot_materializedSelectionMatches_le
    (ordinal : Nat) (parameter : PublicParameter) (target : Position)
    (leftRoot : Digest)
    (signer : Message → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    Pr[fun result : Digest × Option Probe =>
        materializedOrdinalSelectionMatches target result.1 result.2 | do
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      let selection ← materializedRootAvoidingOrdinalSelection ordinal parameter target
        leftRoot rightRoot signer computation candidates state fuel table cache
      pure (rightRoot, selection)] ≤
      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  let reference := materializedRootAvoidingOrdinalSelection ordinal parameter target leftRoot
    leftRoot signer computation candidates state fuel table cache
  calc
    _ ≤ Pr[fun result : Digest × Option Probe =>
          materializedOrdinalSelectionMatches target result.1 result.2 | do
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        let selection ← reference
        pure (rightRoot, selection)] := by
      apply probEvent_bind_le_bind_of_forall_le
      intro rightRoot _hrightRoot
      rw [show (do
          let selection ← materializedRootAvoidingOrdinalSelection ordinal parameter target
            leftRoot rightRoot signer computation candidates state fuel table cache
          pure (rightRoot, selection)) =
        (fun selection => (rightRoot, selection)) <$>
          materializedRootAvoidingOrdinalSelection ordinal parameter target leftRoot rightRoot
            signer computation candidates state fuel table cache by
          simp [map_eq_bind_pure_comp],
        show (do
          let selection ← reference
          pure (rightRoot, selection)) =
        (fun selection => (rightRoot, selection)) <$> reference by
          simp [map_eq_bind_pure_comp], probEvent_map, probEvent_map]
      exact probEvent_materializedRootAvoidingOrdinalSelection_match_le_actual_guard ordinal
        parameter target leftRoot rightRoot rightRoot signer computation candidates state fuel table
        cache
    _ ≤ Pr[fun result : Digest × Option Probe =>
          result.1 = selectedProbeDigest result.2 | do
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        let selection ← reference
        pure (rightRoot, selection)] := by
      apply probEvent_mono
      intro result _hresult hmatch
      exact materializedOrdinalSelectionMatches_root_eq_selectedProbeDigest hmatch
    _ ≤ _ := by
      apply probEvent_uniform_root_matches_distribution_independent_guess_le
        (fun _rightRoot => reference) reference
      · intro rightRoot
        rfl

set_option maxRecDepth 100000 in
theorem probEvent_sampledComparisonRoot_materializedSelectionMatches_le_mul
    (ordinal : Nat) (parameter : PublicParameter) (target : Position)
    (leftRoot : Digest)
    (signer : Message → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    Pr[fun result : Digest × Option Probe =>
        materializedOrdinalSelectionMatches target result.1 result.2 | do
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      let selection ← materializedRootAvoidingOrdinalSelection ordinal parameter target
        leftRoot rightRoot signer computation candidates state fuel table cache
      pure (rightRoot, selection)] ≤
      Pr[materializedOrdinalSelectionAt target |
          materializedRootAvoidingOrdinalSelection ordinal parameter target leftRoot leftRoot signer
            computation candidates state fuel table cache] *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  let reference := materializedRootAvoidingOrdinalSelection ordinal parameter target leftRoot
    leftRoot signer computation candidates state fuel table cache
  calc
    _ ≤ Pr[fun result : Digest × Option Probe =>
          materializedOrdinalSelectionMatches target result.1 result.2 | do
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        let selection ← reference
        pure (rightRoot, selection)] := by
      apply probEvent_bind_le_bind_of_forall_le
      intro rightRoot _hrightRoot
      rw [show (do
          let selection ← materializedRootAvoidingOrdinalSelection ordinal parameter target
            leftRoot rightRoot signer computation candidates state fuel table cache
          pure (rightRoot, selection)) =
        (fun selection => (rightRoot, selection)) <$>
          materializedRootAvoidingOrdinalSelection ordinal parameter target leftRoot rightRoot
            signer computation candidates state fuel table cache by
          simp [map_eq_bind_pure_comp],
        show (do
          let selection ← reference
          pure (rightRoot, selection)) =
        (fun selection => (rightRoot, selection)) <$> reference by
          simp [map_eq_bind_pure_comp], probEvent_map, probEvent_map]
      exact probEvent_materializedRootAvoidingOrdinalSelection_match_le_actual_guard ordinal
        parameter target leftRoot rightRoot rightRoot signer computation candidates state fuel table
        cache
    _ ≤ Pr[fun result : Digest × Option Probe =>
          materializedOrdinalSelectionAt target result.2 ∧
            result.1 = selectedProbeDigest result.2 | do
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        let selection ← reference
        pure (rightRoot, selection)] := by
      apply probEvent_mono
      intro result _hresult hmatch
      exact ⟨materializedOrdinalSelectionAt_of_matches hmatch,
        materializedOrdinalSelectionMatches_root_eq_selectedProbeDigest hmatch⟩
    _ ≤ _ := by
      apply probEvent_uniform_root_matches_distribution_independent_guess_le_mul
        (fun _rightRoot => reference) reference
      intro rightRoot
      rfl

set_option maxRecDepth 100000 in
theorem probEvent_uniformActualRoot_match_le_of_swap_of_comparison
    (target : Position)
    (run : Digest → Digest → ProbComp (Option Probe))
    (reference : Digest → ProbComp (Option Probe))
    (hswap : ∀ leftRoot rightRoot,
      evalDist (run leftRoot rightRoot) = evalDist (run rightRoot leftRoot))
    (hcomparison : ∀ leftRoot rightRoot,
      Pr[materializedOrdinalSelectionMatches target rightRoot | run leftRoot rightRoot] ≤
        Pr[materializedOrdinalSelectionMatches target rightRoot | reference leftRoot]) :
    Pr[fun result : Digest × Digest × Option Probe =>
        materializedOrdinalSelectionMatches target result.1 result.2.2 | do
      let leftRoot ← ($ᵗ Digest : ProbComp Digest)
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      let selection ← run leftRoot rightRoot
      pure (leftRoot, rightRoot, selection)] ≤
      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  let sampled := ($ᵗ Digest : ProbComp Digest)
  let actual : ProbComp (Digest × Digest × Option Probe) := do
    let leftRoot ← sampled
    let rightRoot ← sampled
    let selection ← run leftRoot rightRoot
    pure (leftRoot, rightRoot, selection)
  let swapped : ProbComp (Digest × Digest × Option Probe) := do
    let leftRoot ← sampled
    let rightRoot ← sampled
    let selection ← run rightRoot leftRoot
    pure (leftRoot, rightRoot, selection)
  let comparison : ProbComp (Digest × Digest × Option Probe) := do
    let leftRoot ← sampled
    let rightRoot ← sampled
    let selection ← run leftRoot rightRoot
    pure (rightRoot, leftRoot, selection)
  let referenceComparison : ProbComp (Digest × Digest × Option Probe) := do
    let leftRoot ← sampled
    let rightRoot ← sampled
    let selection ← reference leftRoot
    pure (rightRoot, leftRoot, selection)
  have hreplace : evalDist actual = evalDist swapped := by
    unfold actual swapped
    apply evalDist_bind_congr
    intro leftRoot _hleftRoot
    apply evalDist_bind_congr
    intro rightRoot _hrightRoot
    rw [evalDist_bind, evalDist_bind, hswap leftRoot rightRoot]
  have hcommute : evalDist swapped = evalDist comparison := by
    unfold swapped comparison
    exact OracleComp.DeferredSampling.evalDist_bind_comm sampled sampled
      (fun leftRoot rightRoot => do
        let selection ← run rightRoot leftRoot
        pure (leftRoot, rightRoot, selection))
  change Pr[fun result : Digest × Digest × Option Probe =>
      materializedOrdinalSelectionMatches target result.1 result.2.2 | actual] ≤ _
  calc
    _ = Pr[fun result : Digest × Digest × Option Probe =>
          materializedOrdinalSelectionMatches target result.1 result.2.2 | comparison] :=
      OracleComp.probEvent_congr' (fun _ _ => Iff.rfl) (hreplace.trans hcommute)
    _ ≤ Pr[fun result : Digest × Digest × Option Probe =>
          materializedOrdinalSelectionMatches target result.1 result.2.2 |
          referenceComparison] := by
      unfold comparison referenceComparison
      apply probEvent_bind_le_bind_of_forall_le
      intro leftRoot _hleftRoot
      apply probEvent_bind_le_bind_of_forall_le
      intro rightRoot _hrightRoot
      rw [show (do
          let selection ← run leftRoot rightRoot
          pure (rightRoot, leftRoot, selection)) =
        (fun selection => (rightRoot, leftRoot, selection)) <$> run leftRoot rightRoot by
          simp [map_eq_bind_pure_comp],
        show (do
          let selection ← reference leftRoot
          pure (rightRoot, leftRoot, selection)) =
        (fun selection => (rightRoot, leftRoot, selection)) <$> reference leftRoot by
          simp [map_eq_bind_pure_comp], probEvent_map, probEvent_map]
      exact hcomparison leftRoot rightRoot
    _ ≤ ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
      unfold referenceComparison
      apply probEvent_bind_le_of_forall_le
      intro leftRoot _hleftRoot
      let fixed : ProbComp (Digest × Option Probe) := do
        let rightRoot ← sampled
        let selection ← reference leftRoot
        pure (rightRoot, selection)
      have hfixed : Pr[fun result : Digest × Option Probe =>
          materializedOrdinalSelectionMatches target result.1 result.2 | fixed] ≤
          ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
        calc
          _ ≤ Pr[fun result : Digest × Option Probe =>
                result.1 = selectedProbeDigest result.2 | fixed] := by
            apply probEvent_mono
            intro result _hresult hmatch
            exact materializedOrdinalSelectionMatches_root_eq_selectedProbeDigest hmatch
          _ ≤ _ := by
            unfold fixed
            apply probEvent_uniform_root_matches_distribution_independent_guess_le
              (fun _rightRoot => reference leftRoot) (reference leftRoot)
            intro rightRoot
            rfl
      calc
        _ = Pr[fun result : Digest × Option Probe =>
            materializedOrdinalSelectionMatches target result.1 result.2 | fixed] := by
          rw [show (do
              let rightRoot ← sampled
              let selection ← reference leftRoot
              pure (rightRoot, leftRoot, selection)) =
            (fun result : Digest × Option Probe => (result.1, leftRoot, result.2)) <$>
              fixed by
                simp [fixed, map_eq_bind_pure_comp], probEvent_map]
          rfl
        _ ≤ _ := hfixed

set_option maxRecDepth 100000 in
theorem probEvent_uniformActualRoot_match_le_of_swap_of_comparison_mul
    (target : Position)
    (run : Digest → Digest → ProbComp (Option Probe))
    (reference : Digest → ProbComp (Option Probe))
    (hswap : ∀ leftRoot rightRoot,
      evalDist (run leftRoot rightRoot) = evalDist (run rightRoot leftRoot))
    (hcomparison : ∀ leftRoot,
      Pr[fun result : Digest × Option Probe =>
          materializedOrdinalSelectionMatches target result.1 result.2 | do
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        let selection ← run leftRoot rightRoot
        pure (rightRoot, selection)] ≤
        Pr[materializedOrdinalSelectionAt target | reference leftRoot] *
          ((2 ^ digestBits : Nat) : ENNReal)⁻¹) :
    Pr[fun result : Digest × Digest × Option Probe =>
        materializedOrdinalSelectionMatches target result.1 result.2.2 | do
      let leftRoot ← ($ᵗ Digest : ProbComp Digest)
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      let selection ← run leftRoot rightRoot
      pure (leftRoot, rightRoot, selection)] ≤
      Pr[fun result : Digest × Option Probe =>
          materializedOrdinalSelectionAt target result.2 | do
        let leftRoot ← ($ᵗ Digest : ProbComp Digest)
        let selection ← reference leftRoot
        pure (leftRoot, selection)] *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  let sampled := ($ᵗ Digest : ProbComp Digest)
  let actual : ProbComp (Digest × Digest × Option Probe) := do
    let leftRoot ← sampled
    let rightRoot ← sampled
    let selection ← run leftRoot rightRoot
    pure (leftRoot, rightRoot, selection)
  let swapped : ProbComp (Digest × Digest × Option Probe) := do
    let leftRoot ← sampled
    let rightRoot ← sampled
    let selection ← run rightRoot leftRoot
    pure (leftRoot, rightRoot, selection)
  let comparison : ProbComp (Digest × Digest × Option Probe) := do
    let leftRoot ← sampled
    let rightRoot ← sampled
    let selection ← run leftRoot rightRoot
    pure (rightRoot, leftRoot, selection)
  let referenceRun : ProbComp (Digest × Option Probe) := do
    let leftRoot ← sampled
    let selection ← reference leftRoot
    pure (leftRoot, selection)
  have hreplace : evalDist actual = evalDist swapped := by
    unfold actual swapped
    apply evalDist_bind_congr
    intro leftRoot _hleftRoot
    apply evalDist_bind_congr
    intro rightRoot _hrightRoot
    rw [evalDist_bind, evalDist_bind, hswap leftRoot rightRoot]
  have hcommute : evalDist swapped = evalDist comparison := by
    unfold swapped comparison
    exact OracleComp.DeferredSampling.evalDist_bind_comm sampled sampled
      (fun leftRoot rightRoot => do
        let selection ← run rightRoot leftRoot
        pure (leftRoot, rightRoot, selection))
  change Pr[fun result : Digest × Digest × Option Probe =>
      materializedOrdinalSelectionMatches target result.1 result.2.2 | actual] ≤ _
  calc
    _ = Pr[fun result : Digest × Digest × Option Probe =>
          materializedOrdinalSelectionMatches target result.1 result.2.2 | comparison] :=
      OracleComp.probEvent_congr' (fun _ _ => Iff.rfl) (hreplace.trans hcommute)
    _ = ∑' leftRoot, (evalDist sampled) leftRoot *
          Pr[fun result : Digest × Digest × Option Probe =>
              materializedOrdinalSelectionMatches target result.1 result.2.2 | do
            let rightRoot ← sampled
            let selection ← run leftRoot rightRoot
            pure (rightRoot, leftRoot, selection)] := by
      unfold comparison
      rw [probEvent_bind_eq_tsum]
      simp only [probOutput_def]
    _ ≤ ∑' leftRoot, (evalDist sampled) leftRoot *
          (Pr[materializedOrdinalSelectionAt target | reference leftRoot] *
            ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
      apply ENNReal.tsum_le_tsum
      intro leftRoot
      rw [show ((do
          let rightRoot ← sampled
          let selection ← run leftRoot rightRoot
          pure (rightRoot, leftRoot, selection)) :
            ProbComp (Digest × Digest × Option Probe)) =
        (fun result : Digest × Option Probe => (result.1, leftRoot, result.2)) <$>
          ((do
            let rightRoot ← sampled
            let selection ← run leftRoot rightRoot
            pure (rightRoot, selection)) : ProbComp (Digest × Option Probe)) by
          simp [map_eq_bind_pure_comp], probEvent_map]
      gcongr
      exact hcomparison leftRoot
    _ = (∑' leftRoot, (evalDist sampled) leftRoot *
          Pr[materializedOrdinalSelectionAt target | reference leftRoot]) *
          ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
      simp_rw [← mul_assoc]
      rw [ENNReal.tsum_mul_right]
    _ = Pr[fun result : Digest × Option Probe =>
          materializedOrdinalSelectionAt target result.2 | referenceRun] *
          ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
      unfold referenceRun
      rw [probEvent_bind_eq_tsum]
      apply congrArg (fun value => value * ((2 ^ digestBits : Nat) : ENNReal)⁻¹)
      apply tsum_congr
      intro leftRoot
      rw [show (do
          let selection ← reference leftRoot
          pure (leftRoot, selection)) =
        (fun selection => (leftRoot, selection)) <$> reference leftRoot by
          simp [map_eq_bind_pure_comp], probEvent_map]
      rfl

set_option maxRecDepth 100000 in
theorem probEvent_uniformActualRoot_materializedActualSelectionMatches_le
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe)
    (state : Digest → LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : Digest → SplitHashCache)
    (hswap : ∀ leftRoot rightRoot,
      evalDist
          (materializedActualRootAvoidingOrdinalSelection ordinal parameter publicRoot target
            leftRoot rightRoot ftsSecret computation candidates (state leftRoot) fuel table
            (cache leftRoot)) =
        evalDist
          (materializedActualRootAvoidingOrdinalSelection ordinal parameter publicRoot target
            rightRoot leftRoot ftsSecret computation candidates (state rightRoot) fuel table
            (cache rightRoot))) :
    Pr[fun result : Digest × Digest × Option Probe =>
        materializedOrdinalSelectionMatches target result.1 result.2.2 | do
      let leftRoot ← ($ᵗ Digest : ProbComp Digest)
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      let selection ← materializedActualRootAvoidingOrdinalSelection ordinal parameter
        publicRoot target leftRoot rightRoot ftsSecret computation candidates (state leftRoot) fuel
        table (cache leftRoot)
      pure (leftRoot, rightRoot, selection)] ≤
      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  let run : Digest → Digest → ProbComp (Option Probe) :=
    fun leftRoot rightRoot =>
      materializedActualRootAvoidingOrdinalSelection ordinal parameter publicRoot target leftRoot
        rightRoot ftsSecret computation candidates (state leftRoot) fuel table (cache leftRoot)
  let reference : Digest → ProbComp (Option Probe) :=
    fun leftRoot =>
      materializedActualRootAvoidingOrdinalSelection ordinal parameter publicRoot target leftRoot
        leftRoot ftsSecret computation candidates (state leftRoot) fuel table (cache leftRoot)
  apply probEvent_uniformActualRoot_match_le_of_swap_of_comparison target run reference
  · intro leftRoot rightRoot
    exact hswap leftRoot rightRoot
  · intro leftRoot rightRoot
    exact probEvent_materializedRootAvoidingOrdinalSelection_match_le_actual_guard ordinal
      parameter target leftRoot rightRoot rightRoot (maskedSign parameter publicRoot ftsSecret)
      computation candidates (state leftRoot) fuel table (cache leftRoot)

end SphincsSecurity.Concrete.OtsProbeSimulation
