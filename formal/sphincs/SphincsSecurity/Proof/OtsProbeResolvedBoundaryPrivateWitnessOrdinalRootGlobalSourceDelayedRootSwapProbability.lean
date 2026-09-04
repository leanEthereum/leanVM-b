import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSourceDelayedRootSwapSelector

/-!
# Permissive root-swap probability

The symmetric two-root selector is dominated, for a fixed match event, by the selector whose
comparison guard repeats the actual root. This makes the comparison root independent of the
selected probe.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

def PermissiveOptionMatchRel
    (target : Position) (matchRoot : Digest) :
    Option PermissivePrivateOrdinalSelection →
      Option PermissivePrivateOrdinalSelection → Prop :=
  fun left right =>
    materializedOrdinalSelectionMatches target matchRoot
        (erasePermissivePrivateOrdinalSelection left) →
      materializedOrdinalSelectionMatches target matchRoot
        (erasePermissivePrivateOrdinalSelection right)

theorem relTriple_none_any_permissiveOptionMatch
    (target : Position) (matchRoot : Digest)
    (right : ProbComp (Option PermissivePrivateOrdinalSelection)) :
    RelTriple (pure none : ProbComp (Option PermissivePrivateOrdinalSelection)) right
      (PermissiveOptionMatchRel target matchRoot) := by
  have hbase := relTriple_true
    (pure none : ProbComp (Option PermissivePrivateOrdinalSelection)) right
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun value => value = none) (by intro value hvalue; simpa using hvalue)
  apply relTriple_post_mono hsupported
  intro left right hrelation
  rw [hrelation.2]
  simp [PermissiveOptionMatchRel, materializedOrdinalSelectionMatches,
    erasePermissivePrivateOrdinalSelection]

theorem relTriple_finishPermissiveSelection_weaken
    (target : Position) (matchRoot : Digest)
    (leftObserve rightObserve : LazyRevealProbe.State Coordinate → Nat → α →
      SplitHashCache → List Probe → ProbComp (Option PermissivePrivateOrdinalSelection))
    (candidates : List Probe)
    (result : Option (CleanRunResult (α × SplitHashCache)))
    (hrecursive : ∀ (resolved : CleanRunResult (α × SplitHashCache)),
      RelTriple
        (continuePermissiveRootAvoidingDetailedOrdinalSelection target leftObserve
          resolved.state resolved.remaining resolved.value.1 resolved.value.2 candidates)
        (continuePermissiveRootAvoidingDetailedOrdinalSelection target rightObserve
          resolved.state resolved.remaining resolved.value.1 resolved.value.2 candidates)
        (PermissiveOptionMatchRel target matchRoot)) :
    RelTriple
      (finishPermissiveDetailedPrivateOrdinalSelection
        (continuePermissiveRootAvoidingDetailedOrdinalSelection target leftObserve)
        candidates result)
      (finishPermissiveDetailedPrivateOrdinalSelection
        (continuePermissiveRootAvoidingDetailedOrdinalSelection target rightObserve)
        candidates result)
      (PermissiveOptionMatchRel target matchRoot) := by
  cases result with
  | none => exact relTriple_pure_pure (fun h => h)
  | some resolved =>
      simp only [finishPermissiveDetailedPrivateOrdinalSelection]
      exact hrecursive resolved

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_permissiveRootAvoidingDetailedOrdinalSelection_weakenComparison
    (ordinal : Nat) (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot matchRoot : Digest)
    (signer : Message → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    RelTriple
      (permissiveRootAvoidingDetailedOrdinalSelection ordinal parameter target leftRoot rightRoot
        signer computation candidates state fuel table cache)
      (permissiveRootAvoidingDetailedOrdinalSelection ordinal parameter target leftRoot leftRoot
        signer computation candidates state fuel table cache)
      (PermissiveOptionMatchRel target matchRoot) := by
  induction computation using OracleComp.inductionOn generalizing candidates state fuel cache with
  | pure value =>
      simp only [permissiveRootAvoidingDetailedOrdinalSelection, OracleComp.construct_pure]
      by_cases hselected : ordinal < candidates.length <;>
        simp only [hselected, ↓reduceDIte] <;>
        exact relTriple_pure_pure (fun h => h)
  | query_bind query next ih =>
      rw [permissiveRootAvoidingDetailedOrdinalSelection, OracleComp.construct_query_bind,
        permissiveRootAvoidingDetailedOrdinalSelection, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure (fun h => h)
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                let leftObserve :=
                  fun nextState remaining value nextCache laterCandidates =>
                    permissiveRootAvoidingDetailedOrdinalSelection ordinal parameter target
                      leftRoot rightRoot signer (next value) laterCandidates nextState remaining
                      table nextCache
                let rightObserve :=
                  fun nextState remaining value nextCache laterCandidates =>
                    permissiveRootAvoidingDetailedOrdinalSelection ordinal parameter target
                      leftRoot leftRoot signer (next value) laterCandidates nextState remaining
                      table nextCache
                apply relTriple_bind
                  (relTriple_refl
                    (runPermissiveFromTable state fuel table ((splitUniformImpl n).run cache)))
                intro leftResult rightResult hresult
                subst rightResult
                apply relTriple_finishPermissiveSelection_weaken target matchRoot leftObserve
                  rightObserve candidates leftResult
                intro resolved
                unfold continuePermissiveRootAvoidingDetailedOrdinalSelection
                by_cases hrevealed : Coordinate.position target ∈ resolved.state.revealed
                · simp [hrevealed, PermissiveOptionMatchRel,
                    materializedOrdinalSelectionMatches,
                    erasePermissivePrivateOrdinalSelection]
                · simpa [hrevealed, leftObserve, rightObserve] using
                    ih resolved.value.1 candidates resolved.state resolved.remaining
                      resolved.value.2
            | inr input =>
                let nextCandidates := permissiveRootAwareCandidates parameter input table state
                  candidates
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hactual : ordinal <
                      (permissiveRootAwareCandidates parameter input table state candidates).length := by
                    simpa [nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  exact relTriple_pure_pure (fun h => h)
                · have hactual : ¬ordinal <
                      (permissiveRootAwareCandidates parameter input table state candidates).length := by
                    simpa [nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  let publicContext := materializedCanonicalContext table state
                  let plan := purePlanProbingHashQuery parameter input publicContext.state
                  let candidate? := rootAwareCandidateForPlan? parameter input plan
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
                    let leftObserve :=
                      fun nextState remaining value nextCache laterCandidates =>
                        permissiveRootAvoidingDetailedOrdinalSelection ordinal parameter target
                          leftRoot rightRoot signer (next value) laterCandidates nextState remaining
                          table nextCache
                    let rightObserve :=
                      fun nextState remaining value nextCache laterCandidates =>
                        permissiveRootAvoidingDetailedOrdinalSelection ordinal parameter target
                          leftRoot leftRoot signer (next value) laterCandidates nextState remaining
                          table nextCache
                    apply relTriple_bind
                      (relTriple_refl
                        (runPermissiveFromTable state fuel table
                          (delayedPermissivePublicAction parameter input table state cache)))
                    intro leftResult rightResult hresult
                    subst rightResult
                    apply relTriple_finishPermissiveSelection_weaken target matchRoot leftObserve
                      rightObserve nextCandidates leftResult
                    intro resolved
                    unfold continuePermissiveRootAvoidingDetailedOrdinalSelection
                    by_cases hrevealed : Coordinate.position target ∈ resolved.state.revealed
                    · simp [hrevealed, PermissiveOptionMatchRel,
                        materializedOrdinalSelectionMatches,
                        erasePermissivePrivateOrdinalSelection]
                    · simpa [hrevealed, leftObserve, rightObserve] using
                        ih resolved.value.1 nextCandidates resolved.state resolved.remaining
                          resolved.value.2
                  · have hsafeActual : ¬RootAwareCandidateAvoidsRoots target leftRoot rightRoot
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [publicContext, plan, candidate?] using hsafe
                    simp only [hsafeActual, ↓reduceIte]
                    exact relTriple_none_any_permissiveOptionMatch target matchRoot _
        | inr message =>
            let leftObserve :=
              fun nextState remaining value nextCache laterCandidates =>
                permissiveRootAvoidingDetailedOrdinalSelection ordinal parameter target leftRoot
                  rightRoot signer (next value) laterCandidates nextState remaining table nextCache
            let rightObserve :=
              fun nextState remaining value nextCache laterCandidates =>
                permissiveRootAvoidingDetailedOrdinalSelection ordinal parameter target leftRoot
                  leftRoot signer (next value) laterCandidates nextState remaining table nextCache
            apply relTriple_bind
              (relTriple_refl
                (runPermissiveFromTable state fuel table ((signer message).run cache)))
            intro leftResult rightResult hresult
            subst rightResult
            apply relTriple_finishPermissiveSelection_weaken target matchRoot leftObserve
              rightObserve candidates leftResult
            intro resolved
            unfold continuePermissiveRootAvoidingDetailedOrdinalSelection
            by_cases hrevealed : Coordinate.position target ∈ resolved.state.revealed
            · simp [hrevealed, PermissiveOptionMatchRel, materializedOrdinalSelectionMatches,
                erasePermissivePrivateOrdinalSelection]
            · simpa [hrevealed, leftObserve, rightObserve] using
                ih resolved.value.1 candidates resolved.state resolved.remaining resolved.value.2

theorem probEvent_permissiveRootAvoidingSelection_match_le_reference
    (ordinal : Nat) (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot matchRoot : Digest)
    (signer : Message → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    Pr[fun selection => materializedOrdinalSelectionMatches target matchRoot
          (erasePermissivePrivateOrdinalSelection selection) |
        permissiveRootAvoidingDetailedOrdinalSelection ordinal parameter target leftRoot rightRoot
          signer computation candidates state fuel table cache] ≤
      Pr[fun selection => materializedOrdinalSelectionMatches target matchRoot
          (erasePermissivePrivateOrdinalSelection selection) |
        permissiveRootAvoidingDetailedOrdinalSelection ordinal parameter target leftRoot leftRoot
          signer computation candidates state fuel table cache] :=
  probEvent_le_of_relTriple
    (relTriple_permissiveRootAvoidingDetailedOrdinalSelection_weakenComparison ordinal parameter
      target leftRoot rightRoot matchRoot signer computation candidates state fuel table cache)
    (fun _ _ hrelation => hrelation)

set_option maxRecDepth 100000 in
theorem probEvent_sampledComparisonRoot_permissiveRootAvoidingSelection_le_mul
    (ordinal : Nat) (parameter : PublicParameter) (target : Position)
    (leftRoot : Digest)
    (signer : Message → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    Pr[fun result : Digest × Option PermissivePrivateOrdinalSelection =>
        materializedOrdinalSelectionMatches target result.1
          (erasePermissivePrivateOrdinalSelection result.2) | do
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      let selection ← permissiveRootAvoidingDetailedOrdinalSelection ordinal parameter target
        leftRoot rightRoot signer computation candidates state fuel table cache
      pure (rightRoot, selection)] ≤
      Pr[fun selection => materializedOrdinalSelectionAt target
          (erasePermissivePrivateOrdinalSelection selection) |
        permissiveRootAvoidingDetailedOrdinalSelection ordinal parameter target leftRoot leftRoot
          signer computation candidates state fuel table cache] *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  let reference := permissiveRootAvoidingDetailedOrdinalSelection ordinal parameter target
    leftRoot leftRoot signer computation candidates state fuel table cache
  calc
    _ ≤ Pr[fun result : Digest × Option PermissivePrivateOrdinalSelection =>
          materializedOrdinalSelectionMatches target result.1
            (erasePermissivePrivateOrdinalSelection result.2) | do
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        let selection ← reference
        pure (rightRoot, selection)] := by
      apply probEvent_bind_le_bind_of_forall_le
      intro rightRoot _hrightRoot
      rw [show (do
          let selection ← permissiveRootAvoidingDetailedOrdinalSelection ordinal parameter
            target leftRoot rightRoot signer computation candidates state fuel table cache
          pure (rightRoot, selection)) =
        (fun selection => (rightRoot, selection)) <$>
          permissiveRootAvoidingDetailedOrdinalSelection ordinal parameter target leftRoot
            rightRoot signer computation candidates state fuel table cache by
          simp [map_eq_bind_pure_comp],
        show (do
          let selection ← reference
          pure (rightRoot, selection)) =
        (fun selection => (rightRoot, selection)) <$> reference by
          simp [map_eq_bind_pure_comp], probEvent_map, probEvent_map]
      exact probEvent_permissiveRootAvoidingSelection_match_le_reference ordinal parameter target
        leftRoot rightRoot rightRoot signer computation candidates state fuel table cache
    _ ≤ Pr[fun result : Digest × Option PermissivePrivateOrdinalSelection =>
          materializedOrdinalSelectionAt target
              (erasePermissivePrivateOrdinalSelection result.2) ∧
            result.1 = selectedProbeDigest
              (erasePermissivePrivateOrdinalSelection result.2) | do
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        let selection ← reference
        pure (rightRoot, selection)] := by
      apply probEvent_mono
      intro result _hresult hmatch
      exact ⟨materializedOrdinalSelectionAt_of_matches hmatch,
        materializedOrdinalSelectionMatches_root_eq_selectedProbeDigest hmatch⟩
    _ ≤ _ := by
      exact probEvent_uniform_root_matches_distribution_independent_guess_le_mul
        (fun _rightRoot => reference) reference (fun _rightRoot => rfl)
        (fun selection => selectedProbeDigest (erasePermissivePrivateOrdinalSelection selection))
        (fun selection => materializedOrdinalSelectionAt target
          (erasePermissivePrivateOrdinalSelection selection))

theorem evalDist_map_erase_permissiveRootAvoidingSelection_family_swap
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (output : Digest → HashOutput) (htruncate : ∀ root, truncateHash (output root) = root)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate)
    (hprivate : Coordinate.position target ∉ state.revealed)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : Digest → SplitHashCache)
    (htargetCache : ∀ root,
      cache root (.hidden (.position target)) = some (output root))
    (hcacheSwap : ∀ leftRoot rightRoot,
      fullSwapRootCache parameter target leftRoot rightRoot (output rightRoot)
        (cache leftRoot) = cache rightRoot)
    (leftRoot rightRoot : Digest) :
    evalDist
        (erasePermissivePrivateOrdinalSelection <$>
          permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter publicRoot target
            leftRoot rightRoot ftsSecret computation candidates
            (preloadPositionValue target (output leftRoot) state) fuel table (cache leftRoot)) =
      evalDist
        (erasePermissivePrivateOrdinalSelection <$>
          permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter publicRoot target
            rightRoot leftRoot ftsSecret computation candidates
            (preloadPositionValue target (output rightRoot) state) fuel table
            (cache rightRoot)) := by
  have hswap :=
    evalDist_map_erase_permissiveRootAvoidingDetailedOrdinalSelection_fullSwap ordinal parameter
      publicRoot target hroot (output leftRoot) (output rightRoot) ftsSecret computation candidates
      state hprivate fuel table (cache leftRoot) (htargetCache leftRoot)
  rw [htruncate leftRoot, htruncate rightRoot] at hswap
  simpa only [hcacheSwap leftRoot rightRoot] using hswap

set_option maxRecDepth 100000 in
theorem probEvent_uniformActualRoot_permissiveRootAvoidingSelection_le_mul
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (output : Digest → HashOutput) (htruncate : ∀ root, truncateHash (output root) = root)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate)
    (hprivate : Coordinate.position target ∉ state.revealed)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : Digest → SplitHashCache)
    (htargetCache : ∀ root,
      cache root (.hidden (.position target)) = some (output root))
    (hcacheSwap : ∀ leftRoot rightRoot,
      fullSwapRootCache parameter target leftRoot rightRoot (output rightRoot)
        (cache leftRoot) = cache rightRoot) :
    Pr[fun result : Digest × Digest × Option Probe =>
        materializedOrdinalSelectionMatches target result.1 result.2.2 | do
      let leftRoot ← ($ᵗ Digest : ProbComp Digest)
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      let selection ← erasePermissivePrivateOrdinalSelection <$>
        permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter publicRoot target
          leftRoot rightRoot ftsSecret computation candidates
          (preloadPositionValue target (output leftRoot) state) fuel table (cache leftRoot)
      pure (leftRoot, rightRoot, selection)] ≤
      Pr[fun result : Digest × Option Probe =>
          materializedOrdinalSelectionAt target result.2 | do
        let leftRoot ← ($ᵗ Digest : ProbComp Digest)
        let selection ← erasePermissivePrivateOrdinalSelection <$>
          permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter publicRoot target
            leftRoot leftRoot ftsSecret computation candidates
            (preloadPositionValue target (output leftRoot) state) fuel table (cache leftRoot)
        pure (leftRoot, selection)] *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  let run : Digest → Digest → ProbComp (Option Probe) :=
    fun leftRoot rightRoot => erasePermissivePrivateOrdinalSelection <$>
      permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter publicRoot target
        leftRoot rightRoot ftsSecret computation candidates
        (preloadPositionValue target (output leftRoot) state) fuel table (cache leftRoot)
  let reference : Digest → ProbComp (Option Probe) :=
    fun leftRoot => erasePermissivePrivateOrdinalSelection <$>
      permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter publicRoot target
        leftRoot leftRoot ftsSecret computation candidates
        (preloadPositionValue target (output leftRoot) state) fuel table (cache leftRoot)
  apply probEvent_uniformActualRoot_match_le_of_swap_of_comparison_mul target run reference
  · intro leftRoot rightRoot
    exact evalDist_map_erase_permissiveRootAvoidingSelection_family_swap ordinal parameter
      publicRoot target hroot output htruncate ftsSecret computation candidates state hprivate fuel
      table cache htargetCache hcacheSwap leftRoot rightRoot
  · intro leftRoot
    simp only [run, reference]
    rw [probEvent_map]
    let raw := fun rightRoot =>
      permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter publicRoot target
        leftRoot rightRoot ftsSecret computation candidates
        (preloadPositionValue target (output leftRoot) state) fuel table (cache leftRoot)
    change Pr[fun result => materializedOrdinalSelectionMatches target result.1 result.2 | do
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        let selection ← erasePermissivePrivateOrdinalSelection <$> raw rightRoot
        pure (rightRoot, selection)] ≤
      Pr[materializedOrdinalSelectionAt target ∘ erasePermissivePrivateOrdinalSelection |
        raw leftRoot] * ((2 ^ digestBits : Nat) : ENNReal)⁻¹
    have hmap :
        (do
          let rightRoot ← ($ᵗ Digest : ProbComp Digest)
          let selection ← erasePermissivePrivateOrdinalSelection <$> raw rightRoot
          pure (rightRoot, selection)) =
        (fun result : Digest × Option PermissivePrivateOrdinalSelection =>
            (result.1, erasePermissivePrivateOrdinalSelection result.2)) <$> (do
          let rightRoot ← ($ᵗ Digest : ProbComp Digest)
          let selection ← raw rightRoot
          pure (rightRoot, selection)) := by
      simp [map_eq_bind_pure_comp]
    rw [hmap, probEvent_map]
    simpa [raw, permissiveActualRootAvoidingDetailedOrdinalSelection, Function.comp_def] using
      (probEvent_sampledComparisonRoot_permissiveRootAvoidingSelection_le_mul ordinal parameter
        target leftRoot (maskedSign parameter publicRoot ftsSecret) computation candidates
        (preloadPositionValue target (output leftRoot) state) fuel table (cache leftRoot))

end SphincsSecurity.Concrete.OtsProbeSimulation
