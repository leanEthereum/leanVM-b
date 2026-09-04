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

def PermissiveFilteredSelectionRel
    (target : Position) : Option PermissivePrivateOrdinalSelection →
      Option PermissivePrivateOrdinalSelection → Prop
  | none, _ => True
  | some left, some right =>
      left = right ∧ Coordinate.position target ∉ left.state.revealed
  | some _, none => False

def PermissiveRootFilterCompleteRel
    (target : Position) (output : HashOutput) (rightRoot : Digest) (ordinal : Nat) :
    Option PermissivePrivateOrdinalSelection →
      Option PermissivePrivateOrdinalSelection → Prop :=
  fun left right =>
    PermissiveDelayedRootGuessAt target output rightRoot ordinal right → left = right

theorem relTriple_none_delayed_of_target_revealed
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (target : Position) (output : HashOutput) (rightRoot : Digest)
    (hrevealed : Coordinate.position target ∈ state.revealed) :
    RelTriple (pure none : ProbComp (Option PermissivePrivateOrdinalSelection))
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        candidates state fuel table cache)
      (PermissiveRootFilterCompleteRel target output rightRoot ordinal) := by
  have hbase := relTriple_true
    (pure none : ProbComp (Option PermissivePrivateOrdinalSelection))
    (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
      candidates state fuel table cache)
  have hleft := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
    (fun value => value = none) (by intro value hvalue; simpa using hvalue)
  have hboth := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
  apply relTriple_post_mono hboth
  intro left right hrelation hgood
  rcases hrelation with ⟨⟨_htrue, hleftNone⟩, hrightSupport⟩
  subst left
  cases right with
  | none => rfl
  | some selection =>
      exfalso
      exact hgood.2.2.1
        (revealed_subset_of_mem_delayedPermissiveDetailedOrdinalSelection ordinal parameter root
          ftsSecret computation candidates state fuel table cache selection hrightSupport hrevealed)

theorem relTriple_none_delayed_of_unsafe_prefix
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (target : Position) (output : HashOutput) (rightRoot : Digest)
    (candidate : Probe) (hmem : candidate ∈ candidates)
    (hlength : candidates.length ≤ ordinal)
    (hunsafe : ¬candidate.AvoidsRoots target (truncateHash output) rightRoot) :
    RelTriple (pure none : ProbComp (Option PermissivePrivateOrdinalSelection))
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        candidates state fuel table cache)
      (PermissiveRootFilterCompleteRel target output rightRoot ordinal) := by
  have hbase := relTriple_true
    (pure none : ProbComp (Option PermissivePrivateOrdinalSelection))
    (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
      candidates state fuel table cache)
  have hleft := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
    (fun value => value = none) (by intro value hvalue; simpa using hvalue)
  have hboth := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
  apply relTriple_post_mono hboth
  intro left right hrelation hgood
  rcases hrelation with ⟨⟨_htrue, hleftNone⟩, hrightSupport⟩
  subst left
  cases right with
  | none => rfl
  | some selection =>
      exfalso
      have hprefix := candidates_isPrefix_of_mem_delayedPermissiveDetailedOrdinalSelection
        ordinal parameter root ftsSecret computation candidates state fuel table cache selection
        hrightSupport
      have htake := hprefix.take ordinal
      have htakePrefix : candidates.IsPrefix (selection.candidates.take ordinal) := by
        rw [(List.take_eq_self_iff candidates).2 hlength] at htake
        exact htake
      have hcandidate : candidate ∈ selection.candidates.take ordinal :=
        htakePrefix.sublist.subset hmem
      exact hunsafe (hgood.2.2.2 candidate hcandidate)

theorem relTriple_finishPermissiveRootFilterComplete
    (target : Position) (output : HashOutput) (rightRoot : Digest) (ordinal : Nat)
    (leftObserve rightObserve : LazyRevealProbe.State Coordinate → Nat → α →
      SplitHashCache → List Probe → ProbComp (Option PermissivePrivateOrdinalSelection))
    (candidates : List Probe)
    (result : Option (CleanRunResult (α × SplitHashCache)))
    (hrecursive : ∀ (resolved : CleanRunResult (α × SplitHashCache)),
      Coordinate.position target ∉ resolved.state.revealed →
      RelTriple
        (leftObserve resolved.state resolved.remaining resolved.value.1 resolved.value.2 candidates)
        (rightObserve resolved.state resolved.remaining resolved.value.1 resolved.value.2 candidates)
        (PermissiveRootFilterCompleteRel target output rightRoot ordinal))
    (hrevealed : ∀ (resolved : CleanRunResult (α × SplitHashCache)),
      Coordinate.position target ∈ resolved.state.revealed →
      RelTriple (pure none : ProbComp (Option PermissivePrivateOrdinalSelection))
        (rightObserve resolved.state resolved.remaining resolved.value.1 resolved.value.2 candidates)
        (PermissiveRootFilterCompleteRel target output rightRoot ordinal)) :
    RelTriple
      (finishPermissiveDetailedPrivateOrdinalSelection
        (continuePermissiveRootAvoidingDetailedOrdinalSelection target leftObserve)
        candidates result)
      (finishPermissiveDetailedPrivateOrdinalSelection rightObserve candidates result)
      (PermissiveRootFilterCompleteRel target output rightRoot ordinal) := by
  cases result with
  | none => exact relTriple_pure_pure (fun hgood => False.elim hgood)
  | some resolved =>
      simp only [finishPermissiveDetailedPrivateOrdinalSelection]
      unfold continuePermissiveRootAvoidingDetailedOrdinalSelection
      by_cases htarget : Coordinate.position target ∈ resolved.state.revealed
      · simp only [htarget, ↓reduceIte]
        exact hrevealed resolved htarget
      · simp only [htarget, ↓reduceIte]
        exact hrecursive resolved htarget

theorem relTriple_none_finishDelayed_of_unsafe_prefix
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (next : α → OracleComp (OracleWorld + SigningSpec) β)
    (step : ProbComp (Option (CleanRunResult (α × SplitHashCache))))
    (candidates : List Probe) (table : OtsSecretIndex → HashOutput)
    (target : Position) (output : HashOutput) (rightRoot : Digest)
    (candidate : Probe) (hmem : candidate ∈ candidates)
    (hlength : candidates.length ≤ ordinal)
    (hunsafe : ¬candidate.AvoidsRoots target (truncateHash output) rightRoot) :
    RelTriple (pure none : ProbComp (Option PermissivePrivateOrdinalSelection))
      (step >>= finishPermissiveDetailedPrivateOrdinalSelection
        (fun state fuel value cache laterCandidates =>
          delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret
            (next value) laterCandidates state fuel table cache)
        candidates)
      (PermissiveRootFilterCompleteRel target output rightRoot ordinal) := by
  let right := step >>= finishPermissiveDetailedPrivateOrdinalSelection
    (fun state fuel value cache laterCandidates =>
      delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret
        (next value) laterCandidates state fuel table cache)
    candidates
  have hbase := relTriple_true
    (pure none : ProbComp (Option PermissivePrivateOrdinalSelection)) right
  have hleft := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
    (fun value => value = none) (by intro value hvalue; simpa using hvalue)
  have hboth := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
  apply relTriple_post_mono hboth
  intro left rightSelection hrelation hgood
  rcases hrelation with ⟨⟨_htrue, hleftNone⟩, hrightSupport⟩
  subst left
  cases rightSelection with
  | none => rfl
  | some selection =>
      exfalso
      change some selection ∈ support right at hrightSupport
      unfold right at hrightSupport
      rw [mem_support_bind_iff] at hrightSupport
      obtain ⟨result, _hresult, hfinish⟩ := hrightSupport
      cases result with
      | none => simp [finishPermissiveDetailedPrivateOrdinalSelection] at hfinish
      | some result =>
          simp only [finishPermissiveDetailedPrivateOrdinalSelection] at hfinish
          have hprefix := candidates_isPrefix_of_mem_delayedPermissiveDetailedOrdinalSelection
            ordinal parameter root ftsSecret (next result.value.1) candidates result.state
            result.remaining table result.value.2 selection hfinish
          have htake := hprefix.take ordinal
          have htakePrefix : candidates.IsPrefix (selection.candidates.take ordinal) := by
            rw [(List.take_eq_self_iff candidates).2 hlength] at htake
            exact htake
          have hcandidate : candidate ∈ selection.candidates.take ordinal :=
            htakePrefix.sublist.subset hmem
          exact hunsafe (hgood.2.2.2 candidate hcandidate)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_delayed_permissiveRootAvoidingDetailedOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (target : Position) (output : HashOutput) (rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    RelTriple
      (permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter root target
        (truncateHash output) rightRoot ftsSecret computation candidates state fuel table cache)
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        candidates state fuel table cache)
      (PermissiveRootFilterCompleteRel target output rightRoot ordinal) := by
  induction computation using OracleComp.inductionOn generalizing candidates state fuel cache with
  | pure value =>
      simp only [permissiveActualRootAvoidingDetailedOrdinalSelection,
        permissiveRootAvoidingDetailedOrdinalSelection,
        delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_pure]
      by_cases hselected : ordinal < candidates.length <;>
        simp only [hselected, ↓reduceDIte] <;>
        exact relTriple_pure_pure (fun _ => rfl)
  | query_bind query next ih =>
      unfold permissiveActualRootAvoidingDetailedOrdinalSelection
      rw [permissiveRootAvoidingDetailedOrdinalSelection, OracleComp.construct_query_bind,
        delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure (fun _ => rfl)
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                let leftObserve :=
                  fun nextState remaining value nextCache laterCandidates =>
                    permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter root
                      target (truncateHash output) rightRoot ftsSecret (next value)
                      laterCandidates nextState remaining table nextCache
                let rightObserve :=
                  fun nextState remaining value nextCache laterCandidates =>
                    delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret
                      (next value) laterCandidates nextState remaining table nextCache
                apply relTriple_bind
                  (relTriple_refl
                    (runPermissiveFromTable state fuel table ((splitUniformImpl n).run cache)))
                intro leftResult rightResult hresult
                subst rightResult
                apply relTriple_finishPermissiveRootFilterComplete target output rightRoot ordinal
                  leftObserve rightObserve candidates leftResult
                · intro resolved _hunrevealed
                  simpa only [leftObserve, rightObserve] using
                    ih resolved.value.1 candidates resolved.state resolved.remaining
                      resolved.value.2
                · intro resolved hrevealed
                  exact relTriple_none_delayed_of_target_revealed ordinal parameter root ftsSecret
                    (next resolved.value.1) candidates resolved.state resolved.remaining table
                    resolved.value.2 target output rightRoot hrevealed
            | inr input =>
                let nextCandidates := permissiveRootAwareCandidates parameter input table state
                  candidates
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hactual : ordinal <
                      (permissiveRootAwareCandidates parameter input table state candidates).length :=
                    by simpa [nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  exact relTriple_pure_pure (fun _ => rfl)
                · have hactual : ¬ordinal <
                      (permissiveRootAwareCandidates parameter input table state candidates).length :=
                    by simpa [nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  let candidate? := rootAwareCandidateForPlan? parameter input
                    (purePlanProbingHashQuery parameter input
                      (materializedCanonicalContext table state).state)
                  by_cases hsafe : RootAwareCandidateAvoidsRoots target (truncateHash output)
                      rightRoot candidate?
                  · have hsafeActual : RootAwareCandidateAvoidsRoots target (truncateHash output)
                        rightRoot
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [candidate?] using hsafe
                    simp only [hsafeActual, ↓reduceIte]
                    let leftObserve :=
                      fun nextState remaining value nextCache laterCandidates =>
                        permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter root
                          target (truncateHash output) rightRoot ftsSecret (next value)
                          laterCandidates nextState remaining table nextCache
                    let rightObserve :=
                      fun nextState remaining value nextCache laterCandidates =>
                        delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret
                          (next value) laterCandidates nextState remaining table nextCache
                    apply relTriple_bind
                      (relTriple_refl
                        (runPermissiveFromTable state fuel table
                          (delayedPermissivePublicAction parameter input table state cache)))
                    intro leftResult rightResult hresult
                    subst rightResult
                    apply relTriple_finishPermissiveRootFilterComplete target output rightRoot
                      ordinal leftObserve rightObserve nextCandidates leftResult
                    · intro resolved _hunrevealed
                      simpa only [leftObserve, rightObserve] using
                        ih resolved.value.1 nextCandidates resolved.state resolved.remaining
                          resolved.value.2
                    · intro resolved hrevealed
                      exact relTriple_none_delayed_of_target_revealed ordinal parameter root
                        ftsSecret (next resolved.value.1) nextCandidates resolved.state
                        resolved.remaining table resolved.value.2 target output rightRoot hrevealed
                  · have hsafeActual : ¬RootAwareCandidateAvoidsRoots target
                        (truncateHash output) rightRoot
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [candidate?] using hsafe
                    simp only [hsafeActual, ↓reduceIte]
                    cases hcandidate : candidate? with
                    | none =>
                        exfalso
                        exact hsafe (by simp [RootAwareCandidateAvoidsRoots, hcandidate])
                    | some candidate =>
                        have hunsafe : ¬candidate.AvoidsRoots target (truncateHash output)
                            rightRoot := by
                          rw [← rootAwareCandidateAvoidsRoots_iff]
                          simpa [hcandidate] using hsafe
                        have hcandidateActual :
                            rootAwareCandidateForPlan? parameter input
                                (permissiveRootAwarePlan parameter input table state) =
                              some candidate := by
                          simpa [candidate?, permissiveRootAwarePlan] using hcandidate
                        have hmem : candidate ∈ nextCandidates := by
                          simp [nextCandidates, permissiveRootAwareCandidates,
                            appendPlannedCandidate, hcandidateActual]
                        have hlength : nextCandidates.length ≤ ordinal := by omega
                        let step := runPermissiveFromTable state fuel table
                          (delayedPermissivePublicAction parameter input table state cache)
                        let rightObserve :=
                          fun nextState remaining value nextCache laterCandidates =>
                            delayedPermissiveDetailedOrdinalSelection ordinal parameter root
                              ftsSecret (next value) laterCandidates nextState remaining table
                              nextCache
                        change RelTriple
                          (pure none : ProbComp (Option PermissivePrivateOrdinalSelection))
                          (step >>= finishPermissiveDetailedPrivateOrdinalSelection rightObserve
                            nextCandidates)
                          (PermissiveRootFilterCompleteRel target output rightRoot ordinal)
                        exact relTriple_none_finishDelayed_of_unsafe_prefix ordinal parameter root
                          ftsSecret next step nextCandidates table target output rightRoot candidate
                          hmem hlength hunsafe
        | inr message =>
            let leftObserve :=
              fun nextState remaining value nextCache laterCandidates =>
                permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter root target
                  (truncateHash output) rightRoot ftsSecret (next value) laterCandidates nextState
                  remaining table nextCache
            let rightObserve :=
              fun nextState remaining value nextCache laterCandidates =>
                delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret
                  (next value) laterCandidates nextState remaining table nextCache
            apply relTriple_bind
              (relTriple_refl
                (runPermissiveFromTable state fuel table
                  ((maskedSign parameter root ftsSecret message).run cache)))
            intro leftResult rightResult hresult
            subst rightResult
            apply relTriple_finishPermissiveRootFilterComplete target output rightRoot ordinal
              leftObserve rightObserve candidates leftResult
            · intro resolved _hunrevealed
              simpa only [leftObserve, rightObserve] using
                ih resolved.value.1 candidates resolved.state resolved.remaining resolved.value.2
            · intro resolved hrevealed
              exact relTriple_none_delayed_of_target_revealed ordinal parameter root ftsSecret
                (next resolved.value.1) candidates resolved.state resolved.remaining table
                resolved.value.2 target output rightRoot hrevealed

def PermissiveTaggedDelayedRootGuessRel
    (target : Position) (rightRoot : Digest) (ordinal : Nat) :
    (HashOutput × Option PermissivePrivateOrdinalSelection) →
      Option PermissivePrivateOrdinalSelection → Prop :=
  fun left right =>
    PermissiveDelayedRootGuess target rightRoot ordinal right →
      PermissiveDelayedRootGuessAt target left.1 rightRoot ordinal left.2

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem valuesLE_of_mem_delayedPermissiveDetailedOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (selection : PermissivePrivateOrdinalSelection)
    (hselection : some selection ∈ support
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        candidates state fuel table cache)) :
    LazyRevealProbe.ValuesLE state selection.state := by
  induction computation using OracleComp.inductionOn generalizing candidates state fuel cache with
  | pure value =>
      simp only [delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_pure] at hselection
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte] at hselection
        simp at hselection
        subst selection
        exact LazyRevealProbe.ValuesLE.refl state
      · simp [hselected] at hselection
  | query_bind query next ih =>
      rw [delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_query_bind] at hselection
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte] at hselection
        simp at hselection
        subst selection
        exact LazyRevealProbe.ValuesLE.refl state
      · simp only [hselected, ↓reduceDIte] at hselection
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                rw [mem_support_bind_iff] at hselection
                obtain ⟨result, hresult, htail⟩ := hselection
                cases result with
                | none => simp [finishPermissiveDetailedPrivateOrdinalSelection] at htail
                | some result =>
                    simp only [finishPermissiveDetailedPrivateOrdinalSelection] at htail
                    exact (valuesLE_of_mem_runPermissiveFromTable
                      ((splitUniformImpl n).run cache) state fuel table result hresult).trans
                      (ih result.value.1 candidates result.state result.remaining result.value.2
                        htail)
            | inr input =>
                let nextCandidates :=
                  permissiveRootAwareCandidates parameter input table state candidates
                by_cases hnextSelected : ordinal < nextCandidates.length
                · simp only [nextCandidates, hnextSelected, ↓reduceDIte] at hselection
                  simp at hselection
                  subst selection
                  exact LazyRevealProbe.ValuesLE.refl state
                · simp only [nextCandidates, hnextSelected, ↓reduceDIte] at hselection
                  rw [mem_support_bind_iff] at hselection
                  obtain ⟨result, hresult, htail⟩ := hselection
                  cases result with
                  | none => simp [finishPermissiveDetailedPrivateOrdinalSelection] at htail
                  | some result =>
                      simp only [finishPermissiveDetailedPrivateOrdinalSelection] at htail
                      exact (valuesLE_of_mem_runPermissiveFromTable
                        (delayedPermissivePublicAction parameter input table state cache)
                        state fuel table result hresult).trans
                        (ih result.value.1 nextCandidates result.state result.remaining
                          result.value.2 htail)
        | inr message =>
            rw [mem_support_bind_iff] at hselection
            obtain ⟨result, hresult, htail⟩ := hselection
            cases result with
            | none => simp [finishPermissiveDetailedPrivateOrdinalSelection] at htail
            | some result =>
                simp only [finishPermissiveDetailedPrivateOrdinalSelection] at htail
                exact (valuesLE_of_mem_runPermissiveFromTable
                  ((maskedSign parameter root ftsSecret message).run cache)
                  state fuel table result hresult).trans
                  (ih result.value.1 candidates result.state result.remaining result.value.2 htail)

theorem PermissiveDetailedSelectionRel.delayedRootGuessAt
    {target : Position} {output : HashOutput} {rightRoot : Digest} {ordinal : Nat}
    {left right : Option PermissivePrivateOrdinalSelection}
    (hrel : PermissiveDetailedSelectionRel left right)
    (hgood : PermissiveDelayedRootGuessAt target output rightRoot ordinal right) :
    PermissiveDelayedRootGuessAt target output rightRoot ordinal left := by
  cases left with
  | none =>
      cases right with
      | none => exact hgood
      | some right => simp [PermissiveDetailedSelectionRel] at hrel
  | some left =>
      cases right with
      | none => simp [PermissiveDetailedSelectionRel] at hrel
      | some right =>
          rcases hrel with ⟨hcandidate, hcandidates, hstate⟩
          refine ⟨hcandidate.trans hgood.1, ?_, ?_, ?_⟩
          · rw [hstate.values]
            exact hgood.2.1
          · rw [hstate.revealed]
            exact hgood.2.2.1
          · rw [hcandidates]
            exact hgood.2.2.2

theorem relTriple_tagged_delayedSelection_of_stateRel
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (left right : LazyRevealProbe.State Coordinate)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (target : Position) (output : HashOutput) (rightRoot : Digest)
    (hstate : PermissiveStateRel left right)
    (hvalue : left.values (.position target) = some output) :
    RelTriple
      ((fun selection => (output, selection)) <$>
        delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
          candidates left fuel table cache)
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        candidates right fuel table cache)
      (PermissiveTaggedDelayedRootGuessRel target rightRoot ordinal) := by
  have hbase := relTriple_delayedPermissiveDetailedOrdinalSelection_of_stateRel ordinal parameter
    root ftsSecret computation candidates candidates left right fuel table cache rfl hstate
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun selection => match selection with
        | none => True
        | some selection => selection.state.values (.position target) = some output)
      (by
        intro selection hselection
        cases selection with
        | none => trivial
        | some selection =>
            exact valuesLE_of_mem_delayedPermissiveDetailedOrdinalSelection ordinal parameter root
              ftsSecret computation candidates left fuel table cache selection hselection
              (.position target) output hvalue)
  rw [map_eq_bind_pure_comp,
    show delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        candidates right fuel table cache =
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
          candidates right fuel table cache >>= pure) by simp]
  apply relTriple_bind hsupported
  intro leftSelection rightSelection hselection
  apply relTriple_pure_pure
  intro hgood
  obtain ⟨rightOutput, hrightGood⟩ := hgood
  have hleftGood := hselection.1.delayedRootGuessAt hrightGood
  cases leftSelection with
  | none => exact False.elim hleftGood
  | some leftSelection =>
      have heq : rightOutput = output :=
        Option.some.inj (hleftGood.2.1.symm.trans hselection.2)
      subst rightOutput
      exact hleftGood

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_sample_preload_runPermissive_finishDetailed_taggedGuess
    (target : Position) (rightRoot : Digest) (ordinal : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) (α × SplitHashCache))
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (leftObserve rightObserve : LazyRevealProbe.State Coordinate → Nat → α →
      SplitHashCache → List Probe → ProbComp (Option PermissivePrivateOrdinalSelection))
    (candidates : List Probe)
    (hvalue : state.values (.position target) = none)
    (hnoPeek : computation.IsQueryBoundP (IsTargetPeek target) 0)
    (hpreloaded : ∀ nextState remaining value nextCache,
      nextState.values (.position target) = none →
      RelTriple
        (LazyRevealProbe.sampleHashOutput >>= fun output =>
          (fun selection => (output, selection)) <$>
            leftObserve (preloadPositionValue target output nextState) remaining value nextCache
              candidates)
        (rightObserve nextState remaining value nextCache candidates)
        (PermissiveTaggedDelayedRootGuessRel target rightRoot ordinal))
    (hsynchronized : ∀ output left right remaining value nextCache,
      PermissiveStateRel left right →
      left.values (.position target) = some output →
      RelTriple
        ((fun selection => (output, selection)) <$>
          leftObserve left remaining value nextCache candidates)
        (rightObserve right remaining value nextCache candidates)
        (PermissiveTaggedDelayedRootGuessRel target rightRoot ordinal)) :
    RelTriple
      (LazyRevealProbe.sampleHashOutput >>= fun output =>
        (fun selection => (output, selection)) <$>
          (runPermissiveFromTable (preloadPositionValue target output state) fuel table
              computation >>=
            finishPermissiveDetailedPrivateOrdinalSelection leftObserve candidates))
      (runPermissiveFromTable state fuel table computation >>=
        finishPermissiveDetailedPrivateOrdinalSelection rightObserve candidates)
      (PermissiveTaggedDelayedRootGuessRel target rightRoot ordinal) := by
  let leftFinish : HashOutput → Option (CleanRunResult (α × SplitHashCache)) →
      ProbComp (HashOutput × Option PermissivePrivateOrdinalSelection) :=
    fun output result => (fun selection => (output, selection)) <$>
      finishPermissiveDetailedPrivateOrdinalSelection leftObserve candidates result
  let rightFinish : Option (CleanRunResult (α × SplitHashCache)) →
      ProbComp (Option PermissivePrivateOrdinalSelection) :=
    finishPermissiveDetailedPrivateOrdinalSelection rightObserve candidates
  simp only [map_eq_bind_pure_comp, bind_assoc]
  change RelTriple
    (LazyRevealProbe.sampleHashOutput >>= fun output =>
      runPermissiveFromTable (preloadPositionValue target output state) fuel table computation >>=
        leftFinish output)
    (runPermissiveFromTable state fuel table computation >>= rightFinish)
    (PermissiveTaggedDelayedRootGuessRel target rightRoot ordinal)
  apply relTriple_sample_preload_runPermissiveFromTable_then_tagged target computation state fuel
    table leftFinish rightFinish
    (PermissiveTaggedDelayedRootGuessRel target rightRoot ordinal) hvalue hnoPeek
  · intro nextState remaining result nextTable hnextValue
    rcases result with ⟨value, nextCache⟩
    simpa only [leftFinish, rightFinish, finishPermissiveDetailedPrivateOrdinalSelection,
      map_eq_bind_pure_comp] using
      hpreloaded nextState remaining value nextCache hnextValue
  · intro output
    exact relTriple_pure_pure (fun hgood => by
      simp [PermissiveDelayedRootGuess, PermissiveDelayedRootGuessAt] at hgood)
  · intro output left right hrelation hpreloadedOutput
    cases left with
    | none =>
        cases right with
        | none => exact relTriple_pure_pure (fun hgood => by
            simp [PermissiveDelayedRootGuess, PermissiveDelayedRootGuessAt] at hgood)
        | some right => exact False.elim hrelation
    | some left =>
        cases right with
        | none => exact False.elim hrelation
        | some right =>
            rcases hrelation with ⟨hstate, hremaining, hvalueEq, _htable⟩
            simp only [leftFinish, rightFinish,
              finishPermissiveDetailedPrivateOrdinalSelection]
            rw [← hremaining, ← hvalueEq]
            exact hsynchronized output left.state right.state left.remaining left.value.1
              left.value.2 hstate hpreloadedOutput

theorem relTriple_sample_preload_pureSelection_taggedGuess
    (target : Position) (rightRoot : Digest) (ordinal : Nat)
    (candidate : Probe) (candidates : List Probe)
    (state : LazyRevealProbe.State Coordinate)
    (hvalue : state.values (.position target) = none) :
    RelTriple
      (LazyRevealProbe.sampleHashOutput >>= fun output =>
        (pure (output, some ⟨candidate, preloadPositionValue target output state, candidates⟩) :
          ProbComp (HashOutput × Option PermissivePrivateOrdinalSelection)))
      (pure (some ⟨candidate, state, candidates⟩) :
        ProbComp (Option PermissivePrivateOrdinalSelection))
      (PermissiveTaggedDelayedRootGuessRel target rightRoot ordinal) := by
  rw [show (pure (some ⟨candidate, state, candidates⟩) :
      ProbComp (Option PermissivePrivateOrdinalSelection)) =
    ((pure () : ProbComp Unit) >>= fun _ => pure (some ⟨candidate, state, candidates⟩)) by simp]
  apply relTriple_bind
    (relTriple_true LazyRevealProbe.sampleHashOutput (pure () : ProbComp Unit))
  intro output _unit _hrelation
  apply relTriple_pure_pure
  intro hgood
  obtain ⟨_rightOutput, hgood⟩ := hgood
  exfalso
  have himpossible := hgood.2.1
  rw [hvalue] at himpossible
  simp at himpossible

theorem relTriple_sample_preload_pureNone_taggedGuess
    (target : Position) (rightRoot : Digest) (ordinal : Nat) :
    RelTriple
      (LazyRevealProbe.sampleHashOutput >>= fun output =>
        pure (output, (none : Option PermissivePrivateOrdinalSelection)))
      (pure none : ProbComp (Option PermissivePrivateOrdinalSelection))
      (PermissiveTaggedDelayedRootGuessRel target rightRoot ordinal) := by
  rw [show (pure none : ProbComp (Option PermissivePrivateOrdinalSelection)) =
    ((pure () : ProbComp Unit) >>= fun _ =>
      pure (none : Option PermissivePrivateOrdinalSelection)) by simp]
  apply relTriple_bind
    (relTriple_true LazyRevealProbe.sampleHashOutput (pure () : ProbComp Unit))
  intro output _unit _hrelation
  exact relTriple_pure_pure (fun hgood => by
    simp [PermissiveDelayedRootGuess, PermissiveDelayedRootGuessAt] at hgood)

theorem relTriple_sample_preload_delayedSelector_taggedGuess_of_initial_revealed
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (target : Position) (rightRoot : Digest)
    (hrevealed : Coordinate.position target ∈ state.revealed) :
    RelTriple
      (LazyRevealProbe.sampleHashOutput >>= fun output =>
        (fun selection => (output, selection)) <$>
          delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
            candidates (preloadPositionValue target output state) fuel table cache)
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        candidates state fuel table cache)
      (PermissiveTaggedDelayedRootGuessRel target rightRoot ordinal) := by
  have hbase := relTriple_true
    (LazyRevealProbe.sampleHashOutput >>= fun output =>
      (fun selection => (output, selection)) <$>
        delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
          candidates (preloadPositionValue target output state) fuel table cache)
    (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
      candidates state fuel table cache)
  have hright := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hbase
  apply relTriple_post_mono hright
  intro left right hrelation hgood
  rcases hrelation with ⟨_htrue, hrightSupport⟩
  cases right with
  | none => simp [PermissiveDelayedRootGuess, PermissiveDelayedRootGuessAt] at hgood
  | some selection =>
      obtain ⟨_rightOutput, hgood⟩ := hgood
      exfalso
      exact hgood.2.2.1
        (revealed_subset_of_mem_delayedPermissiveDetailedOrdinalSelection ordinal parameter root
          ftsSecret computation candidates state fuel table cache selection hrightSupport hrevealed)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_sample_preload_delayedPermissiveDetailedOrdinalSelection_taggedGuess
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (target : Position) (rightRoot : Digest)
    (hvalue : state.values (.position target) = none) :
    RelTriple
      (LazyRevealProbe.sampleHashOutput >>= fun output =>
        (fun selection => (output, selection)) <$>
          delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
            candidates (preloadPositionValue target output state) fuel table cache)
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        candidates state fuel table cache)
      (PermissiveTaggedDelayedRootGuessRel target rightRoot ordinal) := by
  induction computation using OracleComp.inductionOn generalizing candidates state fuel cache with
  | pure value =>
      by_cases hrevealed : Coordinate.position target ∈ state.revealed
      · exact relTriple_sample_preload_delayedSelector_taggedGuess_of_initial_revealed ordinal
          parameter root ftsSecret (pure value) candidates state fuel table cache target rightRoot
          hrevealed
      · simp only [delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_pure]
        by_cases hselected : ordinal < candidates.length
        · simp only [hselected, ↓reduceDIte]
          exact relTriple_sample_preload_pureSelection_taggedGuess target rightRoot ordinal
            (candidates.get ⟨ordinal, hselected⟩) candidates state hvalue
        · simp only [hselected, ↓reduceDIte, map_pure]
          exact relTriple_sample_preload_pureNone_taggedGuess target rightRoot ordinal
  | query_bind query next ih =>
      by_cases hrevealed : Coordinate.position target ∈ state.revealed
      · exact relTriple_sample_preload_delayedSelector_taggedGuess_of_initial_revealed ordinal
          parameter root ftsSecret (liftM (OracleSpec.query query) >>= next) candidates state fuel
          table cache target rightRoot hrevealed
      · simp_rw [delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_query_bind]
        by_cases hselected : ordinal < candidates.length
        · simp only [hselected, ↓reduceDIte]
          exact relTriple_sample_preload_pureSelection_taggedGuess target rightRoot ordinal
            (candidates.get ⟨ordinal, hselected⟩) candidates state hvalue
        · simp only [hselected, ↓reduceDIte]
          cases query with
          | inl worldQuery =>
              cases worldQuery with
              | inl n =>
                  let observe := fun nextState remaining value nextCache laterCandidates =>
                    delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret
                      (next value) laterCandidates nextState remaining table nextCache
                  apply relTriple_sample_preload_runPermissive_finishDetailed_taggedGuess target
                    rightRoot ordinal ((splitUniformImpl n).run cache) state fuel table observe
                    observe candidates hvalue (splitUniformImpl_targetPeekFree target n cache)
                  · intro nextState remaining value nextCache hnextValue
                    simpa only [observe] using
                      ih value candidates nextState remaining nextCache hnextValue
                  · intro output left right remaining value nextCache hstate houtput
                    exact relTriple_tagged_delayedSelection_of_stateRel ordinal parameter root
                      ftsSecret (next value) candidates left right remaining table nextCache target
                      output rightRoot hstate houtput
              | inr input =>
                  let nextCandidates :=
                    permissiveRootAwareCandidates parameter input table state candidates
                  by_cases hnextSelected : ordinal < nextCandidates.length
                  · simp only [nextCandidates, hnextSelected, ↓reduceDIte]
                    rw [show (pure (some
                        ⟨(permissiveRootAwareCandidates parameter input table state candidates).get
                            ⟨ordinal, hnextSelected⟩, state,
                          permissiveRootAwareCandidates parameter input table state candidates⟩) :
                        ProbComp (Option PermissivePrivateOrdinalSelection)) =
                      ((pure () : ProbComp Unit) >>= fun _ => pure (some
                        ⟨(permissiveRootAwareCandidates parameter input table state candidates).get
                            ⟨ordinal, hnextSelected⟩, state,
                          permissiveRootAwareCandidates parameter input table state candidates⟩)) by
                        simp]
                    apply relTriple_bind
                      (relTriple_true LazyRevealProbe.sampleHashOutput (pure () : ProbComp Unit))
                    intro output _unit _hrelation
                    rw [permissiveRootAwareCandidates_preload_hidden target output state hrevealed
                      parameter input table candidates]
                    rw [dif_pos hnextSelected]
                    exact relTriple_pure_pure (by
                      intro hgood
                      obtain ⟨_rightOutput, hgood⟩ := hgood
                      exfalso
                      have himpossible := hgood.2.1
                      rw [hvalue] at himpossible
                      simp at himpossible)
                  · simp_rw [permissiveRootAwareCandidates_preload_hidden target _ state hrevealed
                      parameter input table candidates]
                    simp only [nextCandidates, hnextSelected, ↓reduceDIte]
                    simp_rw [delayedPermissivePublicAction_preload_hidden target _ state hrevealed
                      parameter input table cache]
                    let observe := fun nextState remaining value nextCache laterCandidates =>
                      delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret
                        (next value) laterCandidates nextState remaining table nextCache
                    apply relTriple_sample_preload_runPermissive_finishDetailed_taggedGuess target
                      rightRoot ordinal
                      (delayedPermissivePublicAction parameter input table state cache) state fuel
                      table observe observe nextCandidates hvalue
                      (delayedPermissivePublicAction_targetPeekFree target parameter input table
                        state cache)
                    · intro nextState remaining value nextCache hnextValue
                      simpa only [observe] using
                        ih value nextCandidates nextState remaining nextCache hnextValue
                    · intro output left right remaining value nextCache hstate houtput
                      exact relTriple_tagged_delayedSelection_of_stateRel ordinal parameter root
                        ftsSecret (next value) nextCandidates left right remaining table nextCache
                        target output rightRoot hstate houtput
          | inr message =>
              let observe := fun nextState remaining value nextCache laterCandidates =>
                delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret
                  (next value) laterCandidates nextState remaining table nextCache
              apply relTriple_sample_preload_runPermissive_finishDetailed_taggedGuess target
                rightRoot ordinal ((maskedSign parameter root ftsSecret message).run cache) state
                fuel table observe observe candidates hvalue
                (maskedSign_targetPeekFree target parameter root ftsSecret message cache)
              · intro nextState remaining value nextCache hnextValue
                simpa only [observe] using
                  ih value candidates nextState remaining nextCache hnextValue
              · intro output left right remaining value nextCache hstate houtput
                exact relTriple_tagged_delayedSelection_of_stateRel ordinal parameter root
                  ftsSecret (next value) candidates left right remaining table nextCache target
                  output rightRoot hstate houtput

theorem probEvent_delayedRootGuess_le_taggedPreloaded
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (target : Position) (rightRoot : Digest)
    (hvalue : state.values (.position target) = none) :
    Pr[PermissiveDelayedRootGuess target rightRoot ordinal |
        delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
          candidates state fuel table cache] ≤
      Pr[fun result : HashOutput × Option PermissivePrivateOrdinalSelection =>
          PermissiveDelayedRootGuessAt target result.1 rightRoot ordinal result.2 |
        LazyRevealProbe.sampleHashOutput >>= fun output =>
          (fun selection => (output, selection)) <$>
            delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
              candidates (preloadPositionValue target output state) fuel table cache] := by
  apply probEvent_le_of_relTriple
    (relTriple_symm
      (relTriple_sample_preload_delayedPermissiveDetailedOrdinalSelection_taggedGuess ordinal
        parameter root ftsSecret computation candidates state fuel table cache target rightRoot
        hvalue))
  intro right left hrelation hgood
  exact hrelation hgood

theorem probEvent_taggedPreloaded_le_taggedInstalled
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (target : Position) (rightRoot : Digest) :
    Pr[fun result : HashOutput × Option PermissivePrivateOrdinalSelection =>
        PermissiveDelayedRootGuessAt target result.1 rightRoot ordinal result.2 |
      LazyRevealProbe.sampleHashOutput >>= fun output =>
        (fun selection => (output, selection)) <$>
          delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
            candidates (preloadPositionValue target output state) fuel table cache] ≤
      Pr[fun result : HashOutput × Option PermissivePrivateOrdinalSelection =>
          PermissiveDelayedRootGuessAt target result.1 rightRoot ordinal result.2 |
        LazyRevealProbe.sampleHashOutput >>= fun output =>
          (fun selection => (output, selection)) <$>
            delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
              candidates (preloadPositionValue target output state) fuel table
              (replaceHiddenRootCache target output cache)] := by
  apply probEvent_bind_le_bind_of_forall_le
  intro output _houtput
  rw [probEvent_map, probEvent_map]
  apply probEvent_le_of_relTriple
    (relTriple_delayedPermissiveDetailedOrdinalSelection_of_ordinaryCacheEq ordinal parameter root
      ftsSecret computation candidates (preloadPositionValue target output state) fuel table cache
      (replaceHiddenRootCache target output cache)
      (ordinaryQueryCache_replaceHiddenRootCache target output cache))
  intro left right heq hgood
  rwa [← heq]

theorem relTriple_none_any_permissiveFilteredSelection
    (target : Position)
    (right : ProbComp (Option PermissivePrivateOrdinalSelection)) :
    RelTriple (pure none : ProbComp (Option PermissivePrivateOrdinalSelection)) right
      (PermissiveFilteredSelectionRel target) := by
  have hbase := relTriple_true
    (pure none : ProbComp (Option PermissivePrivateOrdinalSelection)) right
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun value => value = none) (by intro value hvalue; simpa using hvalue)
  apply relTriple_post_mono hsupported
  intro left right hrelation
  rw [hrelation.2]
  trivial

theorem relTriple_finishPermissiveFilteredSelection
    (target : Position)
    (leftObserve rightObserve : LazyRevealProbe.State Coordinate → Nat → α →
      SplitHashCache → List Probe → ProbComp (Option PermissivePrivateOrdinalSelection))
    (candidates : List Probe)
    (result : Option (CleanRunResult (α × SplitHashCache)))
    (hrecursive : ∀ (resolved : CleanRunResult (α × SplitHashCache)),
      Coordinate.position target ∉ resolved.state.revealed →
      RelTriple
        (leftObserve resolved.state resolved.remaining resolved.value.1 resolved.value.2 candidates)
        (rightObserve resolved.state resolved.remaining resolved.value.1 resolved.value.2 candidates)
        (PermissiveFilteredSelectionRel target)) :
    RelTriple
      (finishPermissiveDetailedPrivateOrdinalSelection
        (continuePermissiveRootAvoidingDetailedOrdinalSelection target leftObserve)
        candidates result)
      (finishPermissiveDetailedPrivateOrdinalSelection rightObserve candidates result)
      (PermissiveFilteredSelectionRel target) := by
  cases result with
  | none => exact relTriple_pure_pure trivial
  | some resolved =>
      simp only [finishPermissiveDetailedPrivateOrdinalSelection]
      unfold continuePermissiveRootAvoidingDetailedOrdinalSelection
      by_cases hrevealed : Coordinate.position target ∈ resolved.state.revealed
      · simp only [hrevealed, ↓reduceIte]
        exact relTriple_none_any_permissiveFilteredSelection target _
      · simp only [hrevealed, ↓reduceIte]
        exact hrecursive resolved hrevealed

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_permissiveRootAvoidingDetailedOrdinalSelection_delayed
    (ordinal : Nat) (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate)
    (hprivate : Coordinate.position target ∉ state.revealed)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    RelTriple
      (permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter root target
        leftRoot rightRoot ftsSecret computation candidates state fuel table cache)
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        candidates state fuel table cache)
      (PermissiveFilteredSelectionRel target) := by
  induction computation using OracleComp.inductionOn generalizing candidates state fuel cache with
  | pure value =>
      simp only [permissiveActualRootAvoidingDetailedOrdinalSelection,
        permissiveRootAvoidingDetailedOrdinalSelection,
        delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_pure]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure ⟨rfl, hprivate⟩
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure trivial
  | query_bind query next ih =>
      unfold permissiveActualRootAvoidingDetailedOrdinalSelection
      rw [permissiveRootAvoidingDetailedOrdinalSelection, OracleComp.construct_query_bind,
        delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure ⟨rfl, hprivate⟩
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                let leftObserve :=
                  fun nextState remaining value nextCache laterCandidates =>
                    permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter root
                      target leftRoot rightRoot ftsSecret (next value) laterCandidates nextState
                      remaining table nextCache
                let rightObserve :=
                  fun nextState remaining value nextCache laterCandidates =>
                    delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret
                      (next value) laterCandidates nextState remaining table nextCache
                apply relTriple_bind
                  (relTriple_refl
                    (runPermissiveFromTable state fuel table ((splitUniformImpl n).run cache)))
                intro leftResult rightResult hresult
                subst rightResult
                apply relTriple_finishPermissiveFilteredSelection target leftObserve rightObserve
                  candidates leftResult
                intro resolved hresolvedPrivate
                simpa only [leftObserve, rightObserve] using
                  ih resolved.value.1 candidates resolved.state hresolvedPrivate resolved.remaining
                    resolved.value.2
            | inr input =>
                let nextCandidates := permissiveRootAwareCandidates parameter input table state
                  candidates
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hactual : ordinal <
                      (permissiveRootAwareCandidates parameter input table state candidates).length := by
                    simpa [nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  exact relTriple_pure_pure ⟨rfl, hprivate⟩
                · have hactual : ¬ordinal <
                      (permissiveRootAwareCandidates parameter input table state candidates).length := by
                    simpa [nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  let candidate? := rootAwareCandidateForPlan? parameter input
                    (purePlanProbingHashQuery parameter input
                      (materializedCanonicalContext table state).state)
                  by_cases hsafe : RootAwareCandidateAvoidsRoots target leftRoot rightRoot candidate?
                  · have hsafeActual : RootAwareCandidateAvoidsRoots target leftRoot rightRoot
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [candidate?] using hsafe
                    simp only [hsafeActual, ↓reduceIte]
                    let leftObserve :=
                      fun nextState remaining value nextCache laterCandidates =>
                        permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter root
                          target leftRoot rightRoot ftsSecret (next value) laterCandidates nextState
                          remaining table nextCache
                    let rightObserve :=
                      fun nextState remaining value nextCache laterCandidates =>
                        delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret
                          (next value) laterCandidates nextState remaining table nextCache
                    apply relTriple_bind
                      (relTriple_refl
                        (runPermissiveFromTable state fuel table
                          (delayedPermissivePublicAction parameter input table state cache)))
                    intro leftResult rightResult hresult
                    subst rightResult
                    apply relTriple_finishPermissiveFilteredSelection target leftObserve
                      rightObserve nextCandidates leftResult
                    intro resolved hresolvedPrivate
                    simpa only [leftObserve, rightObserve] using
                      ih resolved.value.1 nextCandidates resolved.state hresolvedPrivate
                        resolved.remaining resolved.value.2
                  · have hsafeActual : ¬RootAwareCandidateAvoidsRoots target leftRoot rightRoot
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [candidate?] using hsafe
                    simp only [hsafeActual, ↓reduceIte]
                    exact relTriple_none_any_permissiveFilteredSelection target _
        | inr message =>
            let leftObserve :=
              fun nextState remaining value nextCache laterCandidates =>
                permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter root target
                  leftRoot rightRoot ftsSecret (next value) laterCandidates nextState remaining table
                  nextCache
            let rightObserve :=
              fun nextState remaining value nextCache laterCandidates =>
                delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret
                  (next value) laterCandidates nextState remaining table nextCache
            apply relTriple_bind
              (relTriple_refl
                (runPermissiveFromTable state fuel table
                  ((maskedSign parameter root ftsSecret message).run cache)))
            intro leftResult rightResult hresult
            subst rightResult
            apply relTriple_finishPermissiveFilteredSelection target leftObserve rightObserve
              candidates leftResult
            intro resolved hresolvedPrivate
            simpa only [leftObserve, rightObserve] using
              ih resolved.value.1 candidates resolved.state hresolvedPrivate resolved.remaining
                resolved.value.2

theorem PermissiveFilteredSelectionRel.targetFiber
    {target : Position}
    {left right : Option PermissivePrivateOrdinalSelection}
    (hroot : IsLayerRoot target)
    (hrel : PermissiveFilteredSelectionRel target left right)
    (hat : materializedOrdinalSelectionAt target
      (erasePermissivePrivateOrdinalSelection left)) :
    permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? right = some target := by
  cases left with
  | none => simp [erasePermissivePrivateOrdinalSelection,
      materializedOrdinalSelectionAt] at hat
  | some left =>
      cases right with
      | none => simp [PermissiveFilteredSelectionRel] at hrel
      | some right =>
          rcases hrel with ⟨rfl, hprivate⟩
          simp only [erasePermissivePrivateOrdinalSelection] at hat
          exact permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?_eq_some_of_candidate
            hat hroot hprivate

theorem probEvent_permissiveRootAvoidingSelection_le_delayedFiber
    (ordinal : Nat) (parameter : PublicParameter) (target : Position)
    (hroot : IsLayerRoot target) (root leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate)
    (hprivate : Coordinate.position target ∉ state.revealed)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    Pr[fun selection => materializedOrdinalSelectionAt target
          (erasePermissivePrivateOrdinalSelection selection) |
      permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter root target
        leftRoot rightRoot ftsSecret computation candidates state fuel table cache] ≤
      Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
          candidates state fuel table cache] := by
  apply probEvent_le_of_relTriple
    (relTriple_permissiveRootAvoidingDetailedOrdinalSelection_delayed ordinal parameter target
      leftRoot rightRoot root ftsSecret computation candidates state hprivate fuel table cache)
  intro left right hrelation hleft
  exact hrelation.targetFiber hroot hleft

set_option maxRecDepth 100000 in
theorem probEvent_sampledHigh_permissiveRootAvoidingSelection_le_installedDelayed
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (rootResult : CleanRunResult (Digest × SplitHashCache))
    (hunrevealed : Coordinate.position target ∉ rootResult.state.revealed) :
    Pr[fun result : Digest × Option Probe =>
        materializedOrdinalSelectionAt target result.2 | do
      let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
      let leftRoot ← ($ᵗ Digest : ProbComp Digest)
      let output := fun root => rootOutputOfParts root high
      let selection ← erasePermissivePrivateOrdinalSelection <$>
        permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter
          rootResult.value.1 target leftRoot leftRoot ftsSecret
          (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
          (preloadPositionValue target (output leftRoot) rootResult.state) rootResult.remaining
          rootResult.table (rootInstalledCache target output rootResult.value.2 leftRoot)
      pure (leftRoot, selection)] ≤
      Pr[fun result =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? result.2 = some target |
        sampledHighInstalledDelayedSelectionAfterRootResult ordinal adversary parameter ftsSecret
          target rootResult] := by
  unfold sampledHighInstalledDelayedSelectionAfterRootResult
  apply probEvent_bind_le_bind_of_forall_le
  intro high _hhigh
  apply probEvent_bind_le_bind_of_forall_le
  intro leftRoot _hleftRoot
  let output := fun root => rootOutputOfParts root high
  let left := permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter
    rootResult.value.1 target leftRoot leftRoot ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
    (preloadPositionValue target (output leftRoot) rootResult.state) rootResult.remaining
    rootResult.table (rootInstalledCache target output rootResult.value.2 leftRoot)
  let leftErased := erasePermissivePrivateOrdinalSelection <$> left
  let right := delayedPermissiveDetailedOrdinalSelection ordinal parameter rootResult.value.1
    ftsSecret (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
    (preloadPositionValue target (output leftRoot) rootResult.state) rootResult.remaining
    rootResult.table (rootInstalledCache target output rootResult.value.2 leftRoot)
  rw [show (do let selection ← leftErased; pure (leftRoot, selection)) =
      (fun selection => (leftRoot, selection)) <$> leftErased by simp [map_eq_bind_pure_comp],
    show (do let selection ← right; pure (leftRoot, selection)) =
      (fun selection => (leftRoot, selection)) <$> right by simp [map_eq_bind_pure_comp],
    probEvent_map, probEvent_map, probEvent_map]
  exact probEvent_permissiveRootAvoidingSelection_le_delayedFiber ordinal parameter target hroot
    rootResult.value.1 leftRoot leftRoot ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
    (preloadPositionValue target (output leftRoot) rootResult.state)
    (by simpa [output] using hunrevealed) rootResult.remaining rootResult.table
    (rootInstalledCache target output rootResult.value.2 leftRoot)

set_option maxRecDepth 100000 in
theorem probEvent_sampledRoots_taggedInstalledGuess_le_mul
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (rootResult : CleanRunResult (Digest × SplitHashCache))
    (hunrevealed : Coordinate.position target ∉ rootResult.state.revealed)
    (hcacheSwap : ∀ high leftRoot rightRoot,
      fullSwapRootCache parameter target leftRoot rightRoot
          (rootOutputOfParts rightRoot high)
          (replaceHiddenRootCache target (rootOutputOfParts leftRoot high) rootResult.value.2) =
        replaceHiddenRootCache target (rootOutputOfParts rightRoot high) rootResult.value.2) :
    Pr[fun result : HashOutput × Digest × Option PermissivePrivateOrdinalSelection =>
        PermissiveDelayedRootGuessAt target result.1 result.2.1 ordinal result.2.2 | do
      let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
      let leftRoot ← ($ᵗ Digest : ProbComp Digest)
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      let output := rootOutputOfParts leftRoot high
      let selection ← delayedPermissiveDetailedOrdinalSelection ordinal parameter
        rootResult.value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
        (preloadPositionValue target output rootResult.state) rootResult.remaining rootResult.table
        (replaceHiddenRootCache target output rootResult.value.2)
      pure (output, rightRoot, selection)] ≤
      Pr[fun result =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? result.2 = some target |
        sampledHighInstalledDelayedSelectionAfterRootResult ordinal adversary parameter ftsSecret
          target rootResult] * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  let delayed := fun high leftRoot =>
    delayedPermissiveDetailedOrdinalSelection ordinal parameter rootResult.value.1 ftsSecret
      (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
      (preloadPositionValue target (rootOutputOfParts leftRoot high) rootResult.state)
      rootResult.remaining rootResult.table
      (replaceHiddenRootCache target (rootOutputOfParts leftRoot high) rootResult.value.2)
  let actual := fun high leftRoot rightRoot =>
    permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter rootResult.value.1
      target (truncateHash (rootOutputOfParts leftRoot high)) rightRoot ftsSecret
      (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
      (preloadPositionValue target (rootOutputOfParts leftRoot high) rootResult.state)
      rootResult.remaining rootResult.table
      (replaceHiddenRootCache target (rootOutputOfParts leftRoot high) rootResult.value.2)
  calc
    _ ≤ Pr[fun result : Digest × Digest × Option Probe =>
          materializedOrdinalSelectionMatches target result.1 result.2.2 | do
        let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
        let leftRoot ← ($ᵗ Digest : ProbComp Digest)
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        let selection ← erasePermissivePrivateOrdinalSelection <$>
          actual high leftRoot rightRoot
        pure (leftRoot, rightRoot, selection)] := by
      apply probEvent_bind_le_bind_of_forall_le
      intro high _hhigh
      apply probEvent_bind_le_bind_of_forall_le
      intro leftRoot _hleftRoot
      apply probEvent_bind_le_bind_of_forall_le
      intro rightRoot _hrightRoot
      have hdelayed : (do
          let selection ← delayed high leftRoot
          pure (rootOutputOfParts leftRoot high, rightRoot, selection)) =
          (fun selection => (rootOutputOfParts leftRoot high, rightRoot, selection)) <$>
            delayed high leftRoot := by simp [map_eq_bind_pure_comp]
      have hactual : (do
          let selection ← erasePermissivePrivateOrdinalSelection <$>
            actual high leftRoot rightRoot
          pure (leftRoot, rightRoot, selection)) =
          (fun selection => (leftRoot, rightRoot, selection)) <$>
            (erasePermissivePrivateOrdinalSelection <$> actual high leftRoot rightRoot) := by
        simp [map_eq_bind_pure_comp]
      rw [hdelayed, hactual, probEvent_map, probEvent_map, probEvent_map]
      change Pr[PermissiveDelayedRootGuessAt target (rootOutputOfParts leftRoot high) rightRoot
          ordinal | delayed high leftRoot] ≤
        Pr[materializedOrdinalSelectionMatches target leftRoot ∘
            erasePermissivePrivateOrdinalSelection | actual high leftRoot rightRoot]
      apply probEvent_le_of_relTriple
        (relTriple_symm
          (relTriple_delayed_permissiveRootAvoidingDetailedOrdinalSelection ordinal parameter
            rootResult.value.1 target (rootOutputOfParts leftRoot high) rightRoot ftsSecret
            (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
            (preloadPositionValue target (rootOutputOfParts leftRoot high) rootResult.state)
            rootResult.remaining rootResult.table
            (replaceHiddenRootCache target (rootOutputOfParts leftRoot high)
              rootResult.value.2)))
      intro right left hrelation hgood
      have heq := hrelation hgood
      rw [heq]
      cases right with
      | none => exact False.elim hgood
      | some selection =>
          simpa [Function.comp_def, materializedOrdinalSelectionMatches,
            erasePermissivePrivateOrdinalSelection, truncateHash_rootOutputOfParts] using hgood.1
    _ ≤ Pr[fun result : Digest × Option Probe =>
          materializedOrdinalSelectionAt target result.2 | do
        let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
        let leftRoot ← ($ᵗ Digest : ProbComp Digest)
        let selection ← erasePermissivePrivateOrdinalSelection <$> actual high leftRoot leftRoot
        pure (leftRoot, selection)] *
          ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
      apply probEvent_bind_le_bind_mul_of_forall
      intro high _hhigh
      simpa [actual, truncateHash_rootOutputOfParts, rootInstalledCache] using
        (probEvent_uniformActualRoot_permissiveRootAvoidingSelection_le_mul ordinal parameter
          rootResult.value.1 target hroot (fun root => rootOutputOfParts root high)
          (fun root => truncateHash_rootOutputOfParts root high) ftsSecret
          (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
          rootResult.state hunrevealed rootResult.remaining rootResult.table
          (fun root => replaceHiddenRootCache target (rootOutputOfParts root high)
            rootResult.value.2)
          (by intro root; simp [replaceHiddenRootCache])
          (hcacheSwap high))
    _ ≤ _ := by
      gcongr
      simpa [actual, truncateHash_rootOutputOfParts, rootInstalledCache] using
        (probEvent_sampledHigh_permissiveRootAvoidingSelection_le_installedDelayed ordinal
          adversary parameter ftsSecret target hroot rootResult hunrevealed)

set_option maxRecDepth 100000 in
theorem probEvent_delayedRootGuess_afterRootResult_le_mul
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (rootResult : CleanRunResult (Digest × SplitHashCache))
    (hvalue : rootResult.state.values (.position target) = none)
    (hunrevealed : Coordinate.position target ∉ rootResult.state.revealed)
    (hcacheSwap : ∀ high leftRoot rightRoot,
      fullSwapRootCache parameter target leftRoot rightRoot
          (rootOutputOfParts rightRoot high)
          (replaceHiddenRootCache target (rootOutputOfParts leftRoot high) rootResult.value.2) =
        replaceHiddenRootCache target (rootOutputOfParts rightRoot high) rootResult.value.2) :
    Pr[fun result : Option PermissivePrivateOrdinalSelection × Digest =>
        PermissiveDelayedRootGuess target result.2 ordinal result.1 | do
      let selection ← delayedPermissiveDetailedOrdinalSelection ordinal parameter
        rootResult.value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
        rootResult.state rootResult.remaining rootResult.table rootResult.value.2
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (selection, rightRoot)] ≤
      Pr[fun result =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? result.2 = some target |
        sampledHighInstalledDelayedSelectionAfterRootResult ordinal adversary parameter ftsSecret
          target rootResult] * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  let raw := delayedPermissiveDetailedOrdinalSelection ordinal parameter rootResult.value.1
    ftsSecret (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
    rootResult.state rootResult.remaining rootResult.table rootResult.value.2
  let installed := fun output =>
    delayedPermissiveDetailedOrdinalSelection ordinal parameter rootResult.value.1 ftsSecret
      (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
      (preloadPositionValue target output rootResult.state) rootResult.remaining rootResult.table
      (replaceHiddenRootCache target output rootResult.value.2)
  let reordered : ProbComp (Option PermissivePrivateOrdinalSelection × Digest) := do
    let rightRoot ← ($ᵗ Digest : ProbComp Digest)
    let selection ← raw
    pure (selection, rightRoot)
  let tagged : ProbComp (HashOutput × Digest × Option PermissivePrivateOrdinalSelection) := do
    let rightRoot ← ($ᵗ Digest : ProbComp Digest)
    let output ← LazyRevealProbe.sampleHashOutput
    let selection ← installed output
    pure (output, rightRoot, selection)
  have hreorder : evalDist (do
      let selection ← raw
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (selection, rightRoot)) = evalDist reordered := by
    exact OracleComp.DeferredSampling.evalDist_bind_comm raw
      ($ᵗ Digest : ProbComp Digest) (fun selection rightRoot => pure (selection, rightRoot))
  calc
    _ = Pr[fun result : Option PermissivePrivateOrdinalSelection × Digest =>
          PermissiveDelayedRootGuess target result.2 ordinal result.1 | reordered] := by
      apply OracleComp.probEvent_congr' (fun _ _ => Iff.rfl)
      exact hreorder
    _ ≤ Pr[fun result : HashOutput × Digest × Option PermissivePrivateOrdinalSelection =>
          PermissiveDelayedRootGuessAt target result.1 result.2.1 ordinal result.2.2 |
        tagged] := by
      unfold reordered tagged
      apply probEvent_bind_le_bind_of_forall_le
      intro rightRoot _hrightRoot
      have hraw : (do let selection ← raw; pure (selection, rightRoot)) =
          (fun selection => (selection, rightRoot)) <$> raw := by
        simp [map_eq_bind_pure_comp]
      have htaggedPair : (do
          let output ← LazyRevealProbe.sampleHashOutput
          let selection ← installed output
          pure (output, rightRoot, selection)) =
          (fun result : HashOutput × Option PermissivePrivateOrdinalSelection =>
            (result.1, rightRoot, result.2)) <$> (do
              let output ← LazyRevealProbe.sampleHashOutput
              (fun selection => (output, selection)) <$> installed output) := by
        simp [map_eq_bind_pure_comp, bind_assoc]
      rw [hraw, htaggedPair, probEvent_map, probEvent_map]
      calc
        _ ≤ Pr[fun result : HashOutput × Option PermissivePrivateOrdinalSelection =>
              PermissiveDelayedRootGuessAt target result.1 rightRoot ordinal result.2 |
            LazyRevealProbe.sampleHashOutput >>= fun output =>
              (fun selection => (output, selection)) <$>
                delayedPermissiveDetailedOrdinalSelection ordinal parameter rootResult.value.1
                  ftsSecret
                  (retainedGameRestComputation adversary
                    ⟨rootResult.value.1, parameter⟩) []
                  (preloadPositionValue target output rootResult.state) rootResult.remaining
                  rootResult.table rootResult.value.2] :=
          probEvent_delayedRootGuess_le_taggedPreloaded ordinal parameter rootResult.value.1
            ftsSecret
            (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
            rootResult.state rootResult.remaining rootResult.table rootResult.value.2 target
            rightRoot hvalue
        _ ≤ _ := by
          change Pr[fun result : HashOutput × Option PermissivePrivateOrdinalSelection =>
              PermissiveDelayedRootGuessAt target result.1 rightRoot ordinal result.2 |
            LazyRevealProbe.sampleHashOutput >>= fun output =>
              (fun selection => (output, selection)) <$>
                delayedPermissiveDetailedOrdinalSelection ordinal parameter rootResult.value.1
                  ftsSecret
                  (retainedGameRestComputation adversary
                    ⟨rootResult.value.1, parameter⟩) []
                  (preloadPositionValue target output rootResult.state) rootResult.remaining
                  rootResult.table rootResult.value.2] ≤
            Pr[fun result : HashOutput × Option PermissivePrivateOrdinalSelection =>
                PermissiveDelayedRootGuessAt target result.1 rightRoot ordinal result.2 |
              LazyRevealProbe.sampleHashOutput >>= fun output =>
                (fun selection => (output, selection)) <$> installed output]
          simpa only [installed] using
            (probEvent_taggedPreloaded_le_taggedInstalled ordinal parameter rootResult.value.1
              ftsSecret
              (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
              rootResult.state rootResult.remaining rootResult.table rootResult.value.2 target
              rightRoot)
    _ = Pr[fun result : HashOutput × Digest × Option PermissivePrivateOrdinalSelection =>
          PermissiveDelayedRootGuessAt target result.1 result.2.1 ordinal result.2.2 | do
        let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
        let leftRoot ← ($ᵗ Digest : ProbComp Digest)
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        let output := rootOutputOfParts leftRoot high
        let selection ← installed output
        pure (output, rightRoot, selection)] := by
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
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        let selection ← installed output
        pure (output, rightRoot, selection)
      have htagged : evalDist tagged = evalDist (parts >>= continuation) := by
        calc
          _ = evalDist (LazyRevealProbe.sampleHashOutput >>= continuation) := by
            unfold tagged continuation
            exact OracleComp.DeferredSampling.evalDist_bind_comm
              ($ᵗ Digest : ProbComp Digest) LazyRevealProbe.sampleHashOutput
              (fun rightRoot output => do
                let selection ← installed output
                pure (output, rightRoot, selection))
          _ = _ := (evalDist_bind_eq_of_evalDist_eq hparts continuation).symm
      apply OracleComp.probEvent_congr' (fun _ _ => Iff.rfl)
      calc
        evalDist tagged = evalDist (parts >>= continuation) := htagged
        _ = _ := by simp [parts, continuation, bind_assoc]
    _ ≤ _ := probEvent_sampledRoots_taggedInstalledGuess_le_mul ordinal adversary parameter
      ftsSecret target hroot rootResult hunrevealed hcacheSwap

theorem fullSwapRootCache_replace_of_swapCanonical_eq
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (leftOutput rightOutput : HashOutput)
    (cache : SplitHashCache)
    (hcache : swapCanonicalRootEncodingCache parameter target leftRoot rightRoot cache = cache) :
    fullSwapRootCache parameter target leftRoot rightRoot rightOutput
        (replaceHiddenRootCache target leftOutput cache) =
      replaceHiddenRootCache target rightOutput cache := by
  unfold fullSwapRootCache
  funext key
  cases key with
  | ordinary input =>
      simpa [swapCanonicalRootEncodingCache, replaceHiddenRootCache] using
        congrFun hcache (.ordinary input)
  | hidden coordinate =>
      by_cases heq : coordinate = .position target
      · subst coordinate
        simp [replaceHiddenRootCache]
      · simp [swapCanonicalRootEncodingCache, replaceHiddenRootCache, heq]

set_option maxRecDepth 100000 in
theorem probEvent_delayedRootGuess_afterRootResult_le_installed_mul
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (rootResult : CleanRunResult (Digest × SplitHashCache))
    (hvalue : rootResult.state.values (.position target) = none)
    (hunrevealed : Coordinate.position target ∉ rootResult.state.revealed)
    (hbaseSwap : ∀ leftRoot rightRoot,
      swapCanonicalRootEncodingCache parameter target leftRoot rightRoot
          rootResult.value.2 = rootResult.value.2) :
    Pr[fun result : Option PermissivePrivateOrdinalSelection × Digest =>
        PermissiveDelayedRootGuess target result.2 ordinal result.1 | do
      let selection ← delayedPermissiveDetailedOrdinalSelection ordinal parameter
        rootResult.value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
        rootResult.state rootResult.remaining rootResult.table rootResult.value.2
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (selection, rightRoot)] ≤
      Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        installedDelayedPermissiveDetailedSelectionAfterRootResult ordinal adversary parameter
          ftsSecret target rootResult] * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  have hfullSwap (high : RootOutputHigh) (leftRoot rightRoot : Digest) :
      fullSwapRootCache parameter target leftRoot rightRoot
          (rootOutputOfParts rightRoot high)
          (replaceHiddenRootCache target (rootOutputOfParts leftRoot high)
            rootResult.value.2) =
        replaceHiddenRootCache target (rootOutputOfParts rightRoot high)
          rootResult.value.2 := by
    exact fullSwapRootCache_replace_of_swapCanonical_eq parameter target leftRoot rightRoot
      (rootOutputOfParts leftRoot high) (rootOutputOfParts rightRoot high)
      rootResult.value.2 (hbaseSwap leftRoot rightRoot)
  calc
    _ ≤ Pr[fun result =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? result.2 = some target |
        sampledHighInstalledDelayedSelectionAfterRootResult ordinal adversary parameter
          ftsSecret target rootResult] * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
      probEvent_delayedRootGuess_afterRootResult_le_mul ordinal adversary parameter ftsSecret
        target hroot rootResult hvalue hunrevealed hfullSwap
    _ = _ := by
      congr 1
      rw [show Pr[fun result =>
            permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? result.2 = some target |
          sampledHighInstalledDelayedSelectionAfterRootResult ordinal adversary parameter
            ftsSecret target rootResult] =
          Pr[fun selection =>
            permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
            Prod.snd <$> sampledHighInstalledDelayedSelectionAfterRootResult ordinal adversary
              parameter ftsSecret target rootResult] by
              rw [probEvent_map]
              rfl]
      apply OracleComp.probEvent_congr' (fun _ _ => Iff.rfl)
      exact evalDist_sampledHighInstalledDelayed_snd_eq_installed ordinal adversary parameter
        ftsSecret target rootResult

end SphincsSecurity.Concrete.OtsProbeSimulation
