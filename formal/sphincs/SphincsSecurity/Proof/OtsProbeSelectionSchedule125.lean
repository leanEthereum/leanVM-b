import SphincsSecurity.Proof.OtsProbePermissiveFuel125

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot

set_option maxRecDepth 100000 in
theorem relTriple_delayed_rootAware_permissiveSelection
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (left right : LazyRevealProbe.State Coordinate)
    (leftFuel rightFuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hstate : PermissiveStateRel left right)
    (hleftFuel : ordinal < candidates.length + leftFuel)
    (hrightFuel : ordinal < candidates.length + rightFuel) :
    RelTriple
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        candidates left leftFuel table cache)
      (permissiveDetailedRootAwareOrdinalSelection ordinal parameter root ftsSecret computation
        candidates right rightFuel table cache)
      PermissiveDetailedSelectionRel := by
  induction computation using OracleComp.inductionOn generalizing
      candidates left right leftFuel rightFuel cache with
  | pure value =>
      simp only [delayedPermissiveDetailedOrdinalSelection,
        permissiveDetailedRootAwareOrdinalSelection, OracleComp.construct_pure]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure ⟨rfl, rfl, hstate⟩
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure trivial
  | query_bind query next ih =>
      rw [delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_query_bind,
        permissiveDetailedRootAwareOrdinalSelection, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure ⟨rfl, rfl, hstate⟩
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                apply relTriple_bind
                  (relTriple_runPermissive_probeFree_of_stateRel
                    ((splitUniformImpl n).run cache) left right leftFuel rightFuel table hstate
                    (splitUniformImpl_probeFree n cache))
                intro leftResult rightResult hresult
                cases leftResult with
                | none => exact False.elim hresult
                | some leftResult =>
                    cases rightResult with
                    | none => exact False.elim hresult
                    | some rightResult =>
                        rcases hresult with ⟨hstate, hleft, hright, hvalue, _htable⟩
                        simp only [finishPermissiveDetailedPrivateOrdinalSelection, ← hvalue]
                        exact ih leftResult.value.1 candidates leftResult.state rightResult.state
                          leftResult.remaining rightResult.remaining leftResult.value.2 hstate
                          (by omega) (by omega)
            | inr input =>
                let nextCandidates := permissiveRootAwareCandidates parameter input table left
                  candidates
                have hnext : permissiveRootAwareCandidates parameter input table right candidates =
                    nextCandidates :=
                  (permissiveRootAwareCandidates_eq_of_stateRel parameter input table candidates
                    hstate).symm
                dsimp only
                rw [hnext]
                by_cases hnextSelected : ordinal < nextCandidates.length
                · simp only [nextCandidates, hnextSelected, ↓reduceDIte]
                  exact relTriple_pure_pure ⟨rfl, rfl, hstate⟩
                · simp only [nextCandidates, hnextSelected, ↓reduceDIte]
                  apply relTriple_bind
                    (relTriple_delayed_rootAware_permissivePublicAction parameter input left right
                      leftFuel rightFuel table cache hstate (by omega) (by omega))
                  intro leftResult rightResult hresult
                  cases leftResult with
                  | none => exact False.elim hresult
                  | some leftResult =>
                      cases rightResult with
                      | none => exact False.elim hresult
                      | some rightResult =>
                          rcases hresult with ⟨hstate, hleft, hright, hvalue, _htable⟩
                          have hlength : nextCandidates.length = candidates.length +
                              (rootAwareCandidateForPlan? parameter input
                                (permissiveRootAwarePlan parameter input table left)).isSome.toNat :=
                            appendPlannedCandidate_length candidates _
                          simp only [finishPermissiveDetailedPrivateOrdinalSelection, ← hvalue]
                          exact ih leftResult.value.1 nextCandidates leftResult.state
                            rightResult.state leftResult.remaining rightResult.remaining
                            leftResult.value.2 hstate (by omega) (by omega)
        | inr message =>
            apply relTriple_bind
              (relTriple_runPermissive_probeFree_of_stateRel
                ((maskedSign parameter root ftsSecret message).run cache) left right leftFuel
                rightFuel table hstate (maskedSign_probeFree parameter root ftsSecret message cache))
            intro leftResult rightResult hresult
            cases leftResult with
            | none => exact False.elim hresult
            | some leftResult =>
                cases rightResult with
                | none => exact False.elim hresult
                | some rightResult =>
                    rcases hresult with ⟨hstate, hleft, hright, hvalue, _htable⟩
                    simp only [finishPermissiveDetailedPrivateOrdinalSelection, ← hvalue]
                    exact ih leftResult.value.1 candidates leftResult.state rightResult.state
                      leftResult.remaining rightResult.remaining leftResult.value.2 hstate
                      (by omega) (by omega)

def InitialSelectionFuelRel (leftFuel rightFuel : Nat) :
    Option (CleanRunResult α) → Option (CleanRunResult α) → Prop
  | none, none => True
  | some left, some right => PermissiveCleanFuelRel leftFuel rightFuel (some left) (some right)
  | _, _ => False

set_option maxRecDepth 100000 in
theorem relTriple_rootAwareProductionInitialRun_fuel
    (leftFuel rightFuel : Nat) (table : OtsSecretIndex → HashOutput) :
    RelTriple (rootAwareProductionInitialRun leftFuel table)
      (rootAwareProductionInitialRun rightFuel table)
      (InitialSelectionFuelRel leftFuel rightFuel) := by
  let computation := maskedPublishedTreeRoot.run emptySplitHashCache
  have hfree := maskedPublishedTreeRoot_probeFree emptySplitHashCache
  have hbase := relTriple_runObservedCleanFromTable_fuel_of_isQueryBoundP computation []
    LazyRevealProbe.State.empty leftFuel rightFuel 0 table hfree (by omega) (by omega)
  have hleft := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
    (fun result => result ∈ support
      (runObservedCleanFromTable [] LazyRevealProbe.State.empty leftFuel table computation))
    (fun result hresult => hresult)
  have hboth := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
  have hproject : RelTriple
      (runObservedCleanFromTable [] LazyRevealProbe.State.empty leftFuel table computation)
      (runObservedCleanFromTable [] LazyRevealProbe.State.empty rightFuel table computation)
      (fun left right => InitialSelectionFuelRel leftFuel rightFuel
        (projectObservedCleanRun left) (projectObservedCleanRun right)) := by
    apply relTriple_post_mono hboth
    intro left right hresult
    obtain ⟨⟨hrel, hleft⟩, hright⟩ := hresult
    cases left with
    | none =>
        cases right with
        | none => trivial
        | some right => exact False.elim hrel
    | some left =>
        cases right with
        | none => exact False.elim hrel
        | some right =>
            have hleftFuel := remaining_eq_fuel_of_mem_observed_of_probeFree computation []
              LazyRevealProbe.State.empty leftFuel table left hfree hleft
            have hrightFuel := remaining_eq_fuel_of_mem_observed_of_probeFree computation []
              LazyRevealProbe.State.empty rightFuel table right hfree hright
            exact ⟨⟨congrArg LazyRevealProbe.State.values hrel.1,
                congrArg LazyRevealProbe.State.revealed hrel.1⟩,
              hleftFuel, hrightFuel, hrel.2.2.1, hrel.2.1⟩
  have hmapped := relTriple_map (f := projectObservedCleanRun) (g := projectObservedCleanRun)
    hproject
  rw [map_projectObservedCleanRun_runObservedCleanFromTable,
    map_projectObservedCleanRun_runObservedCleanFromTable] at hmapped
  exact hmapped

set_option maxRecDepth 100000 in
theorem relTriple_delayed_rootAware_commonSelection
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (leftFuel rightFuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hleftFuel : ordinal < leftFuel) (hrightFuel : ordinal < rightFuel) :
    RelTriple
      (delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
        ftsSecret leftFuel table)
      (permissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
        ftsSecret rightFuel table)
      PermissiveDetailedSelectionRel := by
  unfold delayedPermissiveDetailedSelectionExperimentAfterTable
    permissiveDetailedSelectionExperimentAfterTable
  apply relTriple_bind (relTriple_rootAwareProductionInitialRun_fuel leftFuel rightFuel table)
  intro left right hresult
  cases left with
  | none =>
      cases right with
      | none => exact relTriple_pure_pure trivial
      | some right => exact False.elim hresult
  | some left =>
      cases right with
      | none => exact False.elim hresult
      | some right =>
          rcases hresult with ⟨hstate, hleft, hright, hvalue, htable⟩
          simp only [delayedPermissiveDetailedSelectionAfterRootResult,
            permissiveDetailedSelectionAfterRootResult, ← hvalue, ← htable]
          exact relTriple_delayed_rootAware_permissiveSelection ordinal parameter left.value.1
            ftsSecret (retainedGameRestComputation adversary ⟨left.value.1, parameter⟩) []
            left.state right.state left.remaining right.remaining left.table left.value.2 hstate
            (by simpa [hleft]) (by simpa [hright])

theorem probEvent_delayedCommon_nonRoot_le_rootAwareCommon
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (leftFuel rightFuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hleftFuel : ordinal < leftFuel) (hrightFuel : ordinal < rightFuel) :
    Pr[PermissiveSelectionNonRoot |
      delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
        ftsSecret leftFuel table] ≤
    Pr[PermissiveSelectionNonRoot |
      permissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
        ftsSecret rightFuel table] := by
  apply probEvent_le_of_relTriple
    (relTriple_delayed_rootAware_commonSelection ordinal adversary parameter ftsSecret
      leftFuel rightFuel table hleftFuel hrightFuel)
  intro left right hrelation hnonRoot
  cases left with
  | none => exact False.elim hnonRoot
  | some left =>
      cases right with
      | none => exact False.elim hrelation
      | some right =>
          change ¬right.candidate.IsLayerRoot
          rw [← hrelation.1]
          exact hnonRoot

end SphincsSecurity.Concrete.OtsProbeSimulation
