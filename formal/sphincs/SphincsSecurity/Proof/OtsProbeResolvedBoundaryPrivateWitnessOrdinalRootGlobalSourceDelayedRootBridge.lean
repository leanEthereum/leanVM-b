import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSourceDelayedRootProduction

/-!
# Delayed source to materialized root bridge

The delayed source coupling retains the selected candidate, its hidden value and the complete
candidate prefix. This packages exactly the common-selector event that can survive the
failure-retaining materialized root selector.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def PermissiveDelayedRootGuessAt
    (target : Position) (output : HashOutput) (rightRoot : Digest) (ordinal : Nat) :
    Option PermissivePrivateOrdinalSelection → Prop
  | none => False
  | some selection =>
      selection.candidate = ⟨.position target, truncateHash output⟩ ∧
        selection.state.values (.position target) = some output ∧
        Coordinate.position target ∉ selection.state.revealed ∧
        CandidatesAvoidRoots target (truncateHash output) rightRoot
          (selection.candidates.take ordinal)

def PermissiveDelayedRootGuess
    (target : Position) (rightRoot : Digest) (ordinal : Nat) :
    Option PermissivePrivateOrdinalSelection → Prop :=
  fun selection => ∃ output, PermissiveDelayedRootGuessAt target output rightRoot ordinal selection

theorem DelayedPermissiveSelectionRel.delayedRootGuess
    {target : Position} {rightRoot : Digest} {ordinal : Nat}
    {left : Option PrivateOrdinalSelection}
    {right : Option PermissivePrivateOrdinalSelection}
    (hrel : DelayedPermissiveSelectionRel target rightRoot ordinal left right)
    (hgood : privateOrdinalSelectionGoodForSomeOutput target rightRoot ordinal left) :
    PermissiveDelayedRootGuess target rightRoot ordinal right := by
  obtain ⟨output, leftSelection, rightSelection, hleft, hright, hleftGood, hcandidate,
    hcandidates, hposition, hvalue⟩ := hrel hgood
  rw [hright]
  refine ⟨output, hcandidate.symm.trans hleftGood.1, hvalue, ?_, ?_⟩
  · obtain ⟨selected, hselected, _hroot, hunrevealed⟩ :=
      (permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?_eq_some_iff target
        (some rightSelection)).mp hposition
    cases Option.some.inj hselected
    exact hunrevealed
  rw [← hcandidates]
  exact hleftGood.2.2.2.2

theorem probEvent_privateOrdinalSelectionGoodForSomeOutput_le_delayedRootGuess
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (target : Position) (rightRoot : Digest)
    (hroot : IsLayerRoot target) :
    Pr[privateOrdinalSelectionGoodForSomeOutput target rightRoot ordinal |
        granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter table ftsSecret
          fuel] ≤
      Pr[PermissiveDelayedRootGuess target rightRoot ordinal |
        delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
          ftsSecret fuel table] := by
  apply probEvent_le_of_relTriple
    (relTriple_granularAllCanonicalPrivateOrdinalSelection_permissiveDelayed ordinal adversary
      parameter table ftsSecret fuel target rightRoot hroot)
  intro left right hrelation hgood
  exact hrelation.delayedRootGuess hgood

theorem candidates_isPrefix_of_mem_delayedPermissiveDetailedOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (selection : PermissivePrivateOrdinalSelection)
    (hselection : some selection ∈ support
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        candidates state fuel table cache)) :
    candidates.IsPrefix selection.candidates := by
  induction computation using OracleComp.inductionOn generalizing candidates state fuel cache with
  | pure value =>
      simp only [delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_pure] at hselection
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte] at hselection
        simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hselection
        subst selection
        simpa using List.prefix_refl candidates
      · simp [hselected] at hselection
  | query_bind query next ih =>
      rw [delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_query_bind] at hselection
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte] at hselection
        simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hselection
        subst selection
        simpa using List.prefix_refl candidates
      · simp only [hselected, ↓reduceDIte] at hselection
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                rw [mem_support_bind_iff] at hselection
                obtain ⟨result, _hresult, htail⟩ := hselection
                cases result with
                | none => simp [finishPermissiveDetailedPrivateOrdinalSelection] at htail
                | some result =>
                    simp only [finishPermissiveDetailedPrivateOrdinalSelection] at htail
                    exact ih result.value.1 candidates result.state result.remaining result.value.2
                      htail
            | inr input =>
                let nextCandidates :=
                  permissiveRootAwareCandidates parameter input table state candidates
                have hprefix : candidates.IsPrefix nextCandidates := by
                  unfold nextCandidates permissiveRootAwareCandidates
                  cases rootAwareCandidateForPlan? parameter input
                      (permissiveRootAwarePlan parameter input table state) <;>
                    simp [appendPlannedCandidate]
                by_cases hnextSelected : ordinal < nextCandidates.length
                · simp only [nextCandidates, hnextSelected, ↓reduceDIte] at hselection
                  simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hselection
                  subst selection
                  exact hprefix
                · simp only [nextCandidates, hnextSelected, ↓reduceDIte] at hselection
                  rw [mem_support_bind_iff] at hselection
                  obtain ⟨result, _hresult, htail⟩ := hselection
                  cases result with
                  | none => simp [finishPermissiveDetailedPrivateOrdinalSelection] at htail
                  | some result =>
                      simp only [finishPermissiveDetailedPrivateOrdinalSelection] at htail
                      exact hprefix.trans
                        (ih result.value.1 nextCandidates result.state result.remaining
                          result.value.2 htail)
        | inr message =>
            rw [mem_support_bind_iff] at hselection
            obtain ⟨result, _hresult, htail⟩ := hselection
            cases result with
            | none => simp [finishPermissiveDetailedPrivateOrdinalSelection] at htail
            | some result =>
                simp only [finishPermissiveDetailedPrivateOrdinalSelection] at htail
                exact ih result.value.1 candidates result.state result.remaining result.value.2
                  htail

end SphincsSecurity.Concrete.OtsProbeSimulation
