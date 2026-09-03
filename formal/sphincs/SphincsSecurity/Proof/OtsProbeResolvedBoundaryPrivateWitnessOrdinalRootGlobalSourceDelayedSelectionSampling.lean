import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSourceDelayedSelector
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveProductionCommonSelectionSampling
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveProductionCommonization

/-!
# Delayed selector target preloading

Sampling one hidden structural value before the delayed permissive selector does not increase the
selector's fiber at that position. This is the target-independent step that removes the fixed
position after the fresh-output charge has been exposed.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option linter.constructorNameAsVariable false

theorem revealed_subset_of_mem_delayedPermissiveDetailedOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (selection : PermissivePrivateOrdinalSelection)
    (hselection : some selection ∈ support
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        candidates state fuel table cache)) :
    state.revealed ⊆ selection.state.revealed := by
  induction computation using OracleComp.inductionOn generalizing candidates state fuel cache with
  | pure value =>
      simp only [delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_pure] at hselection
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte] at hselection
        simp at hselection
        subst selection
        exact Finset.Subset.rfl
      · simp [hselected] at hselection
  | query_bind query next ih =>
      rw [delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_query_bind] at hselection
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte] at hselection
        simp at hselection
        subst selection
        exact Finset.Subset.rfl
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
                    exact (revealed_subset_of_mem_runPermissiveFromTable
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
                  exact Finset.Subset.rfl
                · simp only [nextCandidates, hnextSelected, ↓reduceDIte] at hselection
                  rw [mem_support_bind_iff] at hselection
                  obtain ⟨result, hresult, htail⟩ := hselection
                  cases result with
                  | none => simp [finishPermissiveDetailedPrivateOrdinalSelection] at htail
                  | some result =>
                      simp only [finishPermissiveDetailedPrivateOrdinalSelection] at htail
                      exact (revealed_subset_of_mem_runPermissiveFromTable
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
                exact (revealed_subset_of_mem_runPermissiveFromTable
                  ((maskedSign parameter root ftsSecret message).run cache)
                  state fuel table result hresult).trans
                  (ih result.value.1 candidates result.state result.remaining result.value.2 htail)

theorem delayedUnrevealedLayerRootPosition_ne_of_initial_revealed
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (target : Position) (htarget : Coordinate.position target ∈ state.revealed)
    (selection : Option PermissivePrivateOrdinalSelection)
    (hselection : selection ∈ support
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        candidates state fuel table cache)) :
    permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection ≠ some target := by
  cases selection with
  | none => simp [permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?]
  | some selection =>
      intro heq
      rw [permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?_eq_some_iff] at heq
      obtain ⟨selected, hselected, _hcandidate, hunrevealed⟩ := heq
      cases hselected
      exact hunrevealed
        (revealed_subset_of_mem_delayedPermissiveDetailedOrdinalSelection ordinal parameter root
          ftsSecret computation candidates state fuel table cache selection hselection htarget)

theorem delayedPermissivePublicAction_preload_hidden
    (target : Position) (output : HashOutput)
    (state : LazyRevealProbe.State Coordinate)
    (hhidden : Coordinate.position target ∉ state.revealed)
    (parameter : PublicParameter) (input : HashInput)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    delayedPermissivePublicAction parameter input table
        (preloadPositionValue target output state) cache =
      delayedPermissivePublicAction parameter input table state cache := by
  unfold delayedPermissivePublicAction
  dsimp only
  have hvalues :=
    materializedCanonicalContext_values_preload_hidden table state target output hhidden
  have hplan := purePlanProbingHashQuery_eq_of_values_eq hvalues parameter input
  rw [hplan]
  exact congrArg (fun computation => computation.run cache)
    (probingHashQueryAfterPublicPlan_eq_of_values_eq parameter input hvalues _)

theorem delayedPermissivePublicAction_targetPeekFree
    (target : Position) (parameter : PublicParameter) (input : HashInput)
    (table : OtsSecretIndex → HashOutput)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) :
    (delayedPermissivePublicAction parameter input table state cache).IsQueryBoundP
      (IsTargetPeek target) 0 := by
  unfold delayedPermissivePublicAction
  apply (show TargetPeekFree target
      (probingHashQueryAfterPublicPlan parameter input
        (materializedCanonicalContext table state).state
        (purePlanProbingHashQuery parameter input
          (materializedCanonicalContext table state).state)) by
    unfold probingHashQueryAfterPublicPlan
    exact (executeCandidate?_targetPeekFree target
        (purePlanProbingHashQuery parameter input
          (materializedCanonicalContext table state).state).candidate?).bind fun _ =>
      probingHashQueryPublicAction_targetPeekFree target parameter input
        (materializedCanonicalContext table state).state
        (purePlanProbingHashQuery parameter input
          (materializedCanonicalContext table state).state).action) cache

theorem permissiveOrdinaryCacheCouples_publicPlan
    (parameter : PublicParameter) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery) :
    PermissiveOrdinaryCacheCouples
      (probingHashQueryAfterPublicPlan parameter input publicState plan) := by
  unfold probingHashQueryAfterPublicPlan
  exact (permissiveOrdinaryCacheCouples_executeCandidate? plan.candidate?).bind fun _ =>
    permissiveOrdinaryCacheCouples_publicAction parameter input publicState plan.action

set_option maxRecDepth 100000 in
theorem relTriple_delayedPermissiveDetailedOrdinalSelection_of_ordinaryCacheEq
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (leftCache rightCache : SplitHashCache)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache) :
    RelTriple
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        candidates state fuel table leftCache)
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        candidates state fuel table rightCache)
      (fun left right => left = right) := by
  induction computation using OracleComp.inductionOn generalizing
      candidates state fuel leftCache rightCache with
  | pure value =>
      simp only [delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_pure]
      by_cases hselected : ordinal < candidates.length <;> simp [hselected]
  | query_bind query next ih =>
      rw [delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_query_bind,
        delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp [hselected]
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                apply relTriple_bind
                  (permissiveOrdinaryCacheCouples_splitUniformImpl n leftCache rightCache hcache
                    state fuel table)
                intro leftResult rightResult hresult
                cases leftResult with
                | none =>
                    cases rightResult with
                    | none => simp [finishPermissiveDetailedPrivateOrdinalSelection]
                    | some rightResult => exact False.elim hresult
                | some leftResult =>
                    cases rightResult with
                    | none => exact False.elim hresult
                    | some rightResult =>
                        rcases hresult with
                          ⟨hstate, hremaining, htable, hvalue, hnextCache⟩
                        simp only [finishPermissiveDetailedPrivateOrdinalSelection]
                        simpa only [hstate, hremaining, hvalue,
                          delayedPermissiveDetailedOrdinalSelection] using
                          ih leftResult.value.1 candidates leftResult.state
                            leftResult.remaining leftResult.value.2 rightResult.value.2 hnextCache
            | inr input =>
                let nextCandidates :=
                  permissiveRootAwareCandidates parameter input table state candidates
                by_cases hnextSelected : ordinal < nextCandidates.length
                · simp [nextCandidates, hnextSelected]
                · simp only [nextCandidates, hnextSelected, ↓reduceDIte]
                  have haction :=
                    permissiveOrdinaryCacheCouples_publicPlan parameter input
                      (materializedCanonicalContext table state).state
                      (purePlanProbingHashQuery parameter input
                        (materializedCanonicalContext table state).state)
                      leftCache rightCache hcache state fuel table
                  apply relTriple_bind (by
                    simpa only [delayedPermissivePublicAction] using haction)
                  intro leftResult rightResult hresult
                  cases leftResult with
                  | none =>
                      cases rightResult with
                      | none => simp [finishPermissiveDetailedPrivateOrdinalSelection]
                      | some rightResult => exact False.elim hresult
                  | some leftResult =>
                      cases rightResult with
                      | none => exact False.elim hresult
                      | some rightResult =>
                          rcases hresult with
                            ⟨hstate, hremaining, htable, hvalue, hnextCache⟩
                          simp only [finishPermissiveDetailedPrivateOrdinalSelection]
                          simpa only [hstate, hremaining, hvalue,
                            delayedPermissiveDetailedOrdinalSelection] using
                            ih leftResult.value.1 nextCandidates leftResult.state
                              leftResult.remaining leftResult.value.2 rightResult.value.2 hnextCache
        | inr message =>
            apply relTriple_bind
              (permissiveOrdinaryCacheCouples_maskedSign parameter root ftsSecret message
                leftCache rightCache hcache state fuel table)
            intro leftResult rightResult hresult
            cases leftResult with
            | none =>
                cases rightResult with
                | none => simp [finishPermissiveDetailedPrivateOrdinalSelection]
                | some rightResult => exact False.elim hresult
            | some leftResult =>
                cases rightResult with
                | none => exact False.elim hresult
                | some rightResult =>
                    rcases hresult with ⟨hstate, hremaining, htable, hvalue, hnextCache⟩
                    simp only [finishPermissiveDetailedPrivateOrdinalSelection]
                    simpa only [hstate, hremaining, hvalue,
                      delayedPermissiveDetailedOrdinalSelection] using
                      ih leftResult.value.1 candidates leftResult.state leftResult.remaining
                        leftResult.value.2 rightResult.value.2 hnextCache

theorem relTriple_delayedPermissiveDetailedOrdinalSelection_targetFiber_of_stateRel
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (left right : LazyRevealProbe.State Coordinate)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (target : Position) (hstate : PermissiveStateRel left right) :
    RelTriple
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        candidates left fuel table cache)
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        candidates right fuel table cache)
      (PermissiveTargetFiberRel target) := by
  apply relTriple_post_mono
    (relTriple_delayedPermissiveDetailedOrdinalSelection_of_stateRel ordinal parameter root
      ftsSecret computation candidates candidates left right fuel table cache rfl hstate)
  intro leftSelection rightSelection hselection hleft
  rw [hselection.positionFiber_eq] at hleft
  exact hleft

noncomputable def permissivePrivateOrdinalSelectionTargetProbe?
    (target : Position) : Option PermissivePrivateOrdinalSelection → Option Probe
  | none => none
  | some selection =>
      if permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? (some selection) =
          some target then
        some selection.candidate
      else
        none

def PermissiveTargetProbeRel (target : Position) :
    Option PermissivePrivateOrdinalSelection →
      Option PermissivePrivateOrdinalSelection → Prop :=
  fun left right =>
    permissivePrivateOrdinalSelectionTargetProbe? target left =
      permissivePrivateOrdinalSelectionTargetProbe? target right

def PermissiveTargetGuess (target : Position) :
    Option PermissivePrivateOrdinalSelection → Prop
  | none => False
  | some selection => ∃ output,
      permissivePrivateOrdinalSelectionTargetProbe? target (some selection) =
        some selection.candidate ∧
      selection.state.values (.position target) = some output ∧
      selection.candidate.candidate = truncateHash output

theorem DelayedPermissiveSelectionRel.targetGuess
    {target : Position} {rightRoot : Digest} {ordinal : Nat}
    {left : Option PrivateOrdinalSelection}
    {right : Option PermissivePrivateOrdinalSelection}
    (hrel : DelayedPermissiveSelectionRel target rightRoot ordinal left right)
    (hgood : privateOrdinalSelectionGoodForSomeOutput target rightRoot ordinal left) :
    PermissiveTargetGuess target right := by
  obtain ⟨leftOutput, leftSelection, rightSelection, hleft, hright, hleftGood, hcandidate,
    hposition, hvalue⟩ := hrel hgood
  rw [hright]
  refine ⟨leftOutput, ?_, hvalue, ?_⟩
  · simp only [permissivePrivateOrdinalSelectionTargetProbe?]
    rw [if_pos hposition]
  · rw [← hcandidate]
    exact congrArg Probe.candidate hleftGood.1

theorem PermissiveDetailedSelectionRel.targetGuess_iff
    {target : Position} {left right : Option PermissivePrivateOrdinalSelection}
    (hrel : PermissiveDetailedSelectionRel left right) :
    PermissiveTargetGuess target left ↔ PermissiveTargetGuess target right := by
  cases left with
  | none =>
      cases right with
      | none => simp [PermissiveTargetGuess]
      | some right => exact False.elim hrel
  | some left =>
      cases right with
      | none => exact False.elim hrel
      | some right =>
          rcases hrel with ⟨hcandidate, _hcandidates, hstate⟩
          have hprobe : permissivePrivateOrdinalSelectionTargetProbe? target (some left) =
              permissivePrivateOrdinalSelectionTargetProbe? target (some right) := by
            have hposition :=
              (show PermissiveDetailedSelectionRel (some left) (some right) from
                ⟨hcandidate, _hcandidates, hstate⟩).positionFiber_eq
            simp only [permissivePrivateOrdinalSelectionTargetProbe?]
            rw [hposition, hcandidate]
          constructor
          · rintro ⟨output, htarget, hvalue, hdigest⟩
            refine ⟨output, ?_, ?_, ?_⟩
            · rw [← hprobe]
              simpa [hcandidate] using htarget
            · rw [← hstate.values]
              exact hvalue
            · rw [← hcandidate]
              exact hdigest
          · rintro ⟨output, htarget, hvalue, hdigest⟩
            refine ⟨output, ?_, ?_, ?_⟩
            · rw [hprobe]
              simpa [hcandidate] using htarget
            · rw [hstate.values]
              exact hvalue
            · rw [hcandidate]
              exact hdigest

theorem DelayedPermissiveSelectionRel.targetProbe_eq
    {target : Position} {leftOutput : HashOutput} {rightRoot : Digest} {ordinal : Nat}
    {left : PrivateOrdinalSelection}
    {right : Option PermissivePrivateOrdinalSelection}
    (hrel : DelayedPermissiveSelectionRel target rightRoot ordinal (some left) right)
    (hgood : left.GoodForRoots target leftOutput rightRoot ordinal) :
    permissivePrivateOrdinalSelectionTargetProbe? target right = some left.candidate := by
  obtain ⟨_output, leftSelection, rightSelection, hleft, hright, _hgood, hcandidate, hposition⟩ :=
    hrel ⟨leftOutput, hgood⟩
  cases Option.some.inj hleft
  rw [hright]
  simp only [permissivePrivateOrdinalSelectionTargetProbe?]
  rw [if_pos hposition.1, hcandidate]

theorem PermissiveDetailedSelectionRel.targetProbe_eq
    {target : Position} {left right : Option PermissivePrivateOrdinalSelection}
    (hrel : PermissiveDetailedSelectionRel left right) :
    PermissiveTargetProbeRel target left right := by
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some right => exact False.elim hrel
  | some left =>
      cases right with
      | none => exact False.elim hrel
      | some right =>
          have hposition := hrel.positionFiber_eq
          rcases hrel with ⟨hcandidate, _hcandidates, hstate⟩
          unfold PermissiveTargetProbeRel
          simp only [permissivePrivateOrdinalSelectionTargetProbe?]
          rw [hposition, hcandidate]

theorem relTriple_delayedPermissiveDetailedOrdinalSelection_targetProbe_of_stateRel
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (left right : LazyRevealProbe.State Coordinate)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (target : Position) (hstate : PermissiveStateRel left right) :
    RelTriple
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        candidates left fuel table cache)
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        candidates right fuel table cache)
      (PermissiveTargetProbeRel target) := by
  apply relTriple_post_mono
    (relTriple_delayedPermissiveDetailedOrdinalSelection_of_stateRel ordinal parameter root
      ftsSecret computation candidates candidates left right fuel table cache rfl hstate)
  intro leftSelection rightSelection hselection
  exact hselection.targetProbe_eq

theorem permissivePrivateOrdinalSelectionTargetProbe?_eq_none_of_position_ne
    (target : Position) (selection : Option PermissivePrivateOrdinalSelection)
    (hne : permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection ≠
      some target) :
    permissivePrivateOrdinalSelectionTargetProbe? target selection = none := by
  cases selection with
  | none => rfl
  | some selection =>
      simp [permissivePrivateOrdinalSelectionTargetProbe?, hne]

theorem permissiveTargetProbeRel_preload_sameSelection
    (target : Position) (candidate : Probe) (candidates : List Probe)
    (state : LazyRevealProbe.State Coordinate) (output : HashOutput) :
    PermissiveTargetProbeRel target
      (some ⟨candidate, preloadPositionValue target output state, candidates⟩)
      (some ⟨candidate, state, candidates⟩) := by
  unfold PermissiveTargetProbeRel permissivePrivateOrdinalSelectionTargetProbe?
  have hposition :
      permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?
          (some ⟨candidate, preloadPositionValue target output state, candidates⟩) =
        permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?
          (some ⟨candidate, state, candidates⟩) := by
    simp only [permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?]
    rw [preloadPositionValue_revealed]
  change (if permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?
        (some ⟨candidate, preloadPositionValue target output state, candidates⟩) = some target then
      some candidate else none) =
    (if permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?
        (some ⟨candidate, state, candidates⟩) = some target then some candidate else none)
  rw [hposition]

theorem relTriple_sample_preload_pureSelection_targetProbe
    (target : Position) (candidate : Probe) (candidates : List Probe)
    (state : LazyRevealProbe.State Coordinate) :
    RelTriple
      (LazyRevealProbe.sampleHashOutput >>= fun output =>
        pure (some ⟨candidate, preloadPositionValue target output state, candidates⟩))
      (pure (some ⟨candidate, state, candidates⟩) :
        ProbComp (Option PermissivePrivateOrdinalSelection))
      (PermissiveTargetProbeRel target) := by
  rw [show (pure (some ⟨candidate, state, candidates⟩) :
      ProbComp (Option PermissivePrivateOrdinalSelection)) =
        (pure () >>= fun _ => pure (some ⟨candidate, state, candidates⟩)) by simp]
  apply relTriple_bind
    (relTriple_true LazyRevealProbe.sampleHashOutput (pure () : ProbComp Unit))
  intro output _ _
  exact relTriple_pure_pure
    (permissiveTargetProbeRel_preload_sameSelection target candidate candidates state output)

theorem relTriple_sample_preload_runPermissive_finishDetailed_targetProbe
    (target : Position)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) (α × SplitHashCache))
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (leftObserve rightObserve : LazyRevealProbe.State Coordinate → Nat → α →
      SplitHashCache → List Probe →
        ProbComp (Option PermissivePrivateOrdinalSelection))
    (candidates : List Probe)
    (hvalue : state.values (.position target) = none)
    (hnoPeek : computation.IsQueryBoundP (IsTargetPeek target) 0)
    (hpreloaded : ∀ nextState remaining value nextCache,
      nextState.values (.position target) = none →
      RelTriple
        (LazyRevealProbe.sampleHashOutput >>= fun output =>
          leftObserve (preloadPositionValue target output nextState) remaining value nextCache
            candidates)
        (rightObserve nextState remaining value nextCache candidates)
        (PermissiveTargetProbeRel target))
    (hsynchronized : ∀ left right remaining value cache,
      PermissiveStateRel left right →
      RelTriple
        (leftObserve left remaining value cache candidates)
        (rightObserve right remaining value cache candidates)
        (PermissiveTargetProbeRel target)) :
    RelTriple
      (LazyRevealProbe.sampleHashOutput >>= fun output =>
        runPermissiveFromTable (preloadPositionValue target output state) fuel table computation >>=
          finishPermissiveDetailedPrivateOrdinalSelection leftObserve candidates)
      (runPermissiveFromTable state fuel table computation >>=
        finishPermissiveDetailedPrivateOrdinalSelection rightObserve candidates)
      (PermissiveTargetProbeRel target) := by
  apply relTriple_sample_preload_runPermissiveFromTable_then target computation state fuel table
    (finishPermissiveDetailedPrivateOrdinalSelection leftObserve candidates)
    (finishPermissiveDetailedPrivateOrdinalSelection rightObserve candidates)
    (PermissiveTargetProbeRel target) hvalue hnoPeek
  · intro nextState remaining result nextTable hnextValue
    rcases result with ⟨value, nextCache⟩
    simp only [finishPermissiveDetailedPrivateOrdinalSelection]
    exact hpreloaded nextState remaining value nextCache hnextValue
  · intro left right hresult
    cases left with
    | none =>
        cases right with
        | none => simp [finishPermissiveDetailedPrivateOrdinalSelection,
            PermissiveTargetProbeRel]
        | some right => exact False.elim hresult
    | some left =>
        cases right with
        | none => exact False.elim hresult
        | some right =>
            rcases hresult with ⟨hstate, hremaining, hvalue, htable⟩
            have hvalueEq := congrArg Prod.fst hvalue
            have hcacheEq := congrArg Prod.snd hvalue
            simp only [finishPermissiveDetailedPrivateOrdinalSelection]
            rw [← hremaining, ← hvalueEq, ← hcacheEq]
            exact hsynchronized left.state right.state left.remaining left.value.1
              left.value.2 hstate

theorem relTriple_sample_preload_delayedSelector_targetProbe_of_initial_revealed
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (target : Position) (hrevealed : Coordinate.position target ∈ state.revealed) :
    RelTriple
      (LazyRevealProbe.sampleHashOutput >>= fun output =>
        delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
          candidates (preloadPositionValue target output state) fuel table cache)
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        candidates state fuel table cache)
      (PermissiveTargetProbeRel target) := by
  have hbase := relTriple_true
    (LazyRevealProbe.sampleHashOutput >>= fun output =>
      delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        candidates (preloadPositionValue target output state) fuel table cache)
    (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
      candidates state fuel table cache)
  have hleft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun selection =>
        permissivePrivateOrdinalSelectionTargetProbe? target selection = none)
      (by
        intro selection hselection
        rw [mem_support_bind_iff] at hselection
        obtain ⟨output, _houtput, htail⟩ := hselection
        apply permissivePrivateOrdinalSelectionTargetProbe?_eq_none_of_position_ne
        exact delayedUnrevealedLayerRootPosition_ne_of_initial_revealed ordinal parameter root
          ftsSecret computation candidates (preloadPositionValue target output state) fuel table
          cache target (by simpa using hrevealed) selection htail)
  have hboth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
  apply relTriple_post_mono hboth
  intro left right hrelation
  rcases hrelation with ⟨⟨_relation, hleftNone⟩, hrightSupport⟩
  have hrightNone : permissivePrivateOrdinalSelectionTargetProbe? target right = none := by
    apply permissivePrivateOrdinalSelectionTargetProbe?_eq_none_of_position_ne
    exact delayedUnrevealedLayerRootPosition_ne_of_initial_revealed ordinal parameter root
      ftsSecret computation candidates state fuel table cache target hrevealed right hrightSupport
  unfold PermissiveTargetProbeRel
  rw [hleftNone, hrightNone]

theorem relTriple_sample_preload_delayedSelector_targetFiber_of_initial_revealed
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (target : Position) (hrevealed : Coordinate.position target ∈ state.revealed) :
    RelTriple
      (LazyRevealProbe.sampleHashOutput >>= fun output =>
        delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
          candidates (preloadPositionValue target output state) fuel table cache)
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        candidates state fuel table cache)
      (PermissiveTargetFiberRel target) := by
  have hbase := relTriple_true
    (LazyRevealProbe.sampleHashOutput >>= fun output =>
      delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        candidates (preloadPositionValue target output state) fuel table cache)
    (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
      candidates state fuel table cache)
  have hleft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun selection =>
        permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection ≠ some target)
      (by
        intro selection hselection
        rw [mem_support_bind_iff] at hselection
        obtain ⟨output, _houtput, htail⟩ := hselection
        exact delayedUnrevealedLayerRootPosition_ne_of_initial_revealed ordinal parameter root
          ftsSecret computation candidates (preloadPositionValue target output state) fuel table
          cache target (by simpa using hrevealed) selection htail)
  apply relTriple_post_mono hleft
  intro left right hrelation hfiber
  exact False.elim (hrelation.2 hfiber)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_sample_preload_delayedPermissiveDetailedOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (target : Position) (hvalue : state.values (.position target) = none) :
    RelTriple
      (LazyRevealProbe.sampleHashOutput >>= fun output =>
        delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
          candidates (preloadPositionValue target output state) fuel table cache)
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        candidates state fuel table cache)
      (PermissiveTargetFiberRel target) := by
  induction computation using OracleComp.inductionOn generalizing candidates state fuel cache with
  | pure value =>
      by_cases hrevealed : Coordinate.position target ∈ state.revealed
      · exact relTriple_sample_preload_delayedSelector_targetFiber_of_initial_revealed ordinal
          parameter root ftsSecret (pure value) candidates state fuel table cache target hrevealed
      · simp only [delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_pure]
        by_cases hselected : ordinal < candidates.length
        · simp only [hselected, ↓reduceDIte]
          exact relTriple_sample_preload_pureSelection_targetFiber target
            (candidates.get ⟨ordinal, hselected⟩) candidates state
        · simp only [hselected, ↓reduceDIte]
          apply relTriple_of_evalDist_eq_left
            (OracleComp.DeferredSampling.evalDist_bind_const_neverFails
              LazyRevealProbe.sampleHashOutput (by
                simp [LazyRevealProbe.sampleHashOutput]) (pure none))
          exact relTriple_pure_pure (by simp [PermissiveTargetFiberRel])
  | query_bind query next ih =>
      by_cases hrevealed : Coordinate.position target ∈ state.revealed
      · exact relTriple_sample_preload_delayedSelector_targetFiber_of_initial_revealed ordinal
          parameter root ftsSecret (liftM (OracleSpec.query query) >>= next) candidates state fuel
          table cache target hrevealed
      · simp_rw [delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_query_bind]
        by_cases hselected : ordinal < candidates.length
        · simp only [hselected, ↓reduceDIte]
          exact relTriple_sample_preload_pureSelection_targetFiber target
            (candidates.get ⟨ordinal, hselected⟩) candidates state
        · simp only [hselected, ↓reduceDIte]
          cases query with
          | inl worldQuery =>
              cases worldQuery with
              | inl n =>
                  let observe : LazyRevealProbe.State Coordinate → Nat → Fin (n + 1) →
                      SplitHashCache → List Probe →
                        ProbComp (Option PermissivePrivateOrdinalSelection) :=
                    fun nextState remaining output nextCache laterCandidates =>
                      delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret
                        (next output) laterCandidates nextState remaining table nextCache
                  apply relTriple_sample_preload_runPermissive_finishDetailed target
                    ((splitUniformImpl n).run cache) state fuel table observe observe candidates
                    hvalue (splitUniformImpl_targetPeekFree target n cache)
                  · intro nextState remaining output nextCache hnextValue
                    simpa only [observe] using
                      ih output candidates nextState remaining nextCache hnextValue
                  · intro left right remaining output nextCache hstate
                    exact
                      relTriple_delayedPermissiveDetailedOrdinalSelection_targetFiber_of_stateRel
                        ordinal parameter root ftsSecret (next output) candidates left right
                        remaining table nextCache target hstate
              | inr input =>
                  let nextCandidates :=
                    permissiveRootAwareCandidates parameter input table state candidates
                  by_cases hnextSelected : ordinal < nextCandidates.length
                  · simp only [nextCandidates, hnextSelected, ↓reduceDIte]
                    rw [show (pure (some
                        ⟨(permissiveRootAwareCandidates parameter input table state candidates).get
                            ⟨ordinal, hnextSelected⟩,
                          state,
                          permissiveRootAwareCandidates parameter input table state candidates⟩) :
                        ProbComp (Option PermissivePrivateOrdinalSelection)) =
                      (pure () >>= fun _ => pure (some
                        ⟨(permissiveRootAwareCandidates parameter input table state candidates).get
                            ⟨ordinal, hnextSelected⟩,
                          state,
                          permissiveRootAwareCandidates parameter input table state candidates⟩)) by simp]
                    apply relTriple_bind
                      (relTriple_true LazyRevealProbe.sampleHashOutput (pure () : ProbComp Unit))
                    intro output _ _
                    rw [permissiveRootAwareCandidates_preload_hidden target output state hrevealed
                      parameter input table candidates]
                    have hnextSelected' : ordinal <
                        (permissiveRootAwareCandidates parameter input table state candidates).length :=
                      hnextSelected
                    rw [dif_pos hnextSelected']
                    exact relTriple_pure_pure
                      (permissiveTargetFiberRel_preload_sameSelection target
                        ((permissiveRootAwareCandidates parameter input table state candidates).get
                          ⟨ordinal, hnextSelected⟩)
                        (permissiveRootAwareCandidates parameter input table state candidates)
                        state output)
                  · simp_rw [permissiveRootAwareCandidates_preload_hidden target _ state hrevealed
                      parameter input table candidates]
                    simp only [nextCandidates, hnextSelected, ↓reduceDIte]
                    simp_rw [delayedPermissivePublicAction_preload_hidden target _ state hrevealed
                      parameter input table cache]
                    let observe : LazyRevealProbe.State Coordinate → Nat → HashOutput →
                        SplitHashCache → List Probe →
                          ProbComp (Option PermissivePrivateOrdinalSelection) :=
                      fun nextState remaining output nextCache laterCandidates =>
                        delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret
                          (next output) laterCandidates nextState remaining table nextCache
                    apply relTriple_sample_preload_runPermissive_finishDetailed target
                      (delayedPermissivePublicAction parameter input table state cache)
                      state fuel table observe observe nextCandidates hvalue
                      (delayedPermissivePublicAction_targetPeekFree target parameter input table
                        state cache)
                    · intro nextState remaining output nextCache hnextValue
                      simpa only [observe] using
                        ih output nextCandidates nextState remaining nextCache hnextValue
                    · intro left right remaining output nextCache hstate
                      exact
                        relTriple_delayedPermissiveDetailedOrdinalSelection_targetFiber_of_stateRel
                          ordinal parameter root ftsSecret (next output) nextCandidates left right
                          remaining table nextCache target hstate
          | inr message =>
              let observe : LazyRevealProbe.State Coordinate → Nat → Option Signature →
                  SplitHashCache → List Probe →
                    ProbComp (Option PermissivePrivateOrdinalSelection) :=
                fun nextState remaining output nextCache laterCandidates =>
                  delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret
                    (next output) laterCandidates nextState remaining table nextCache
              apply relTriple_sample_preload_runPermissive_finishDetailed target
                ((maskedSign parameter root ftsSecret message).run cache) state fuel table
                observe observe candidates hvalue
                (maskedSign_targetPeekFree target parameter root ftsSecret message cache)
              · intro nextState remaining output nextCache hnextValue
                simpa only [observe] using
                  ih output candidates nextState remaining nextCache hnextValue
              · intro left right remaining output nextCache hstate
                exact
                  relTriple_delayedPermissiveDetailedOrdinalSelection_targetFiber_of_stateRel
                    ordinal parameter root ftsSecret (next output) candidates left right remaining
                    table nextCache target hstate

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_sample_preload_delayedPermissiveDetailedOrdinalSelection_targetProbe
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (target : Position) (hvalue : state.values (.position target) = none) :
    RelTriple
      (LazyRevealProbe.sampleHashOutput >>= fun output =>
        delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
          candidates (preloadPositionValue target output state) fuel table cache)
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        candidates state fuel table cache)
      (PermissiveTargetProbeRel target) := by
  induction computation using OracleComp.inductionOn generalizing candidates state fuel cache with
  | pure value =>
      by_cases hrevealed : Coordinate.position target ∈ state.revealed
      · exact relTriple_sample_preload_delayedSelector_targetProbe_of_initial_revealed ordinal
          parameter root ftsSecret (pure value) candidates state fuel table cache target hrevealed
      · simp only [delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_pure]
        by_cases hselected : ordinal < candidates.length
        · simp only [hselected, ↓reduceDIte]
          exact relTriple_sample_preload_pureSelection_targetProbe target
            (candidates.get ⟨ordinal, hselected⟩) candidates state
        · simp only [hselected, ↓reduceDIte]
          apply relTriple_of_evalDist_eq_left
            (OracleComp.DeferredSampling.evalDist_bind_const_neverFails
              LazyRevealProbe.sampleHashOutput (by
                simp [LazyRevealProbe.sampleHashOutput]) (pure none))
          exact relTriple_pure_pure (by simp [PermissiveTargetProbeRel])
  | query_bind query next ih =>
      by_cases hrevealed : Coordinate.position target ∈ state.revealed
      · exact relTriple_sample_preload_delayedSelector_targetProbe_of_initial_revealed ordinal
          parameter root ftsSecret (liftM (OracleSpec.query query) >>= next) candidates state fuel
          table cache target hrevealed
      · simp_rw [delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_query_bind]
        by_cases hselected : ordinal < candidates.length
        · simp only [hselected, ↓reduceDIte]
          exact relTriple_sample_preload_pureSelection_targetProbe target
            (candidates.get ⟨ordinal, hselected⟩) candidates state
        · simp only [hselected, ↓reduceDIte]
          cases query with
          | inl worldQuery =>
              cases worldQuery with
              | inl n =>
                  let observe : LazyRevealProbe.State Coordinate → Nat → Fin (n + 1) →
                      SplitHashCache → List Probe →
                        ProbComp (Option PermissivePrivateOrdinalSelection) :=
                    fun nextState remaining output nextCache laterCandidates =>
                      delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret
                        (next output) laterCandidates nextState remaining table nextCache
                  apply relTriple_sample_preload_runPermissive_finishDetailed_targetProbe target
                    ((splitUniformImpl n).run cache) state fuel table observe observe candidates
                    hvalue (splitUniformImpl_targetPeekFree target n cache)
                  · intro nextState remaining output nextCache hnextValue
                    simpa only [observe] using
                      ih output candidates nextState remaining nextCache hnextValue
                  · intro left right remaining output nextCache hstate
                    exact
                      relTriple_delayedPermissiveDetailedOrdinalSelection_targetProbe_of_stateRel
                        ordinal parameter root ftsSecret (next output) candidates left right
                        remaining table nextCache target hstate
              | inr input =>
                  let nextCandidates :=
                    permissiveRootAwareCandidates parameter input table state candidates
                  by_cases hnextSelected : ordinal < nextCandidates.length
                  · simp only [nextCandidates, hnextSelected, ↓reduceDIte]
                    rw [show (pure (some
                        ⟨(permissiveRootAwareCandidates parameter input table state candidates).get
                            ⟨ordinal, hnextSelected⟩,
                          state,
                          permissiveRootAwareCandidates parameter input table state candidates⟩) :
                        ProbComp (Option PermissivePrivateOrdinalSelection)) =
                      (pure () >>= fun _ => pure (some
                        ⟨(permissiveRootAwareCandidates parameter input table state candidates).get
                            ⟨ordinal, hnextSelected⟩,
                          state,
                          permissiveRootAwareCandidates parameter input table state candidates⟩)) by simp]
                    apply relTriple_bind
                      (relTriple_true LazyRevealProbe.sampleHashOutput (pure () : ProbComp Unit))
                    intro output _ _
                    rw [permissiveRootAwareCandidates_preload_hidden target output state hrevealed
                      parameter input table candidates]
                    have hnextSelected' : ordinal <
                        (permissiveRootAwareCandidates parameter input table state candidates).length :=
                      hnextSelected
                    rw [dif_pos hnextSelected']
                    exact relTriple_pure_pure
                      (permissiveTargetProbeRel_preload_sameSelection target
                        ((permissiveRootAwareCandidates parameter input table state candidates).get
                          ⟨ordinal, hnextSelected⟩)
                        (permissiveRootAwareCandidates parameter input table state candidates)
                        state output)
                  · simp_rw [permissiveRootAwareCandidates_preload_hidden target _ state hrevealed
                      parameter input table candidates]
                    simp only [nextCandidates, hnextSelected, ↓reduceDIte]
                    simp_rw [delayedPermissivePublicAction_preload_hidden target _ state hrevealed
                      parameter input table cache]
                    let observe : LazyRevealProbe.State Coordinate → Nat → HashOutput →
                        SplitHashCache → List Probe →
                          ProbComp (Option PermissivePrivateOrdinalSelection) :=
                      fun nextState remaining output nextCache laterCandidates =>
                        delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret
                          (next output) laterCandidates nextState remaining table nextCache
                    apply relTriple_sample_preload_runPermissive_finishDetailed_targetProbe target
                      (delayedPermissivePublicAction parameter input table state cache)
                      state fuel table observe observe nextCandidates hvalue
                      (delayedPermissivePublicAction_targetPeekFree target parameter input table
                        state cache)
                    · intro nextState remaining output nextCache hnextValue
                      simpa only [observe] using
                        ih output nextCandidates nextState remaining nextCache hnextValue
                    · intro left right remaining output nextCache hstate
                      exact
                        relTriple_delayedPermissiveDetailedOrdinalSelection_targetProbe_of_stateRel
                          ordinal parameter root ftsSecret (next output) nextCandidates left right
                          remaining table nextCache target hstate
          | inr message =>
              let observe : LazyRevealProbe.State Coordinate → Nat → Option Signature →
                  SplitHashCache → List Probe →
                    ProbComp (Option PermissivePrivateOrdinalSelection) :=
                fun nextState remaining output nextCache laterCandidates =>
                  delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret
                    (next output) laterCandidates nextState remaining table nextCache
              apply relTriple_sample_preload_runPermissive_finishDetailed_targetProbe target
                ((maskedSign parameter root ftsSecret message).run cache) state fuel table
                observe observe candidates hvalue
                (maskedSign_targetPeekFree target parameter root ftsSecret message cache)
              · intro nextState remaining output nextCache hnextValue
                simpa only [observe] using
                  ih output candidates nextState remaining nextCache hnextValue
              · intro left right remaining output nextCache hstate
                exact
                  relTriple_delayedPermissiveDetailedOrdinalSelection_targetProbe_of_stateRel
                    ordinal parameter root ftsSecret (next output) candidates left right remaining
                    table nextCache target hstate

noncomputable def preloadedDelayedPermissiveDetailedSelectionAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    ProbComp (Option PermissivePrivateOrdinalSelection) := do
  let output ← LazyRevealProbe.sampleHashOutput
  delayedPermissiveDetailedOrdinalSelection ordinal parameter rootResult.value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
    (preloadPositionValue target output rootResult.state) rootResult.remaining rootResult.table
    rootResult.value.2

noncomputable def installedDelayedPermissiveDetailedSelectionAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    ProbComp (Option PermissivePrivateOrdinalSelection) := do
  let output ← LazyRevealProbe.sampleHashOutput
  delayedPermissiveDetailedOrdinalSelection ordinal parameter rootResult.value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
    (preloadPositionValue target output rootResult.state) rootResult.remaining rootResult.table
    (replaceHiddenRootCache target output rootResult.value.2)

theorem relTriple_installedDelayedSelection_preloaded_afterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    RelTriple
      (installedDelayedPermissiveDetailedSelectionAfterRootResult ordinal adversary parameter
        ftsSecret target rootResult)
      (preloadedDelayedPermissiveDetailedSelectionAfterRootResult ordinal adversary parameter
        ftsSecret target rootResult)
      (fun left right => left = right) := by
  unfold installedDelayedPermissiveDetailedSelectionAfterRootResult
    preloadedDelayedPermissiveDetailedSelectionAfterRootResult
  apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
  intro leftOutput rightOutput heq
  subst rightOutput
  exact relTriple_delayedPermissiveDetailedOrdinalSelection_of_ordinaryCacheEq ordinal parameter
    rootResult.value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
    (preloadPositionValue target leftOutput rootResult.state) rootResult.remaining rootResult.table
    (replaceHiddenRootCache target leftOutput rootResult.value.2) rootResult.value.2
    (ordinaryQueryCache_replaceHiddenRootCache target leftOutput rootResult.value.2)

theorem relTriple_preloadedDelayedSelection_common_afterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache))
    (hvalue : rootResult.state.values (.position target) = none) :
    RelTriple
      (preloadedDelayedPermissiveDetailedSelectionAfterRootResult ordinal adversary parameter
        ftsSecret target rootResult)
      (delayedPermissiveDetailedSelectionAfterRootResult ordinal adversary parameter ftsSecret
        rootResult)
      (PermissiveTargetFiberRel target) := by
  unfold preloadedDelayedPermissiveDetailedSelectionAfterRootResult
    delayedPermissiveDetailedSelectionAfterRootResult
  exact relTriple_sample_preload_delayedPermissiveDetailedOrdinalSelection ordinal parameter
    rootResult.value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) [] rootResult.state
    rootResult.remaining rootResult.table rootResult.value.2 target hvalue

theorem relTriple_preloadedDelayedSelection_common_targetProbe_afterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache))
    (hvalue : rootResult.state.values (.position target) = none) :
    RelTriple
      (preloadedDelayedPermissiveDetailedSelectionAfterRootResult ordinal adversary parameter
        ftsSecret target rootResult)
      (delayedPermissiveDetailedSelectionAfterRootResult ordinal adversary parameter ftsSecret
        rootResult)
      (PermissiveTargetProbeRel target) := by
  unfold preloadedDelayedPermissiveDetailedSelectionAfterRootResult
    delayedPermissiveDetailedSelectionAfterRootResult
  exact relTriple_sample_preload_delayedPermissiveDetailedOrdinalSelection_targetProbe ordinal
    parameter rootResult.value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) [] rootResult.state
    rootResult.remaining rootResult.table rootResult.value.2 target hvalue

theorem relTriple_installedDelayedSelection_common_targetProbe_afterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache))
    (hvalue : rootResult.state.values (.position target) = none) :
    RelTriple
      (installedDelayedPermissiveDetailedSelectionAfterRootResult ordinal adversary parameter
        ftsSecret target rootResult)
      (delayedPermissiveDetailedSelectionAfterRootResult ordinal adversary parameter ftsSecret
        rootResult)
      (PermissiveTargetProbeRel target) := by
  have hglued := SphincsSecurity.relTriple_trans_exists
    (relTriple_installedDelayedSelection_preloaded_afterRootResult ordinal adversary parameter
      ftsSecret target rootResult)
    (relTriple_preloadedDelayedSelection_common_targetProbe_afterRootResult ordinal adversary
      parameter ftsSecret target rootResult hvalue)
  apply relTriple_post_mono hglued
  intro left right hrelation
  obtain ⟨middle, hleft, hright⟩ := hrelation
  subst middle
  exact hright

noncomputable def preloadedDelayedPermissiveDetailedSelectionExperimentAfterTable
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    ProbComp (Option PermissivePrivateOrdinalSelection) := do
  let rootResult ← rootAwareProductionInitialRun fuel table
  match rootResult with
  | none => pure none
  | some result =>
      preloadedDelayedPermissiveDetailedSelectionAfterRootResult ordinal adversary parameter
        ftsSecret target result

noncomputable def installedDelayedPermissiveDetailedSelectionExperimentAfterTable
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    ProbComp (Option PermissivePrivateOrdinalSelection) := do
  let rootResult ← rootAwareProductionInitialRun fuel table
  match rootResult with
  | none => pure none
  | some result =>
      installedDelayedPermissiveDetailedSelectionAfterRootResult ordinal adversary parameter
        ftsSecret target result

set_option maxRecDepth 100000 in
theorem relTriple_installedDelayedSelection_common_targetProbe_afterTable
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    RelTriple
      (installedDelayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary
        parameter ftsSecret target fuel table)
      (delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
        ftsSecret fuel table)
      (PermissiveTargetProbeRel target) := by
  unfold installedDelayedPermissiveDetailedSelectionExperimentAfterTable
    delayedPermissiveDetailedSelectionExperimentAfterTable
  let initial := rootAwareProductionInitialRun fuel table
  have hbase := relTriple_refl initial
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (InitialRootOptionFacts target)
      (initialRootOptionFacts_of_mem target hroot hparent fuel table)
  apply relTriple_bind hsupported
  intro leftResult rightResult hrelation
  rcases hrelation with ⟨heq, hinitial⟩
  subst rightResult
  cases leftResult with
  | none => exact relTriple_pure_pure rfl
  | some rootResult =>
      exact relTriple_installedDelayedSelection_common_targetProbe_afterRootResult ordinal
        adversary parameter ftsSecret target rootResult hinitial.1

set_option maxRecDepth 100000 in
theorem evalDist_installedDelayedSelection_common_targetProbe_afterTable
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    evalDist
        (permissivePrivateOrdinalSelectionTargetProbe? target <$>
          installedDelayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary
            parameter ftsSecret target fuel table) =
      evalDist
        (permissivePrivateOrdinalSelectionTargetProbe? target <$>
          delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
            ftsSecret fuel table) := by
  have hrel := relTriple_installedDelayedSelection_common_targetProbe_afterTable ordinal adversary
    parameter ftsSecret target hroot hparent fuel table
  have hmapped : RelTriple
      (permissivePrivateOrdinalSelectionTargetProbe? target <$>
        installedDelayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary
          parameter ftsSecret target fuel table)
      (permissivePrivateOrdinalSelectionTargetProbe? target <$>
        delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
          ftsSecret fuel table)
      (fun left right => left = right) :=
    relTriple_map hrel
  exact evalDist_eq_of_relTriple_eqRel hmapped

set_option maxRecDepth 100000 in
theorem probEvent_preloadedDelayedSelection_fiber_le_common
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    Pr[fun selection =>
        permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
      preloadedDelayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
        ftsSecret target fuel table] ≤
      Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
          ftsSecret fuel table] := by
  unfold preloadedDelayedPermissiveDetailedSelectionExperimentAfterTable
    delayedPermissiveDetailedSelectionExperimentAfterTable
  apply probEvent_bind_le_bind_of_forall_le_of_invariant
    (invariant := InitialRootOptionFacts target)
  · exact initialRootOptionFacts_of_mem target hroot hparent fuel table
  · intro rootResult hinitial
    cases rootResult with
    | none =>
        simp [permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?]
    | some rootResult =>
        apply probEvent_le_of_relTriple
          (relTriple_preloadedDelayedSelection_common_afterRootResult ordinal adversary parameter
            ftsSecret target rootResult hinitial.1)
        intro left right hrelation hleft
        exact hrelation hleft

set_option maxRecDepth 100000 in
theorem probEvent_installedDelayedSelection_fiber_le_common
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    Pr[fun selection =>
        permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
      installedDelayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
        ftsSecret target fuel table] ≤
      Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
          ftsSecret fuel table] := by
  calc
    _ ≤ Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        preloadedDelayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
          ftsSecret target fuel table] := by
      unfold installedDelayedPermissiveDetailedSelectionExperimentAfterTable
        preloadedDelayedPermissiveDetailedSelectionExperimentAfterTable
      apply probEvent_bind_le_bind_of_forall_le
      intro rootResult _hrootResult
      cases rootResult with
      | none => simp [permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?]
      | some rootResult =>
          apply probEvent_le_of_relTriple
            (relTriple_installedDelayedSelection_preloaded_afterRootResult ordinal adversary
              parameter ftsSecret target rootResult)
          intro left right heq hleft
          rwa [← heq]
    _ ≤ _ := probEvent_preloadedDelayedSelection_fiber_le_common ordinal adversary parameter
      ftsSecret target hroot hparent fuel table

set_option maxRecDepth 100000 in
theorem probEvent_privateOrdinalSelectionGoodForSomeOutput_le_targetGuess
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (target : Position) (rightRoot : Digest)
    (hroot : IsLayerRoot target) :
    Pr[privateOrdinalSelectionGoodForSomeOutput target rightRoot ordinal |
        granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter table ftsSecret
          fuel] ≤
      Pr[PermissiveTargetGuess target |
        delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
          ftsSecret fuel table] := by
  apply probEvent_le_of_relTriple
    (relTriple_granularAllCanonicalPrivateOrdinalSelection_permissiveDelayed ordinal adversary
      parameter table ftsSecret fuel target rightRoot hroot)
  intro left right hrelation hgood
  exact hrelation.targetGuess hgood

end SphincsSecurity.Concrete.OtsProbeSimulation
