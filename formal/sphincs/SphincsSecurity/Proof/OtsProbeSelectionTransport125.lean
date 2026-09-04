import SphincsSecurity.Proof.OtsProbeNonRootSelectionMass125

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot

/-- A successful canonical selection names the same candidate in the common execution. -/
def CanonicalSelectionPreserved :
    Option PrivateOrdinalSelection → Option PermissivePrivateOrdinalSelection → Prop
  | none, _ => True
  | some _, none => False
  | some left, some right => left.candidate = right.candidate

theorem relTriple_none_any_selectionPreserved
    (right : ProbComp (Option PermissivePrivateOrdinalSelection)) :
    RelTriple (pure none : ProbComp (Option PrivateOrdinalSelection)) right
      CanonicalSelectionPreserved := by
  have hbase := relTriple_true (pure none : ProbComp (Option PrivateOrdinalSelection)) right
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun value => value = none) (by intro value hvalue; simpa using hvalue)
  apply relTriple_post_mono hsupported
  intro left right hrelation
  rw [hrelation.2]
  trivial

theorem relTriple_selectionPreserved_trans
    {left : ProbComp (Option PrivateOrdinalSelection)}
    {middle right : ProbComp (Option PermissivePrivateOrdinalSelection)}
    (hleft : RelTriple left middle CanonicalSelectionPreserved)
    (hright : RelTriple middle right PermissiveDetailedSelectionRel) :
    RelTriple left right CanonicalSelectionPreserved := by
  apply relTriple_post_mono (SphincsSecurity.relTriple_trans_exists hleft hright)
  intro leftSelection rightSelection hrelation
  obtain ⟨middleSelection, hfirst, hsecond⟩ := hrelation
  cases leftSelection with
  | none => trivial
  | some leftSelected =>
      cases middleSelection with
      | none => exact False.elim hfirst
      | some middleSelected =>
          cases rightSelection with
          | none => exact False.elim hsecond
          | some rightSelected => exact hfirst.trans hsecond.1

set_option maxRecDepth 100000 in
theorem relTriple_finishDirect_selectionPreserved
    (table : OtsSecretIndex → HashOutput)
    (leftObserve : DeferredContext → Nat → (α × SplitHashCache) → List Probe →
      ProbComp (Option PrivateOrdinalSelection))
    (rightObserve : LazyRevealProbe.State Coordinate → Nat → α → SplitHashCache →
      List Probe → ProbComp (Option PermissivePrivateOrdinalSelection))
    (leftCandidates rightCandidates : List Probe)
    (left : DirectWitnessResult (α × SplitHashCache))
    (right : Option (CleanRunResult (α × SplitHashCache)))
    (hrelation : DirectWitnessPermissiveRunRel table left right)
    (hrecursive : ∀ leftResult rightResult,
      left = .done leftResult → right = some rightResult →
      leftResult.value = rightResult.value →
      leftResult.remaining = rightResult.remaining →
      (materializedDeferredState
          (canonicalizeMaterializedValues table leftResult.context)).values =
        rightResult.state.values →
      (canonicalizeMaterializedValues table leftResult.context).state.revealed =
        rightResult.state.revealed →
      (canonicalizeMaterializedValues table leftResult.context).Valid →
      DeferredCompletable table (canonicalizeMaterializedValues table leftResult.context) →
      ChainState.ValidFor (fun _ ↦ True)
          (canonicalizeMaterializedValues table leftResult.context).state →
      CanonicalMaterializedValues table
        (canonicalizeMaterializedValues table leftResult.context) →
      PublishedValues
        (canonicalizeMaterializedValues table leftResult.context).state →
      RelTriple
        (leftObserve (canonicalizeMaterializedValues table leftResult.context)
          leftResult.remaining leftResult.value leftCandidates)
        (rightObserve rightResult.state rightResult.remaining rightResult.value.1
          rightResult.value.2 rightCandidates)
        (CanonicalSelectionPreserved)) :
    RelTriple
      (finishDirectPrivateOrdinalSelection
        (canonicalizeDirectPrivateOrdinalSelection table leftObserve) leftCandidates left)
      (finishPermissiveDetailedPrivateOrdinalSelection rightObserve rightCandidates right)
      (CanonicalSelectionPreserved) := by
  cases left with
  | stoppedFuel =>
      exact relTriple_none_any_selectionPreserved _
  | stoppedOrdinary =>
      exact relTriple_none_any_selectionPreserved _
  | stoppedPrivate witness =>
      exact relTriple_none_any_selectionPreserved _
  | done leftResult =>
      rcases hrelation with hreject | ⟨rightResult, hright, hvalue, hremaining,
          _hleftTable, _hrightTable, hrevealed, hmaterialized, hchainValid, hcontext⟩
      · rcases hreject with hprivate | hpublished | hcompletable
        · rw [show finishDirectPrivateOrdinalSelection
              (canonicalizeDirectPrivateOrdinalSelection table leftObserve) leftCandidates
              (.done leftResult) = pure none by
            simp [finishDirectPrivateOrdinalSelection,
              canonicalizeDirectPrivateOrdinalSelection, hprivate]]
          exact relTriple_none_any_selectionPreserved _
        · rw [show finishDirectPrivateOrdinalSelection
              (canonicalizeDirectPrivateOrdinalSelection table leftObserve) leftCandidates
              (.done leftResult) = pure none by
            simp [finishDirectPrivateOrdinalSelection,
              canonicalizeDirectPrivateOrdinalSelection, hpublished]]
          exact relTriple_none_any_selectionPreserved _
        · rw [show finishDirectPrivateOrdinalSelection
              (canonicalizeDirectPrivateOrdinalSelection table leftObserve) leftCandidates
              (.done leftResult) = pure none by
            simp [finishDirectPrivateOrdinalSelection,
              canonicalizeDirectPrivateOrdinalSelection, hcompletable]]
          exact relTriple_none_any_selectionPreserved _
      · subst right
        let canonical := canonicalizeMaterializedValues table leftResult.context
        unfold finishDirectPrivateOrdinalSelection
          finishPermissiveDetailedPrivateOrdinalSelection
          canonicalizeDirectPrivateOrdinalSelection
        by_cases hprivate : PrivateStructuralHit canonical
        · simp only [canonical, hprivate, ↓reduceIte]
          exact relTriple_none_any_selectionPreserved _
        · simp only [canonical, hprivate, ↓reduceIte]
          by_cases hpublished : PublishedValues leftResult.context.state
          · simp only [hpublished, ↓reduceIte]
            by_cases hcompletable : DeferredCompletable table
                (canonicalizeMaterializedValues table leftResult.context)
            · simp only [hcompletable, ↓reduceIte]
              have hcanonicalMaterialized :
                  (materializedDeferredState canonical).values = rightResult.state.values := by
                rw [ScratchLocal.materializedDeferredState_canonicalize_eq table leftResult.context
                  hcontext.1.leftStarts hchainValid hcontext.2.1.valuesConsistent]
                exact hmaterialized
              have hcanonicalRevealed :
                  canonical.state.revealed = rightResult.state.revealed := by
                simpa [canonical, canonicalizeMaterializedValues_revealed] using hrevealed
              have hcanonicalValid : canonical.Valid :=
                canonicalizeMaterializedValues_valid table leftResult.context hcontext.2.1
                  hcontext.1.leftClean
              have hcanonicalChainValid : ChainState.ValidFor (fun _ ↦ True) canonical.state :=
                hchainValid.canonicalizeMaterializedValues table hcontext.1.leftStarts
              have hcanonicalCanonical : CanonicalMaterializedValues table canonical :=
                canonicalizeMaterializedValues_canonical table leftResult.context
                  hcontext.2.1.valuesConsistent
              have hcanonicalPublished : PublishedValues canonical.state :=
                hpublished.to_canonicalizedMaterializedValues
              simpa [hvalue, hremaining] using
                hrecursive leftResult rightResult rfl rfl hvalue hremaining
                  hcanonicalMaterialized hcanonicalRevealed hcanonicalValid hcompletable
                  hcanonicalChainValid hcanonicalCanonical hcanonicalPublished
            · simp only [hcompletable, ↓reduceIte]
              exact relTriple_none_any_selectionPreserved _
          · simp only [hpublished, ↓reduceIte]
            exact relTriple_none_any_selectionPreserved _

set_option maxRecDepth 100000 in
theorem relTriple_directBoundary_selectionPreserved
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hvalid : context.Valid)
    (hcompletable : DeferredCompletable table context)
    (hchainValid : ChainState.ValidFor (fun _ ↦ True) context.state)
    (hcanonical : CanonicalMaterializedValues table context)
    (hpublished : PublishedValues context.state)
    (hhash : DelayedHashActionCouples table parameter) :
    RelTriple
      (directDetailedBoundaryPrivateOrdinalSelection ordinal parameter root ftsSecret computation
        candidates context fuel table cache)
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        candidates (materializedDeferredState context) fuel table cache)
      (CanonicalSelectionPreserved) := by
  induction computation using OracleComp.inductionOn generalizing
      candidates context fuel cache with
  | pure value =>
      simp only [directDetailedBoundaryPrivateOrdinalSelection,
        delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_pure]
      by_cases hselected : ordinal < candidates.length
      · simp only [selectedPrivateOrdinal?, hselected, ↓reduceDIte]
        exact relTriple_pure_pure rfl
      · simp only [selectedPrivateOrdinal?, hselected, ↓reduceDIte]
        exact relTriple_pure_pure trivial
  | query_bind query next ih =>
      rw [directDetailedBoundaryPrivateOrdinalSelection, OracleComp.construct_query_bind,
        delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure rfl
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                let leftObserve : DeferredContext → Nat →
                    (Fin (n + 1) × SplitHashCache) → List Probe →
                      ProbComp (Option PrivateOrdinalSelection) :=
                  fun nextContext remaining value laterCandidates =>
                    directDetailedBoundaryPrivateOrdinalSelection ordinal parameter root ftsSecret
                      (next value.1) laterCandidates nextContext remaining table value.2
                let rightObserve : LazyRevealProbe.State Coordinate → Nat → Fin (n + 1) →
                    SplitHashCache → List Probe →
                      ProbComp (Option PermissivePrivateOrdinalSelection) :=
                  fun nextState remaining output nextCache laterCandidates =>
                    delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret
                      (next output) laterCandidates nextState remaining table nextCache
                apply relTriple_bind
                  (relTriple_runDirectResolvedWitness_runPermissiveFromTable
                    (splitUniformImpl n) context fuel table cache hvalid hcompletable hchainValid
                    (preservesChainValid_splitUniformImpl (fun _ ↦ True) n)
                    (directWitnessFinalizationMaterializedCouples_splitUniformImpl table n))
                intro leftResult rightResult hresult
                apply relTriple_finishDirect_selectionPreserved table leftObserve rightObserve candidates candidates leftResult
                    rightResult hresult
                intro nextLeft nextRight _hleft _hright hvalue hremaining hvalues hrevealed
                  hnextValid hnextCompletable hnextChainValid hnextCanonical hnextPublished
                let canonical := canonicalizeMaterializedValues table nextLeft.context
                have hbase := ih nextLeft.value.1 candidates canonical nextLeft.remaining
                  nextLeft.value.2 hnextValid hnextCompletable hnextChainValid
                    hnextCanonical hnextPublished
                have hstate : PermissiveStateRel (materializedDeferredState canonical)
                    nextRight.state := ⟨hvalues, hrevealed⟩
                have htransport :=
                  relTriple_delayedPermissiveDetailedOrdinalSelection_of_stateRel ordinal
                    parameter root ftsSecret (next nextLeft.value.1) candidates candidates
                    (materializedDeferredState canonical) nextRight.state nextLeft.remaining table
                    nextLeft.value.2 rfl hstate
                simpa only [leftObserve, rightObserve, canonical, ← hvalue, ← hremaining] using
                  relTriple_selectionPreserved_trans
                    hbase htransport
            | inr input =>
                let plan := purePlanProbingHashQuery parameter input context.state
                let nextCandidates := appendPlannedCandidate candidates
                  (rootAwarePlannedCandidate? parameter input context.state)
                have hrightCandidates :
                    permissiveRootAwareCandidates parameter input table
                        (materializedDeferredState context) candidates = nextCandidates := by
                  exact permissiveRootAwareCandidates_materializedDeferredState_eq parameter input
                    table context candidates hvalid hcompletable hcanonical
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hrightSelected : ordinal <
                      (permissiveRootAwareCandidates parameter input table
                        (materializedDeferredState context) candidates).length := by
                    rwa [hrightCandidates]
                  simp only [nextCandidates, hnextSelected, hrightSelected, ↓reduceDIte]
                  have hcandidate :
                      nextCandidates.get ⟨ordinal, hnextSelected⟩ =
                        (permissiveRootAwareCandidates parameter input table
                          (materializedDeferredState context) candidates).get
                            ⟨ordinal, hrightSelected⟩ := by
                    rw [List.get_eq_getElem, List.get_eq_getElem]
                    simp only [hrightCandidates]
                  apply relTriple_pure_pure
                  exact hcandidate
                · have hrightSelected : ¬ordinal <
                      (permissiveRootAwareCandidates parameter input table
                        (materializedDeferredState context) candidates).length := by
                    rwa [hrightCandidates]
                  simp only [nextCandidates, hnextSelected, hrightSelected, ↓reduceDIte]
                  let leftObserve : DeferredContext → Nat →
                      (HashOutput × SplitHashCache) → List Probe →
                        ProbComp (Option PrivateOrdinalSelection) :=
                    fun nextContext remaining value laterCandidates =>
                      directDetailedBoundaryPrivateOrdinalSelection ordinal parameter root
                        ftsSecret (next value.1) laterCandidates nextContext remaining table value.2
                  let rightObserve : LazyRevealProbe.State Coordinate → Nat → HashOutput →
                      SplitHashCache → List Probe →
                        ProbComp (Option PermissivePrivateOrdinalSelection) :=
                    fun nextState remaining output nextCache laterCandidates =>
                      delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret
                        (next output) laterCandidates nextState remaining table nextCache
                  apply relTriple_bind (hhash input context fuel cache hvalid hcompletable
                    hchainValid hcanonical hpublished)
                  intro leftResult rightResult hresult
                  apply relTriple_finishDirect_selectionPreserved
                    table leftObserve rightObserve nextCandidates
                    (permissiveRootAwareCandidates parameter input table
                      (materializedDeferredState context) candidates)
                    leftResult rightResult hresult
                  intro nextLeft nextRight _hleft _hright hvalue hremaining hvalues hrevealed
                    hnextValid hnextCompletable hnextChainValid hnextCanonical hnextPublished
                  let canonical := canonicalizeMaterializedValues table nextLeft.context
                  have hbase := ih nextLeft.value.1 nextCandidates canonical nextLeft.remaining
                    nextLeft.value.2 hnextValid hnextCompletable hnextChainValid
                      hnextCanonical hnextPublished
                  have hstate : PermissiveStateRel (materializedDeferredState canonical)
                      nextRight.state := ⟨hvalues, hrevealed⟩
                  have htransport :=
                    relTriple_delayedPermissiveDetailedOrdinalSelection_of_stateRel ordinal
                      parameter root ftsSecret (next nextLeft.value.1) nextCandidates
                      (permissiveRootAwareCandidates parameter input table
                        (materializedDeferredState context) candidates)
                      (materializedDeferredState canonical) nextRight.state nextLeft.remaining
                      table nextLeft.value.2 hrightCandidates.symm hstate
                  simpa only [leftObserve, rightObserve, canonical, ← hvalue, ← hremaining] using
                    relTriple_selectionPreserved_trans
                      hbase htransport
        | inr message =>
            let leftObserve : DeferredContext → Nat →
                (Option Signature × SplitHashCache) → List Probe →
                  ProbComp (Option PrivateOrdinalSelection) :=
              fun nextContext remaining value laterCandidates =>
                directDetailedBoundaryPrivateOrdinalSelection ordinal parameter root ftsSecret
                  (next value.1) laterCandidates nextContext remaining table value.2
            let rightObserve : LazyRevealProbe.State Coordinate → Nat → Option Signature →
                SplitHashCache → List Probe →
                  ProbComp (Option PermissivePrivateOrdinalSelection) :=
              fun nextState remaining output nextCache laterCandidates =>
                delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret
                  (next output) laterCandidates nextState remaining table nextCache
            apply relTriple_bind
              (relTriple_runDirectResolvedWitness_runPermissiveFromTable
                (maskedSign parameter root ftsSecret message) context fuel table cache hvalid
                hcompletable hchainValid
                (preservesChainValid_maskedSign_true parameter root ftsSecret message)
                (directWitnessFinalizationMaterializedCouples_maskedSign table parameter root
                  ftsSecret message))
            intro leftResult rightResult hresult
            apply relTriple_finishDirect_selectionPreserved table leftObserve rightObserve candidates candidates leftResult
                rightResult hresult
            intro nextLeft nextRight _hleft _hright hvalue hremaining hvalues hrevealed
              hnextValid hnextCompletable hnextChainValid hnextCanonical hnextPublished
            let canonical := canonicalizeMaterializedValues table nextLeft.context
            have hbase := ih nextLeft.value.1 candidates canonical nextLeft.remaining
              nextLeft.value.2 hnextValid hnextCompletable hnextChainValid
                hnextCanonical hnextPublished
            have hstate : PermissiveStateRel (materializedDeferredState canonical)
                nextRight.state := ⟨hvalues, hrevealed⟩
            have htransport :=
              relTriple_delayedPermissiveDetailedOrdinalSelection_of_stateRel ordinal parameter
                root ftsSecret (next nextLeft.value.1) candidates candidates
                (materializedDeferredState canonical) nextRight.state nextLeft.remaining table
                nextLeft.value.2 rfl hstate
            simpa only [leftObserve, rightObserve, canonical, ← hvalue, ← hremaining] using
              relTriple_selectionPreserved_trans
                hbase htransport

set_option maxRecDepth 100000 in
theorem relTriple_finishGranularPrivateOrdinalSelection_preserved
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (leftResult : DirectWitnessResult (Digest × SplitHashCache))
    (rightResult : Option (CleanRunResult (Digest × SplitHashCache)))
    (hresult : DirectWitnessPermissiveRunRel table leftResult rightResult) :
    RelTriple
      (finishDirectPrivateOrdinalSelection
        (canonicalizeDirectPrivateOrdinalSelection table
          (granularPrivateOrdinalSelectionObserve ordinal adversary parameter table ftsSecret)) []
        leftResult)
      (finishDelayedPermissiveDetailedSelection ordinal adversary parameter table ftsSecret
        rightResult)
      (CanonicalSelectionPreserved) := by
  unfold finishDelayedPermissiveDetailedSelection
  apply relTriple_finishDirect_selectionPreserved table
    (granularPrivateOrdinalSelectionObserve ordinal adversary parameter table ftsSecret)
    (delayedPermissiveDetailedSelectionObserve ordinal adversary parameter table ftsSecret)
    [] [] leftResult rightResult hresult
  intro left right _hleft _hright hvalue hremaining hvalues hrevealed hvalid hcompletable
    hchainValid hcanonical hpublished
  have hbase := relTriple_directBoundary_selectionPreserved ordinal
    parameter left.value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨left.value.1, parameter⟩) []
    (canonicalizeMaterializedValues table left.context) left.remaining table left.value.2
    hvalid hcompletable hchainValid hcanonical hpublished (delayedHashActionCouples table parameter)
  have hstate : PermissiveStateRel
      (materializedDeferredState (canonicalizeMaterializedValues table left.context)) right.state :=
    ⟨hvalues, hrevealed⟩
  have htransport :=
    relTriple_delayedPermissiveDetailedOrdinalSelection_of_stateRel ordinal parameter left.value.1
      ftsSecret (retainedGameRestComputation adversary ⟨left.value.1, parameter⟩) [] []
      (materializedDeferredState (canonicalizeMaterializedValues table left.context)) right.state
      left.remaining table left.value.2 rfl hstate
  simpa only [granularPrivateOrdinalSelectionObserve, delayedPermissiveDetailedSelectionObserve,
    ← hvalue, ← hremaining] using
    relTriple_selectionPreserved_trans hbase htransport

set_option maxRecDepth 100000 in
theorem relTriple_granularAllCanonicalPrivateOrdinalSelection_preserved
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) :
    RelTriple
      (granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter table ftsSecret fuel)
      (delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
        ftsSecret fuel table)
      (CanonicalSelectionPreserved) := by
  rw [granularAllCanonicalPrivateOrdinalSelection_eq_bind_finish]
  unfold delayedPermissiveDetailedSelectionExperimentAfterTable rootAwareProductionInitialRun
  have hempty : materializedDeferredState emptyWitnessDeferredContext =
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) := by
    unfold materializedDeferredState emptyWitnessDeferredContext LazyRevealProbe.State.empty
    rw [LazyRevealProbe.State.mk.injEq]
    refine ⟨rfl, ?_, rfl, rfl⟩
    funext coordinate
    cases coordinate <;> rfl
  have hinitial : RelTriple
      (runDirectResolvedWitnessFromTable emptyWitnessDeferredContext fuel table
        (maskedPublishedTreeRoot.run emptySplitHashCache))
      (runCleanFromTable (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        fuel table (maskedPublishedTreeRoot.run emptySplitHashCache))
      (DirectWitnessPermissiveRunRel table) := by
    rw [← hempty]
    exact relTriple_runDirectResolvedWitness_runCleanFromTable maskedPublishedTreeRoot
      emptyWitnessDeferredContext fuel table emptySplitHashCache DeferredContext.valid_empty
      (deferredCompletable_empty table)
      (by simp [ChainState.ValidFor, emptyWitnessDeferredContext,
        LazyRevealProbe.State.empty])
      preservesChainValid_maskedPublishedTreeRoot_true
      (directWitnessFinalizationMaterializedCouples_maskedPublishedTreeRoot table)
  refine relTriple_bind
    (R := DirectWitnessPermissiveRunRel table)
    hinitial ?_
  intro leftResult rightResult hresult
  have hfixed := relTriple_finishGranularPrivateOrdinalSelection_preserved ordinal adversary
    parameter table ftsSecret leftResult rightResult hresult
  cases leftResult with
  | stoppedFuel =>
      exact relTriple_none_any_selectionPreserved _
  | stoppedOrdinary =>
      exact relTriple_none_any_selectionPreserved _
  | stoppedPrivate witness =>
      exact relTriple_none_any_selectionPreserved _
  | done leftResult =>
      rcases hresult with hreject | ⟨cleanResult, hright, hvalue, hremaining,
        hleftTable, hrightTable, hrevealed, hmaterialized, hchainValid, hcontext⟩
      · rcases hreject with hprivate | hpublished | hcompletable
        · rw [show finishDirectPrivateOrdinalSelection
              (canonicalizeDirectPrivateOrdinalSelection table
                (granularPrivateOrdinalSelectionObserve ordinal adversary parameter table
                  ftsSecret)) [] (.done leftResult) = pure none by
            simp [finishDirectPrivateOrdinalSelection,
              canonicalizeDirectPrivateOrdinalSelection, hprivate]]
          exact relTriple_none_any_selectionPreserved _
        · rw [show finishDirectPrivateOrdinalSelection
              (canonicalizeDirectPrivateOrdinalSelection table
                (granularPrivateOrdinalSelectionObserve ordinal adversary parameter table
                  ftsSecret)) [] (.done leftResult) = pure none by
            simp [finishDirectPrivateOrdinalSelection,
              canonicalizeDirectPrivateOrdinalSelection, hpublished]]
          exact relTriple_none_any_selectionPreserved _
        · rw [show finishDirectPrivateOrdinalSelection
              (canonicalizeDirectPrivateOrdinalSelection table
                (granularPrivateOrdinalSelectionObserve ordinal adversary parameter table
                  ftsSecret)) [] (.done leftResult) = pure none by
            simp [finishDirectPrivateOrdinalSelection,
              canonicalizeDirectPrivateOrdinalSelection, hcompletable]]
          exact relTriple_none_any_selectionPreserved _
      · subst rightResult
        change RelTriple
          (finishDirectPrivateOrdinalSelection
            (canonicalizeDirectPrivateOrdinalSelection table
              (granularPrivateOrdinalSelectionObserve ordinal adversary parameter table
                ftsSecret)) [] (.done leftResult))
          (delayedPermissiveDetailedSelectionAfterRootResult ordinal adversary parameter
            ftsSecret cleanResult)
          (CanonicalSelectionPreserved)
        rw [show delayedPermissiveDetailedSelectionAfterRootResult ordinal adversary parameter
              ftsSecret cleanResult =
            finishDelayedPermissiveDetailedSelection ordinal adversary parameter table ftsSecret
              (some cleanResult) by
          simp only [delayedPermissiveDetailedSelectionAfterRootResult,
            finishDelayedPermissiveDetailedSelection,
            finishPermissiveDetailedPrivateOrdinalSelection,
            delayedPermissiveDetailedSelectionObserve]
          rw [hrightTable]]
        exact hfixed

end SphincsSecurity.Concrete.OtsProbeSimulation
