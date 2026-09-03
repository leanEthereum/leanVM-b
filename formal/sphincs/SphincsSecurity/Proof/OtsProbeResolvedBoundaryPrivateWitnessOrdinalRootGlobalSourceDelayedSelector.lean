import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSourceDelayedCoupling
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveProductionCommonExperiment
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveReverse

/-!
# Delayed source common selector

The delayed-source comparison records every root-aware candidate, including an encoding-domain
candidate, but executes only the hash action made by the source game. Keeping that schedule avoids
turning a proof-only candidate at an earlier ordinal into a spurious revealed position.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def DelayedPermissiveSelectionRel
    (target : Position) (leftOutput : HashOutput) (rightRoot : Digest) (ordinal : Nat) :
    Option PrivateOrdinalSelection → Option PermissivePrivateOrdinalSelection → Prop :=
  fun left right =>
    privateOrdinalSelectionGoodForRoots target leftOutput rightRoot ordinal left →
      permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? right = some target

theorem delayedPermissiveSelectionRel_selected
    (target : Position) (leftOutput : HashOutput) (rightRoot : Digest) (ordinal : Nat)
    (hroot : IsLayerRoot target) (candidate : Probe)
    (candidates : List Probe) (left : DeferredContext)
    (right : LazyRevealProbe.State Coordinate)
    (hrevealed : left.state.revealed = right.revealed) :
    DelayedPermissiveSelectionRel target leftOutput rightRoot ordinal
      (some ⟨candidate, left, candidates⟩) (some ⟨candidate, right, candidates⟩) := by
  intro hgood
  change PrivateOrdinalSelection.GoodForRoots target leftOutput rightRoot ordinal
    ⟨candidate, left, candidates⟩ at hgood
  exact permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?_eq_some_of_candidate
    (by simpa using congrArg Probe.coordinate hgood.1)
    hroot (by simpa [← hrevealed] using hgood.2.2.1)

theorem relTriple_none_any_delayedPermissiveSelection
    (target : Position) (leftOutput : HashOutput) (rightRoot : Digest) (ordinal : Nat)
    (right : ProbComp (Option PermissivePrivateOrdinalSelection)) :
    RelTriple (pure none : ProbComp (Option PrivateOrdinalSelection)) right
      (DelayedPermissiveSelectionRel target leftOutput rightRoot ordinal) := by
  have hbase := relTriple_true (pure none : ProbComp (Option PrivateOrdinalSelection)) right
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun value => value = none) (by
        intro value hvalue
        simpa using hvalue)
  apply relTriple_post_mono hsupported
  intro left right hrelation
  rw [hrelation.2]
  simp [DelayedPermissiveSelectionRel, privateOrdinalSelectionGoodForRoots]

set_option maxRecDepth 100000 in
theorem relTriple_finishDirect_delayedPermissiveSelection
    (target : Position) (leftOutput : HashOutput) (rightRoot : Digest) (ordinal : Nat)
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
      RelTriple
        (leftObserve (canonicalizeMaterializedValues table leftResult.context)
          leftResult.remaining leftResult.value leftCandidates)
        (rightObserve rightResult.state rightResult.remaining rightResult.value.1
          rightResult.value.2 rightCandidates)
        (DelayedPermissiveSelectionRel target leftOutput rightRoot ordinal)) :
    RelTriple
      (finishDirectPrivateOrdinalSelection
        (canonicalizeDirectPrivateOrdinalSelection table leftObserve) leftCandidates left)
      (finishPermissiveDetailedPrivateOrdinalSelection rightObserve rightCandidates right)
      (DelayedPermissiveSelectionRel target leftOutput rightRoot ordinal) := by
  cases left with
  | stoppedFuel =>
      exact relTriple_none_any_delayedPermissiveSelection target leftOutput rightRoot ordinal _
  | stoppedOrdinary =>
      exact relTriple_none_any_delayedPermissiveSelection target leftOutput rightRoot ordinal _
  | stoppedPrivate witness =>
      exact relTriple_none_any_delayedPermissiveSelection target leftOutput rightRoot ordinal _
  | done leftResult =>
      cases right with
      | none => exact False.elim hrelation
      | some rightResult =>
          rcases hrelation with
            ⟨hvalue, hremaining, _hleftTable, _hrightTable, hrevealed, hmaterialized,
              hchainValid, hcontext⟩
          let canonical := canonicalizeMaterializedValues table leftResult.context
          unfold finishDirectPrivateOrdinalSelection
            finishPermissiveDetailedPrivateOrdinalSelection
            canonicalizeDirectPrivateOrdinalSelection
          by_cases hprivate : PrivateStructuralHit canonical
          · simp only [canonical, hprivate, ↓reduceIte]
            exact relTriple_none_any_delayedPermissiveSelection target leftOutput rightRoot ordinal _
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
                simpa [hvalue, hremaining] using
                  hrecursive leftResult rightResult rfl rfl hvalue hremaining
                    hcanonicalMaterialized hcanonicalRevealed hcanonicalValid hcompletable
                    hcanonicalChainValid hcanonicalCanonical
              · simp only [hcompletable, ↓reduceIte]
                exact relTriple_none_any_delayedPermissiveSelection target leftOutput rightRoot
                  ordinal _
            · simp only [hpublished, ↓reduceIte]
              exact relTriple_none_any_delayedPermissiveSelection target leftOutput rightRoot
                ordinal _

noncomputable def delayedPermissivePublicAction
    (parameter : PublicParameter) (input : HashInput)
    (table : OtsSecretIndex → HashOutput)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) :
    OracleComp (LazyRevealProbe.World Coordinate) (HashOutput × SplitHashCache) :=
  let publicContext := materializedCanonicalContext table state
  let plan := purePlanProbingHashQuery parameter input publicContext.state
  (probingHashQueryAfterPublicPlan parameter input publicContext.state plan).run cache

noncomputable def delayedPermissiveDetailedOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp (Option PermissivePrivateOrdinalSelection) := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp (OracleWorld + SigningSpec) α =>
      List Probe → LazyRevealProbe.State Coordinate → Nat →
        (OtsSecretIndex → HashOutput) → SplitHashCache →
          ProbComp (Option PermissivePrivateOrdinalSelection))
    (fun _value candidates state _fuel _table _cache =>
      if hselected : ordinal < candidates.length then
        pure (some ⟨candidates.get ⟨ordinal, hselected⟩, state, candidates⟩)
      else pure none)
    (fun query _next recursivelyRun candidates state fuel table cache =>
      if hselected : ordinal < candidates.length then
        pure (some ⟨candidates.get ⟨ordinal, hselected⟩, state, candidates⟩)
      else
        match query with
        | .inl (.inl n) =>
            runPermissiveFromTable state fuel table ((splitUniformImpl n).run cache) >>=
              finishPermissiveDetailedPrivateOrdinalSelection
                (fun nextState remaining value nextCache laterCandidates =>
                  recursivelyRun value laterCandidates nextState remaining table nextCache)
                candidates
        | .inl (.inr input) =>
            let nextCandidates := permissiveRootAwareCandidates parameter input table state
              candidates
            if hnextSelected : ordinal < nextCandidates.length then
              pure (some ⟨nextCandidates.get ⟨ordinal, hnextSelected⟩, state,
                nextCandidates⟩)
            else
              runPermissiveFromTable state fuel table
                  (delayedPermissivePublicAction parameter input table state cache) >>=
                finishPermissiveDetailedPrivateOrdinalSelection
                  (fun nextState remaining value nextCache laterCandidates =>
                    recursivelyRun value laterCandidates nextState remaining table nextCache)
                  nextCandidates
        | .inr message =>
            runPermissiveFromTable state fuel table
                ((maskedSign parameter root ftsSecret message).run cache) >>=
              finishPermissiveDetailedPrivateOrdinalSelection
                (fun nextState remaining value nextCache laterCandidates =>
                  recursivelyRun value laterCandidates nextState remaining table nextCache)
                candidates)
    computation candidates state fuel table cache

theorem delayedPermissivePublicAction_eq_of_stateRel
    (parameter : PublicParameter) (input : HashInput)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    {left right : LazyRevealProbe.State Coordinate}
    (hstate : PermissiveStateRel left right) :
    delayedPermissivePublicAction parameter input table left cache =
      delayedPermissivePublicAction parameter input table right cache := by
  unfold delayedPermissivePublicAction
  dsimp only
  have hplan := permissiveRootAwarePlan_eq_of_stateRel parameter input table hstate
  have hvalues := materializedCanonicalContext_values_eq_of_permissiveStateRel table hstate
  unfold permissiveRootAwarePlan at hplan
  rw [hplan]
  exact congrArg (fun computation => computation.run cache)
    (probingHashQueryAfterPublicPlan_eq_of_values_eq parameter input hvalues _)

theorem materializedCanonicalContext_values_eq_canonicalContext
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hcanonical : CanonicalMaterializedValues table context) :
    (materializedCanonicalContext table (materializedDeferredState context)).state.values =
      context.state.values := by
  have hle := finalizationContextLE_materializedDeferredContext hvalid hcompletable
  have hrevealed : context.state.revealed =
      (materializedDeferredContext context).state.revealed := by
    simp [materializedDeferredContext, directDeferredContext, materializedDeferredState]
  have hvalues := canonicalized_right_values_eq_of_finalizationContextLE hle hrevealed hcanonical
  simpa [materializedCanonicalContext, materializedDeferredContext] using hvalues

theorem permissiveRootAwareCandidates_materializedDeferredState_eq
    (parameter : PublicParameter) (input : HashInput)
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (candidates : List Probe)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hcanonical : CanonicalMaterializedValues table context) :
    permissiveRootAwareCandidates parameter input table (materializedDeferredState context)
        candidates =
      appendPlannedCandidate candidates
        (rootAwarePlannedCandidate? parameter input context.state) := by
  unfold permissiveRootAwareCandidates permissiveRootAwarePlan
  rw [purePlanProbingHashQuery_eq_of_values_eq
    (materializedCanonicalContext_values_eq_canonicalContext table context hvalid hcompletable
      hcanonical) parameter input]
  rw [rootAwareCandidateForPlan?_purePlan]

theorem delayedPermissivePublicAction_materializedDeferredState_eq
    (parameter : PublicParameter) (input : HashInput)
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (cache : SplitHashCache)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hcanonical : CanonicalMaterializedValues table context) :
    delayedPermissivePublicAction parameter input table (materializedDeferredState context) cache =
      (probingHashQueryAfterPublicPlan parameter input context.state
        (purePlanProbingHashQuery parameter input context.state)).run cache := by
  unfold delayedPermissivePublicAction
  dsimp only
  have hvalues := materializedCanonicalContext_values_eq_canonicalContext table context hvalid
    hcompletable hcanonical
  have hplan := purePlanProbingHashQuery_eq_of_values_eq hvalues parameter input
  rw [hplan]
  exact congrArg (fun computation => computation.run cache)
    (probingHashQueryAfterPublicPlan_eq_of_values_eq parameter input hvalues _)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem relTriple_delayedPermissiveDetailedOrdinalSelection_of_stateRel
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (leftCandidates rightCandidates : List Probe)
    (left right : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hcandidates : leftCandidates = rightCandidates)
    (hstate : PermissiveStateRel left right) :
    RelTriple
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        leftCandidates left fuel table cache)
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        rightCandidates right fuel table cache)
      PermissiveDetailedSelectionRel := by
  induction computation using OracleComp.inductionOn generalizing
      leftCandidates rightCandidates left right fuel cache with
  | pure value =>
      subst rightCandidates
      simp only [delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_pure]
      by_cases hselected : ordinal < leftCandidates.length
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure ⟨rfl, rfl, hstate⟩
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure trivial
  | query_bind query next ih =>
      subst rightCandidates
      rw [delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_query_bind,
        delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < leftCandidates.length
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure ⟨rfl, rfl, hstate⟩
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
                apply relTriple_bind
                  (relTriple_runPermissiveFromTable_of_stateRel
                    ((splitUniformImpl n).run cache) left right fuel table hstate)
                intro leftResult rightResult hresult
                apply relTriple_finishPermissiveDetailedSelection observe observe leftCandidates
                  leftCandidates leftResult rightResult rfl hresult
                intro nextLeft nextRight hnext
                rcases hnext with ⟨hnextState, hremaining, hvalue, htable⟩
                simpa only [observe, hremaining, hvalue,
                  delayedPermissiveDetailedOrdinalSelection] using
                  ih nextLeft.value.1 leftCandidates leftCandidates nextLeft.state nextRight.state
                    nextLeft.remaining nextLeft.value.2 rfl hnextState
            | inr input =>
                let leftNext :=
                  permissiveRootAwareCandidates parameter input table left leftCandidates
                let rightNext :=
                  permissiveRootAwareCandidates parameter input table right leftCandidates
                have hnext : leftNext = rightNext :=
                  permissiveRootAwareCandidates_eq_of_stateRel parameter input table
                    leftCandidates hstate
                by_cases hnextSelected : ordinal < leftNext.length
                · have hrightSelected : ordinal < rightNext.length := by rwa [← hnext]
                  simp only [leftNext, rightNext, hnextSelected, hrightSelected, ↓reduceDIte]
                  have hcandidate :
                      (permissiveRootAwareCandidates parameter input table left leftCandidates).get
                          ⟨ordinal, hnextSelected⟩ =
                        (permissiveRootAwareCandidates parameter input table right leftCandidates).get
                          ⟨ordinal, hrightSelected⟩ := by
                    dsimp only [leftNext, rightNext] at hnext
                    rw [List.get_eq_getElem, List.get_eq_getElem]
                    simpa only [hnext]
                  exact relTriple_pure_pure ⟨hcandidate, hnext, hstate⟩
                · have hrightSelected : ¬ordinal < rightNext.length := by rwa [← hnext]
                  simp only [leftNext, rightNext, hnextSelected, hrightSelected, ↓reduceDIte]
                  let observe : LazyRevealProbe.State Coordinate → Nat → HashOutput →
                      SplitHashCache → List Probe →
                        ProbComp (Option PermissivePrivateOrdinalSelection) :=
                    fun nextState remaining output nextCache laterCandidates =>
                      delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret
                        (next output) laterCandidates nextState remaining table nextCache
                  apply relTriple_bind
                    (by
                      rw [delayedPermissivePublicAction_eq_of_stateRel parameter input table cache
                        hstate]
                      exact relTriple_runPermissiveFromTable_of_stateRel _ left right fuel table
                        hstate)
                  intro leftResult rightResult hresult
                  apply relTriple_finishPermissiveDetailedSelection observe observe leftNext
                    rightNext leftResult rightResult hnext hresult
                  intro nextLeft nextRight hnextResult
                  rcases hnextResult with ⟨hnextState, hremaining, hvalue, htable⟩
                  simpa only [observe, hremaining, hvalue,
                    delayedPermissiveDetailedOrdinalSelection] using
                    ih nextLeft.value.1 leftNext rightNext nextLeft.state nextRight.state
                      nextLeft.remaining nextLeft.value.2 hnext hnextState
        | inr message =>
            let observe : LazyRevealProbe.State Coordinate → Nat → Option Signature →
                SplitHashCache → List Probe →
                  ProbComp (Option PermissivePrivateOrdinalSelection) :=
              fun nextState remaining output nextCache laterCandidates =>
                delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret
                  (next output) laterCandidates nextState remaining table nextCache
            apply relTriple_bind
              (relTriple_runPermissiveFromTable_of_stateRel
                ((maskedSign parameter root ftsSecret message).run cache)
                left right fuel table hstate)
            intro leftResult rightResult hresult
            apply relTriple_finishPermissiveDetailedSelection observe observe leftCandidates
              leftCandidates leftResult rightResult rfl hresult
            intro nextLeft nextRight hnext
            rcases hnext with ⟨hnextState, hremaining, hvalue, htable⟩
            simpa only [observe, hremaining, hvalue,
              delayedPermissiveDetailedOrdinalSelection] using
              ih nextLeft.value.1 leftCandidates leftCandidates nextLeft.state nextRight.state
                nextLeft.remaining nextLeft.value.2 rfl hnextState

theorem relTriple_delayedPermissiveSelection_trans
    (target : Position) (leftOutput : HashOutput) (rightRoot : Digest) (ordinal : Nat)
    {left : ProbComp (Option PrivateOrdinalSelection)}
    {middle right : ProbComp (Option PermissivePrivateOrdinalSelection)}
    (hleft : RelTriple left middle
      (DelayedPermissiveSelectionRel target leftOutput rightRoot ordinal))
    (hright : RelTriple middle right PermissiveDetailedSelectionRel) :
    RelTriple left right
      (DelayedPermissiveSelectionRel target leftOutput rightRoot ordinal) := by
  have hglued := SphincsSecurity.relTriple_trans_exists hleft hright
  apply relTriple_post_mono hglued
  intro leftSelection rightSelection hrelation hgood
  obtain ⟨middleSelection, hfirst, hsecond⟩ := hrelation
  have hmiddle := hfirst hgood
  rw [hsecond.positionFiber_eq] at hmiddle
  exact hmiddle

def DelayedHashActionCouples
    (table : OtsSecretIndex → HashOutput) (parameter : PublicParameter) : Prop :=
  ∀ (input : HashInput) (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache),
    context.Valid → DeferredCompletable table context →
    ChainState.ValidFor (fun _ ↦ True) context.state →
    CanonicalMaterializedValues table context →
    RelTriple
      (runDirectResolvedWitnessFromTable context fuel table
        ((probingHashQueryAfterPlan parameter input
          (purePlanProbingHashQuery parameter input context.state)).run cache))
      (runPermissiveFromTable (materializedDeferredState context) fuel table
        (delayedPermissivePublicAction parameter input table
          (materializedDeferredState context) cache))
      (DirectWitnessPermissiveRunRel table)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_directBoundary_delayedPermissiveDetailedOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (target : Position) (leftOutput : HashOutput) (rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hroot : IsLayerRoot target) (hvalid : context.Valid)
    (hcompletable : DeferredCompletable table context)
    (hchainValid : ChainState.ValidFor (fun _ ↦ True) context.state)
    (hcanonical : CanonicalMaterializedValues table context)
    (hhash : DelayedHashActionCouples table parameter) :
    RelTriple
      (directDetailedBoundaryPrivateOrdinalSelection ordinal parameter root ftsSecret computation
        candidates context fuel table cache)
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        candidates (materializedDeferredState context) fuel table cache)
      (DelayedPermissiveSelectionRel target leftOutput rightRoot ordinal) := by
  induction computation using OracleComp.inductionOn generalizing
      candidates context fuel cache with
  | pure value =>
      simp only [directDetailedBoundaryPrivateOrdinalSelection,
        delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_pure]
      by_cases hselected : ordinal < candidates.length
      · simp only [selectedPrivateOrdinal?, hselected, ↓reduceDIte]
        exact relTriple_pure_pure
          (delayedPermissiveSelectionRel_selected target leftOutput rightRoot ordinal hroot
            _ candidates context (materializedDeferredState context) (by
              simp [materializedDeferredState]))
      · simp only [selectedPrivateOrdinal?, hselected, ↓reduceDIte]
        exact relTriple_pure_pure (by
          simp [DelayedPermissiveSelectionRel, privateOrdinalSelectionGoodForRoots])
  | query_bind query next ih =>
      rw [directDetailedBoundaryPrivateOrdinalSelection, OracleComp.construct_query_bind,
        delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure
          (delayedPermissiveSelectionRel_selected target leftOutput rightRoot ordinal hroot
            _ candidates context (materializedDeferredState context) (by
              simp [materializedDeferredState]))
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
                apply relTriple_finishDirect_delayedPermissiveSelection target leftOutput rightRoot
                  ordinal table leftObserve rightObserve candidates candidates leftResult
                    rightResult hresult
                intro nextLeft nextRight _hleft _hright hvalue hremaining hvalues hrevealed
                  hnextValid hnextCompletable hnextChainValid hnextCanonical
                let canonical := canonicalizeMaterializedValues table nextLeft.context
                have hbase := ih nextLeft.value.1 candidates canonical nextLeft.remaining
                  nextLeft.value.2 hnextValid hnextCompletable hnextChainValid
                    hnextCanonical
                have hstate : PermissiveStateRel (materializedDeferredState canonical)
                    nextRight.state := ⟨hvalues, hrevealed⟩
                have htransport :=
                  relTriple_delayedPermissiveDetailedOrdinalSelection_of_stateRel ordinal
                    parameter root ftsSecret (next nextLeft.value.1) candidates candidates
                    (materializedDeferredState canonical) nextRight.state nextLeft.remaining table
                    nextLeft.value.2 rfl hstate
                simpa only [leftObserve, rightObserve, canonical, ← hvalue, ← hremaining] using
                  relTriple_delayedPermissiveSelection_trans target leftOutput rightRoot ordinal
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
                    simpa only [hrightCandidates]
                  apply relTriple_pure_pure
                  change DelayedPermissiveSelectionRel target leftOutput rightRoot ordinal
                    (some ⟨nextCandidates.get ⟨ordinal, hnextSelected⟩, context,
                      nextCandidates⟩)
                    (some ⟨(permissiveRootAwareCandidates parameter input table
                      (materializedDeferredState context) candidates).get
                        ⟨ordinal, hrightSelected⟩,
                      materializedDeferredState context,
                      permissiveRootAwareCandidates parameter input table
                        (materializedDeferredState context) candidates⟩)
                  intro hgood
                  change PrivateOrdinalSelection.GoodForRoots target leftOutput rightRoot ordinal
                    ⟨nextCandidates.get ⟨ordinal, hnextSelected⟩, context,
                      nextCandidates⟩ at hgood
                  apply permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?_eq_some_of_candidate
                  · have hsource := congrArg Probe.coordinate hgood.1
                    change (nextCandidates.get ⟨ordinal, hnextSelected⟩).coordinate =
                      .position target at hsource
                    have hsame := congrArg Probe.coordinate hcandidate.symm
                    exact hsame.trans hsource
                  · exact hroot
                  · simpa [materializedDeferredState] using hgood.2.2.1
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
                    hchainValid hcanonical)
                  intro leftResult rightResult hresult
                  apply relTriple_finishDirect_delayedPermissiveSelection target leftOutput
                    rightRoot ordinal table leftObserve rightObserve nextCandidates
                    (permissiveRootAwareCandidates parameter input table
                      (materializedDeferredState context) candidates)
                    leftResult rightResult hresult
                  intro nextLeft nextRight _hleft _hright hvalue hremaining hvalues hrevealed
                    hnextValid hnextCompletable hnextChainValid hnextCanonical
                  let canonical := canonicalizeMaterializedValues table nextLeft.context
                  have hbase := ih nextLeft.value.1 nextCandidates canonical nextLeft.remaining
                    nextLeft.value.2 hnextValid hnextCompletable hnextChainValid
                      hnextCanonical
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
                    relTriple_delayedPermissiveSelection_trans target leftOutput rightRoot ordinal
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
            apply relTriple_finishDirect_delayedPermissiveSelection target leftOutput rightRoot
              ordinal table leftObserve rightObserve candidates candidates leftResult
                rightResult hresult
            intro nextLeft nextRight _hleft _hright hvalue hremaining hvalues hrevealed
              hnextValid hnextCompletable hnextChainValid hnextCanonical
            let canonical := canonicalizeMaterializedValues table nextLeft.context
            have hbase := ih nextLeft.value.1 candidates canonical nextLeft.remaining
              nextLeft.value.2 hnextValid hnextCompletable hnextChainValid
                hnextCanonical
            have hstate : PermissiveStateRel (materializedDeferredState canonical)
                nextRight.state := ⟨hvalues, hrevealed⟩
            have htransport :=
              relTriple_delayedPermissiveDetailedOrdinalSelection_of_stateRel ordinal parameter
                root ftsSecret (next nextLeft.value.1) candidates candidates
                (materializedDeferredState canonical) nextRight.state nextLeft.remaining table
                nextLeft.value.2 rfl hstate
            simpa only [leftObserve, rightObserve, canonical, ← hvalue, ← hremaining] using
              relTriple_delayedPermissiveSelection_trans target leftOutput rightRoot ordinal
                hbase htransport

noncomputable def delayedPermissiveDetailedSelectionAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    ProbComp (Option PermissivePrivateOrdinalSelection) :=
  delayedPermissiveDetailedOrdinalSelection ordinal parameter rootResult.value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) [] rootResult.state
    rootResult.remaining rootResult.table rootResult.value.2

noncomputable def delayedPermissiveDetailedSelectionExperimentAfterTable
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    ProbComp (Option PermissivePrivateOrdinalSelection) := do
  let rootResult ← rootAwareProductionInitialRun fuel table
  match rootResult with
  | none => pure none
  | some result =>
      delayedPermissiveDetailedSelectionAfterRootResult ordinal adversary parameter ftsSecret result

end SphincsSecurity.Concrete.OtsProbeSimulation
