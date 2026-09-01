import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootComparison

/-!
# Eager layer-root selection

The source selector may learn its selected layer root lazily during an earlier signer or structural
computation. The materialized comparison samples that root before the retained run. This file
connects the two schedules while retaining the installed root in the comparison state.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

def privateOrdinalSelectionGoodForSomeRoot
    (target : Position) (rightRoot : Digest) (ordinal : Nat) :
    Option PrivateOrdinalSelection → Prop
  | none => False
  | some selection => ∃ output,
      selection.GoodForRoots target output rightRoot ordinal

def RootSelectionSomeOutputBridgeRel
    (target : Position) (leftOutput : HashOutput) (rightRoot : Digest) (ordinal : Nat) :
    Option PrivateOrdinalSelection → MaterializedSelectionOutcome → Prop :=
  fun left right =>
    privateOrdinalSelectionGoodForSomeRoot target rightRoot ordinal left →
      right.isFailure ∨ right.Matches target (truncateHash leftOutput)

theorem PrivateOrdinalSelection.goodForStoredRoot
    {table : OtsSecretIndex → HashOutput}
    {selection : PrivateOrdinalSelection} {right : DeferredContext}
    {target : Position} {output leftOutput : HashOutput} {rightRoot : Digest} {ordinal : Nat}
    (hgood : selection.GoodForRoots target output rightRoot ordinal)
    (hcontext : FinalizationContextLE table selection.context right)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hstored : right.state.values (.position target) = some leftOutput) :
    selection.GoodForRoots target leftOutput rightRoot ordinal := by
  have hleftResolved :
      resolvedCompletionValue table selection.context (.position target) = some output := by
    simp [resolvedCompletionValue, DeferredContext.positionValue, hgood.2.1, hgood.2.2.2.1]
  have hrightResolved : resolvedCompletionValue table right (.position target) = some output := by
    rw [← hcontext.view.valueEq]
    exact hleftResolved
  have hrightValue : right.state.values (.position target) = some output := by
    rw [hrightMaterialized] at hrightResolved
    change (match right.state.values (.position target) with
      | some value => some value
      | none => right.state.values (.position target)) = some output at hrightResolved
    cases hvalue : right.state.values (.position target) with
    | none => simp [hvalue] at hrightResolved
    | some value => simpa [hvalue] using hrightResolved
  have houtput : output = leftOutput := by
    rw [hstored] at hrightValue
    exact (Option.some.inj hrightValue).symm
  simpa [houtput] using hgood

theorem relTriple_pure_none_rootSelectionSomeOutputBridge
    (target : Position) (leftOutput : HashOutput) (rightRoot : Digest) (ordinal : Nat)
    (right : ProbComp MaterializedSelectionOutcome) :
    RelTriple (pure none : ProbComp (Option PrivateOrdinalSelection)) right
      (RootSelectionSomeOutputBridgeRel target leftOutput rightRoot ordinal) := by
  have hbase := relTriple_true
    (pure none : ProbComp (Option PrivateOrdinalSelection)) right
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun value => value = none) (by intro value hvalue; simpa using hvalue)
  apply relTriple_post_mono hsupported
  intro left _right hrelation hgood
  rw [hrelation.2] at hgood
  exact False.elim hgood

theorem relTriple_any_failed_rootSelectionSomeOutputBridge
    (target : Position) (leftOutput : HashOutput) (rightRoot : Digest) (ordinal : Nat)
    (left : ProbComp (Option PrivateOrdinalSelection)) :
    RelTriple left (pure .failed : ProbComp MaterializedSelectionOutcome)
      (RootSelectionSomeOutputBridgeRel target leftOutput rightRoot ordinal) := by
  have hbase := relTriple_true left
    (pure .failed : ProbComp MaterializedSelectionOutcome)
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hbase
  apply relTriple_post_mono hsupported
  intro _left right hrelation _hgood
  have hright : right = .failed := by simpa using hrelation.2
  subst right
  exact Or.inl trivial

theorem stateValue_of_done_runDirectResolvedDetailedFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (target : Position) (output : HashOutput)
    (hvalue : context.state.values (.position target) = some output)
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table computation)) :
    result.context.state.values (.position target) = some output := by
  exact valuesLE_of_done_runDirectResolvedDetailedFromTable computation context fuel table result
    hresult (.position target) output hvalue

set_option maxRecDepth 100000 in
theorem relTriple_finishRootSelectionSomeOutputBridge
    (target : Position) (leftOutput : HashOutput) (rightRoot : Digest)
    (ordinal : Nat) (table : OtsSecretIndex → HashOutput)
    (leftObserve : DeferredContext → Nat → (α × SplitHashCache) → List Probe →
      ProbComp (Option PrivateOrdinalSelection))
    (rightObserve : LazyRevealProbe.State Coordinate → Nat → α → SplitHashCache →
      List Probe → ProbComp MaterializedSelectionOutcome)
    (candidates : List Probe)
    (leftResult rightResult : DirectDetailedResult (α × SplitHashCache))
    (hrelation : DirectDetailedOrdinaryStableRunEq table leftResult rightResult)
    (hrightSupport : rightResult ∈ support rightRun)
    (initialRight : DeferredContext) (rightFuel : Nat)
    (rightComputation : OracleComp (LazyRevealProbe.World Coordinate) (α × SplitHashCache))
    (hstored : initialRight.state.values (.position target) = some leftOutput)
    (hrightRun : rightRun =
      runDirectResolvedDetailedFromTable initialRight rightFuel table rightComputation)
    (hrecursive : ∀ originalLeft originalRight left right,
      leftResult = .done originalLeft → rightResult = .done originalRight →
      OrdinaryMaterializedRunEq table left right →
      CanonicalMaterializedValues table left.context →
      right.context.state.values (.position target) = some leftOutput →
      RelTriple
        (leftObserve left.context left.remaining left.value candidates)
        (rightObserve right.context.state right.remaining right.value.1 right.value.2 candidates)
        (RootSelectionSomeOutputBridgeRel target leftOutput rightRoot ordinal)) :
    RelTriple
      (finishDirectDetailedPrivateOrdinalSelection
        (canonicalizeDirectPrivateOrdinalSelection table leftObserve) candidates leftResult)
      (finishMaterializedSelectionOutcome target table rightObserve candidates rightResult)
      (RootSelectionSomeOutputBridgeRel target leftOutput rightRoot ordinal) := by
  cases leftResult with
  | stopped leftReason =>
      exact relTriple_pure_none_rootSelectionSomeOutputBridge target leftOutput rightRoot ordinal _
  | done left =>
      cases rightResult with
      | stopped rightReason =>
          exact relTriple_any_failed_rootSelectionSomeOutputBridge target leftOutput rightRoot
            ordinal _
      | done right =>
          have hrightValue : right.context.state.values (.position target) = some leftOutput := by
            rw [hrightRun] at hrightSupport
            exact stateValue_of_done_runDirectResolvedDetailedFromTable rightComputation
              initialRight rightFuel table right target leftOutput hstored hrightSupport
          rcases hrelation with hclean | hdoomed
          · have hcanonical := hclean.canonicalize_left
            let canonical := canonicalizeMaterializedValues table left.context
            have hleftCompletable : DeferredCompletable table canonical :=
              hcanonical.context_le.leftCompletable
            have hnotPrivate : ¬PrivateStructuralHit canonical :=
              not_privateStructuralHit_of_deferredCompletable hleftCompletable
            have hrightCompletable :
                DeferredCompletable table (directDeferredContext right.context.state) := by
              rw [← hclean.right_materialized]
              exact hclean.context_le.rightCompletable
            unfold finishDirectDetailedPrivateOrdinalSelection
              finishMaterializedSelectionOutcome
            unfold canonicalizeDirectPrivateOrdinalSelection
            simp only [canonical, hnotPrivate, ↓reduceIte, hclean.left_published, ↓reduceIte,
              hleftCompletable, hrightCompletable]
            have hrevealed : canonical.state.revealed = right.context.state.revealed :=
              hcanonical.revealed_eq
            by_cases htargetRevealed : Coordinate.position target ∈ canonical.state.revealed
            · have hrightRevealed :
                  Coordinate.position target ∈ right.context.state.revealed := by
                rw [← hrevealed]
                exact htargetRevealed
              simp only [hrightRevealed, ↓reduceIte]
              exact relTriple_any_failed_rootSelectionSomeOutputBridge target leftOutput rightRoot
                ordinal _
            · have hrightRevealed :
                  Coordinate.position target ∉ right.context.state.revealed := by
                intro hmem
                exact htargetRevealed (by rwa [hrevealed])
              simp only [hrightRevealed, ↓reduceIte]
              have hcanonicalValues : CanonicalMaterializedValues table canonical :=
                canonicalizeMaterializedValues_canonical table left.context
                  hclean.context_le.view.leftConsistent
              exact hrecursive left right { left with context := canonical } right rfl rfl
                hcanonical hcanonicalValues hrightValue
          · unfold finishMaterializedSelectionOutcome
            have hnotCompletable :
                ¬DeferredCompletable table (directDeferredContext right.context.state) := by
              rw [← hdoomed.2]
              exact hdoomed.1.2.2.2
            simp only [hnotCompletable, ↓reduceIte]
            exact relTriple_any_failed_rootSelectionSomeOutputBridge target leftOutput rightRoot
              ordinal _

set_option maxRecDepth 100000 in
theorem relTriple_rootSelectionSomeOutput_step
    (target : Position) (leftOutput : HashOutput) (rightRoot : Digest)
    (ordinal : Nat) (table : OtsSecretIndex → HashOutput)
    (leftObserve : DeferredContext → Nat → (α × SplitHashCache) → List Probe →
      ProbComp (Option PrivateOrdinalSelection))
    (rightObserve : LazyRevealProbe.State Coordinate → Nat → α → SplitHashCache →
      List Probe → ProbComp MaterializedSelectionOutcome)
    (candidates : List Probe)
    (leftWitnessRun : ProbComp (DirectWitnessResult (α × SplitHashCache)))
    (leftDetailedRun rightRun : ProbComp (DirectDetailedResult (α × SplitHashCache)))
    (hleft : evalDist
        (leftWitnessRun >>= finishDirectPrivateOrdinalSelection
          (canonicalizeDirectPrivateOrdinalSelection table leftObserve) candidates) =
      evalDist
        (leftDetailedRun >>= finishDirectDetailedPrivateOrdinalSelection
          (canonicalizeDirectPrivateOrdinalSelection table leftObserve) candidates))
    (hstep : RelTriple leftDetailedRun rightRun (DirectDetailedOrdinaryStableRunEq table))
    (initialRight : DeferredContext) (rightFuel : Nat)
    (rightComputation : OracleComp (LazyRevealProbe.World Coordinate) (α × SplitHashCache))
    (hrightRun : rightRun =
      runDirectResolvedDetailedFromTable initialRight rightFuel table rightComputation)
    (hstored : initialRight.state.values (.position target) = some leftOutput)
    (hrecursive : ∀ left right,
      OrdinaryMaterializedRunEq table left right →
      CanonicalMaterializedValues table left.context →
      right.context.state.values (.position target) = some leftOutput →
      RelTriple
        (leftObserve left.context left.remaining left.value candidates)
        (rightObserve right.context.state right.remaining right.value.1 right.value.2 candidates)
        (RootSelectionSomeOutputBridgeRel target leftOutput rightRoot ordinal)) :
    RelTriple
      (leftWitnessRun >>= finishDirectPrivateOrdinalSelection
        (canonicalizeDirectPrivateOrdinalSelection table leftObserve) candidates)
      (rightRun >>= finishMaterializedSelectionOutcome target table rightObserve candidates)
      (RootSelectionSomeOutputBridgeRel target leftOutput rightRoot ordinal) := by
  apply relTriple_of_evalDist_eq_left hleft
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hstep
  apply relTriple_bind hsupported
  intro leftResult rightResult hrelation
  exact relTriple_finishRootSelectionSomeOutputBridge target leftOutput rightRoot ordinal table
    leftObserve rightObserve candidates leftResult rightResult hrelation.1 hrelation.2 initialRight
    rightFuel rightComputation hstored hrightRun
    (by
      intro _originalLeft _originalRight left right _hleft _hright hnext hcanonical hvalue
      exact hrecursive left right hnext hcanonical hvalue)

noncomputable def candidateFinalizationObserve
    (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (fuel : Nat) (candidate : Probe) : ProbComp Bool :=
  runResolvedObserve (resolvedFinalizationObserve table) context (fuel + 1) table (do
    (probe candidate).run emptySplitHashCache)

theorem evalDist_candidateFinalizationObserve_eq_true_of_goodForRoots
    (table : OtsSecretIndex → HashOutput)
    (selection : PrivateOrdinalSelection) (fuel : Nat)
    (target : Position) (output : HashOutput) (rightRoot : Digest) (ordinal : Nat)
    (hvalid : selection.context.Valid)
    (hcompletable : DeferredCompletable table selection.context)
    (hgood : selection.GoodForRoots target output rightRoot ordinal) :
    evalDist (candidateFinalizationObserve table selection.context fuel selection.candidate) =
      evalDist (pure true : ProbComp Bool) := by
  have hstarts := startTableAgrees_of_deferredCompletable hcompletable
  obtain ⟨completion, hcompletion⟩ := hcompletable
  have hdoomed : ¬DeferredCompletable table
      { selection.context with
        state := selection.context.state.addPending
          (.position target) (truncateHash output) } := by
    simpa using not_congr
      (deferredCompletable_addPending_position_iff target output (truncateHash output)
        hcompletion hgood.2.2.2.1)
  unfold candidateFinalizationObserve
  rw [show selection.candidate = ⟨.position target, truncateHash output⟩ from hgood.1]
  unfold probe
  rw [StateT.run_liftM, LazyRevealProbe.probeQuery,
    runResolvedObserve, runResolvedFromTable_probe_query_bind]
  simp only [hgood.2.2.1, ↓reduceIte]
  exact evalDist_runResolvedObserve_eq_true_of_not_completable_auto
    { selection.context with
      state := selection.context.state.addPending (.position target) (truncateHash output) }
    fuel table (pure ((), emptySplitHashCache))
    (hvalid.valuesConsistent.addPending (.position target) (truncateHash output))
    (hstarts.addPending (.position target) (truncateHash output)) hdoomed

instance candidateFinalizationObserve_observerDooms
    (table : OtsSecretIndex → HashOutput) :
    ObserverDooms table (candidateFinalizationObserve table) where
  eq_true context fuel candidate hconsistent hstarts hdoomed := by
    exact evalDist_runResolvedObserve_eq_true_of_not_completable_auto
      (observe := resolvedFinalizationObserve table) context (fuel + 1) table
      ((probe candidate).run emptySplitHashCache) hconsistent hstarts hdoomed

instance candidateFinalizationObserve_observerSynchronized
    (table : OtsSecretIndex → HashOutput) :
    ObserverSynchronized table (candidateFinalizationObserve table) where
  eq_of_synchronized left right fuel candidate hcontext hvalues hrevealed := by
    exact evalDist_runResolvedObserve_eq_of_finalizationSynchronized
      (observe := resolvedFinalizationObserve table)
      ((probe candidate).run emptySplitHashCache) left right (fuel + 1) table hcontext
      hvalues hrevealed

instance candidateFinalizationObserve_observerPositionNeutral
    (table : OtsSecretIndex → HashOutput) :
    ObserverPositionNeutral table (candidateFinalizationObserve table) where
  eq_resolve position context fuel candidate hvalid hcompletable hensured := by
    exact evalDist_resolveDeferredPositionValue_then_runResolvedObserve_auto position
      (observe := resolvedFinalizationObserve table)
      ((probe candidate).run emptySplitHashCache) context (fuel + 1) table hvalid
      hcompletable hensured

noncomputable def ordinalRootFinalizationObserve
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (rightRoot : Digest) (ordinal : Nat)
    (context : DeferredContext) (fuel : Nat) (candidates : List Probe) : ProbComp Bool := by
  classical
  exact if hselected : ordinal < candidates.length then
    let candidate := candidates.get ⟨ordinal, hselected⟩
    if candidate.coordinate = .position target ∧
        CandidatesAvoidRoot target rightRoot (candidates.take ordinal) then
      candidateFinalizationObserve table context fuel candidate
    else resolvedFinalizationObserve table context fuel ()
  else resolvedFinalizationObserve table context fuel ()

instance ordinalRootFinalizationObserve_observerDooms
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (rightRoot : Digest) (ordinal : Nat) (candidates : List Probe) :
    ObserverDooms table
      (fun context fuel (_value : Unit) =>
        ordinalRootFinalizationObserve table target rightRoot ordinal context fuel candidates) where
  eq_true context fuel _value hconsistent hstarts hdoomed := by
    unfold ordinalRootFinalizationObserve
    by_cases hselected : ordinal < candidates.length
    · simp only [hselected, ↓reduceDIte]
      by_cases hgate :
          (candidates.get ⟨ordinal, hselected⟩).coordinate = .position target ∧
            CandidatesAvoidRoot target rightRoot (candidates.take ordinal)
      · simp only [hgate]
        exact ObserverDooms.eq_true
          (table := table) (observe := candidateFinalizationObserve table)
          context fuel _ hconsistent hstarts hdoomed
      · simp only [hgate]
        exact ObserverDooms.eq_true
          (table := table) (observe := resolvedFinalizationObserve table)
          context fuel () hconsistent hstarts hdoomed
    · simp only [hselected, ↓reduceDIte]
      exact ObserverDooms.eq_true
        (table := table) (observe := resolvedFinalizationObserve table)
        context fuel () hconsistent hstarts hdoomed

instance ordinalRootFinalizationObserve_observerPositionNeutral
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (rightRoot : Digest) (ordinal : Nat) (candidates : List Probe) :
    ObserverPositionNeutral table
      (fun context fuel (_value : Unit) =>
        ordinalRootFinalizationObserve table target rightRoot ordinal context fuel candidates) where
  eq_resolve position context fuel _value hvalid hcompletable hensured := by
    unfold ordinalRootFinalizationObserve
    by_cases hselected : ordinal < candidates.length
    · simp only [hselected, ↓reduceDIte]
      by_cases hgate :
          (candidates.get ⟨ordinal, hselected⟩).coordinate = .position target ∧
            CandidatesAvoidRoot target rightRoot (candidates.take ordinal)
      · simp only [hgate]
        exact ObserverPositionNeutral.eq_resolve
          (table := table) (observe := candidateFinalizationObserve table)
          position context fuel _ hvalid hcompletable hensured
      · simp only [hgate]
        exact ObserverPositionNeutral.eq_resolve
          (table := table) (observe := resolvedFinalizationObserve table)
          position context fuel () hvalid hcompletable hensured
    · simp only [hselected, ↓reduceDIte]
      exact ObserverPositionNeutral.eq_resolve
        (table := table) (observe := resolvedFinalizationObserve table)
        position context fuel () hvalid hcompletable hensured

noncomputable def directBoundaryPrivateOrdinalFinalizationRisk
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) : ProbComp Bool := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp (OracleWorld + SigningSpec) α =>
      List Probe → DeferredContext → Nat → (OtsSecretIndex → HashOutput) →
        SplitHashCache → ProbComp Bool)
    (fun _value candidates context fuel table _cache =>
      ordinalRootFinalizationObserve table target rightRoot ordinal context fuel candidates)
    (fun query _next recursivelyRun candidates context fuel table cache =>
      if hselected : ordinal < candidates.length then
        ordinalRootFinalizationObserve table target rightRoot ordinal context fuel candidates
      else
        match query with
        | .inl (.inl n) =>
            runResolvedObserve
              (canonicalizeObserve table
                (fun nextContext remaining value =>
                  recursivelyRun value.1 candidates nextContext remaining table value.2))
              context fuel table ((splitUniformImpl n).run cache)
        | .inl (.inr input) =>
            let plan := purePlanProbingHashQuery parameter input context.state
            let nextCandidates := appendPlannedCandidate candidates
              (rootAwarePlannedCandidate? parameter input context.state)
            if hnextSelected : ordinal < nextCandidates.length then
              ordinalRootFinalizationObserve table target rightRoot ordinal context fuel
                nextCandidates
            else
              runResolvedObserve
                (canonicalizeObserve table
                  (fun nextContext remaining value =>
                    recursivelyRun value.1 nextCandidates nextContext remaining table value.2))
                context fuel table ((probingHashQueryAfterPlan parameter input plan).run cache)
        | .inr message =>
            runResolvedObserve
              (canonicalizeObserve table
                (fun nextContext remaining value =>
                  recursivelyRun value.1 candidates nextContext remaining table value.2))
              context fuel table ((maskedSign parameter root ftsSecret message).run cache))
    computation candidates context fuel table cache

set_option maxRecDepth 100000 in
theorem directBoundaryPrivateOrdinalFinalizationRisk_dooms
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hdoomed : ¬DeferredCompletable table context) :
    evalDist (directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root ftsSecret
        target rightRoot computation candidates context fuel table cache) =
      evalDist (pure true : ProbComp Bool) := by
  induction computation using OracleComp.inductionOn generalizing
      candidates context fuel cache with
  | pure value =>
      rw [directBoundaryPrivateOrdinalFinalizationRisk, OracleComp.construct_pure]
      exact ObserverDooms.eq_true
        (table := table)
        (observe := fun context fuel (_value : Unit) =>
          ordinalRootFinalizationObserve table target rightRoot ordinal context fuel candidates)
        context fuel () hconsistent hstarts hdoomed
  | query_bind query next ih =>
      rw [directBoundaryPrivateOrdinalFinalizationRisk, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact ObserverDooms.eq_true
          (table := table)
          (observe := fun context fuel (_value : Unit) =>
            ordinalRootFinalizationObserve table target rightRoot ordinal context fuel candidates)
          context fuel () hconsistent hstarts hdoomed
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                let nextObserve : DeferredContext → Nat →
                    (Fin (n + 1) × SplitHashCache) → ProbComp Bool :=
                  fun nextContext remaining value =>
                    directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root ftsSecret
                      target rightRoot (next value.1) candidates nextContext remaining table value.2
                letI : ObserverDooms table nextObserve := ⟨by
                  intro nextContext remaining value hnextConsistent hnextStarts hnextDoomed
                  exact ih value.1 candidates nextContext remaining value.2 hnextConsistent
                    hnextStarts hnextDoomed⟩
                exact evalDist_runResolvedObserve_eq_true_of_not_completable_auto
                  (observe := canonicalizeObserve table nextObserve) context fuel table
                  ((splitUniformImpl n).run cache) hconsistent hstarts hdoomed
            | inr input =>
                let plan := purePlanProbingHashQuery parameter input context.state
                let nextCandidates := appendPlannedCandidate candidates
                  (rootAwarePlannedCandidate? parameter input context.state)
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hactual : ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwarePlannedCandidate? parameter input context.state)).length := by
                    simpa [nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  exact ObserverDooms.eq_true
                    (table := table)
                    (observe := fun context fuel (_value : Unit) =>
                      ordinalRootFinalizationObserve table target rightRoot ordinal context fuel
                        nextCandidates)
                    context fuel () hconsistent hstarts hdoomed
                · have hactual : ¬ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwarePlannedCandidate? parameter input context.state)).length := by
                    simpa [nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  let nextObserve : DeferredContext → Nat →
                      (HashOutput × SplitHashCache) → ProbComp Bool :=
                    fun nextContext remaining value =>
                      directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root
                        ftsSecret target rightRoot (next value.1) nextCandidates nextContext
                        remaining table value.2
                  letI : ObserverDooms table nextObserve := ⟨by
                    intro nextContext remaining value hnextConsistent hnextStarts hnextDoomed
                    exact ih value.1 nextCandidates nextContext remaining value.2 hnextConsistent
                      hnextStarts hnextDoomed⟩
                  exact evalDist_runResolvedObserve_eq_true_of_not_completable_auto
                    (observe := canonicalizeObserve table nextObserve) context fuel table
                    ((probingHashQueryAfterPlan parameter input plan).run cache)
                    hconsistent hstarts hdoomed
        | inr message =>
            let nextObserve : DeferredContext → Nat →
                (Option Signature × SplitHashCache) → ProbComp Bool :=
              fun nextContext remaining value =>
                directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root ftsSecret
                  target rightRoot (next value.1) candidates nextContext remaining table value.2
            letI : ObserverDooms table nextObserve := ⟨by
              intro nextContext remaining value hnextConsistent hnextStarts hnextDoomed
              exact ih value.1 candidates nextContext remaining value.2 hnextConsistent
                hnextStarts hnextDoomed⟩
            exact evalDist_runResolvedObserve_eq_true_of_not_completable_auto
              (observe := canonicalizeObserve table nextObserve) context fuel table
              ((maskedSign parameter root ftsSecret message).run cache)
              hconsistent hstarts hdoomed

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem evalDist_resolveDeferredPositionValue_then_directBoundaryPrivateOrdinalFinalizationRisk
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rightRoot : Digest)
    (position : Position)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hensured : Coordinate.position position ∈ context.state.ensured) :
    evalDist (resolveDeferredPositionValue position context >>= fun resolved =>
      match resolved with
      | none => pure true
      | some resolved =>
          directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root ftsSecret target
            rightRoot computation candidates resolved.toDeferredContext fuel table cache) =
      evalDist (directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root ftsSecret
        target rightRoot computation candidates context fuel table cache) := by
  induction computation using OracleComp.inductionOn generalizing
      candidates context fuel cache position with
  | pure value =>
      rw [directBoundaryPrivateOrdinalFinalizationRisk, OracleComp.construct_pure]
      exact ObserverPositionNeutral.eq_resolve
        (table := table)
        (observe := fun context fuel (_value : Unit) =>
          ordinalRootFinalizationObserve table target rightRoot ordinal context fuel candidates)
        position context fuel () hvalid hcompletable hensured
  | query_bind query next ih =>
      by_cases hselected : ordinal < candidates.length
      · simp only [directBoundaryPrivateOrdinalFinalizationRisk,
          OracleComp.construct_query_bind, hselected, ↓reduceDIte]
        exact ObserverPositionNeutral.eq_resolve
          (table := table)
          (observe := fun context fuel (_value : Unit) =>
            ordinalRootFinalizationObserve table target rightRoot ordinal context fuel candidates)
          position context fuel () hvalid hcompletable hensured
      · cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                simp only [directBoundaryPrivateOrdinalFinalizationRisk,
                  OracleComp.construct_query_bind, hselected, ↓reduceDIte]
                let nextObserve : DeferredContext → Nat →
                    (Fin (n + 1) × SplitHashCache) → ProbComp Bool :=
                  fun nextContext remaining value =>
                    directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root ftsSecret
                      target rightRoot (next value.1) candidates nextContext remaining table value.2
                letI : ObserverDooms table nextObserve := ⟨by
                  intro nextContext remaining value hnextConsistent hnextStarts hnextDoomed
                  exact directBoundaryPrivateOrdinalFinalizationRisk_dooms ordinal parameter root
                    ftsSecret target rightRoot (next value.1) candidates nextContext remaining table
                    value.2 hnextConsistent hnextStarts hnextDoomed⟩
                letI : ObserverPositionNeutral table nextObserve := ⟨by
                  intro position nextContext remaining value hnextValid hnextCompletable
                    hnextEnsured
                  exact ih value.1 position candidates nextContext remaining value.2 hnextValid
                    hnextCompletable hnextEnsured⟩
                have hmove :=
                  evalDist_resolveDeferredPositionValue_then_runResolvedObserve_auto position
                    (observe := canonicalizeObserve table nextObserve)
                    ((splitUniformImpl n).run cache) context fuel table hvalid hcompletable hensured
                exact hmove
            | inr input =>
                let plan := purePlanProbingHashQuery parameter input context.state
                let nextCandidates := appendPlannedCandidate candidates
                  (rootAwarePlannedCandidate? parameter input context.state)
                let nextObserve : DeferredContext → Nat →
                    (HashOutput × SplitHashCache) → ProbComp Bool :=
                  fun nextContext remaining value =>
                    directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root ftsSecret
                      target rightRoot (next value.1) nextCandidates nextContext remaining table
                      value.2
                have hnormalize : evalDist (resolveDeferredPositionValue position context >>=
                    fun resolved => match resolved with
                    | none => pure true
                    | some resolved =>
                        if hnextSelected : ordinal < nextCandidates.length then
                          ordinalRootFinalizationObserve table target rightRoot ordinal
                            resolved.toDeferredContext fuel nextCandidates
                        else runResolvedObserve (canonicalizeObserve table nextObserve)
                          resolved.toDeferredContext fuel table
                          ((probingHashQueryAfterPlan parameter input plan).run cache)) =
                    evalDist (resolveDeferredPositionValue position context >>= fun resolved =>
                      match resolved with
                      | none => pure true
                      | some resolved =>
                          directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root
                            ftsSecret target rightRoot
                            (liftM (OracleSpec.query (Sum.inl (Sum.inr input))) >>= next)
                            candidates resolved.toDeferredContext fuel table cache) := by
                  apply evalDist_bind_congr
                  intro resolved hresolved
                  cases resolved with
                  | none => rfl
                  | some resolved =>
                      have hvalues := resolveDeferredPositionValue_preserves_state_values position
                        context resolved hresolved
                      have hplan : purePlanProbingHashQuery parameter input resolved.state = plan := by
                        simpa [plan] using
                          (purePlanProbingHashQuery_eq_of_values_eq hvalues parameter input)
                      have hcandidate :
                          rootAwarePlannedCandidate? parameter input resolved.state =
                            rootAwarePlannedCandidate? parameter input context.state := by
                        unfold rootAwarePlannedCandidate?
                        rw [hplan]
                      simp only [directBoundaryPrivateOrdinalFinalizationRisk,
                        OracleComp.construct_query_bind, hselected, ↓reduceDIte, hplan, hcandidate]
                      rfl
                rw [← hnormalize]
                rw [directBoundaryPrivateOrdinalFinalizationRisk,
                  OracleComp.construct_query_bind]
                simp only [hselected, ↓reduceDIte]
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hactual : ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwarePlannedCandidate? parameter input context.state)).length := by
                    simpa [nextCandidates] using hnextSelected
                  simp only [hnextSelected, hactual, ↓reduceDIte]
                  have hneutral := ObserverPositionNeutral.eq_resolve
                    (table := table)
                    (observe := fun context fuel (_value : Unit) =>
                      ordinalRootFinalizationObserve table target rightRoot ordinal context fuel
                        nextCandidates)
                    position context fuel () hvalid hcompletable hensured
                  exact hneutral
                · have hactual : ¬ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwarePlannedCandidate? parameter input context.state)).length := by
                    simpa [nextCandidates] using hnextSelected
                  simp only [hnextSelected, hactual, ↓reduceDIte]
                  letI : ObserverDooms table nextObserve := ⟨by
                    intro nextContext remaining value hnextConsistent hnextStarts hnextDoomed
                    exact directBoundaryPrivateOrdinalFinalizationRisk_dooms ordinal parameter root
                      ftsSecret target rightRoot (next value.1) nextCandidates nextContext remaining
                      table value.2 hnextConsistent hnextStarts hnextDoomed⟩
                  letI : ObserverPositionNeutral table nextObserve := ⟨by
                    intro nextPosition nextContext remaining value hnextValid hnextCompletable
                      hnextEnsured
                    exact ih value.1 nextPosition nextCandidates nextContext remaining value.2
                      hnextValid hnextCompletable hnextEnsured⟩
                  have hmove :=
                    evalDist_resolveDeferredPositionValue_then_runResolvedObserve_auto position
                      (observe := canonicalizeObserve table nextObserve)
                      ((probingHashQueryAfterPlan parameter input plan).run cache) context fuel table
                      hvalid hcompletable hensured
                  exact hmove
        | inr message =>
            simp only [directBoundaryPrivateOrdinalFinalizationRisk,
              OracleComp.construct_query_bind, hselected, ↓reduceDIte]
            let nextObserve : DeferredContext → Nat →
                (Option Signature × SplitHashCache) → ProbComp Bool :=
              fun nextContext remaining value =>
                directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root ftsSecret
                  target rightRoot (next value.1) candidates nextContext remaining table value.2
            letI : ObserverDooms table nextObserve := ⟨by
              intro nextContext remaining value hnextConsistent hnextStarts hnextDoomed
              exact directBoundaryPrivateOrdinalFinalizationRisk_dooms ordinal parameter root
                ftsSecret target rightRoot (next value.1) candidates nextContext remaining table
                value.2 hnextConsistent hnextStarts hnextDoomed⟩
            letI : ObserverPositionNeutral table nextObserve := ⟨by
              intro position nextContext remaining value hnextValid hnextCompletable hnextEnsured
              exact ih value.1 position candidates nextContext remaining value.2 hnextValid
                hnextCompletable hnextEnsured⟩
            have hmove :=
              evalDist_resolveDeferredPositionValue_then_runResolvedObserve_auto position
                (observe := canonicalizeObserve table nextObserve)
                ((maskedSign parameter root ftsSecret message).run cache) context fuel table hvalid
                hcompletable hensured
            exact hmove

end SphincsSecurity.Concrete.OtsProbeSimulation
