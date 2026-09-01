import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedSelectorCoupling

/-!
# Non-root stopped ordinal projection

A selected stopped snapshot at a non-root position makes the existing non-root candidate observer
fire. This module connects the exact ordinal selector to that observer before lifting its one-unit
bound through public-root construction and table sampling.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false

noncomputable def privateOrdinalSelectionNonRootFire :
    Option PrivateOrdinalSelection → ProbComp Bool
  | none => pure false
  | some selection =>
      nonRootHiddenPrivateCandidateFire selection.candidate selection.context

theorem privateOrdinalSelectionNonRootFire_eq_true_of_goodForActualRoot
    (selection : PrivateOrdinalSelection) (target : Position) (output : HashOutput)
    (ordinal : Nat)
    (hgood : selection.GoodForActualRoot target output ordinal)
    (hnonRoot : ¬IsLayerRoot target) :
    privateOrdinalSelectionNonRootFire (some selection) = pure true := by
  unfold privateOrdinalSelectionNonRootFire nonRootHiddenPrivateCandidateFire
  have hcoordinate : selection.candidate.coordinate = .position target := by
    rw [hgood.1]
  have hcandidateRoot : ¬selection.candidate.IsLayerRoot := by
    simpa [Probe.IsLayerRoot, hcoordinate] using hnonRoot
  change (if selection.candidate.IsLayerRoot then pure false
    else hiddenPrivateCandidateFire selection.candidate selection.context) = pure true
  rw [if_neg hcandidateRoot]
  rw [hiddenPrivateCandidateFire_of_not_revealed selection.candidate selection.context (by
    simpa [hcoordinate] using hgood.2.2.1)]
  unfold privateCandidateFire deferredPositionOutput DeferredContext.positionValue
  rw [hgood.1]
  simp [hgood.2.1, hgood.2.2.2.1]

theorem finishDirectPrivateOrdinalSelection_bind_nonRootFire
    (selectionObserve : DeferredContext → Nat → α → List Probe →
      ProbComp (Option PrivateOrdinalSelection))
    (riskObserve : DeferredContext → Nat → α → List Probe → ProbComp Bool)
    (candidates : List Probe) (result : DirectWitnessResult α)
    (hobserve : ∀ context fuel value laterCandidates,
      selectionObserve context fuel value laterCandidates >>=
          privateOrdinalSelectionNonRootFire =
        riskObserve context fuel value laterCandidates) :
    finishDirectPrivateOrdinalSelection selectionObserve candidates result >>=
        privateOrdinalSelectionNonRootFire =
      finishDirectWitnessOrdinalRisk riskObserve candidates result := by
  cases result with
  | stoppedFuel => simp [finishDirectPrivateOrdinalSelection,
      finishDirectWitnessOrdinalRisk, privateOrdinalSelectionNonRootFire]
  | stoppedOrdinary => simp [finishDirectPrivateOrdinalSelection,
      finishDirectWitnessOrdinalRisk, privateOrdinalSelectionNonRootFire]
  | stoppedPrivate witness => simp [finishDirectPrivateOrdinalSelection,
      finishDirectWitnessOrdinalRisk, privateOrdinalSelectionNonRootFire]
  | done result =>
      simpa [finishDirectPrivateOrdinalSelection, finishDirectWitnessOrdinalRisk] using
        hobserve result.context result.remaining result.value candidates

theorem canonicalizeDirectPrivateOrdinalSelection_bind_nonRootFire
    (table : OtsSecretIndex → HashOutput)
    (selectionObserve : DeferredContext → Nat → α → List Probe →
      ProbComp (Option PrivateOrdinalSelection))
    (riskObserve : DeferredContext → Nat → α → List Probe → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe)
    (hobserve : ∀ nextContext remaining nextValue laterCandidates,
      selectionObserve nextContext remaining nextValue laterCandidates >>=
          privateOrdinalSelectionNonRootFire =
        riskObserve nextContext remaining nextValue laterCandidates) :
    canonicalizeDirectPrivateOrdinalSelection table selectionObserve context fuel value
          candidates >>=
        privateOrdinalSelectionNonRootFire =
      canonicalizeDirectWitnessOrdinalRisk table riskObserve context fuel value candidates := by
  classical
  unfold canonicalizeDirectPrivateOrdinalSelection canonicalizeDirectWitnessOrdinalRisk
  let canonical := canonicalizeMaterializedValues table context
  by_cases hhit : PrivateStructuralHit canonical
  · simp [canonical, hhit, privateOrdinalSelectionNonRootFire]
  · simp only [canonical, hhit, ↓reduceIte]
    by_cases hpublished : PublishedValues context.state
    · simp only [hpublished, ↓reduceIte]
      by_cases hcompletable : DeferredCompletable table canonical
      · simpa [canonical, hcompletable] using hobserve canonical fuel value candidates
      · simp [canonical, hcompletable, privateOrdinalSelectionNonRootFire]
    · simp [hpublished, privateOrdinalSelectionNonRootFire]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem directDetailedBoundaryPrivateOrdinalNonRootRisk_eq_selection_bind_fire
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    directDetailedBoundaryPrivateOrdinalSelection ordinal parameter root ftsSecret computation
          candidates context fuel table cache >>=
        privateOrdinalSelectionNonRootFire =
      directDetailedBoundaryPrivateOrdinalNonRootRisk ordinal parameter root ftsSecret computation
        candidates context fuel table cache := by
  induction computation using OracleComp.inductionOn generalizing
      candidates context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryPrivateOrdinalSelection, OracleComp.construct_pure,
        directDetailedBoundaryPrivateOrdinalNonRootRisk, OracleComp.construct_pure]
      by_cases hselected : ordinal < candidates.length
      · simp [selectedPrivateOrdinal?, hselected, privateOrdinalSelectionNonRootFire]
      · simp [selectedPrivateOrdinal?, hselected, privateOrdinalSelectionNonRootFire]
  | query_bind query next ih =>
      rw [directDetailedBoundaryPrivateOrdinalSelection, OracleComp.construct_query_bind,
        directDetailedBoundaryPrivateOrdinalNonRootRisk, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp [hselected, privateOrdinalSelectionNonRootFire]
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                rw [bind_assoc]
                apply bind_congr
                intro result
                apply finishDirectPrivateOrdinalSelection_bind_nonRootFire
                intro nextContext remaining value laterCandidates
                apply canonicalizeDirectPrivateOrdinalSelection_bind_nonRootFire
                intro finalContext finalRemaining finalValue finalCandidates
                exact ih finalValue.1 finalCandidates finalContext finalRemaining finalValue.2
            | inr input =>
                let nextCandidates := appendPlannedCandidate candidates
                  (rootAwarePlannedCandidate? parameter input context.state)
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hactual : ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwarePlannedCandidate? parameter input context.state)).length := by
                    simpa [nextCandidates] using hnextSelected
                  simp [hactual, privateOrdinalSelectionNonRootFire]
                · have hactual : ¬ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwarePlannedCandidate? parameter input context.state)).length := by
                    simpa [nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  rw [bind_assoc]
                  apply bind_congr
                  intro result
                  apply finishDirectPrivateOrdinalSelection_bind_nonRootFire
                  intro nextContext remaining value laterCandidates
                  apply canonicalizeDirectPrivateOrdinalSelection_bind_nonRootFire
                  intro finalContext finalRemaining finalValue finalCandidates
                  exact ih finalValue.1 finalCandidates finalContext finalRemaining finalValue.2
        | inr message =>
            rw [bind_assoc]
            apply bind_congr
            intro result
            apply finishDirectPrivateOrdinalSelection_bind_nonRootFire
            intro nextContext remaining value laterCandidates
            apply canonicalizeDirectPrivateOrdinalSelection_bind_nonRootFire
            intro finalContext finalRemaining finalValue finalCandidates
            exact ih finalValue.1 finalCandidates finalContext finalRemaining finalValue.2

noncomputable def granularAllCanonicalPrivateOrdinalSelection
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp (Option PrivateOrdinalSelection) :=
  runDirectResolvedWitnessFromTable emptyWitnessDeferredContext fuel table
      (maskedPublishedTreeRoot.run emptySplitHashCache) >>=
    finishDirectPrivateOrdinalSelection
      (canonicalizeDirectPrivateOrdinalSelection table
        (fun context remaining value candidates =>
          directDetailedBoundaryPrivateOrdinalSelection ordinal parameter value.1 ftsSecret
            (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
            candidates context remaining table value.2)) []

attribute [local irreducible] maskedPublishedTreeRoot in
set_option maxRecDepth 100000 in
theorem privateOrdinalSelectionPendingCovered_of_mem_granularAllCanonical
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (output : Option PrivateOrdinalSelection)
    (houtput : output ∈ support
      (granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter table ftsSecret
        fuel)) :
    PrivateOrdinalSelectionPendingCovered ordinal output := by
  unfold granularAllCanonicalPrivateOrdinalSelection at houtput
  rw [mem_support_bind_iff] at houtput
  obtain ⟨result, hresult, hfinish⟩ := houtput
  apply privateOrdinalSelectionPendingCovered_of_mem_finish ordinal _ [] result
    (output := output) (houtput := hfinish)
  intro resolved nextOutput heq hnextOutput
  subst result
  have hdetailed : DirectDetailedResult.done resolved ∈ support
      (runDirectResolvedDetailedFromTable emptyWitnessDeferredContext fuel table
        (maskedPublishedTreeRoot.run emptySplitHashCache)) := by
    rw [← map_erase_runDirectResolvedWitnessFromTable
      (maskedPublishedTreeRoot.run emptySplitHashCache) emptyWitnessDeferredContext fuel table,
      support_map]
    exact ⟨DirectWitnessResult.done resolved, hresult, rfl⟩
  have hprobeBound : (maskedPublishedTreeRoot.run emptySplitHashCache).IsQueryBoundP
      (IsUncoveredProbe []) 0 :=
    OracleComp.IsQueryBoundP.of_imp (isUncoveredProbe_imp_isProbe [])
      (maskedPublishedTreeRoot_probeFree emptySplitHashCache)
  have hnextCovered := pendingCoveredBy_of_done_runDirectResolvedDetailedFromTable []
    (maskedPublishedTreeRoot.run emptySplitHashCache) emptyWitnessDeferredContext fuel table
      resolved pendingCoveredBy_empty hprobeBound hdetailed
  apply privateOrdinalSelectionPendingCovered_of_mem_canonicalize ordinal table _
    resolved.context resolved.remaining resolved.value [] _ hnextCovered nextOutput hnextOutput
  intro nextContext finalOutput hfinalCovered hfinalOutput
  exact privateOrdinalSelectionPendingCovered_of_mem_direct ordinal parameter resolved.value.1
    ftsSecret (retainedGameRestComputation adversary ⟨resolved.value.1, parameter⟩) []
    nextContext resolved.remaining table resolved.value.2 hfinalCovered (by simp) finalOutput
    hfinalOutput

noncomputable def granularAllCanonicalPrivateOrdinalNonRootRisk
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) : ProbComp Bool :=
  runDirectResolvedWitnessFromTable emptyWitnessDeferredContext fuel table
      (maskedPublishedTreeRoot.run emptySplitHashCache) >>=
    finishDirectWitnessOrdinalRisk
      (canonicalizeDirectWitnessOrdinalRisk table
        (fun context remaining value candidates =>
          directDetailedBoundaryPrivateOrdinalNonRootRisk ordinal parameter value.1 ftsSecret
            (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
            candidates context remaining table value.2)) []

theorem granularAllCanonicalPrivateOrdinalSelection_bind_nonRootFire
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter table ftsSecret fuel >>=
        privateOrdinalSelectionNonRootFire =
      granularAllCanonicalPrivateOrdinalNonRootRisk ordinal adversary parameter table ftsSecret
        fuel := by
  unfold granularAllCanonicalPrivateOrdinalSelection
    granularAllCanonicalPrivateOrdinalNonRootRisk
  rw [bind_assoc]
  apply bind_congr
  intro result
  apply finishDirectPrivateOrdinalSelection_bind_nonRootFire
  intro context remaining value candidates
  apply canonicalizeDirectPrivateOrdinalSelection_bind_nonRootFire
  intro nextContext nextRemaining nextValue nextCandidates
  exact directDetailedBoundaryPrivateOrdinalNonRootRisk_eq_selection_bind_fire ordinal parameter
    nextValue.1 ftsSecret (retainedGameRestComputation adversary ⟨nextValue.1, parameter⟩)
    nextCandidates nextContext nextRemaining table nextValue.2

attribute [local irreducible] maskedPublishedTreeRoot in
set_option maxRecDepth 100000 in
theorem candidatePositionsFreshExceptLayerRoots_of_done_maskedPublishedTreeRoot
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (result : ResolvedRunResult (Digest × SplitHashCache))
    (hresult : DirectWitnessResult.done result ∈ support
      (runDirectResolvedWitnessFromTable emptyWitnessDeferredContext fuel table
        (maskedPublishedTreeRoot.run emptySplitHashCache))) :
    CandidatePositionsFreshExceptLayerRoots
      (canonicalizeMaterializedValues table result.context) := by
  let computation := maskedPublishedTreeRoot.run emptySplitHashCache
  have hdetailed : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable emptyWitnessDeferredContext fuel table computation) := by
    rw [← map_erase_runDirectResolvedWitnessFromTable computation emptyWitnessDeferredContext fuel
      table, support_map]
    exact ⟨DirectWitnessResult.done result, hresult, rfl⟩
  have hdirect := mem_support_runDirectResolvedFromTable_of_done_detailed computation
    emptyWitnessDeferredContext fuel table result hdetailed
  have hraw := raw_done_of_mem_runDirectResolvedFromTable computation
    emptyWitnessDeferredContext fuel table result hdirect
  intro position parent hparent hhidden
  by_cases hroot : IsLayerRoot position
  · exact Or.inr hroot
  · left
    have hne : position ≠ layerRootPosition topLayer rootTree := by
      intro heq
      exact hroot ⟨topLayer, rootTree, heq⟩
    have hpreserves := preservesCoordinate_maskedPublishedTreeRoot_of_ne position hne
    have hsame := hpreserves
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) emptySplitHashCache fuel
      result.context.state result.remaining result.value.1 result.value.2 hraw
    have hstate : result.context.state.values (.position position) = none := by
      rw [hsame.1]
      rfl
    have hprivate : result.context.values position = none :=
      auxiliaryPositionValue_none_of_done_runDirectResolvedWitnessFromTable position computation
        emptyWitnessDeferredContext fuel table result (by rfl) (by
          simp [emptyWitnessDeferredContext, emptyDeferredStructuralValues]) hresult hstate
    have hfinalHidden : Coordinate.position position ∉ result.context.state.revealed := by
      simpa [canonicalizeMaterializedValues_revealed] using hhidden
    constructor
    · unfold canonicalizeMaterializedValues publicMaterializedValues
      simp [hfinalHidden]
    · exact hprivate

attribute [local irreducible] maskedPublishedTreeRoot in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_granularAllCanonicalPrivateOrdinalNonRootRisk_le
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[fun hit : Bool => hit = true |
        granularAllCanonicalPrivateOrdinalNonRootRisk ordinal adversary parameter table ftsSecret
          fuel] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  unfold granularAllCanonicalPrivateOrdinalNonRootRisk
  apply probEvent_bind_le_of_forall_le
  intro result hresult
  apply probEvent_finishDirectWitnessOrdinalRisk_le table _ [] result _
  intro resolved heq hpublished _hcompletable
  subst result
  exact probEvent_directDetailedBoundaryPrivateOrdinalNonRootRisk_le ordinal parameter
    resolved.value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨resolved.value.1, parameter⟩) []
    (canonicalizeMaterializedValues table resolved.context) resolved.remaining table
    resolved.value.2 candidatesHaveStructuralParent_nil
    (candidatePositionsFreshExceptLayerRoots_of_done_maskedPublishedTreeRoot fuel table resolved
      hresult)
    hpublished.to_canonicalizedMaterializedValues

theorem relTriple_granularAllCanonicalSnapshot_privateOrdinalSelection
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    RelTriple
      (granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret fuel)
      (granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter table ftsSecret
        fuel)
      (SnapshotOrdinalSelectionRel ordinal) := by
  unfold granularAllCanonicalPrivateWitnessSnapshot
    granularAllCanonicalPrivateOrdinalSelection
  apply relTriple_runSnapshot_privateOrdinalSelection table ordinal _ _ []
    emptyWitnessDeferredContext fuel (maskedPublishedTreeRoot.run emptySplitHashCache) (by simp)
  intro result _hresult
  exact relTriple_granularRetainedSnapshot_privateOrdinalSelection ordinal adversary parameter
    table ftsSecret (canonicalizeMaterializedValues table result.context) result.remaining
    result.value [] (by simp)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_granularAllCanonicalSnapshot_privateOrdinalSelection_supported
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    RelTriple
      (granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret fuel)
      (granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter table ftsSecret
        fuel)
      (fun source selection =>
        SnapshotOrdinalSelectionRel ordinal source selection ∧
          selection ∈ support
            (granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter table
              ftsSecret fuel)) :=
  SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support
    (relTriple_granularAllCanonicalSnapshot_privateOrdinalSelection ordinal adversary parameter
      table ftsSecret fuel)

attribute [local irreducible] granularAllCanonicalPrivateOrdinalSelection in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_granularAllCanonicalSnapshot_privateOrdinalSelection_pendingCovered
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    RelTriple
      (granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret fuel)
      (granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter table ftsSecret
        fuel)
      (fun source selection =>
        SnapshotOrdinalSelectionRel ordinal source selection ∧
          PrivateOrdinalSelectionPendingCovered ordinal selection) := by
  apply relTriple_post_mono
    (relTriple_granularAllCanonicalSnapshot_privateOrdinalSelection_supported ordinal adversary
      parameter table ftsSecret fuel)
  intro source selection hrelation
  exact ⟨hrelation.1,
    privateOrdinalSelectionPendingCovered_of_mem_granularAllCanonical ordinal adversary parameter
      table ftsSecret fuel selection hrelation.2⟩

def SelectedPrivateSnapshotNonRootHitAt
    (source : PrivateWitnessSnapshotOutput) (ordinal : Nat) : Prop :=
  ∃ selected : Fin source.2.length, ∃ target output,
    selected.val = ordinal ∧
    selectedPrivateSnapshotOrdinal? ordinal source.2 =
      some (privateOrdinalSelectionOfSnapshot selected) ∧
    (privateOrdinalSelectionOfSnapshot selected).GoodForActualRoot target output ordinal ∧
    ¬IsLayerRoot target

theorem selectedPrivateSnapshotHitAt_root_or_nonRoot'
    {source : PrivateWitnessSnapshotOutput} {ordinal : Nat}
    (hhit : SelectedPrivateSnapshotHitAt source ordinal) :
    (∃ selected : Fin source.2.length, ∃ target output,
      selected.val = ordinal ∧
      selectedPrivateSnapshotOrdinal? ordinal source.2 =
        some (privateOrdinalSelectionOfSnapshot selected) ∧
      (privateOrdinalSelectionOfSnapshot selected).GoodForActualRoot target output ordinal ∧
      IsLayerRoot target) ∨
      SelectedPrivateSnapshotNonRootHitAt source ordinal := by
  exact selectedPrivateSnapshotHitAt_root_or_nonRoot hhit

theorem relTriple_granularAllCanonicalSnapshot_nonRootFire
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    RelTriple
      (granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret fuel)
      (granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter table ftsSecret
          fuel >>=
        privateOrdinalSelectionNonRootFire)
      (fun source hit => SelectedPrivateSnapshotNonRootHitAt source ordinal → hit = true) := by
  have hbind : RelTriple
      (granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret fuel >>=
        fun source => pure source)
      (granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter table ftsSecret
          fuel >>=
        privateOrdinalSelectionNonRootFire)
      (fun source hit => SelectedPrivateSnapshotNonRootHitAt source ordinal → hit = true) := by
    apply relTriple_bind
      (relTriple_granularAllCanonicalSnapshot_privateOrdinalSelection ordinal adversary parameter
        table ftsSecret fuel)
    intro source selection hselection
    by_cases hnonRoot : SelectedPrivateSnapshotNonRootHitAt source ordinal
    · obtain ⟨selected, target, output, _hordinal, hselected, hgood, hroot⟩ := hnonRoot
      have hselectionEq : selection = some (privateOrdinalSelectionOfSnapshot selected) := by
        exact hselection.symm.trans hselected
      rw [hselectionEq]
      rw [privateOrdinalSelectionNonRootFire_eq_true_of_goodForActualRoot
        (privateOrdinalSelectionOfSnapshot selected) target output ordinal hgood hroot]
      exact relTriple_pure_pure (fun _ => rfl)
    · have hbase := relTriple_true
          (pure source : ProbComp PrivateWitnessSnapshotOutput)
          (privateOrdinalSelectionNonRootFire selection)
      have hleft :=
        SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
          (fun output => output = source) (by
            intro left hleft
            simpa using hleft)
      exact relTriple_post_mono hleft (fun left _ hrelation h => by
        rw [hrelation.2] at h
        exact False.elim (hnonRoot h))
  simpa using hbind

theorem probEvent_granularAllCanonical_nonRoot_le_selectionFire
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[fun source => SelectedPrivateSnapshotNonRootHitAt source ordinal |
        granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret fuel] ≤
      Pr[fun hit : Bool => hit = true |
        granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter table ftsSecret
            fuel >>=
          privateOrdinalSelectionNonRootFire] := by
  apply probEvent_le_of_relTriple
    (relTriple_granularAllCanonicalSnapshot_nonRootFire ordinal adversary parameter table ftsSecret
      fuel)
  intro source hit hrelation hsource
  exact hrelation hsource

theorem probEvent_granularAllCanonical_selectedNonRoot_le
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[fun source => SelectedPrivateSnapshotNonRootHitAt source ordinal |
        granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret fuel] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    _ ≤ Pr[fun hit : Bool => hit = true |
        granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter table ftsSecret
            fuel >>=
          privateOrdinalSelectionNonRootFire] :=
      probEvent_granularAllCanonical_nonRoot_le_selectionFire ordinal adversary parameter table
        ftsSecret fuel
    _ = Pr[fun hit : Bool => hit = true |
        granularAllCanonicalPrivateOrdinalNonRootRisk ordinal adversary parameter table ftsSecret
          fuel] := by
      rw [granularAllCanonicalPrivateOrdinalSelection_bind_nonRootFire]
    _ ≤ _ := probEvent_granularAllCanonicalPrivateOrdinalNonRootRisk_le ordinal adversary
      parameter table ftsSecret fuel

theorem probEvent_sampledGranularAllCanonical_selectedNonRoot_le
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[fun source => SelectedPrivateSnapshotNonRootHitAt source ordinal |
        sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret fuel] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  unfold sampledGranularAllCanonicalPrivateWitnessSnapshot
  apply probEvent_bind_le_of_forall_le
  intro table _htable
  exact probEvent_granularAllCanonical_selectedNonRoot_le ordinal adversary parameter table
    ftsSecret fuel

end SphincsSecurity.Concrete.OtsProbeSimulation
