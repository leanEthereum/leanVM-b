import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAwareSharedSemantic
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootLazyEagerObservation
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootLazyEagerState
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootLazyEagerSuffix
import SphincsSecurity.Proof.OtsProbeResolvedPrivateRetainedCommutation
import VCVio.OracleComp.EvalDist

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot

def RawObservedPendingSelectorRel
    (table : OtsSecretIndex → HashOutput) (ordinal : Nat) :
    (Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest) →
      (Option PrivateOrdinalSelection × Digest) → Prop :=
  fun observed selection ↦
    ∃ source : PrivateWitnessSnapshotOutput × Digest,
      source.2 = observed.2 ∧
        SnapshotObservedFirstStoppedRel table source.1 observed.1 ∧
        SnapshotOrdinalSelectionRel ordinal source.1 selection.1 ∧
        source.2 = selection.2 ∧
        PrivateOrdinalSelectionPendingCovered ordinal selection.1

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_observedRootComparison_privateOrdinalSelection_raw
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (q : Nat)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q)
    (hq : q ≤ 2 ^ securityBits) :
    RelTriple
      (do
        let observed ← observedMaterializedRetainedRunFromTable adversary parameter ftsSecret
          (2 * q) table
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (observed, rightRoot))
      (do
        let selection ← granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter
          table ftsSecret q
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (selection, rightRoot))
      (RawObservedPendingSelectorRel table ordinal) := by
  have hsourceObserved : RelTriple
      (do
        let source ← granularAllCanonicalPrivateWitnessSnapshot adversary parameter table
          ftsSecret q
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (source, rightRoot))
      (do
        let observed ← observedMaterializedRetainedRunFromTable adversary parameter ftsSecret
          (2 * q) table
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (observed, rightRoot))
      (fun source observed ↦ source.2 = observed.2 ∧
        SnapshotObservedFirstStoppedRel table source.1 observed.1) := by
    apply relTriple_bind
      (relTriple_granularAllSnapshot_observedMaterializedRetained_firstStopped adversary
        parameter ftsSecret q table hbound hq)
    intro source observed hrelation
    apply relTriple_bind (relTriple_refl ($ᵗ Digest : ProbComp Digest))
    intro leftRoot rightRoot hroot
    subst rightRoot
    exact relTriple_pure_pure ⟨rfl, hrelation⟩
  have hsourceSelection :=
    relTriple_snapshotComparison_privateOrdinalSelectionComparison_pendingCovered ordinal
      adversary parameter table ftsSecret q
  have hglued := SphincsSecurity.relTriple_trans_exists (relTriple_symm hsourceObserved)
    hsourceSelection
  apply relTriple_post_mono hglued
  intro observed selection hrelation
  obtain ⟨source, hsource, hselection⟩ := hrelation
  exact ⟨source, hsource.1, hsource.2, hselection.1.1, hselection.1.2,
    hselection.2⟩

def RawObservedResolvedSelectorRel
    (table : OtsSecretIndex → HashOutput) (ordinal : Nat) (target : Position) :
    (Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest) →
      (Option PrivateOrdinalSelection × Digest) → Prop :=
  fun observed resolved ↦
    ∃ selection : Option PrivateOrdinalSelection × Digest,
      RawObservedPendingSelectorRel table ordinal observed selection ∧
        PrivateOrdinalGoodRel target selection.2 ordinal selection.1 resolved.1 ∧
        selection.2 = resolved.2

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_observedRootComparison_resolvedSelector_raw
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (q : Nat) (target : Position)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q)
    (hq : q ≤ 2 ^ securityBits) :
    RelTriple
      (do
        let observed ← observedMaterializedRetainedRunFromTable adversary parameter ftsSecret
          (2 * q) table
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (observed, rightRoot))
      (do
        let selection ← granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter
          table ftsSecret q
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        let resolved ← resolvePrivateOrdinalSelection target selection
        pure (resolved, rightRoot))
      (RawObservedResolvedSelectorRel table ordinal target) := by
  have hbase := relTriple_observedRootComparison_privateOrdinalSelection_raw ordinal adversary
    parameter table ftsSecret q hbound hq
  have hboundPair : RelTriple
      ((do
        let observed ← observedMaterializedRetainedRunFromTable adversary parameter ftsSecret
          (2 * q) table
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (observed, rightRoot)) >>= pure)
      ((do
        let selection ← granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter
          table ftsSecret q
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (selection, rightRoot)) >>= fun selection ↦ do
          let resolved ← resolvePrivateOrdinalSelection target selection.1
          pure (resolved, selection.2))
      (RawObservedResolvedSelectorRel table ordinal target) := by
    apply relTriple_bind hbase
    intro observed selection hrelation
    obtain ⟨source, hsourceRoot, hsourceObserved, hsourceSelection, hselectionRoot,
      hpending⟩ := hrelation
    have hinner : RelTriple
        ((pure selection.1 : ProbComp (Option PrivateOrdinalSelection)) >>= fun _ ↦
          pure observed)
        (resolvePrivateOrdinalSelection target selection.1 >>= fun resolved ↦
          pure (resolved, selection.2))
        (RawObservedResolvedSelectorRel table ordinal target) := by
      apply relTriple_bind
        (relTriple_privateOrdinalSelection_resolve target selection.2 ordinal selection.1 hpending)
      intro original resolved hresolved
      have hgoodRel : PrivateOrdinalGoodRel target selection.2 ordinal selection.1 resolved := by
        rw [← hresolved.2]
        exact hresolved.1
      exact relTriple_pure_pure
        ⟨selection,
          ⟨source, hsourceRoot, hsourceObserved, hsourceSelection, hselectionRoot, hpending⟩,
          hgoodRel, rfl⟩
    simpa using hinner
  simpa [bind_assoc] using hboundPair

theorem RawObservedPendingSelectorRel.data_of_good
    {table : OtsSecretIndex → HashOutput} {ordinal : Nat} {target : Position}
    {result : ObservedCleanRunResult (RetainedGameResult × SplitHashCache)}
    {rightRoot : Digest} {selection : Option PrivateOrdinalSelection × Digest}
    (hrelation : RawObservedPendingSelectorRel table ordinal (some result, rightRoot) selection)
    (hgood : ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
      table ordinal target rightRoot (some result)) :
    ∃ selected output,
      selection.1 = some selected ∧
        selected.GoodForRoots target output selection.2 ordinal ∧
        PendingCoveredBy (selected.candidates.take ordinal) selected.context ∧
        (∀ observed : Fin result.observations.length,
          observed.val = ordinal →
            (result.observations.get observed).coordinate = .position target ∧
              (result.observations.get observed).revealedAtProbe = false ∧
              truncateHash output = (result.observations.get observed).candidate) ∧
        (∀ earlier : Fin result.observations.length,
          earlier.val < ordinal →
            (result.observations.get earlier).toProbe ≠
              ⟨.position target, truncateHash output⟩) ∧
        IsLayerRoot target := by
  obtain ⟨source, hsourceRoot, hsourceObserved, hsourceSelection, hselectionRoot,
    hpending⟩ := hrelation
  have hsourceGood := hsourceObserved.cleanRootGoodForComparisonAt_of_successful hgood
  obtain ⟨sourceSelected, output, hsourceOrdinal, hselectedSource, hgoodRoots⟩ :=
    hsourceGood.goodForRoots
  have hselection : selection.1 =
      some (privateOrdinalSelectionOfSnapshot sourceSelected) := by
    rw [← hsourceSelection, hselectedSource]
  let selected := privateOrdinalSelectionOfSnapshot sourceSelected
  have hselectedGood : selected.GoodForRoots target output selection.2 ordinal := by
    rw [← hselectionRoot, hsourceRoot]
    exact hgoodRoots
  have hcovered : PendingCoveredBy (selected.candidates.take ordinal) selected.context := by
    rw [hselection] at hpending
    exact hpending
  have hgoodData := hgood
  obtain ⟨⟨⟨⟨finalResult, hfinish⟩, _hdoomed,
    observedSelected, hobservedOrdinal, hfirst, hobservedRoot⟩, hposition⟩,
    _hcomparison⟩ := hgoodData
  rcases hsourceObserved.selectedAligned_or_chain_of_successful_firstHit
      finalResult hfinish ordinal hfirst with halignedData | hchain
  · obtain ⟨_hsourceHit, haligned⟩ := halignedData
    obtain ⟨alignedSource, alignedObserved, halignedSource, halignedObserved,
      hcandidates, hprefix, _hsnapshots⟩ := haligned
    have hsourceEq : alignedSource = sourceSelected :=
      Fin.ext (halignedSource.trans hsourceOrdinal.symm)
    have hobservedEq : alignedObserved = observedSelected :=
      Fin.ext (halignedObserved.trans hobservedOrdinal.symm)
    have hselectedLt : ordinal < result.observations.length := by
      rw [← hobservedOrdinal]
      exact observedSelected.isLt
    have hselectedIndex :
        (⟨ordinal, hselectedLt⟩ : Fin result.observations.length) = observedSelected :=
      Fin.ext hobservedOrdinal.symm
    have htargetData :
        (result.observations.get observedSelected).coordinate = .position target ∧
          IsLayerRoot target := by
      simp only [observedFirstLayerRootPosition?, hselectedLt, ↓reduceDIte] at hposition
      rw [candidateLayerRootPosition?_eq_some_iff, hselectedIndex] at hposition
      exact hposition
    have hselectedDigest : truncateHash output =
        (result.observations.get observedSelected).candidate := by
      have hcandidate := hselectedGood.1
      rw [privateOrdinalSelectionOfSnapshot_candidate] at hcandidate
      have hsourceCandidate : (source.1.2.get sourceSelected).probe =
          ⟨.position target, truncateHash output⟩ := by
        simpa [snapshotProbeOrdinal] using hcandidate
      have halignedCandidate : (source.1.2.get alignedSource).probe =
          (result.observations.get alignedObserved).toProbe := hcandidates
      rw [hsourceEq, hsourceCandidate, hobservedEq] at halignedCandidate
      simpa [CleanProbeObservation.toProbe] using congrArg Probe.candidate halignedCandidate
    have hselectedHidden :
        (result.observations.get observedSelected).revealedAtProbe = false := by
      obtain ⟨_firstSelected, _hfirstOrdinal, hhit, _hbefore⟩ := hfirst
      have hsame : _firstSelected = observedSelected :=
        Fin.ext (_hfirstOrdinal.trans hobservedOrdinal.symm)
      subst _firstSelected
      exact hhit.1
    refine ⟨selected, output, hselection, hselectedGood, hcovered, ?_, ?_,
      htargetData.2⟩
    · intro observed hobserved
      have heq : observed = observedSelected :=
        Fin.ext (hobserved.trans hobservedOrdinal.symm)
      subst observed
      exact ⟨htargetData.1, hselectedHidden, hselectedDigest⟩
    · intro earlier hearlier heq
      have hprefixAvoid := hselectedGood.2.2.2.2
      have hobservationMem : (result.observations.get earlier).toProbe ∈
          (result.observations.map CleanProbeObservation.toProbe).take ordinal := by
        rw [List.mem_iff_get]
        let index : Fin
            ((result.observations.map CleanProbeObservation.toProbe).take ordinal).length :=
          ⟨earlier.val, by simp [hearlier]⟩
        refine ⟨index, ?_⟩
        simp [index]
      have hselectedMem : (result.observations.get earlier).toProbe ∈
          selected.candidates.take ordinal := by
        change (result.observations.get earlier).toProbe ∈
          (privateOrdinalSelectionOfSnapshot sourceSelected).candidates.take ordinal
        rw [← hsourceOrdinal,
          privateOrdinalSelectionOfSnapshot_candidates_take, hsourceOrdinal, hprefix]
        exact hobservationMem
      exact (hprefixAvoid _ hselectedMem).1 heq
  · exact (not_firstExistingHiddenRootHitAt_of_firstChainStart hchain hfirst observedSelected
      hobservedOrdinal hobservedRoot).elim

noncomputable def resolvedEagerObservedRootComparisonAfterRootResult
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    ProbComp
      (Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest) := do
  let resolved ← resolveDeferredPositionValue target (directDeferredContext rootResult.state)
  let rightRoot ← ($ᵗ Digest : ProbComp Digest)
  match resolved with
  | none => pure (none, rightRoot)
  | some resolved => do
      let observed ← observedMaterializedBoundary parameter rootResult.value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
        (materializedDeferredState resolved.toDeferredContext) rootResult.remaining rootResult.table
        (replaceHiddenRootCache target resolved.output rootResult.value.2)
      pure (retainObservedRoot rootResult.value.1 observed, rightRoot)

theorem evalDist_resolvedEagerObservedRootComparisonAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache))
    (habsent : rootResult.state.values (.position target) = none)
    (hpending : rootResult.state.pending = ∅) :
    evalDist
      (resolvedEagerObservedRootComparisonAfterRootResult adversary parameter ftsSecret target
        rootResult) =
      evalDist ((fun sampled => (sampled.2.2, sampled.2.1)) <$>
        sampledHighEagerObservedRootAwareAfterRootResult ordinal adversary parameter ftsSecret
          target rootResult) := by
  unfold resolvedEagerObservedRootComparisonAfterRootResult
  rw [resolveDeferredPositionValue_fresh target (directDeferredContext rootResult.state)]
  · have hhit : ∀ output, ¬rootResult.state.hitAt (.position target) output := by
      intro output
      simp [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt, hpending]
    simp only [directDeferredContext, hhit, ↓reduceIte]
    unfold sampledHighEagerObservedRootAwareAfterRootResult
    simp only [map_eq_bind_pure_comp, bind_assoc]
    simp only [pure_bind]
    have hclear : rootResult.state.clearPending (.position target) = rootResult.state := by
      rcases hstate : rootResult.state with ⟨pending, values, revealed, ensured⟩
      simp only [LazyRevealProbe.State.clearPending]
      have hp : pending = ∅ := by simpa only [hstate] using hpending
      simp [LazyRevealProbe.State.pendingAway, hp]
    rw [hclear]
    unfold rootInstalledCache
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
      let observed ← observedMaterializedBoundary parameter rootResult.value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
        (materializedDeferredState
          { state := rootResult.state
            values := (directDeferredValues rootResult.state).install target output })
        rootResult.remaining rootResult.table
        (replaceHiddenRootCache target output rootResult.value.2)
      pure (retainObservedRoot rootResult.value.1 observed, rightRoot)
    calc
      _ = evalDist (LazyRevealProbe.sampleHashOutput >>= continuation) := by
        rfl
      _ = evalDist (parts >>= continuation) := by
        rw [evalDist_bind, evalDist_bind, hparts]
      _ = _ := by
        simp [parts, continuation, directDeferredContext, bind_assoc]
  · simpa [directDeferredContext] using habsent
  · simpa [directDeferredContext, directDeferredValues] using habsent

noncomputable def resolvedEagerObservedRootComparisonExperimentAfterTable
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    ProbComp
      (Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest) := do
  let rootResult ← runCleanFromTable
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
    (maskedPublishedTreeRoot.run emptySplitHashCache)
  match rootResult with
  | none => pure (none, 0)
  | some result =>
      resolvedEagerObservedRootComparisonAfterRootResult adversary parameter ftsSecret target result

set_option maxRecDepth 100000 in
theorem evalDist_resolvedEagerObservedRootComparisonExperimentAfterTable
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    evalDist
      (resolvedEagerObservedRootComparisonExperimentAfterTable adversary parameter ftsSecret
        target fuel table) =
      evalDist
        (eagerObservedRootComparisonExperimentAfterTable ordinal adversary parameter ftsSecret
          target fuel table) := by
  unfold resolvedEagerObservedRootComparisonExperimentAfterTable
    eagerObservedRootComparisonExperimentAfterTable
  apply evalDist_bind_congr
  intro rootResult hresult
  cases rootResult with
  | none => rfl
  | some result =>
      have habsent := target_absent_of_mem_runCleanFromTable_maskedPublishedTreeRoot target hroot
        hparent fuel table result hresult
      have hpending := pending_eq_empty_of_mem_runCleanFromTable_maskedPublishedTreeRoot fuel table
        result hresult
      exact evalDist_resolvedEagerObservedRootComparisonAfterRootResult ordinal adversary parameter
        ftsSecret target result habsent.1 hpending

def SuccessfulObservedLazyEagerRel
    (table : OtsSecretIndex → HashOutput) (ordinal : Nat) (target : Position) :
    (Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest) →
      (Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest) →
        Prop :=
  fun lazy eager ↦
    ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
        table ordinal target lazy.2 lazy.1 →
      ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
        table ordinal target eager.2 eager.1

theorem probEvent_successfulObservedRootComparison_eq_indicator
    (table : OtsSecretIndex → HashOutput) (ordinal : Nat) (target : Position)
    (run : ProbComp
      (Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest)) :
    Pr[fun result ↦
        ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
          table ordinal target result.2 result.1 | run] =
      Pr[= true |
        successfulObservedRootComparisonIndicator table ordinal target <$> run] := by
  calc
    _ = Pr[fun result ↦
          successfulObservedRootComparisonIndicator table ordinal target result = true | run] := by
      apply OracleComp.probEvent_congr' (fun result _ ↦ by simp) rfl
    _ = _ := by
      rw [← probEvent_eq_eq_probOutput, probEvent_map]
      rfl

theorem probEvent_observedRootComparison_le_resolvedEager_of_indicator
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (q : Nat) (target : Position)
    (hrel : RelTriple
      (successfulObservedRootComparisonIndicator table ordinal target <$> (do
        let observed ← observedMaterializedRetainedRunFromTable adversary parameter ftsSecret
          (2 * q) table
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (observed, rightRoot)))
      (successfulObservedRootComparisonIndicator table ordinal target <$>
        resolvedEagerObservedRootComparisonExperimentAfterTable adversary parameter ftsSecret
          target (2 * q) table)
      (fun lazy eager ↦ lazy = true → eager = true)) :
    Pr[fun result : Option
          (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest ↦
        ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
          table ordinal target result.2 result.1 | do
      let observed ← observedMaterializedRetainedRunFromTable adversary parameter ftsSecret
        (2 * q) table
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (observed, rightRoot)] ≤
      Pr[fun result ↦
        ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
          table ordinal target result.2 result.1 |
        resolvedEagerObservedRootComparisonExperimentAfterTable adversary parameter ftsSecret
          target (2 * q) table] := by
  rw [probEvent_successfulObservedRootComparison_eq_indicator,
    probEvent_successfulObservedRootComparison_eq_indicator]
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
  apply probEvent_le_of_relTriple hrel
  intro lazy eager hrelation hlazy
  exact hrelation hlazy

theorem probEvent_observedRootComparison_le_resolvedEager
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (q : Nat) (target : Position)
    (hrel : RelTriple
      (do
        let observed ← observedMaterializedRetainedRunFromTable adversary parameter ftsSecret
          (2 * q) table
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (observed, rightRoot))
      (resolvedEagerObservedRootComparisonExperimentAfterTable adversary parameter ftsSecret
        target (2 * q) table)
      (SuccessfulObservedLazyEagerRel table ordinal target)) :
    Pr[fun result : Option
          (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest ↦
        ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
          table ordinal target result.2 result.1 | do
      let observed ← observedMaterializedRetainedRunFromTable adversary parameter ftsSecret
        (2 * q) table
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (observed, rightRoot)] ≤
      Pr[fun result ↦
        ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
          table ordinal target result.2 result.1 |
        resolvedEagerObservedRootComparisonExperimentAfterTable adversary parameter ftsSecret
          target (2 * q) table] := by
  apply probEvent_le_of_relTriple hrel
  intro lazy eager hrelation hgood
  exact hrelation hgood

theorem probEvent_observedRootComparison_le_production_mul_of_lazyEager
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (q : Nat) (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (hfuel : 2 * q < Fintype.card Digest)
    (hrel : RelTriple
      (do
        let observed ← observedMaterializedRetainedRunFromTable adversary parameter ftsSecret
          (2 * q) table
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (observed, rightRoot))
      (resolvedEagerObservedRootComparisonExperimentAfterTable adversary parameter ftsSecret
        target (2 * q) table)
      (SuccessfulObservedLazyEagerRel table ordinal target)) :
    Pr[fun result : Option
          (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest ↦
        ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
          table ordinal target result.2 result.1 | do
      let observed ← observedMaterializedRetainedRunFromTable adversary parameter ftsSecret
        (2 * q) table
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (observed, rightRoot)] ≤
      Pr[fun result ↦ materializedOrdinalSelectionAt target result.2 |
          materializedRootAwareOrdinalProductionExperimentAfterTable ordinal adversary parameter
            ftsSecret target (2 * q) table] *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ ≤ Pr[fun result ↦
          ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
            table ordinal target result.2 result.1 |
          resolvedEagerObservedRootComparisonExperimentAfterTable adversary parameter ftsSecret
            target (2 * q) table] :=
      probEvent_observedRootComparison_le_resolvedEager ordinal adversary parameter table
        ftsSecret q target hrel
    _ = Pr[fun result ↦
          ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
            table ordinal target result.2 result.1 |
          eagerObservedRootComparisonExperimentAfterTable ordinal adversary parameter ftsSecret
            target (2 * q) table] := by
      apply OracleComp.probEvent_congr' (fun _ _ ↦ Iff.rfl)
      exact evalDist_resolvedEagerObservedRootComparisonExperimentAfterTable ordinal adversary
        parameter ftsSecret target hroot hparent (2 * q) table
    _ ≤ _ := probEvent_eagerObservedRootComparison_le_production_mul ordinal adversary parameter
      ftsSecret target hroot hparent (2 * q) table hfuel

end SphincsSecurity.Concrete.OtsProbeSimulation
