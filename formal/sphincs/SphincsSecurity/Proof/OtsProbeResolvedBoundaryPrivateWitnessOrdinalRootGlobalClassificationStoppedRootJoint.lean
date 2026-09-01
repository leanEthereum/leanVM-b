import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootEager
import SphincsSecurity.Proof.MarginalCoupling

/-!
# Joint stopped layer-root endpoint

The successful stopped diagnostic must remain correlated with the materialized root-selection
outcome. The fixed-target definitions below keep that success gate on the observed run and split the
independent comparison-root exception before the stopped coupling is applied. The older source-only
interface is retained as a conditional endpoint, but it is not used to duplicate a comparison failure
across position fibers.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

noncomputable def observedFirstLayerRootPosition?
    (ordinal : Nat) : Option (ObservedCleanRunResult α) → Option Position
  | none => none
  | some result =>
      if hselected : ordinal < result.observations.length then
        candidateLayerRootPosition?
          (result.observations.get ⟨ordinal, hselected⟩).toProbe
      else none

def ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget
    (table : OtsSecretIndex → HashOutput) (ordinal : Nat) (target : Position)
    (observed : Option (ObservedCleanRunResult α)) : Prop :=
  ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt
      table ordinal observed ∧
    observedFirstLayerRootPosition? ordinal observed = some target

theorem successfulDoomedFirstRootHitAtTarget_root
    {table : OtsSecretIndex → HashOutput} {ordinal : Nat} {target : Position}
    {observed : Option (ObservedCleanRunResult α)}
    (hhit : ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget
      table ordinal target observed) :
    ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt
      table ordinal observed :=
  hhit.1

theorem observedFirstLayerRootPosition?_eq_some_of_successfulDoomedFirstRoot
    {table : OtsSecretIndex → HashOutput} {ordinal : Nat}
    {observed : Option (ObservedCleanRunResult α)}
    (hhit : ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt
      table ordinal observed) :
    ∃ target, observedFirstLayerRootPosition? ordinal observed = some target := by
  cases observed with
  | none => simp [ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt] at hhit
  | some result =>
      obtain ⟨_hfinish, _hdoomed, selected, hselected, _hfirst, hroot⟩ := hhit
      obtain ⟨target, hcoordinate, htargetRoot⟩ := hroot
      have hlt : ordinal < result.observations.length := by
        rw [← hselected]
        exact selected.isLt
      have hindex : (⟨ordinal, hlt⟩ : Fin result.observations.length) = selected :=
        Fin.ext hselected.symm
      refine ⟨target, ?_⟩
      simp only [observedFirstLayerRootPosition?, hlt, ↓reduceDIte]
      rw [candidateLayerRootPosition?_eq_some_iff, hindex]
      exact ⟨hcoordinate, htargetRoot⟩

theorem not_successfulDoomedFirstRoot_of_position_eq_none
    {table : OtsSecretIndex → HashOutput} {ordinal : Nat}
    {observed : Option (ObservedCleanRunResult α)}
    (hposition : observedFirstLayerRootPosition? ordinal observed = none) :
    ¬ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt
      table ordinal observed := by
  intro hhit
  obtain ⟨target, htarget⟩ :=
    observedFirstLayerRootPosition?_eq_some_of_successfulDoomedFirstRoot hhit
  rw [hposition] at htarget
  simp at htarget

theorem probEvent_successfulDoomedFirstRoot_le_of_position_fibers
    (table : OtsSecretIndex → HashOutput)
    (run : ProbComp (Option (ObservedCleanRunResult α))) (ordinal : Nat)
    (hfiber : ∀ target,
      Pr[fun observed =>
          ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget
            table ordinal target observed | run] ≤
        Pr[fun observed => observedFirstLayerRootPosition? ordinal observed = some target | run] *
          ((2 ^ digestBits : Nat) : ENNReal)⁻¹) :
    Pr[fun observed =>
        ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt
          table ordinal observed | run] ≤
      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  apply probEvent_le_of_uniform_weighted_fibers run
    (ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt table ordinal)
    (observedFirstLayerRootPosition? ordinal)
    (((2 ^ digestBits : Nat) : ENNReal)⁻¹)
  intro position?
  cases position? with
  | none =>
      have hzero : Pr[fun observed =>
          ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt
              table ordinal observed ∧
            observedFirstLayerRootPosition? ordinal observed = none | run] = 0 := by
        apply probEvent_eq_zero
        intro observed _hobserved hevent
        exact not_successfulDoomedFirstRoot_of_position_eq_none hevent.2 hevent.1
      rw [hzero]
      exact zero_le
  | some target => exact hfiber target

def observedPrefixProbes
    (ordinal : Nat) : Option (ObservedCleanRunResult α) → List Probe
  | none => []
  | some result =>
      (result.observations.take ordinal).map CleanProbeObservation.toProbe

def ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
    (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (target : Position) (rightRoot : Digest)
    (observed : Option (ObservedCleanRunResult α)) : Prop :=
  ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget
      table ordinal target observed ∧
    CandidatesAvoidRoot target rightRoot (observedPrefixProbes ordinal observed)

def ObservedCleanRunOption.SuccessfulDoomedFirstRootComparisonExceptionAt
    (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (target : Position) (rightRoot : Digest)
    (observed : Option (ObservedCleanRunResult α)) : Prop :=
  ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget
      table ordinal target observed ∧
    ¬CandidatesAvoidRoot target rightRoot (observedPrefixProbes ordinal observed)

theorem successfulDoomedFirstRootFiber_split_comparison
    {table : OtsSecretIndex → HashOutput} {ordinal : Nat} {target : Position}
    {rightRoot : Digest} {observed : Option (ObservedCleanRunResult α)}
    (hhit : ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget
      table ordinal target observed) :
    ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
        table ordinal target rightRoot observed ∨
      ObservedCleanRunOption.SuccessfulDoomedFirstRootComparisonExceptionAt
        table ordinal target rightRoot observed := by
  by_cases havoid : CandidatesAvoidRoot target rightRoot
      (observedPrefixProbes ordinal observed)
  · exact Or.inl ⟨hhit, havoid⟩
  · exact Or.inr ⟨hhit, havoid⟩

theorem observedPrefixProbes_length_le
    (ordinal : Nat) (observed : Option (ObservedCleanRunResult α)) :
    (observedPrefixProbes ordinal observed).length ≤ ordinal := by
  cases observed with
  | none => simp [observedPrefixProbes]
  | some result => simp [observedPrefixProbes]

theorem probEvent_successfulDoomedFirstRootComparisonExceptionAt_le
    (table : OtsSecretIndex → HashOutput)
    (run : ProbComp (Option (ObservedCleanRunResult α)))
    (ordinal : Nat) (target : Position) :
    Pr[fun result : Option (ObservedCleanRunResult α) × Digest =>
        ObservedCleanRunOption.SuccessfulDoomedFirstRootComparisonExceptionAt
          table ordinal target result.2 result.1 | do
      let observed ← run
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (observed, rightRoot)] ≤
      Pr[fun observed => ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget
          table ordinal target observed | run] *
        ((ordinal : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  let gate := fun observed : Option (ObservedCleanRunResult α) =>
    ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget
      table ordinal target observed
  let values := fun observed : Option (ObservedCleanRunResult α) =>
    (observedPrefixProbes ordinal observed).map Probe.candidate
  calc
    _ ≤ Pr[fun result : Option (ObservedCleanRunResult α) × Digest =>
          gate result.1 ∧ result.2 ∈ values result.1 | do
        let observed ← run
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (observed, rightRoot)] := by
      apply probEvent_mono
      intro result _hresult hexception
      exact ⟨hexception.1,
        not_candidatesAvoidRoot_mem_candidate_map hexception.2⟩
    _ ≤ Pr[gate | run] *
          ((ordinal : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
      apply probEvent_gate_and_uniformDigest_mem_list_le run gate values ordinal
      intro observed _hobserved _hgate
      simpa [values] using observedPrefixProbes_length_le ordinal observed
    _ = _ := rfl

theorem probEvent_successfulDoomedFirstRootFiber_le_goodComparison_add_weightedException
    (table : OtsSecretIndex → HashOutput)
    (run : ProbComp (Option (ObservedCleanRunResult α)))
    (ordinal : Nat) (target : Position) :
    Pr[fun observed => ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget
        table ordinal target observed | run] ≤
      Pr[fun result : Option (ObservedCleanRunResult α) × Digest =>
          ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
            table ordinal target result.2 result.1 | do
        let observed ← run
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (observed, rightRoot)] +
      Pr[fun observed => ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget
          table ordinal target observed | run] *
        ((ordinal : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  let paired : ProbComp (Option (ObservedCleanRunResult α) × Digest) := do
    let observed ← run
    let rightRoot ← ($ᵗ Digest : ProbComp Digest)
    pure (observed, rightRoot)
  calc
    _ ≤ Pr[fun result =>
          ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
              table ordinal target result.2 result.1 ∨
            ObservedCleanRunOption.SuccessfulDoomedFirstRootComparisonExceptionAt
              table ordinal target result.2 result.1 | paired] := by
      apply probEvent_le_of_relTriple (relTriple_pair_uniform_right run)
      intro observed result hrelation hhit
      rw [← hrelation]
      exact successfulDoomedFirstRootFiber_split_comparison hhit
    _ ≤ Pr[fun result =>
          ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
            table ordinal target result.2 result.1 | paired] +
        Pr[fun result =>
          ObservedCleanRunOption.SuccessfulDoomedFirstRootComparisonExceptionAt
            table ordinal target result.2 result.1 | paired] := probEvent_or_le _ _ _
    _ ≤ _ := add_le_add_right
      (probEvent_successfulDoomedFirstRootComparisonExceptionAt_le
        table run ordinal target) _

theorem SnapshotObservedFirstStoppedRel.cleanRootGoodForComparisonAt_of_successful
    {table : OtsSecretIndex → HashOutput} {ordinal : Nat} {target : Position}
    {source : PrivateWitnessSnapshotOutput}
    {observed : Option (ObservedCleanRunResult (α × SplitHashCache))}
    {rightRoot : Digest}
    (hrelation : SnapshotObservedFirstStoppedRel table source observed)
    (hgood : ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
      table ordinal target rightRoot observed) :
    SelectedPrivateSnapshotCleanRootGoodForComparisonAt
      table source ordinal target rightRoot := by
  cases observed with
  | none =>
      simp [ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
        ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
        ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt] at hgood
  | some result =>
      obtain ⟨⟨⟨⟨finalResult, hfinish⟩, _hdoomed,
        selected, hselected, hfirst, hroot⟩, hposition⟩, hcomparison⟩ := hgood
      rcases hrelation.selectedAligned_or_chain_of_successful_firstHit
          finalResult hfinish ordinal hfirst with ⟨hhit, haligned⟩ | hchain
      · have hclean := hrelation.selectedCleanRoot_of_successful_firstRoot
          finalResult hfinish ordinal selected hselected hfirst hroot
        obtain ⟨sourceSelected, sourceTarget, output, hsourceSelected, hselection,
          hactual, hsourceRoot, hsourceClean⟩ := hclean
        obtain ⟨alignedSource, alignedObserved, halignedSource, halignedObserved,
          hcandidates, hprefix, _hsnapshots⟩ := haligned
        have hsourceEq : sourceSelected = alignedSource :=
          Fin.ext (hsourceSelected.trans halignedSource.symm)
        have hobservedEq : alignedObserved = selected :=
          Fin.ext (halignedObserved.trans hselected.symm)
        have hselectedLt : ordinal < result.observations.length := by
          rw [← hselected]
          exact selected.isLt
        have hselectedIndex :
            (⟨ordinal, hselectedLt⟩ : Fin result.observations.length) = selected :=
          Fin.ext hselected.symm
        have htargetData :
            (result.observations.get selected).coordinate = .position target ∧
              IsLayerRoot target := by
          simp only [observedFirstLayerRootPosition?, hselectedLt, ↓reduceDIte] at hposition
          rw [candidateLayerRootPosition?_eq_some_iff, hselectedIndex] at hposition
          exact hposition
        have htarget : sourceTarget = target := by
          have hsourceCoordinate :
              (source.2.get sourceSelected).probe.coordinate = .position sourceTarget := by
            have hcandidate := congrArg Probe.coordinate hactual.1
            simpa using hcandidate
          have halignedCoordinate :
              (source.2.get alignedSource).probe.coordinate =
                (result.observations.get alignedObserved).coordinate := by
            exact congrArg Probe.coordinate hcandidates
          rw [hsourceEq, halignedCoordinate, hobservedEq, htargetData.1] at hsourceCoordinate
          exact (Coordinate.position.inj hsourceCoordinate).symm
        subst sourceTarget
        have hsourceComparison : CandidatesAvoidRoot target rightRoot
            ((privateOrdinalSelectionOfSnapshot sourceSelected).candidates.take ordinal) := by
          rw [← hsourceSelected,
            privateOrdinalSelectionOfSnapshot_candidates_take, hsourceSelected]
          rw [hprefix]
          simpa [observedPrefixProbes, List.map_take] using hcomparison
        exact ⟨sourceSelected, output, hsourceSelected, hselection, hactual,
          hsourceRoot, hsourceClean, hsourceComparison⟩
      · exact (not_firstExistingHiddenRootHitAt_of_firstChainStart hchain hfirst selected
          hselected hroot).elim

def SuccessfulObservedCleanRootRel
    (table : OtsSecretIndex → HashOutput) (ordinal : Nat) (target : Position) :
    (PrivateWitnessSnapshotOutput × Digest) →
      (Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest) → Prop :=
  fun source observed =>
    source.2 = observed.2 ∧
      (ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
          table ordinal target observed.2 observed.1 →
        SelectedPrivateSnapshotCleanRootGoodForComparisonAt
          table source.1 ordinal target source.2)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_snapshotComparison_observedSuccessfulRootComparison
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
        let source ← granularAllCanonicalPrivateWitnessSnapshot adversary parameter table
          ftsSecret q
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (source, rightRoot))
      (do
        let observed ← observedMaterializedRetainedRunFromTable adversary parameter ftsSecret
          (2 * q) table
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (observed, rightRoot))
      (SuccessfulObservedCleanRootRel table ordinal target) := by
  apply relTriple_bind
    (relTriple_granularAllSnapshot_observedMaterializedRetained_firstStopped adversary parameter
      ftsSecret q table hbound hq)
  intro source observed hrelation
  apply relTriple_bind (relTriple_refl ($ᵗ Digest : ProbComp Digest))
  intro leftRoot rightRoot hroot
  subst rightRoot
  apply relTriple_pure_pure
  refine ⟨rfl, ?_⟩
  intro hgood
  exact hrelation.cleanRootGoodForComparisonAt_of_successful hgood

def SuccessfulObservedPendingSelectorRel
    (table : OtsSecretIndex → HashOutput) (ordinal : Nat) (target : Position) :
    (Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest) →
      (Option PrivateOrdinalSelection × Digest) → Prop :=
  fun observed selection =>
    ∃ source : PrivateWitnessSnapshotOutput × Digest,
      SuccessfulObservedCleanRootRel table ordinal target source observed ∧
        (SnapshotOrdinalSelectionRel ordinal source.1 selection.1 ∧
          source.2 = selection.2) ∧
        PrivateOrdinalSelectionPendingCovered ordinal selection.1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_snapshotComparison_privateOrdinalSelectionComparison_pendingCovered
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    RelTriple
      (do
        let source ← granularAllCanonicalPrivateWitnessSnapshot adversary parameter table
          ftsSecret fuel
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (source, rightRoot))
      (do
        let selection ← granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter
          table ftsSecret fuel
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (selection, rightRoot))
      (fun left right =>
        (SnapshotOrdinalSelectionRel ordinal left.1 right.1 ∧ left.2 = right.2) ∧
          PrivateOrdinalSelectionPendingCovered ordinal right.1) := by
  apply relTriple_bind
    (relTriple_granularAllCanonicalSnapshot_privateOrdinalSelection_pendingCovered ordinal adversary
      parameter table ftsSecret fuel)
  intro source selection hselection
  apply relTriple_bind (relTriple_refl ($ᵗ Digest : ProbComp Digest))
  intro leftRoot rightRoot hroot
  subst rightRoot
  exact relTriple_pure_pure ⟨⟨hselection.1, rfl⟩, hselection.2⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_observedSuccessfulRootComparison_pendingSelector
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
      let selection ← granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter table
        ftsSecret q
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (selection, rightRoot))
      (SuccessfulObservedPendingSelectorRel table ordinal target) := by
  have hobserved := relTriple_snapshotComparison_observedSuccessfulRootComparison ordinal adversary
    parameter table ftsSecret q target hbound hq
  have hselection :=
    relTriple_snapshotComparison_privateOrdinalSelectionComparison_pendingCovered ordinal adversary
      parameter table ftsSecret q
  have hglued := SphincsSecurity.relTriple_trans_exists (relTriple_symm hobserved)
    hselection
  apply relTriple_post_mono hglued
  intro observed selection hrelation
  obtain ⟨source, hsource, hselection⟩ := hrelation
  exact ⟨source, hsource, hselection.1, hselection.2⟩

theorem SuccessfulObservedPendingSelectorRel.goodForRoots_pendingCovered
    {table : OtsSecretIndex → HashOutput} {ordinal : Nat} {target : Position}
    {observed : Option
      (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest}
    {selection : Option PrivateOrdinalSelection × Digest}
    (hrelation : SuccessfulObservedPendingSelectorRel table ordinal target observed selection)
    (hgood : ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
      table ordinal target observed.2 observed.1) :
    ∃ selected output,
      selection.1 = some selected ∧
        selected.GoodForRoots target output selection.2 ordinal ∧
        PrivateOrdinalSelectionPendingCovered ordinal selection.1 := by
  obtain ⟨source, hsource, hselection, hpending⟩ := hrelation
  have hsourceGood := hsource.2 hgood
  obtain ⟨selectedIndex, output, _hordinal, hselected, hgoodRoots⟩ :=
    hsourceGood.goodForRoots
  have hselectionEq : selection.1 =
      some (privateOrdinalSelectionOfSnapshot selectedIndex) :=
    hselection.1.symm.trans hselected
  refine ⟨privateOrdinalSelectionOfSnapshot selectedIndex, output, hselectionEq, ?_, ?_⟩
  · rw [← hselection.2]
    exact hgoodRoots
  · exact hpending

theorem probEvent_observedSuccessfulRootComparison_le_snapshotComparison
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (q : Nat) (target : Position)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q)
    (hq : q ≤ 2 ^ securityBits) :
    Pr[fun result : Option
          (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest =>
        ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
          table ordinal target result.2 result.1 | do
      let observed ← observedMaterializedRetainedRunFromTable adversary parameter ftsSecret
        (2 * q) table
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (observed, rightRoot)] ≤
      Pr[fun result : PrivateWitnessSnapshotOutput × Digest =>
        SelectedPrivateSnapshotCleanRootGoodForComparisonAt
          table result.1 ordinal target result.2 | do
      let source ← granularAllCanonicalPrivateWitnessSnapshot adversary parameter table
        ftsSecret q
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (source, rightRoot)] := by
  apply probEvent_le_of_relTriple
    (relTriple_symm
      (relTriple_snapshotComparison_observedSuccessfulRootComparison ordinal adversary parameter
        table ftsSecret q target hbound hq))
  intro observed source hrelation hgood
  exact hrelation.2 hgood

def SuccessfulObservedRootMaterializedMatchRel
    (table : OtsSecretIndex → HashOutput) (ordinal : Nat) (target : Position) :
    (Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest) →
      (Digest × Digest × MaterializedSelectionOutcome) → Prop :=
  fun observed outcome =>
    ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
        table ordinal target observed.2 observed.1 →
      outcome.2.2.Matches target outcome.1

theorem probEvent_observedSuccessfulRootComparison_le_materializedMatch
    (table : OtsSecretIndex → HashOutput)
    (observed : ProbComp
      (Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache))))
    (outcome : ProbComp (Digest × Digest × MaterializedSelectionOutcome))
    (ordinal : Nat) (target : Position)
    (hrel : RelTriple
      (do
        let result ← observed
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (result, rightRoot))
      outcome (SuccessfulObservedRootMaterializedMatchRel table ordinal target)) :
    Pr[fun result : Option
          (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest =>
        ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
          table ordinal target result.2 result.1 | do
      let result ← observed
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (result, rightRoot)] ≤
      Pr[fun result => result.2.2.Matches target result.1 | outcome] := by
  apply probEvent_le_of_relTriple hrel
  intro left right hrelation hgood
  exact hrelation hgood

theorem probEvent_observedSuccessfulRootComparison_le_production_mul
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (q : Nat) (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (hrel : RelTriple
      (do
        let observed ← observedMaterializedRetainedRunFromTable adversary parameter ftsSecret
          (2 * q) table
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (observed, rightRoot))
      (materializedRootOrdinalOutcomeExperimentAfterTable ordinal adversary parameter ftsSecret
        target q table)
      (SuccessfulObservedRootMaterializedMatchRel table ordinal target)) :
    Pr[fun result : Option
          (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest =>
        ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
          table ordinal target result.2 result.1 | do
      let observed ← observedMaterializedRetainedRunFromTable adversary parameter ftsSecret
        (2 * q) table
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (observed, rightRoot)] ≤
      Pr[fun result => materializedOrdinalSelectionAt target result.2 |
          materializedRootOrdinalProductionExperimentAfterTable ordinal adversary parameter
            ftsSecret target q table] *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ ≤ Pr[fun result => result.2.2.Matches target result.1 |
          materializedRootOrdinalOutcomeExperimentAfterTable ordinal adversary parameter
            ftsSecret target q table] :=
      probEvent_observedSuccessfulRootComparison_le_materializedMatch table
        (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table)
        (materializedRootOrdinalOutcomeExperimentAfterTable ordinal adversary parameter ftsSecret
          target q table) ordinal target hrel
    _ ≤ _ := probEvent_materializedRootOrdinalOutcome_match_le ordinal adversary parameter
      ftsSecret target hroot hparent q table

def CleanRootMaterializedMatchRel
    (table : OtsSecretIndex → HashOutput) (ordinal : Nat) (target : Position) :
    (PrivateWitnessSnapshotOutput × Digest) →
      (Digest × Digest × MaterializedSelectionOutcome) → Prop :=
  fun source outcome =>
    SelectedPrivateSnapshotCleanRootGoodForComparisonAt
        table source.1 ordinal target source.2 →
      outcome.2.2.Matches target outcome.1

theorem not_target_hitAt_of_goodForRoots_of_pendingCovered
    {target : Position} {leftOutput : HashOutput} {rightRoot : Digest}
    {ordinal : Nat} {selection : PrivateOrdinalSelection}
    (hgood : selection.GoodForRoots target leftOutput rightRoot ordinal)
    (hcovered : PendingCoveredBy (selection.candidates.take ordinal) selection.context) :
    ¬selection.context.state.hitAt (.position target) leftOutput := by
  intro hhit
  have hpending : (Coordinate.position target, truncateHash leftOutput) ∈
      selection.context.state.pending := by
    rw [← LazyRevealProbe.State.mem_pendingAt_iff]
    exact hhit
  obtain ⟨candidate, hcandidate, hcoordinate, hdigest⟩ := hcovered _ hpending
  have havoid := hgood.2.2.2.2 candidate hcandidate
  apply havoid.1
  cases candidate
  simp only [Probe.mk.injEq]
  exact ⟨hcoordinate, hdigest⟩

theorem resolveDeferredPositionValue_eq_good_output
    {target : Position} {leftOutput : HashOutput} {rightRoot : Digest}
    {ordinal : Nat} {selection : PrivateOrdinalSelection}
    (hgood : selection.GoodForRoots target leftOutput rightRoot ordinal)
    (hcovered : PendingCoveredBy (selection.candidates.take ordinal) selection.context) :
    resolveDeferredPositionValue target selection.context =
      pure (some (DeferredResolution.mk
        { state := selection.context.state.clearPending (.position target)
          values := selection.context.values }
        leftOutput)) := by
  rw [resolveDeferredPositionValue_of_deferred_value target selection.context leftOutput
    hgood.2.1 hgood.2.2.2.1]
  simp [not_target_hitAt_of_goodForRoots_of_pendingCovered hgood hcovered]

def PrivateOrdinalGoodRel
    (target : Position) (rightRoot : Digest) (ordinal : Nat) :
    Option PrivateOrdinalSelection → Option PrivateOrdinalSelection → Prop :=
  fun left right =>
    privateOrdinalSelectionGoodForSomeOutput target rightRoot ordinal left →
      privateOrdinalSelectionGoodForSomeOutput target rightRoot ordinal right

theorem goodForRoots_clearPending_target
    {target : Position} {leftOutput : HashOutput} {rightRoot : Digest}
    {ordinal : Nat} {selection : PrivateOrdinalSelection}
    (hgood : selection.GoodForRoots target leftOutput rightRoot ordinal) :
    ({ selection with
        context := { selection.context with
          state := selection.context.state.clearPending (.position target) } } :
      PrivateOrdinalSelection).GoodForRoots target leftOutput rightRoot ordinal := by
  rcases hgood with ⟨hcandidate, hstate, hrevealed, hvalue, havoid⟩
  exact ⟨hcandidate, by simpa [LazyRevealProbe.State.clearPending] using hstate,
    by simpa [LazyRevealProbe.State.clearPending] using hrevealed, hvalue, havoid⟩

theorem relTriple_goodSelection_resolveDeferredPositionValue
    (target : Position) (rightRoot : Digest) (ordinal : Nat)
    (selection : PrivateOrdinalSelection)
    (hcovered : PendingCoveredBy (selection.candidates.take ordinal) selection.context) :
    RelTriple
      (pure (some selection) : ProbComp (Option PrivateOrdinalSelection))
      (resolveDeferredPositionValue target selection.context >>= fun resolved =>
        match resolved with
        | none => pure none
        | some resolved => pure (some
            { selection with context := resolved.toDeferredContext }))
      (PrivateOrdinalGoodRel target rightRoot ordinal) := by
  by_cases hgood : privateOrdinalSelectionGoodForSomeOutput target rightRoot ordinal (some selection)
  · obtain ⟨leftOutput, hgood⟩ := hgood
    rw [resolveDeferredPositionValue_eq_good_output hgood hcovered]
    simp only [pure_bind]
    apply relTriple_pure_pure
    intro _hleft
    exact ⟨leftOutput, by
      simpa [DeferredResolution.toDeferredContext] using goodForRoots_clearPending_target hgood⟩
  · apply relTriple_post_mono
      (SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support
        (relTriple_true
          (pure (some selection) : ProbComp (Option PrivateOrdinalSelection))
          (show ProbComp (Option PrivateOrdinalSelection) from
            resolveDeferredPositionValue target selection.context >>= fun resolved =>
              match resolved with
              | none => pure none
              | some resolved => pure (some
                  { selection with context := resolved.toDeferredContext })))
        (fun left => left = some selection) (by intro left hleft; simpa using hleft))
    intro left _right _hrelation hleft
    exact (hgood (_hrelation.2 ▸ hleft)).elim

noncomputable def resolvePrivateOrdinalSelection
    (target : Position) : Option PrivateOrdinalSelection →
      ProbComp (Option PrivateOrdinalSelection)
  | none => pure none
  | some selection =>
      resolveDeferredPositionValue target selection.context >>= fun resolved =>
        match resolved with
        | none => pure none
        | some resolved => pure (some
            { selection with context := resolved.toDeferredContext })

theorem relTriple_privateOrdinalSelection_resolve
    (target : Position) (rightRoot : Digest) (ordinal : Nat)
    (selection : Option PrivateOrdinalSelection)
    (hcovered : PrivateOrdinalSelectionPendingCovered ordinal selection) :
    RelTriple
      (pure selection : ProbComp (Option PrivateOrdinalSelection))
      (resolvePrivateOrdinalSelection target selection)
      (fun left right =>
        PrivateOrdinalGoodRel target rightRoot ordinal left right ∧ left = selection) := by
  apply SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support
  · cases selection with
    | none =>
        exact relTriple_pure_pure (fun hgood => False.elim hgood)
    | some selection =>
        exact relTriple_goodSelection_resolveDeferredPositionValue target rightRoot ordinal
          selection hcovered
  · intro left hleft
    simpa using hleft

def SuccessfulObservedResolvedSelectorRel
    (table : OtsSecretIndex → HashOutput) (ordinal : Nat) (target : Position) :
    (Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest) →
      (Option PrivateOrdinalSelection × Digest) → Prop :=
  fun observed resolved =>
    ∃ selection : Option PrivateOrdinalSelection × Digest,
      SuccessfulObservedPendingSelectorRel table ordinal target observed selection ∧
        PrivateOrdinalGoodRel target selection.2 ordinal selection.1 resolved.1 ∧
        selection.2 = resolved.2

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_observedSuccessfulRootComparison_resolvedSelector
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
      (SuccessfulObservedResolvedSelectorRel table ordinal target) := by
  have hbase := relTriple_observedSuccessfulRootComparison_pendingSelector ordinal adversary
    parameter table ftsSecret q target hbound hq
  have hboundPair : RelTriple
      ((do
        let observed ← observedMaterializedRetainedRunFromTable adversary parameter ftsSecret
          (2 * q) table
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (observed, rightRoot)) >>= fun observed => pure observed)
      ((do
        let selection ← granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter
          table ftsSecret q
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (selection, rightRoot)) >>= fun selection => do
          let resolved ← resolvePrivateOrdinalSelection target selection.1
          pure (resolved, selection.2))
      (SuccessfulObservedResolvedSelectorRel table ordinal target) := by
    apply relTriple_bind hbase
    intro observed selection hrelation
    obtain ⟨source, hsource, hselection, hpending⟩ := hrelation
    have hinner : RelTriple
        ((pure selection.1 : ProbComp (Option PrivateOrdinalSelection)) >>= fun _ => pure observed)
        (resolvePrivateOrdinalSelection target selection.1 >>= fun resolved =>
          pure (resolved, selection.2))
        (SuccessfulObservedResolvedSelectorRel table ordinal target) := by
      apply relTriple_bind
        (relTriple_privateOrdinalSelection_resolve target selection.2 ordinal selection.1
          hpending)
      intro original resolved hresolved
      have hgoodRel : PrivateOrdinalGoodRel target selection.2 ordinal selection.1 resolved := by
        rw [← hresolved.2]
        exact hresolved.1
      exact relTriple_pure_pure
        ⟨selection, ⟨source, hsource, hselection, hpending⟩, hgoodRel, rfl⟩
    simpa using hinner
  simpa [bind_assoc] using hboundPair

theorem SuccessfulObservedResolvedSelectorRel.goodForRoots
    {table : OtsSecretIndex → HashOutput} {ordinal : Nat} {target : Position}
    {observed : Option
      (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest}
    {resolved : Option PrivateOrdinalSelection × Digest}
    (hrelation : SuccessfulObservedResolvedSelectorRel table ordinal target observed resolved)
    (hgood : ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
      table ordinal target observed.2 observed.1) :
    privateOrdinalSelectionGoodForSomeOutput target resolved.2 ordinal resolved.1 := by
  obtain ⟨selection, hselection, hresolved, hroot⟩ := hrelation
  obtain ⟨selected, output, hselected, hgoodRoots, _hcovered⟩ :=
    hselection.goodForRoots_pendingCovered hgood
  rw [← hroot]
  exact hresolved (by rw [hselected]; exact ⟨output, hgoodRoots⟩)

theorem probEvent_cleanRootGoodForComparison_le_materializedMatch
    (table : OtsSecretIndex → HashOutput)
    (source : ProbComp PrivateWitnessSnapshotOutput)
    (outcome : ProbComp (Digest × Digest × MaterializedSelectionOutcome))
    (ordinal : Nat) (target : Position)
    (hrel : RelTriple
      (do
        let result ← source
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (result, rightRoot))
      outcome (CleanRootMaterializedMatchRel table ordinal target)) :
    Pr[fun result : PrivateWitnessSnapshotOutput × Digest =>
        SelectedPrivateSnapshotCleanRootGoodForComparisonAt
          table result.1 ordinal target result.2 | do
      let result ← source
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (result, rightRoot)] ≤
      Pr[fun result => result.2.2.Matches target result.1 | outcome] := by
  apply probEvent_le_of_relTriple hrel
  intro left right hrelation hgood
  exact hrelation hgood

theorem probEvent_cleanRootGoodForComparison_le_production_mul
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat)
    (hrel : RelTriple
      (do
        let source ← granularAllCanonicalPrivateWitnessSnapshot adversary parameter table
          ftsSecret fuel
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (source, rightRoot))
      (materializedRootOrdinalOutcomeExperimentAfterTable ordinal adversary parameter ftsSecret
        target fuel table)
      (CleanRootMaterializedMatchRel table ordinal target)) :
    Pr[fun result : PrivateWitnessSnapshotOutput × Digest =>
        SelectedPrivateSnapshotCleanRootGoodForComparisonAt
          table result.1 ordinal target result.2 | do
      let source ← granularAllCanonicalPrivateWitnessSnapshot adversary parameter table
        ftsSecret fuel
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (source, rightRoot)] ≤
      Pr[fun result => materializedOrdinalSelectionAt target result.2 |
          materializedRootOrdinalProductionExperimentAfterTable ordinal adversary parameter
            ftsSecret target fuel table] *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ ≤ Pr[fun result => result.2.2.Matches target result.1 |
          materializedRootOrdinalOutcomeExperimentAfterTable ordinal adversary parameter ftsSecret
            target fuel table] :=
      probEvent_cleanRootGoodForComparison_le_materializedMatch table
        (granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret fuel)
        (materializedRootOrdinalOutcomeExperimentAfterTable ordinal adversary parameter ftsSecret
          target fuel table) ordinal target hrel
    _ ≤ _ := probEvent_materializedRootOrdinalOutcome_match_le ordinal adversary parameter ftsSecret
      target hroot hparent fuel table

end SphincsSecurity.Concrete.OtsProbeSimulation
