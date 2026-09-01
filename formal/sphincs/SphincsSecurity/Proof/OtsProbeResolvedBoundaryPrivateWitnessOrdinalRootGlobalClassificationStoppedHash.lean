import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedSource

/-!
# Stopped root-aware hash boundary

The root-aware comparison executes its candidate probe before the probe-free public action. This
module exposes the exact hidden-candidate state at that boundary.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem runObservedCleanFromTable_rootAwarePublic_of_hidden
    (parameter : PublicParameter) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery)
    (candidate : Probe)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (remaining : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hcandidate : rootAwareCandidateForPlan? parameter input plan = some candidate)
    (hhidden : candidate.coordinate ∉ state.revealed) :
    runObservedCleanFromTable observations state (remaining + 1) table
        ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run cache) =
      runObservedCleanFromTable
        (observations ++ [cleanProbeObservation state
          candidate.coordinate candidate.candidate])
        (state.addPending candidate.coordinate candidate.candidate) remaining table
        ((probingHashQueryPublicAction parameter input publicState plan.action).run cache) := by
  unfold probingHashQueryAfterRootAwarePublicPlan
  rw [StateT.run_bind]
  simp only [executeCandidate?, hcandidate, probe, StateT.run_liftM,
    LazyRevealProbe.probeQuery]
  simp only [bind_assoc, pure_bind]
  rw [runObservedCleanFromTable_probe_query_bind]
  simp [hhidden]

noncomputable def observedMaterializedHashContinuation
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput) (plan : PlannedHashQuery)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp (Option (ObservedCleanRunResult (α × SplitHashCache))) := do
  let step ← runObservedCleanFromTable observations state fuel table
    ((probingHashQueryAfterRootAwarePublicPlan parameter input
      (materializedCanonicalContext table state).state plan).run cache)
  match step with
  | none => pure none
  | some step =>
      observedMaterializedBoundary parameter root ftsSecret (next step.value.1)
        step.observations step.state step.remaining table step.value.2

set_option maxRecDepth 100000 in
theorem stopped_data_of_mem_observedMaterializedHashContinuation
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput) (plan : PlannedHashQuery) (candidate : Probe)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (remaining : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ObservedCleanRunResult (α × SplitHashCache))
    (hcandidate : rootAwareCandidateForPlan? parameter input plan = some candidate)
    (hhidden : candidate.coordinate ∉ state.revealed)
    (hdoomed : DoomedResolvedContext table
      (directDeferredContext
        (state.addPending candidate.coordinate candidate.candidate)))
    (hresult : some result ∈ support
      (observedMaterializedHashContinuation parameter root ftsSecret input plan next observations
        state (remaining + 1) table cache)) :
    result.table = table ∧
      DoomedResolvedContext table (directDeferredContext result.state) ∧
      (observations ++ [cleanProbeObservation state
        candidate.coordinate candidate.candidate]) <+: result.observations := by
  unfold observedMaterializedHashContinuation at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨step?, hstep, hrest⟩ := hresult
  rw [runObservedCleanFromTable_rootAwarePublic_of_hidden parameter input
    (materializedCanonicalContext table state).state plan candidate observations state remaining
    table cache hcandidate hhidden] at hstep
  cases step? with
  | none => simp at hrest
  | some step =>
      have hstepDoomed := materializedDoomed_of_mem_runObservedCleanFromTable
        ((probingHashQueryPublicAction parameter input
          (materializedCanonicalContext table state).state plan.action).run cache)
        (observations ++ [cleanProbeObservation state
          candidate.coordinate candidate.candidate])
        (state.addPending candidate.coordinate candidate.candidate) remaining table step hdoomed
        hstep
      have hrestDoomed := materializedDoomed_of_mem_observedMaterializedBoundary parameter root
        ftsSecret (next step.value.1) step.observations step.state step.remaining table
        step.value.2 result hstepDoomed.2 hrest
      refine ⟨hrestDoomed.1, hrestDoomed.2, ?_⟩
      exact (observations_prefix_of_mem_runObservedCleanFromTable
        ((probingHashQueryPublicAction parameter input
          (materializedCanonicalContext table state).state plan.action).run cache)
        (observations ++ [cleanProbeObservation state
          candidate.coordinate candidate.candidate])
        (state.addPending candidate.coordinate candidate.candidate) remaining table step hstep).trans
        (observations_prefix_of_mem_observedMaterializedBoundary parameter root ftsSecret
          (next step.value.1) step.observations step.state step.remaining table step.value.2 result
          hrest)

set_option maxRecDepth 100000 in
theorem stopped_cause_of_mem_observedMaterializedHashContinuation
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput) (plan : PlannedHashQuery) (candidate : Probe)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (remaining : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ObservedCleanRunResult (α × SplitHashCache))
    (hcandidate : rootAwareCandidateForPlan? parameter input plan = some candidate)
    (hhidden : candidate.coordinate ∉ state.revealed)
    (hcause : MissingChainStartHit table
        (directDeferredContext
          (state.addPending candidate.coordinate candidate.candidate)) ∨
      FirstExistingHiddenChainStartHit
        (observations ++ [cleanProbeObservation state
          candidate.coordinate candidate.candidate]))
    (hresult : some result ∈ support
      (observedMaterializedHashContinuation parameter root ftsSecret input plan next observations
        state (remaining + 1) table cache)) :
    ObservedStoppedCause table result := by
  unfold observedMaterializedHashContinuation at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨step?, hstep, hrest⟩ := hresult
  rw [runObservedCleanFromTable_rootAwarePublic_of_hidden parameter input
    (materializedCanonicalContext table state).state plan candidate observations state remaining
    table cache hcandidate hhidden] at hstep
  cases step? with
  | none => simp at hrest
  | some step =>
      have hstepCause : MissingChainStartHit table (directDeferredContext step.state) ∨
          FirstExistingHiddenChainStartHit step.observations := by
        rcases hcause with hmissing | hchain
        · exact Or.inl (missingChainStartHit_of_mem_runObservedCleanFromTable
            ((probingHashQueryPublicAction parameter input
              (materializedCanonicalContext table state).state plan.action).run cache)
            (observations ++ [cleanProbeObservation state
              candidate.coordinate candidate.candidate])
            (state.addPending candidate.coordinate candidate.candidate) remaining table step
            hmissing hstep).2
        · exact Or.inr (hchain.prefix
            (observations_prefix_of_mem_runObservedCleanFromTable
              ((probingHashQueryPublicAction parameter input
                (materializedCanonicalContext table state).state plan.action).run cache)
              (observations ++ [cleanProbeObservation state
                candidate.coordinate candidate.candidate])
              (state.addPending candidate.coordinate candidate.candidate) remaining table step
              hstep))
      exact observedStoppedCause_of_mem_observedMaterializedBoundary parameter root ftsSecret
        (next step.value.1) step.observations step.state step.remaining table step.value.2 result
        hstepCause hrest

set_option maxRecDepth 100000 in
theorem candidatesAvoidRoot_of_aligned_tracked
    (table : OtsSecretIndex → HashOutput)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (candidate : Probe) (left right : DeferredContext)
    (hbefore : SnapshotsBefore snapshots left)
    (hcontext : FinalizationContextLE table left right)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hnoEarlier : ∀ observation ∈ observations,
      ¬observation.ExistingHiddenHit)
    (haligned : SnapshotsObservedAt table snapshots observations)
    (htracked : CleanProbeObservationsTrackedBy observations right.state)
    (position : Position) (output : HashOutput)
    (hcandidate : candidate = ⟨.position position, truncateHash output⟩)
    (hstate : left.state.values (.position position) = none)
    (hprivate : left.values position = some output)
    (hhidden : candidate.coordinate ∉ left.state.revealed) :
    CandidatesAvoidRoot position (truncateHash output)
      (snapshots.map PlannedProbeSnapshot.toProbe) := by
  have hleftHidden : Coordinate.position position ∉ left.state.revealed := by
    simpa [hcandidate] using hhidden
  have hleftResolved : resolvedCompletionValue table left (.position position) = some output := by
    simp [resolvedCompletionValue, DeferredContext.positionValue, hstate, hprivate]
  have hrightResolved :
      resolvedCompletionValue table right (.position position) = some output := by
    rw [← hcontext.view.valueEq]
    exact hleftResolved
  have hrightValue : right.state.values (.position position) = some output := by
    rw [hrightMaterialized] at hrightResolved
    cases hvalue : right.state.values (.position position) with
    | none =>
        simp [resolvedCompletionValue, DeferredContext.positionValue, directDeferredContext,
          directDeferredValues, hvalue] at hrightResolved
    | some stored =>
        have hstored : stored = output := by
          simpa [resolvedCompletionValue, DeferredContext.positionValue, directDeferredContext,
            directDeferredValues, hvalue] using hrightResolved
        simpa [hvalue, hstored]
  intro earlier hearlier heq
  obtain ⟨mappedOrdinal, hmapped⟩ := List.mem_iff_get.mp hearlier
  let snapshotOrdinal : Fin snapshots.length :=
    ⟨mappedOrdinal.val, by simpa using mappedOrdinal.isLt⟩
  have hsnapshotProbe : (snapshots.get snapshotOrdinal).probe = earlier := by
    simpa [snapshotOrdinal] using hmapped
  let observationOrdinal : Fin observations.length :=
    ⟨snapshotOrdinal.val, by rw [← haligned.length_eq]; exact snapshotOrdinal.isLt⟩
  have hpair := haligned.get snapshotOrdinal.isLt observationOrdinal.isLt
  have hpair' : PlannedProbeSnapshot.ObservedAt table
      (snapshots.get snapshotOrdinal) (observations.get observationOrdinal) := by
    simpa [observationOrdinal] using hpair
  have hobservationProbe :
      (observations.get observationOrdinal).toProbe =
        ⟨.position position, truncateHash output⟩ := by
    rw [hpair'.1, hsnapshotProbe, heq]
  have hobservationCoordinate :
      (observations.get observationOrdinal).coordinate = .position position :=
    congrArg Probe.coordinate hobservationProbe
  have hobservationCandidate :
      (observations.get observationOrdinal).candidate = truncateHash output :=
    congrArg Probe.candidate hobservationProbe
  have hsnapshotHidden : Coordinate.position position ∉
      (snapshots.get snapshotOrdinal).context.state.revealed := by
    intro hrevealed
    exact hleftHidden
      ((hbefore (snapshots.get snapshotOrdinal) (List.get_mem _ _)).1 hrevealed)
  have hobservationHidden :
      (observations.get observationOrdinal).revealedAtProbe = false := by
    rw [hpair'.2.2.1, hobservationCoordinate]
    exact decide_eq_false hsnapshotHidden
  have hobservationTracked := htracked (observations.get observationOrdinal)
    (List.get_mem _ _)
  cases hobservationValue :
      (observations.get observationOrdinal).valueAtProbe with
  | some stored =>
      have hstored := hobservationTracked.1 stored hobservationValue
      rw [hobservationCoordinate, hrightValue] at hstored
      have heqStored : stored = output := Option.some.inj hstored.symm
      subst stored
      exact (hnoEarlier (observations.get observationOrdinal) (List.get_mem _ _)
        ⟨hobservationHidden, output, hobservationValue, hobservationCandidate.symm⟩).elim
  | none =>
      rcases hobservationTracked.2 hobservationValue hobservationHidden with
        hpending | ⟨stored, hstored, hmismatch⟩
      · rw [hobservationCoordinate, hrightValue] at hpending
        simp at hpending
      · rw [hobservationCoordinate, hrightValue] at hstored
        have heqStored : stored = output := Option.some.inj hstored.symm
        subst stored
        exact (hmismatch hobservationCandidate.symm).elim

set_option maxRecDepth 100000 in
theorem relTriple_source_observedMaterializedHashContinuation_firstStopped_of_private
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput) (plan : PlannedHashQuery) (candidate : Probe)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (source : ProbComp PrivateWitnessSnapshotOutput)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (left right : DeferredContext) (remaining : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hcandidate : rootAwareCandidateForPlan? parameter input plan = some candidate)
    (hcontext : FinalizationContextLE table left right)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hhidden : candidate.coordinate ∉ right.state.revealed)
    (hnoEarlier : ∀ observation ∈ observations,
      ¬observation.ExistingHiddenHit)
    (haligned : SnapshotsObservedAt table snapshots observations)
    (hbefore : SnapshotsBefore snapshots left)
    (htracked : CleanProbeObservationsTrackedBy observations right.state)
    (hsource : ∀ output ∈ support source,
      PrivateWitnessSnapshotExtends
        (snapshots ++ [(⟨candidate, left⟩ : PlannedProbeSnapshot)]) output)
    (hhit : PrivateStructuralHit
      ({ left with
        state := left.state.addPending candidate.coordinate candidate.candidate } :
        DeferredContext))
    (hdoomed : DoomedResolvedContext table
      (directDeferredContext
        (right.state.addPending candidate.coordinate candidate.candidate))) :
    RelTriple source
      (observedMaterializedHashContinuation parameter root ftsSecret input plan next observations
        right.state (remaining + 1) table cache)
      (SnapshotObservedFirstStoppedRel table) := by
  have hbase := relTriple_true source
    (observedMaterializedHashContinuation parameter root ftsSecret input plan next observations
      right.state (remaining + 1) table cache)
  have hleft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun output => output ∈ support source) (fun output houtput => houtput)
  have hboth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
  apply relTriple_post_mono hboth
  intro sourceOutput observed hrelation
  cases observed with
  | none => exact Or.inl rfl
  | some result =>
      have hdata := stopped_data_of_mem_observedMaterializedHashContinuation parameter root
        ftsSecret input plan candidate next observations right.state remaining table cache result
        hcandidate hhidden hdoomed hrelation.2
      have hfirst := firstExistingHiddenHitAt_append_of_privateStructuralHit table candidate
        observations left right hcontext hrightMaterialized hhidden hnoEarlier hhit
      right
      right
      left
      have hlength : snapshots.length = observations.length := haligned.length_eq
      have hleftHidden : candidate.coordinate ∉ left.state.revealed := by
        rwa [hrevealed]
      have hextends := hsource sourceOutput hrelation.1.2
      have hfirstResult : FirstExistingHiddenHitAt result snapshots.length := by
        simpa [hlength] using hfirst.prefix hdata.2.2
      have hselected : SelectedPrivateSnapshotHitAt sourceOutput snapshots.length :=
        selectedPrivateSnapshotHitAt_of_appended_privateStructuralHit snapshots candidate left
          sourceOutput hextends hcontext.leftCompletable hleftHidden
          (fun position output hcandidate' hstate hprivate =>
            candidatesAvoidRoot_of_aligned_tracked table snapshots observations candidate left right
              hbefore hcontext hrightMaterialized hnoEarlier haligned htracked position output
              hcandidate' hstate hprivate hleftHidden)
          hhit
      have hsourceLt : snapshots.length < sourceOutput.2.length := by
        have hprefixLength := hextends.length_le
        simpa using (Nat.lt_of_lt_of_le (by simp : snapshots.length <
          (snapshots ++ [(⟨candidate, left⟩ : PlannedProbeSnapshot)]).length) hprefixLength)
      let sourceOrdinal : Fin sourceOutput.2.length := ⟨snapshots.length, hsourceLt⟩
      have hsourceProbe : (sourceOutput.2.get sourceOrdinal).probe = candidate := by
        obtain ⟨tail, htail⟩ := hextends
        simp [← htail, sourceOrdinal]
      have hobservedLt : observations.length < result.observations.length :=
        (by simp : observations.length <
          (observations ++ [cleanProbeObservation right.state candidate.coordinate
            candidate.candidate]).length) |>.trans_le hdata.2.2.length_le
      let observedOrdinal : Fin result.observations.length :=
        ⟨observations.length, hobservedLt⟩
      have hobservedProbe :
          (result.observations.get observedOrdinal).toProbe = candidate := by
        obtain ⟨tail, htail⟩ := hdata.2.2
        simp [← htail, observedOrdinal, cleanProbeObservation,
          CleanProbeObservation.toProbe]
      have hselectedAligned :
          SelectedSnapshotObservationAlignedAt sourceOutput result snapshots.length :=
        ⟨sourceOrdinal, observedOrdinal, rfl, hlength.symm,
          hsourceProbe.trans hobservedProbe.symm⟩
      exact ⟨result, snapshots.length, rfl, hdata.1, hdata.2.1, hfirstResult, hselected,
        hselectedAligned⟩

set_option maxRecDepth 100000 in
theorem relTriple_source_observedMaterializedHashContinuation_firstStopped_of_cause
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput) (plan : PlannedHashQuery) (candidate : Probe)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (source : ProbComp PrivateWitnessSnapshotOutput)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (remaining : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hcandidate : rootAwareCandidateForPlan? parameter input plan = some candidate)
    (hhidden : candidate.coordinate ∉ state.revealed)
    (hdoomed : DoomedResolvedContext table
      (directDeferredContext
        (state.addPending candidate.coordinate candidate.candidate)))
    (hcause : MissingChainStartHit table
        (directDeferredContext
          (state.addPending candidate.coordinate candidate.candidate)) ∨
      FirstExistingHiddenChainStartHit
        (observations ++ [cleanProbeObservation state
          candidate.coordinate candidate.candidate])) :
    RelTriple source
      (observedMaterializedHashContinuation parameter root ftsSecret input plan next observations
        state (remaining + 1) table cache)
      (SnapshotObservedFirstStoppedRel table) := by
  have hbase := relTriple_true source
    (observedMaterializedHashContinuation parameter root ftsSecret input plan next observations
      state (remaining + 1) table cache)
  have hboth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hbase
  apply relTriple_post_mono hboth
  intro sourceOutput observed hrelation
  cases observed with
  | none => exact Or.inl rfl
  | some result =>
      have hdata := stopped_data_of_mem_observedMaterializedHashContinuation parameter root
        ftsSecret input plan candidate next observations state remaining table cache result
        hcandidate hhidden hdoomed hrelation.2
      right
      right
      right
      exact ⟨result, rfl, hdata.1, hdata.2.1,
        stopped_cause_of_mem_observedMaterializedHashContinuation parameter root ftsSecret input
          plan candidate next observations state remaining table cache result hcandidate hhidden
          hcause hrelation.2⟩

set_option maxRecDepth 100000 in
theorem relTriple_source_observedMaterializedHashContinuation_firstStopped_of_notCompletable
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput) (plan : PlannedHashQuery) (candidate : Probe)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (source : ProbComp PrivateWitnessSnapshotOutput)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (left right : DeferredContext) (remaining : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hcandidate : rootAwareCandidateForPlan? parameter input plan = some candidate)
    (hcontext : FinalizationContextLE table left right)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hcanonical : CanonicalMaterializedValues table left)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hhidden : candidate.coordinate ∉ right.state.revealed)
    (hnoEarlier : ∀ observation ∈ observations,
      ¬observation.ExistingHiddenHit)
    (haligned : SnapshotsObservedAt table snapshots observations)
    (hbefore : SnapshotsBefore snapshots left)
    (htracked : CleanProbeObservationsTrackedBy observations right.state)
    (hsource : ∀ output ∈ support source,
      PrivateWitnessSnapshotExtends
        (snapshots ++ [(⟨candidate, left⟩ : PlannedProbeSnapshot)]) output)
    (hcard : (right.state.addPending candidate.coordinate candidate.candidate).pending.card <
      Fintype.card Digest)
    (hnotCompletable : ¬DeferredCompletable table
      ({ right with
        state := right.state.addPending candidate.coordinate candidate.candidate } :
        DeferredContext)) :
    RelTriple source
      (observedMaterializedHashContinuation parameter root ftsSecret input plan next observations
        right.state (remaining + 1) table cache)
      (SnapshotObservedFirstStoppedRel table) := by
  let nextRight : DeferredContext :=
    { right with
      state := right.state.addPending candidate.coordinate candidate.candidate }
  have hnextRight : nextRight = directDeferredContext
      (right.state.addPending candidate.coordinate candidate.candidate) := by
    dsimp [nextRight]
    rw [hrightMaterialized]
    simp [directDeferredContext, directDeferredValues_addPending]
  have hdoomed : DoomedResolvedContext table
      (directDeferredContext
        (right.state.addPending candidate.coordinate candidate.candidate)) := by
    rw [← hnextRight]
    exact ⟨hcontext.rightValid.valuesConsistent.addPending candidate.coordinate
      candidate.candidate,
      hcontext.view.rightStarts.addPending candidate.coordinate candidate.candidate,
      hnotCompletable⟩
  have hcauses := candidateStopCause_of_not_completable table candidate observations left right
    hcontext hrevealed hcanonical hrightMaterialized hhidden hnoEarlier hcard hnotCompletable
  rcases hcauses with hprivate | hmissing | hchain
  · exact relTriple_source_observedMaterializedHashContinuation_firstStopped_of_private
      parameter root ftsSecret input plan candidate next source snapshots observations left right
      remaining table cache hcandidate hcontext hrevealed hrightMaterialized hhidden hnoEarlier
      haligned hbefore htracked hsource hprivate hdoomed
  · apply relTriple_source_observedMaterializedHashContinuation_firstStopped_of_cause
      parameter root ftsSecret input plan candidate next source observations right.state remaining
      table cache hcandidate hhidden hdoomed
    exact Or.inl (by rwa [← hnextRight])
  · exact relTriple_source_observedMaterializedHashContinuation_firstStopped_of_cause
      parameter root ftsSecret input plan candidate next source observations right.state remaining
      table cache hcandidate hhidden hdoomed (Or.inr hchain)
