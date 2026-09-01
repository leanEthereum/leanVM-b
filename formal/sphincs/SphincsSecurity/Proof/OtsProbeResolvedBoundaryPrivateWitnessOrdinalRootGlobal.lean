import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelectionBoundary

/-!
# Global root boundary

The early clean failure is split before the delayed witness is classified by ordinal or position.
This module contains the probability rule used by that split. The failure event lives on the
comparison run, while the residual event stays on the original run, so later unions cannot copy
the failure term.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

structure CleanProbeObservation where
  coordinate : Coordinate
  candidate : Digest
  valueAtProbe : Option HashOutput
  revealedAtProbe : Bool
deriving DecidableEq

def CleanProbeObservation.toProbe (observation : CleanProbeObservation) : Probe :=
  ⟨observation.coordinate, observation.candidate⟩

def cleanProbeObservation (state : LazyRevealProbe.State Coordinate)
    (coordinate : Coordinate) (candidate : Digest) : CleanProbeObservation :=
  { coordinate := coordinate
    candidate := candidate
    valueAtProbe := state.values coordinate
    revealedAtProbe := decide (coordinate ∈ state.revealed) }

def CleanProbeObservation.TrackedBy
    (observation : CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) : Prop :=
  (∀ output, observation.valueAtProbe = some output →
      state.values observation.coordinate = some output) ∧
    (observation.valueAtProbe = none → observation.revealedAtProbe = false →
      ((observation.coordinate, observation.candidate) ∈ state.pending ∧
          state.values observation.coordinate = none) ∨
        ∃ output, state.values observation.coordinate = some output ∧
          truncateHash output ≠ observation.candidate)

def CleanProbeObservationsTrackedBy
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) : Prop :=
  ∀ observation ∈ observations, observation.TrackedBy state

def CleanProbeObservationsCoverPending
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) : Prop :=
  ∀ entry ∈ state.pending,
    ∃ observation ∈ observations,
      observation.coordinate = entry.1 ∧
        observation.candidate = entry.2 ∧ observation.revealedAtProbe = false

theorem CleanProbeObservationsCoverPending.mono
    {prior later : List CleanProbeObservation}
    {state : LazyRevealProbe.State Coordinate}
    (hcovered : CleanProbeObservationsCoverPending prior state)
    (hsublist : prior.Sublist later) :
    CleanProbeObservationsCoverPending later state := by
  intro entry hentry
  obtain ⟨observation, hobservation, hcoordinate, hcandidate, hhidden⟩ :=
    hcovered entry hentry
  exact ⟨observation, hsublist.subset hobservation, hcoordinate, hcandidate, hhidden⟩

theorem CleanProbeObservationsCoverPending.state_subset
    {observations : List CleanProbeObservation}
    {left right : LazyRevealProbe.State Coordinate}
    (hcovered : CleanProbeObservationsCoverPending observations right)
    (hsubset : left.pending ⊆ right.pending) :
    CleanProbeObservationsCoverPending observations left := by
  intro entry hentry
  exact hcovered entry (hsubset hentry)

theorem CleanProbeObservationsCoverPending.ensure
    {observations : List CleanProbeObservation}
    {state : LazyRevealProbe.State Coordinate}
    (hcovered : CleanProbeObservationsCoverPending observations state)
    (coordinate : Coordinate) :
    CleanProbeObservationsCoverPending observations (state.ensure coordinate) := by
  exact hcovered

theorem CleanProbeObservationsCoverPending.publish
    {observations : List CleanProbeObservation}
    {state : LazyRevealProbe.State Coordinate}
    (hcovered : CleanProbeObservationsCoverPending observations state)
    (coordinate : Coordinate) :
    CleanProbeObservationsCoverPending observations (state.publish coordinate) := by
  exact hcovered

theorem CleanProbeObservationsCoverPending.materialize
    {observations : List CleanProbeObservation}
    {state : LazyRevealProbe.State Coordinate}
    (hcovered : CleanProbeObservationsCoverPending observations state)
    (coordinate : Coordinate) (output : HashOutput) :
    CleanProbeObservationsCoverPending observations
      (state.materialize coordinate output) := by
  apply hcovered.state_subset
  intro entry hentry
  exact (Finset.mem_filter.1 hentry).1

theorem cleanProbeObservationsCoverPending_append_revealed
    {observations : List CleanProbeObservation}
    {state : LazyRevealProbe.State Coordinate}
    (hcovered : CleanProbeObservationsCoverPending observations state)
    (coordinate : Coordinate) (candidate : Digest) :
    CleanProbeObservationsCoverPending
      (observations ++ [cleanProbeObservation state coordinate candidate]) state := by
  apply hcovered.mono
  exact List.sublist_append_left _ _

theorem cleanProbeObservationsCoverPending_append_hidden
    {observations : List CleanProbeObservation}
    {state : LazyRevealProbe.State Coordinate}
    (hcovered : CleanProbeObservationsCoverPending observations state)
    (coordinate : Coordinate) (candidate : Digest)
    (hhidden : coordinate ∉ state.revealed) :
    CleanProbeObservationsCoverPending
      (observations ++ [cleanProbeObservation state coordinate candidate])
      (state.addPending coordinate candidate) := by
  intro entry hentry
  simp only [LazyRevealProbe.State.addPending, Finset.mem_insert] at hentry
  rcases hentry with rfl | hold
  · exact ⟨cleanProbeObservation state coordinate candidate, by simp,
      by simp [cleanProbeObservation], by simp [cleanProbeObservation], by
        simp [cleanProbeObservation, hhidden]⟩
  · obtain ⟨observation, hobservation, hcoordinate, hcandidate, hhidden⟩ :=
      hcovered entry hold
    exact ⟨observation, by simp [hobservation], hcoordinate, hcandidate, hhidden⟩

def CleanProbeObservation.ResolvedSafe
    (observation : CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) : Prop :=
  observation.valueAtProbe = none → observation.revealedAtProbe = false →
    ∀ output, state.values observation.coordinate = some output →
      truncateHash output ≠ observation.candidate

def CleanProbeObservationsResolvedSafe
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) : Prop :=
  ∀ observation ∈ observations, observation.ResolvedSafe state

theorem CleanProbeObservation.resolvedSafe_of_trackedBy
    {observation : CleanProbeObservation}
    {state : LazyRevealProbe.State Coordinate}
    (htracked : observation.TrackedBy state) : observation.ResolvedSafe state := by
  intro hnone hhidden output hvalue
  rcases htracked.2 hnone hhidden with hpending | hmaterialized
  · rw [hpending.2] at hvalue
    simp at hvalue
  · obtain ⟨stored, hstored, hmismatch⟩ := hmaterialized
    have : stored = output := Option.some.inj (hstored.symm.trans hvalue)
    subst output
    exact hmismatch

theorem cleanProbeObservationsResolvedSafe_of_trackedBy
    {observations : List CleanProbeObservation}
    {state : LazyRevealProbe.State Coordinate}
  (htracked : CleanProbeObservationsTrackedBy observations state) :
    CleanProbeObservationsResolvedSafe observations state := by
  intro observation hobservation
  exact CleanProbeObservation.resolvedSafe_of_trackedBy
    (htracked observation hobservation)

theorem CleanProbeObservation.TrackedBy.ensure
    {observation : CleanProbeObservation}
    {state : LazyRevealProbe.State Coordinate}
    (htracked : observation.TrackedBy state) (coordinate : Coordinate) :
    observation.TrackedBy (state.ensure coordinate) := by
  simpa [CleanProbeObservation.TrackedBy, LazyRevealProbe.State.ensure] using htracked

theorem CleanProbeObservation.TrackedBy.addPending
    {observation : CleanProbeObservation}
    {state : LazyRevealProbe.State Coordinate}
    (htracked : observation.TrackedBy state) (coordinate : Coordinate)
    (candidate : Digest) :
    observation.TrackedBy (state.addPending coordinate candidate) := by
  constructor
  · simpa [LazyRevealProbe.State.addPending] using htracked.1
  · intro hnone hhidden
    rcases htracked.2 hnone hhidden with hpending | hmaterialized
    · exact Or.inl ⟨Finset.mem_insert_of_mem hpending.1, hpending.2⟩
    · exact Or.inr hmaterialized

theorem CleanProbeObservation.TrackedBy.publish
    {observation : CleanProbeObservation}
    {state : LazyRevealProbe.State Coordinate}
    (htracked : observation.TrackedBy state) (coordinate : Coordinate) :
    observation.TrackedBy (state.publish coordinate) := by
  simpa [CleanProbeObservation.TrackedBy, LazyRevealProbe.State.publish] using htracked

theorem CleanProbeObservation.TrackedBy.materialize
    {observation : CleanProbeObservation}
    {state : LazyRevealProbe.State Coordinate}
    (htracked : observation.TrackedBy state) (coordinate : Coordinate)
    (output : HashOutput) (hvalue : state.values coordinate = none)
    (hmiss : ¬state.hitAt coordinate output) :
    observation.TrackedBy (state.materialize coordinate output) := by
  constructor
  · intro stored hobservation
    have hstored := htracked.1 stored hobservation
    by_cases heq : observation.coordinate = coordinate
    · subst coordinate
      rw [hvalue] at hstored
      simp at hstored
    · simpa [LazyRevealProbe.State.materialize, Function.update_of_ne heq] using hstored
  · intro hnone hhidden
    rcases htracked.2 hnone hhidden with hpending | hmaterialized
    · by_cases heq : observation.coordinate = coordinate
      · subst coordinate
        right
        refine ⟨output, by simp [LazyRevealProbe.State.materialize], ?_⟩
        intro hdigest
        apply hmiss
        unfold LazyRevealProbe.State.hitAt
        rw [LazyRevealProbe.State.mem_pendingAt_iff]
        simpa [hdigest] using hpending.1
      · left
        refine ⟨?_, ?_⟩
        · simp only [LazyRevealProbe.State.materialize,
            LazyRevealProbe.State.pendingAway, Finset.mem_filter]
          exact ⟨hpending.1, heq⟩
        · simp [LazyRevealProbe.State.materialize, Function.update_of_ne heq]
          exact hpending.2
    · obtain ⟨stored, hstored, hmismatch⟩ := hmaterialized
      by_cases heq : observation.coordinate = coordinate
      · subst coordinate
        rw [hvalue] at hstored
        simp at hstored
      · right
        refine ⟨stored, ?_, hmismatch⟩
        simpa [LazyRevealProbe.State.materialize, Function.update_of_ne heq] using hstored

theorem CleanProbeObservation.TrackedBy.complete
    {observation : CleanProbeObservation}
    {state : LazyRevealProbe.State Coordinate}
    (htracked : observation.TrackedBy state) (coordinate : Coordinate)
    (output : HashOutput) (hvalue : state.values coordinate = none)
    (hmiss : ¬state.hitAt coordinate output) :
    observation.TrackedBy (state.complete coordinate output) := by
  constructor
  · intro stored hobservation
    have hstored := htracked.1 stored hobservation
    by_cases heq : observation.coordinate = coordinate
    · subst coordinate
      rw [hvalue] at hstored
      simp at hstored
    · simpa [LazyRevealProbe.State.complete, Function.update_of_ne heq] using hstored
  · intro hnone hhidden
    rcases htracked.2 hnone hhidden with hpending | hmaterialized
    · by_cases heq : observation.coordinate = coordinate
      · subst coordinate
        right
        refine ⟨output, by simp [LazyRevealProbe.State.complete], ?_⟩
        intro hdigest
        apply hmiss
        unfold LazyRevealProbe.State.hitAt
        rw [LazyRevealProbe.State.mem_pendingAt_iff]
        simpa [hdigest] using hpending.1
      · left
        refine ⟨?_, ?_⟩
        · simp only [LazyRevealProbe.State.complete,
            LazyRevealProbe.State.pendingAway, Finset.mem_filter]
          exact ⟨hpending.1, heq⟩
        · simp [LazyRevealProbe.State.complete, Function.update_of_ne heq]
          exact hpending.2
    · obtain ⟨stored, hstored, hmismatch⟩ := hmaterialized
      by_cases heq : observation.coordinate = coordinate
      · subst coordinate
        rw [hvalue] at hstored
        simp at hstored
      · right
        refine ⟨stored, ?_, hmismatch⟩
        simpa [LazyRevealProbe.State.complete, Function.update_of_ne heq] using hstored

theorem CleanProbeObservation.TrackedBy.clearPending
    {observation : CleanProbeObservation}
    {state : LazyRevealProbe.State Coordinate}
    (htracked : observation.TrackedBy state) (coordinate : Coordinate)
    (output : HashOutput) (hvalue : state.values coordinate = some output) :
    observation.TrackedBy (state.clearPending coordinate) := by
  constructor
  · simpa [LazyRevealProbe.State.clearPending] using htracked.1
  · intro hnone hhidden
    rcases htracked.2 hnone hhidden with hpending | hmaterialized
    · by_cases heq : observation.coordinate = coordinate
      · subst coordinate
        rw [hvalue] at hpending
        simp at hpending
      · left
        refine ⟨?_, ?_⟩
        · simp only [LazyRevealProbe.State.clearPending,
            LazyRevealProbe.State.pendingAway, Finset.mem_filter]
          exact ⟨hpending.1, heq⟩
        · exact hpending.2
    · exact Or.inr hmaterialized

theorem CleanProbeObservationsTrackedBy.ensure
    {observations : List CleanProbeObservation}
    {state : LazyRevealProbe.State Coordinate}
    (htracked : CleanProbeObservationsTrackedBy observations state)
    (coordinate : Coordinate) :
    CleanProbeObservationsTrackedBy observations (state.ensure coordinate) := by
  intro observation hobservation
  exact (htracked observation hobservation).ensure coordinate

theorem CleanProbeObservationsTrackedBy.addPending
    {observations : List CleanProbeObservation}
    {state : LazyRevealProbe.State Coordinate}
    (htracked : CleanProbeObservationsTrackedBy observations state)
    (coordinate : Coordinate) (candidate : Digest) :
    CleanProbeObservationsTrackedBy observations
      (state.addPending coordinate candidate) := by
  intro observation hobservation
  exact (htracked observation hobservation).addPending coordinate candidate

theorem CleanProbeObservationsTrackedBy.publish
    {observations : List CleanProbeObservation}
    {state : LazyRevealProbe.State Coordinate}
    (htracked : CleanProbeObservationsTrackedBy observations state)
    (coordinate : Coordinate) :
    CleanProbeObservationsTrackedBy observations (state.publish coordinate) := by
  intro observation hobservation
  exact (htracked observation hobservation).publish coordinate

theorem CleanProbeObservationsTrackedBy.materialize
    {observations : List CleanProbeObservation}
    {state : LazyRevealProbe.State Coordinate}
    (htracked : CleanProbeObservationsTrackedBy observations state)
    (coordinate : Coordinate) (output : HashOutput)
    (hvalue : state.values coordinate = none)
    (hmiss : ¬state.hitAt coordinate output) :
    CleanProbeObservationsTrackedBy observations
      (state.materialize coordinate output) := by
  intro observation hobservation
  exact (htracked observation hobservation).materialize coordinate output hvalue hmiss

theorem CleanProbeObservationsTrackedBy.complete
    {observations : List CleanProbeObservation}
    {state : LazyRevealProbe.State Coordinate}
    (htracked : CleanProbeObservationsTrackedBy observations state)
    (coordinate : Coordinate) (output : HashOutput)
    (hvalue : state.values coordinate = none)
    (hmiss : ¬state.hitAt coordinate output) :
    CleanProbeObservationsTrackedBy observations
      (state.complete coordinate output) := by
  intro observation hobservation
  exact (htracked observation hobservation).complete coordinate output hvalue hmiss

theorem CleanProbeObservationsTrackedBy.clearPending
    {observations : List CleanProbeObservation}
    {state : LazyRevealProbe.State Coordinate}
    (htracked : CleanProbeObservationsTrackedBy observations state)
    (coordinate : Coordinate) (output : HashOutput)
    (hvalue : state.values coordinate = some output) :
    CleanProbeObservationsTrackedBy observations
      (state.clearPending coordinate) := by
  intro observation hobservation
  exact (htracked observation hobservation).clearPending coordinate output hvalue

theorem cleanProbeObservationsTrackedBy_append_revealed
    {observations : List CleanProbeObservation}
    {state : LazyRevealProbe.State Coordinate}
    (htracked : CleanProbeObservationsTrackedBy observations state)
    (coordinate : Coordinate) (candidate : Digest)
    (hrevealed : coordinate ∈ state.revealed) :
    CleanProbeObservationsTrackedBy
      (observations ++ [cleanProbeObservation state coordinate candidate]) state := by
  intro observation hobservation
  simp only [List.mem_append, List.mem_singleton] at hobservation
  rcases hobservation with hold | rfl
  · exact htracked observation hold
  · constructor
    · intro output hvalue
      simpa [cleanProbeObservation] using hvalue
    · intro _hnone hhidden
      simp [cleanProbeObservation, hrevealed] at hhidden

theorem cleanProbeObservationsTrackedBy_append_hidden
    {observations : List CleanProbeObservation}
    {state : LazyRevealProbe.State Coordinate}
    (htracked : CleanProbeObservationsTrackedBy observations state)
    (coordinate : Coordinate) (candidate : Digest)
    (hhidden : coordinate ∉ state.revealed) :
    CleanProbeObservationsTrackedBy
      (observations ++ [cleanProbeObservation state coordinate candidate])
      (state.addPending coordinate candidate) := by
  intro observation hobservation
  simp only [List.mem_append, List.mem_singleton] at hobservation
  rcases hobservation with hold | rfl
  · exact (htracked observation hold).addPending coordinate candidate
  · constructor
    · intro output hvalue
      simpa [cleanProbeObservation, LazyRevealProbe.State.addPending] using hvalue
    · intro hnone _hrevealed
      exact Or.inl
        ⟨by simp [cleanProbeObservation, LazyRevealProbe.State.addPending], hnone⟩

structure ObservedCleanRunResult (alpha : Type) where
  state : LazyRevealProbe.State Coordinate
  remaining : Nat
  value : alpha
  table : OtsSecretIndex → HashOutput
  observations : List CleanProbeObservation

def WitnessFirstUsesDelayedLayerRoot
    (output : PrivateWitnessPlanOutput)
    (observations : List CleanProbeObservation) : Prop :=
  ∃ witness, ∃ sourceOrdinal : Fin output.2.length,
    ∃ observationOrdinal : Fin observations.length,
      output.1 = some witness ∧
        sourceOrdinal.val = observationOrdinal.val ∧
        firstPrivateWitnessOrdinal? witness output.2 = some sourceOrdinal ∧
        (output.2.get sourceOrdinal).IsLayerRoot ∧
        (observations.get observationOrdinal).valueAtProbe = some witness.output

set_option maxRecDepth 100000 in
theorem witnessFirstUsesDelayedLayerRoot_of_aligned_tracked
    {output : PrivateWitnessPlanOutput}
    {result : ObservedCleanRunResult α}
    (hfirst : WitnessFirstUsesSomeLayerRoot output)
    (halign : output.2.IsPrefix
      (result.observations.map CleanProbeObservation.toProbe))
    (htracked : CleanProbeObservationsTrackedBy result.observations result.state)
    (hstored : ∀ witness, output.1 = some witness →
      result.state.values (Coordinate.position witness.position) = some witness.output)
    (hselectedHidden : ∀ witness (sourceOrdinal : Fin output.2.length)
      (observationOrdinal : Fin result.observations.length),
      output.1 = some witness →
      sourceOrdinal.val = observationOrdinal.val →
      firstPrivateWitnessOrdinal? witness output.2 = some sourceOrdinal →
      (result.observations.get observationOrdinal).revealedAtProbe = false) :
    WitnessFirstUsesDelayedLayerRoot output result.observations := by
  obtain ⟨ordinal, witness, sourceOrdinal, hwitness, hordinal, hsourceFirst, hroot⟩ := hfirst
  have hlength : output.2.length ≤ result.observations.length := by
    simpa using halign.length_le
  let observationOrdinal : Fin result.observations.length :=
    ⟨sourceOrdinal.val, sourceOrdinal.isLt.trans_le hlength⟩
  have hordinalValue : sourceOrdinal.val = observationOrdinal.val := rfl
  have hprobe : (result.observations.get observationOrdinal).toProbe =
      output.2.get sourceOrdinal := by
    rw [List.get_eq_getElem, List.get_eq_getElem]
    change (result.observations[sourceOrdinal.val]).toProbe =
      output.2[sourceOrdinal.val]
    rw [halign.getElem sourceOrdinal.isLt, List.getElem_map]
  have hmatch := privateWitnessAtOrdinal_of_firstPrivateWitnessOrdinal?_eq_some hsourceFirst
  unfold PrivateWitnessAtOrdinal at hmatch
  have hobservationCoordinate :
      (result.observations.get observationOrdinal).coordinate =
        Coordinate.position witness.position := by
    exact congrArg Probe.coordinate hprobe |>.trans hmatch.1
  have hobservationCandidate :
      (result.observations.get observationOrdinal).candidate = truncateHash witness.output := by
    exact congrArg Probe.candidate hprobe |>.trans hmatch.2.symm
  have hhidden := hselectedHidden witness sourceOrdinal observationOrdinal hwitness
    hordinalValue hsourceFirst
  have hobservationTracked := htracked (result.observations.get observationOrdinal)
    (List.get_mem _ _)
  cases hvalue : (result.observations.get observationOrdinal).valueAtProbe with
  | none =>
      have hsafe := CleanProbeObservation.resolvedSafe_of_trackedBy hobservationTracked
      have hfinalAtObservation : result.state.values
          (result.observations.get observationOrdinal).coordinate = some witness.output := by
        rw [hobservationCoordinate]
        exact hstored witness hwitness
      have hmismatch := hsafe hvalue hhidden witness.output hfinalAtObservation
      exact False.elim (hmismatch (hobservationCandidate.symm))
  | some stored =>
      have hstoredAtFinal := hobservationTracked.1 stored hvalue
      rw [hobservationCoordinate] at hstoredAtFinal
      have hstoredEq : stored = witness.output :=
        Option.some.inj (hstoredAtFinal.symm.trans (hstored witness hwitness))
      subst stored
      exact ⟨witness, sourceOrdinal, observationOrdinal, hwitness,
        hordinalValue, hsourceFirst, hroot, hvalue⟩

def ObservedCleanRunResult.toClean
    (result : ObservedCleanRunResult α) : CleanRunResult α :=
  ⟨result.state, result.remaining, result.value, result.table⟩

def projectObservedCleanRun :
    Option (ObservedCleanRunResult α) → Option (CleanRunResult α)
  | none => none
  | some result => some result.toClean

noncomputable def runObservedCleanFromTable
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    ProbComp (Option (ObservedCleanRunResult α)) :=
  OracleComp.construct
    (C := fun _ : OracleComp (LazyRevealProbe.World Coordinate) α =>
      List CleanProbeObservation → LazyRevealProbe.State Coordinate → Nat →
        (OtsSecretIndex → HashOutput) →
          ProbComp (Option (ObservedCleanRunResult α)))
    (fun value observations state remaining table =>
      pure (some ⟨state, remaining, value, table, observations⟩))
    (fun input _next recursivelyRun observations state fuel table =>
      match input with
      | .uniform n => do
          let output ← liftM (unifSpec.query n)
          recursivelyRun output observations state fuel table
      | .hashOutput => do
          let output ← LazyRevealProbe.sampleHashOutput
          recursivelyRun output observations state fuel table
      | .ensure coordinate =>
          recursivelyRun () observations (state.ensure coordinate) fuel table
      | .probe coordinate candidate =>
          match fuel with
          | 0 => pure none
          | remaining + 1 =>
              let observation := cleanProbeObservation state coordinate candidate
              let nextObservations := observations ++ [observation]
              if coordinate ∈ state.revealed then
                recursivelyRun () nextObservations state remaining table
              else
                recursivelyRun () nextObservations
                  (state.addPending coordinate candidate) remaining table
      | .peek coordinate =>
          recursivelyRun (state.values coordinate) observations state fuel table
      | .publish coordinate =>
          recursivelyRun () observations (state.publish coordinate) fuel table
      | .reveal coordinate =>
          match state.values coordinate with
          | some output => recursivelyRun output observations state fuel table
          | none =>
              match coordinate with
              | .chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  if state.hitAt coordinate output then
                    pure none
                  else
                    recursivelyRun output observations
                      (state.materialize coordinate output) fuel table
              | .position _ => do
                  let output ← LazyRevealProbe.sampleHashOutput
                  if state.hitAt coordinate output then
                    pure none
                  else
                    recursivelyRun output observations
                      (state.materialize coordinate output) fuel table)
    computation observations state fuel table

theorem runObservedCleanFromTable_probe_query_bind
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (candidate : Digest)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) α) :
    runObservedCleanFromTable observations state fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.probe coordinate candidate)) :
            OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      match fuel with
      | 0 => pure none
      | remaining + 1 =>
          let observation := cleanProbeObservation state coordinate candidate
          let nextObservations := observations ++ [observation]
          if coordinate ∈ state.revealed then
            runObservedCleanFromTable nextObservations state remaining table (next ())
          else
            runObservedCleanFromTable nextObservations
              (state.addPending coordinate candidate) remaining table (next ()) := by
  rfl

set_option maxRecDepth 100000 in
theorem cleanProbeObservationsTrackedBy_of_mem_runObservedCleanFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (htracked : CleanProbeObservationsTrackedBy observations state)
    (result : ObservedCleanRunResult α)
    (hresult : some result ∈ support
      (runObservedCleanFromTable observations state fuel table computation)) :
    CleanProbeObservationsTrackedBy result.observations result.state := by
  induction computation using OracleComp.inductionOn generalizing
      observations state fuel table with
  | pure value =>
      simp [runObservedCleanFromTable] at hresult
      subst result
      exact htracked
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output observations state fuel table htracked hrest
      | hashOutput =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output observations state fuel table htracked hrest
      | ensure coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
          exact ih () observations (state.ensure coordinate) fuel table
            (htracked.ensure coordinate) hresult
      | probe coordinate candidate =>
          rw [runObservedCleanFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · exact ih ()
                  (observations ++ [cleanProbeObservation state coordinate candidate])
                  state remaining table
                  (cleanProbeObservationsTrackedBy_append_revealed htracked coordinate candidate
                    hrevealed)
                  (by simpa [hrevealed] using hresult)
              · exact ih ()
                  (observations ++ [cleanProbeObservation state coordinate candidate])
                  (state.addPending coordinate candidate) remaining table
                  (cleanProbeObservationsTrackedBy_append_hidden htracked coordinate candidate
                    hrevealed)
                  (by simpa [hrevealed] using hresult)
      | peek coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
          exact ih (state.values coordinate) observations state fuel table htracked hresult
      | publish coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
          exact ih () observations (state.publish coordinate) fuel table
            (htracked.publish coordinate) hresult
      | reveal coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
          cases hvalue : state.values coordinate with
          | some output =>
              simp only [hvalue] at hresult
              exact ih output observations state fuel table htracked hresult
          | none =>
              simp only [hvalue] at hresult
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : state.hitAt
                      (.chainStart lay tree leafIdx chainIdx) output
                  · simp [output, hhit] at hresult
                  · simp only [output, hhit, ↓reduceIte] at hresult
                    change some result ∈ support
                      (runObservedCleanFromTable observations
                        (state.materialize (.chainStart lay tree leafIdx chainIdx) output)
                        fuel table (next output)) at hresult
                    exact ih output observations
                      (state.materialize (.chainStart lay tree leafIdx chainIdx) output)
                      fuel table
                      (htracked.materialize (.chainStart lay tree leafIdx chainIdx) output
                        hvalue hhit)
                      hresult
              | position position =>
                  rw [mem_support_bind_iff] at hresult
                  obtain ⟨output, _houtput, hrest⟩ := hresult
                  by_cases hhit : state.hitAt (.position position) output
                  · simp [hhit] at hrest
                  · simp only [hhit, ↓reduceIte] at hrest
                    change some result ∈ support
                      (runObservedCleanFromTable observations
                        (state.materialize (.position position) output)
                        fuel table (next output)) at hrest
                    exact ih output observations (state.materialize (.position position) output)
                      fuel table (htracked.materialize (.position position) output hvalue hhit)
                      hrest

set_option maxRecDepth 100000 in
theorem cleanProbeObservationsCoverPending_of_mem_runObservedCleanFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hcovered : CleanProbeObservationsCoverPending observations state)
    (result : ObservedCleanRunResult α)
    (hresult : some result ∈ support
      (runObservedCleanFromTable observations state fuel table computation)) :
    CleanProbeObservationsCoverPending result.observations result.state := by
  induction computation using OracleComp.inductionOn generalizing
      observations state fuel table with
  | pure value =>
      simp [runObservedCleanFromTable] at hresult
      subst result
      exact hcovered
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output observations state fuel table hcovered hrest
      | hashOutput =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output observations state fuel table hcovered hrest
      | ensure coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
          exact ih () observations (state.ensure coordinate) fuel table
            (hcovered.ensure coordinate) hresult
      | probe coordinate candidate =>
          rw [runObservedCleanFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · exact ih ()
                  (observations ++ [cleanProbeObservation state coordinate candidate])
                  state remaining table
                  (cleanProbeObservationsCoverPending_append_revealed hcovered coordinate
                    candidate)
                  (by simpa [hrevealed] using hresult)
              · exact ih ()
                  (observations ++ [cleanProbeObservation state coordinate candidate])
                  (state.addPending coordinate candidate) remaining table
                  (cleanProbeObservationsCoverPending_append_hidden hcovered coordinate candidate
                    hrevealed)
                  (by simpa [hrevealed] using hresult)
      | peek coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
          exact ih (state.values coordinate) observations state fuel table hcovered hresult
      | publish coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
          exact ih () observations (state.publish coordinate) fuel table
            (hcovered.publish coordinate) hresult
      | reveal coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
          cases hvalue : state.values coordinate with
          | some output =>
              simp only [hvalue] at hresult
              exact ih output observations state fuel table hcovered hresult
          | none =>
              simp only [hvalue] at hresult
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : state.hitAt
                      (.chainStart lay tree leafIdx chainIdx) output
                  · simp [output, hhit] at hresult
                  · simp only [output, hhit, ↓reduceIte] at hresult
                    change some result ∈ support
                      (runObservedCleanFromTable observations
                        (state.materialize (.chainStart lay tree leafIdx chainIdx) output)
                        fuel table (next output)) at hresult
                    exact ih output observations
                      (state.materialize (.chainStart lay tree leafIdx chainIdx) output)
                      fuel table (hcovered.materialize _ output) hresult
              | position position =>
                  rw [mem_support_bind_iff] at hresult
                  obtain ⟨output, _houtput, hrest⟩ := hresult
                  by_cases hhit : state.hitAt (.position position) output
                  · simp [hhit] at hrest
                  · simp only [hhit, ↓reduceIte] at hrest
                    change some result ∈ support
                      (runObservedCleanFromTable observations
                        (state.materialize (.position position) output)
                        fuel table (next output)) at hrest
                    exact ih output observations (state.materialize (.position position) output)
                      fuel table (hcovered.materialize _ output) hrest

set_option maxRecDepth 100000 in
theorem remaining_add_pending_card_le_of_mem_runObservedCleanFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (result : ObservedCleanRunResult α)
    (hresult : some result ∈ support
      (runObservedCleanFromTable observations state fuel table computation)) :
    result.remaining + result.state.pending.card ≤ fuel + state.pending.card := by
  induction computation using OracleComp.inductionOn generalizing
      observations state fuel table with
  | pure value =>
      simp [runObservedCleanFromTable] at hresult
      subst result
      simp
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output observations state fuel table hrest
      | hashOutput =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output observations state fuel table hrest
      | ensure coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
          simpa only [LazyRevealProbe.State.pending_card_ensure] using
            ih () observations (state.ensure coordinate) fuel table hresult
      | probe coordinate candidate =>
          rw [runObservedCleanFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · have htail := ih ()
                  (observations ++ [cleanProbeObservation state coordinate candidate])
                  state remaining table (by simpa [hrevealed] using hresult)
                omega
              · have htail := ih ()
                  (observations ++ [cleanProbeObservation state coordinate candidate])
                  (state.addPending coordinate candidate) remaining table
                  (by simpa [hrevealed] using hresult)
                have hadd := state.pending_card_addPending_le coordinate candidate
                omega
      | peek coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
          exact ih (state.values coordinate) observations state fuel table hresult
      | publish coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
          exact ih () observations (state.publish coordinate) fuel table hresult
      | reveal coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
          cases hvalue : state.values coordinate with
          | some output =>
              simp only [hvalue] at hresult
              exact ih output observations state fuel table hresult
          | none =>
              simp only [hvalue] at hresult
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : state.hitAt
                      (.chainStart lay tree leafIdx chainIdx) output
                  · simp [output, hhit] at hresult
                  · simp only [output, hhit, ↓reduceIte] at hresult
                    have htail := ih output observations
                      (state.materialize (.chainStart lay tree leafIdx chainIdx) output)
                      fuel table hresult
                    have haway := state.pendingAway_card_add_pendingAt_card_le
                      (.chainStart lay tree leafIdx chainIdx)
                    simp only [LazyRevealProbe.State.pending_card_materialize] at htail
                    omega

              | position position =>
                  rw [mem_support_bind_iff] at hresult
                  obtain ⟨output, _houtput, hrest⟩ := hresult
                  by_cases hhit : state.hitAt (.position position) output
                  · simp [hhit] at hrest
                  · simp only [hhit, ↓reduceIte] at hrest
                    have htail := ih output observations
                      (state.materialize (.position position) output) fuel table hrest
                    have haway := state.pendingAway_card_add_pendingAt_card_le
                      (.position position)
                    simp only [LazyRevealProbe.State.pending_card_materialize] at htail
                    omega

set_option maxRecDepth 100000 in
theorem observations_length_add_remaining_eq_of_mem_runObservedCleanFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (result : ObservedCleanRunResult α)
    (hresult : some result ∈ support
      (runObservedCleanFromTable observations state fuel table computation)) :
    result.observations.length + result.remaining = observations.length + fuel := by
  induction computation using OracleComp.inductionOn generalizing
      observations state fuel table with
  | pure value =>
      simp [runObservedCleanFromTable] at hresult
      subst result
      rfl
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output observations state fuel table hrest
      | hashOutput =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output observations state fuel table hrest
      | ensure coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
          exact ih () observations (state.ensure coordinate) fuel table hresult
      | probe coordinate candidate =>
          rw [runObservedCleanFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · have htail := ih ()
                  (observations ++ [cleanProbeObservation state coordinate candidate])
                  state remaining table (by simpa [hrevealed] using hresult)
                simp only [List.length_append, List.length_singleton] at htail
                omega
              · have htail := ih ()
                  (observations ++ [cleanProbeObservation state coordinate candidate])
                  (state.addPending coordinate candidate) remaining table
                  (by simpa [hrevealed] using hresult)
                simp only [List.length_append, List.length_singleton] at htail
                omega
      | peek coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
          exact ih (state.values coordinate) observations state fuel table hresult
      | publish coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
          exact ih () observations (state.publish coordinate) fuel table hresult
      | reveal coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
          cases hvalue : state.values coordinate with
          | some output =>
              simp only [hvalue] at hresult
              exact ih output observations state fuel table hresult
          | none =>
              simp only [hvalue] at hresult
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : state.hitAt
                      (.chainStart lay tree leafIdx chainIdx) output
                  · simp [output, hhit] at hresult
                  · simp only [output, hhit, ↓reduceIte] at hresult
                    exact ih output observations
                      (state.materialize (.chainStart lay tree leafIdx chainIdx) output)
                      fuel table hresult
              | position position =>
                  rw [mem_support_bind_iff] at hresult
                  obtain ⟨output, _houtput, hrest⟩ := hresult
                  by_cases hhit : state.hitAt (.position position) output
                  · simp [hhit] at hrest
                  · simp only [hhit, ↓reduceIte] at hrest
                    exact ih output observations
                      (state.materialize (.position position) output) fuel table hrest

set_option maxRecDepth 100000 in
theorem map_projectObservedCleanRun_runObservedCleanFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) :
    projectObservedCleanRun <$>
        runObservedCleanFromTable observations state fuel table computation =
      runCleanFromTable state fuel table computation := by
  induction computation using OracleComp.inductionOn generalizing
      observations state fuel with
  | pure value =>
      simp [runObservedCleanFromTable, runCleanFromTable, projectObservedCleanRun,
        ObservedCleanRunResult.toClean]
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
            runCleanFromTable_uniform_query_bind, map_bind]
          apply bind_congr
          intro output
          exact ih output observations state fuel
      | hashOutput =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
            runCleanFromTable_hashOutput_query_bind, map_bind]
          apply bind_congr
          intro output
          exact ih output observations state fuel
      | ensure coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
            runCleanFromTable_ensure_query_bind]
          exact ih () observations (state.ensure coordinate) fuel
      | probe coordinate candidate =>
          rw [runObservedCleanFromTable_probe_query_bind,
            runCleanFromTable_probe_query_bind]
          cases fuel with
          | zero => simp [projectObservedCleanRun]
          | succ remaining =>
              let observation := cleanProbeObservation state coordinate candidate
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [hrevealed, ↓reduceIte]
                simpa [observation, hrevealed] using
                  (ih () (observations ++ [observation]) state remaining)
              · simp only [hrevealed, ↓reduceIte]
                simpa [observation, hrevealed] using
                  (ih () (observations ++ [observation])
                    (state.addPending coordinate candidate) remaining)
      | peek coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
            runCleanFromTable_peek_query_bind]
          exact ih (state.values coordinate) observations state fuel
      | publish coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
            runCleanFromTable_publish_query_bind]
          exact ih () observations (state.publish coordinate) fuel
      | reveal coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
            runCleanFromTable_reveal_query_bind]
          cases hvalue : state.values coordinate with
          | some output =>
              simp only [hvalue]
              exact ih output observations state fuel
          | none =>
              simp only [hvalue]
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : state.hitAt (.chainStart lay tree leafIdx chainIdx) output
                  · simp [output, hhit, projectObservedCleanRun]
                  · simp only [output, hhit, ↓reduceIte]
                    exact ih output observations
                      (state.materialize (.chainStart lay tree leafIdx chainIdx) output) fuel
              | position position =>
                  simp only [map_bind]
                  apply bind_congr
                  intro output
                  by_cases hhit : state.hitAt (.position position) output
                  · simp [hhit, projectObservedCleanRun]
                  · simp only [hhit, ↓reduceIte]
                    exact ih output observations
                      (state.materialize (.position position) output) fuel

theorem startTableAgrees_of_mem_runObservedCleanFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hagrees : StartTableAgrees state table)
    (result : ObservedCleanRunResult α)
    (hresult : some result ∈ support
      (runObservedCleanFromTable observations state fuel table computation)) :
    result.table = table ∧ StartTableAgrees result.state table := by
  have hmapped : some result.toClean ∈ support
      (projectObservedCleanRun <$>
        runObservedCleanFromTable observations state fuel table computation) := by
    rw [support_map, Set.mem_image]
    exact ⟨some result, hresult, rfl⟩
  rw [map_projectObservedCleanRun_runObservedCleanFromTable] at hmapped
  exact startTableAgrees_of_mem_runCleanFromTable computation state fuel table hagrees
    result.toClean hmapped

noncomputable def finishObservedCleanRunFromTable :
    Option (ObservedCleanRunResult α) →
      ProbComp (Option (ObservedCleanRunResult α))
  | none => pure none
  | some result => do
      let finalized ← finalizeCleanFromTable result.state.coordinates.toList
        result.state result.table
      match finalized with
      | none => pure none
      | some (finalState, finalTable) =>
          pure (some
            ⟨finalState, result.remaining, result.value, finalTable, result.observations⟩)

set_option maxRecDepth 100000 in
theorem cleanProbeObservationsTrackedBy_of_mem_finalizeCleanFromTable :
    ∀ (coordinates : List Coordinate)
      (state : LazyRevealProbe.State Coordinate)
      (table : OtsSecretIndex → HashOutput)
      (observations : List CleanProbeObservation),
      CleanProbeObservationsTrackedBy observations state →
      ∀ finalState finalTable,
        some (finalState, finalTable) ∈ support
          (finalizeCleanFromTable coordinates state table) →
        CleanProbeObservationsTrackedBy observations finalState
  | [], state, table, observations, htracked, finalState, finalTable, hresult => by
      simp [finalizeCleanFromTable] at hresult
      obtain ⟨rfl, rfl⟩ := hresult
      exact htracked
  | coordinate :: remaining, state, table, observations, htracked,
      finalState, finalTable, hresult => by
      rw [finalizeCleanFromTable.eq_def] at hresult
      cases hvalue : state.values coordinate with
      | some output =>
          simp only [hvalue] at hresult
          exact cleanProbeObservationsTrackedBy_of_mem_finalizeCleanFromTable remaining
            (state.clearPending coordinate) table observations
            (htracked.clearPending coordinate output hvalue) finalState finalTable hresult
      | none =>
          simp only [hvalue] at hresult
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              let output := table ⟨lay, tree, leafIdx, chainIdx⟩
              by_cases hhit : state.hitAt (.chainStart lay tree leafIdx chainIdx) output
              · simp [output, hhit] at hresult
              · simp only [output, hhit, ↓reduceIte] at hresult
                exact cleanProbeObservationsTrackedBy_of_mem_finalizeCleanFromTable remaining
                  (state.complete (.chainStart lay tree leafIdx chainIdx) output) table
                  observations
                  (htracked.complete (.chainStart lay tree leafIdx chainIdx) output hvalue hhit)
                  finalState finalTable hresult
          | position position =>
              rw [mem_support_bind_iff] at hresult
              obtain ⟨output, _houtput, hrest⟩ := hresult
              by_cases hhit : state.hitAt (.position position) output
              · simp [hhit] at hrest
              · simp only [hhit, ↓reduceIte] at hrest
                exact cleanProbeObservationsTrackedBy_of_mem_finalizeCleanFromTable remaining
                  (state.complete (.position position) output) table observations
                  (htracked.complete (.position position) output hvalue hhit)
                  finalState finalTable hrest

theorem cleanProbeObservationsTrackedBy_of_mem_finishObservedCleanRunFromTable
    (result finalResult : ObservedCleanRunResult α)
    (htracked : CleanProbeObservationsTrackedBy result.observations result.state)
    (hresult : some finalResult ∈ support
      (finishObservedCleanRunFromTable (some result))) :
    CleanProbeObservationsTrackedBy finalResult.observations finalResult.state := by
  unfold finishObservedCleanRunFromTable at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨finalized, hfinalized, hreturn⟩ := hresult
  cases finalized with
  | none => simp at hreturn
  | some value =>
      rcases value with ⟨finalState, finalTable⟩
      simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hreturn
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hreturn
      exact cleanProbeObservationsTrackedBy_of_mem_finalizeCleanFromTable
        result.state.coordinates.toList result.state result.table result.observations
        htracked finalState finalTable hfinalized

theorem map_projectObservedCleanRun_finishObservedCleanRunFromTable
    (result : Option (ObservedCleanRunResult α)) :
    projectObservedCleanRun <$> finishObservedCleanRunFromTable result =
      finishCleanRunFromTable (projectObservedCleanRun result) := by
  cases result with
  | none => simp [finishObservedCleanRunFromTable, finishCleanRunFromTable,
      projectObservedCleanRun]
  | some result =>
      unfold finishObservedCleanRunFromTable finishCleanRunFromTable
      rw [map_bind]
      apply bind_congr
      intro finalized
      cases finalized <;>
        simp [projectObservedCleanRun, ObservedCleanRunResult.toClean]

theorem map_projectObservedCleanRun_bind_finishObservedCleanRunFromTable
    (run : ProbComp (Option (ObservedCleanRunResult α))) :
    projectObservedCleanRun <$> (run >>= finishObservedCleanRunFromTable) =
      (projectObservedCleanRun <$> run) >>= finishCleanRunFromTable := by
  calc
    _ = run >>= fun result =>
        projectObservedCleanRun <$> finishObservedCleanRunFromTable result := map_bind _ _ _
    _ = run >>= fun result =>
        finishCleanRunFromTable (projectObservedCleanRun result) := by
      apply bind_congr
      intro result
      exact map_projectObservedCleanRun_finishObservedCleanRunFromTable result
    _ = _ := by simp [map_eq_bind_pure_comp, bind_assoc]

noncomputable def sampledObservedRootAwareClean
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp (Option
      (ObservedCleanRunResult (RetainedGameResult × SplitHashCache))) := do
  let base ← sampleOtsHashTable
  let table := completedStartTable
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) base
  let result ← runObservedCleanFromTable [] LazyRevealProbe.State.empty fuel table
    (rootAwareCleanRetainedRun adversary parameter ftsSecret)
  finishObservedCleanRunFromTable result

set_option maxRecDepth 100000 in
theorem map_projectObservedCleanRun_sampledObservedRootAwareClean
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    projectObservedCleanRun <$>
        sampledObservedRootAwareClean adversary parameter ftsSecret fuel =
      sampledRunThenFinalizeClean
        (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel
        (rootAwareCleanRetainedRun adversary parameter ftsSecret) := by
  unfold sampledObservedRootAwareClean sampledRunThenFinalizeClean
  rw [map_bind]
  apply bind_congr
  intro base
  dsimp only
  rw [map_projectObservedCleanRun_bind_finishObservedCleanRunFromTable,
    map_projectObservedCleanRun_runObservedCleanFromTable]

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledObservedRootAwareClean_none_le
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q) :
    Pr[= none |
        sampledObservedRootAwareClean adversary parameter ftsSecret q] ≤
      (q : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ = Pr[= none | projectObservedCleanRun <$>
        sampledObservedRootAwareClean adversary parameter ftsSecret q] := by
      rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput, probEvent_map]
      apply OracleComp.probEvent_congr'
      · intro result _hresult
        cases result <;> simp [projectObservedCleanRun]
      · rfl
    _ = Pr[= none | sampledRunThenFinalizeClean
        (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) q
        (rootAwareCleanRetainedRun adversary parameter ftsSecret)] :=
      OracleComp.probOutput_congr rfl
        (congrArg evalDist
          (map_projectObservedCleanRun_sampledObservedRootAwareClean adversary parameter
            ftsSecret q))
    _ ≤ _ := probEvent_sampledRootAwareCleanRetainedRun_none_le adversary parameter
      ftsSecret q hbound

theorem probEvent_le_failure_add_residual_of_relTriple
    (left : ProbComp α) (right : ProbComp β)
    (relation : α → β → Prop)
    (event residual : α → Prop) (failure : β → Prop)
    (hrel : RelTriple left right relation)
    (hclassify : ∀ leftOutput rightOutput,
      relation leftOutput rightOutput → event leftOutput →
        ¬residual leftOutput → failure rightOutput) :
    Pr[event | left] ≤ Pr[failure | right] + Pr[residual | left] := by
  calc
    _ = Pr[fun output =>
        (event output ∧ residual output) ∨
          (event output ∧ ¬residual output) | left] := by
      apply OracleComp.probEvent_congr'
      intro output _houtput
      tauto
      rfl
    _ ≤ Pr[fun output => event output ∧ residual output | left] +
        Pr[fun output => event output ∧ ¬residual output | left] :=
      probEvent_or_le _ _ _
    _ ≤ Pr[residual | left] + Pr[failure | right] := by
      apply add_le_add
      · apply probEvent_mono
        intro output _houtput hboth
        exact hboth.2
      · apply probEvent_le_of_relTriple hrel
        intro leftOutput rightOutput hrelation hboth
        exact hclassify leftOutput rightOutput hrelation hboth.1 hboth.2
    _ = Pr[failure | right] + Pr[residual | left] := add_comm _ _

end SphincsSecurity.Concrete.OtsProbeSimulation
