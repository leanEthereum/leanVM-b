import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSourceHidden

/-!
# Global root coupling boundary

This file states the target-neutral postcondition of the adaptive coupling. A successful observed
run must turn every source-side layer-root witness into a delayed source snapshot. The failure
alternative is therefore charged once, before any ordinal or position is selected.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

def SnapshotObservedRootRel
    (source : PrivateWitnessSnapshotOutput)
    (observed : Option
      (ObservedCleanRunResult (RetainedGameResult × SplitHashCache))) : Prop :=
  observed = none ∨
    (WitnessFirstUsesSomeLayerRoot (erasePrivateWitnessSnapshotOutput source) →
      WitnessFirstUsesSomeDelayedLayerRootSnapshot source)

def PlannedProbeSnapshot.ObservedAt
    (table : OtsSecretIndex → HashOutput)
    (snapshot : PlannedProbeSnapshot) (observation : CleanProbeObservation) : Prop :=
  observation.toProbe = snapshot.probe ∧
    (∀ position, observation.coordinate = .position position →
      observation.valueAtProbe = snapshot.context.positionValue position) ∧
    observation.revealedAtProbe =
      decide (observation.coordinate ∈ snapshot.context.state.revealed) ∧
    PublishedValues snapshot.context.state ∧
    CanonicalMaterializedValues table snapshot.context

def SnapshotsObservedAt
    (table : OtsSecretIndex → HashOutput)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation) : Prop :=
  List.Forall₂ (PlannedProbeSnapshot.ObservedAt table) snapshots observations

theorem SnapshotsObservedAt.map_toProbe_eq
    {table : OtsSecretIndex → HashOutput}
    {snapshots : List PlannedProbeSnapshot}
    {observations : List CleanProbeObservation}
    (haligned : SnapshotsObservedAt table snapshots observations) :
    snapshots.map PlannedProbeSnapshot.toProbe =
      observations.map CleanProbeObservation.toProbe := by
  induction haligned with
  | nil => rfl
  | cons hhead htail ih =>
      simp only [List.map_cons, PlannedProbeSnapshot.toProbe, ih, List.cons.injEq, and_true]
      exact hhead.1.symm

theorem SnapshotsObservedAt.published
    {table : OtsSecretIndex → HashOutput}
    {snapshots : List PlannedProbeSnapshot}
    {observations : List CleanProbeObservation}
    (haligned : SnapshotsObservedAt table snapshots observations) :
    ∀ snapshot ∈ snapshots, PublishedValues snapshot.context.state := by
  induction haligned with
  | nil => simp
  | cons hhead htail ih =>
      intro snapshot hsnapshot
      simp only [List.mem_cons] at hsnapshot
      rcases hsnapshot with rfl | hrest
      · exact hhead.2.2.2.1
      · exact ih snapshot hrest

theorem SnapshotsObservedAt.append
    {table : OtsSecretIndex → HashOutput}
    {snapshots : List PlannedProbeSnapshot}
    {observations : List CleanProbeObservation}
    (haligned : SnapshotsObservedAt table snapshots observations)
    {snapshot : PlannedProbeSnapshot} {observation : CleanProbeObservation}
    (hnext : snapshot.ObservedAt table observation) :
    SnapshotsObservedAt table (snapshots ++ [snapshot])
      (observations ++ [observation]) := by
  induction haligned with
  | nil => exact .cons hnext .nil
  | cons hhead htail ih => exact .cons hhead ih

theorem PlannedProbeSnapshot.observedAt_of_finalizationContextLE
    (table : OtsSecretIndex → HashOutput)
    (snapshot : PlannedProbeSnapshot)
    (state : LazyRevealProbe.State Coordinate)
    (hcontext : FinalizationContextLE table snapshot.context
      (directDeferredContext state))
    (hrevealed : snapshot.context.state.revealed = state.revealed)
    (hpublished : PublishedValues snapshot.context.state)
    (hcanonical : CanonicalMaterializedValues table snapshot.context) :
    snapshot.ObservedAt table
      (cleanProbeObservation state snapshot.probe.coordinate snapshot.probe.candidate) := by
  refine ⟨rfl, ?_, ?_, hpublished, hcanonical⟩
  · intro position hcoordinate
    unfold cleanProbeObservation
    change state.values snapshot.probe.coordinate = snapshot.context.positionValue position
    change snapshot.probe.coordinate = .position position at hcoordinate
    rw [hcoordinate]
    have hvalue := congrFun hcontext.view.valueEq (.position position)
    cases hstate : state.values (.position position) <;>
      simpa [resolvedCompletionValue, directDeferredContext, directDeferredValues,
        DeferredContext.positionValue, hstate] using hvalue.symm
  · change decide (snapshot.probe.coordinate ∈ state.revealed) =
      decide (snapshot.probe.coordinate ∈ snapshot.context.state.revealed)
    rw [hrevealed]

theorem canonical_value_none_of_not_revealed
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hcanonical : CanonicalMaterializedValues table context)
    {coordinate : Coordinate} (hhidden : coordinate ∉ context.state.revealed) :
    context.state.values coordinate = none := by
  rw [hcanonical]
  simp [publicMaterializedValues, hhidden]

set_option maxRecDepth 100000 in
theorem witnessFirstUsesSomeDelayedLayerRootSnapshot_of_observedDelayed
    {table : OtsSecretIndex → HashOutput}
    {source : PrivateWitnessSnapshotOutput}
    {observations : List CleanProbeObservation}
    (haligned : SnapshotsObservedAt table source.2 observations)
    (hdelayed : WitnessFirstUsesDelayedLayerRoot
      (erasePrivateWitnessSnapshotOutput source) observations)
    (hselectedHidden : ∀ witness
      (sourceOrdinal : Fin
        (erasePrivateWitnessSnapshotOutput source).2.length)
      (observationOrdinal : Fin observations.length),
      source.1 = some witness →
      sourceOrdinal.val = observationOrdinal.val →
      firstPrivateWitnessOrdinal? witness
          (erasePrivateWitnessSnapshotOutput source).2 = some sourceOrdinal →
      (observations.get observationOrdinal).revealedAtProbe = false) :
    WitnessFirstUsesSomeDelayedLayerRootSnapshot source := by
  obtain ⟨witness, sourceOrdinal, observationOrdinal, hwitness, hordinal,
    hfirst, hroot, hvalue⟩ := hdelayed
  have hsourceLength :
      (erasePrivateWitnessSnapshotOutput source).2.length = source.2.length := by
    simp [erasePrivateWitnessSnapshotOutput]
  let snapshotOrdinal : Fin source.2.length :=
    ⟨sourceOrdinal.val, by
      rw [← hsourceLength]
      exact sourceOrdinal.isLt⟩
  have hobservationLt : snapshotOrdinal.val < observations.length := by
    rw [← haligned.length_eq]
    exact snapshotOrdinal.isLt
  have hpair := haligned.get snapshotOrdinal.isLt hobservationLt
  let alignedObservationOrdinal : Fin observations.length :=
    ⟨snapshotOrdinal.val, hobservationLt⟩
  have halignedOrdinal : alignedObservationOrdinal = observationOrdinal := by
    apply Fin.ext
    exact hordinal
  have hpair' : PlannedProbeSnapshot.ObservedAt table
      (source.2.get snapshotOrdinal) (observations.get observationOrdinal) := by
    simpa [alignedObservationOrdinal, halignedOrdinal] using hpair
  have hprobe :
      (observations.get observationOrdinal).toProbe =
        (source.2.get snapshotOrdinal).probe := by
    rw [← halignedOrdinal]
    exact hpair.1
  have hcoordinate :
      (observations.get observationOrdinal).coordinate =
        Coordinate.position witness.position := by
    have hsourceProbe :
        (erasePrivateWitnessSnapshotOutput source).2.get sourceOrdinal =
          (source.2.get snapshotOrdinal).probe := by
      simp [erasePrivateWitnessSnapshotOutput, snapshotOrdinal]
    have hmatch := privateWitnessAtOrdinal_of_firstPrivateWitnessOrdinal?_eq_some hfirst
    unfold PrivateWitnessAtOrdinal at hmatch
    rw [hsourceProbe] at hmatch
    exact congrArg Probe.coordinate hprobe |>.trans hmatch.1
  have hhiddenObservation := hselectedHidden witness sourceOrdinal observationOrdinal hwitness
    hordinal hfirst
  have hhiddenSnapshot : Coordinate.position witness.position ∉
      (source.2.get snapshotOrdinal).context.state.revealed := by
    intro hrevealed
    have hfalse : decide ((observations.get observationOrdinal).coordinate ∈
        (source.2.get snapshotOrdinal).context.state.revealed) = false :=
      hpair'.2.2.1.symm.trans hhiddenObservation
    simp only [decide_eq_false_iff_not] at hfalse
    apply hfalse
    rw [hcoordinate]
    exact hrevealed
  have hstate : (source.2.get snapshotOrdinal).context.state.values
      (.position witness.position) = none :=
    canonical_value_none_of_not_revealed hpair.2.2.2.2 hhiddenSnapshot
  have hpositionValue : (source.2.get snapshotOrdinal).context.positionValue
      witness.position = some witness.output := by
    have hcompletion := hpair'.2.1 witness.position hcoordinate
    exact hcompletion.symm.trans hvalue
  have hsourceFirst : firstPrivateWitnessOrdinal? witness
      (source.2.map PlannedProbeSnapshot.toProbe) =
        some (snapshotProbeOrdinal snapshotOrdinal) := by
    simpa [erasePrivateWitnessSnapshotOutput, snapshotProbeOrdinal, snapshotOrdinal] using hfirst
  have hwitnessSource : source.1 = some witness := by
    simpa [erasePrivateWitnessSnapshotOutput] using hwitness
  have hsourceProbe :
      (erasePrivateWitnessSnapshotOutput source).2.get sourceOrdinal =
        (source.2.get snapshotOrdinal).probe := by
    simp [erasePrivateWitnessSnapshotOutput, snapshotOrdinal]
  have hsnapshotRoot : (source.2.get snapshotOrdinal).probe.IsLayerRoot := by
    rw [← hsourceProbe]
    exact hroot
  refine ⟨snapshotOrdinal.val, witness, snapshotOrdinal, hwitnessSource, rfl,
    hsourceFirst, hsnapshotRoot, hstate, hhiddenSnapshot, ?_⟩
  exact deferredValue_eq_of_positionValue_eq_of_state_none hstate hpositionValue

set_option maxRecDepth 100000 in
theorem witnessFirstUsesSomeDelayedLayerRootSnapshot_of_aligned_tracked
    {table : OtsSecretIndex → HashOutput}
    {source : PrivateWitnessSnapshotOutput}
    {result : ObservedCleanRunResult α}
    (haligned : SnapshotsObservedAt table source.2 result.observations)
    (hfirst : WitnessFirstUsesSomeLayerRoot
      (erasePrivateWitnessSnapshotOutput source))
    (htracked : CleanProbeObservationsTrackedBy result.observations result.state)
    (hstored : ∀ witness,
      (erasePrivateWitnessSnapshotOutput source).1 = some witness →
        result.state.values (Coordinate.position witness.position) = some witness.output)
    (hselectedHidden : ∀ witness
      (sourceOrdinal : Fin
        (erasePrivateWitnessSnapshotOutput source).2.length)
      (observationOrdinal : Fin result.observations.length),
      (erasePrivateWitnessSnapshotOutput source).1 = some witness →
      sourceOrdinal.val = observationOrdinal.val →
      firstPrivateWitnessOrdinal? witness
          (erasePrivateWitnessSnapshotOutput source).2 = some sourceOrdinal →
      (result.observations.get observationOrdinal).revealedAtProbe = false) :
    WitnessFirstUsesSomeDelayedLayerRootSnapshot source := by
  apply witnessFirstUsesSomeDelayedLayerRootSnapshot_of_observedDelayed haligned
    (witnessFirstUsesDelayedLayerRoot_of_aligned_tracked hfirst ?_ htracked hstored
      hselectedHidden)
    hselectedHidden
  change source.2.map PlannedProbeSnapshot.toProbe <+:
    result.observations.map CleanProbeObservation.toProbe
  rw [haligned.map_toProbe_eq]

def attachCleanProbeObservations (observations : List CleanProbeObservation) :
    Option (CleanRunResult α) → Option (ObservedCleanRunResult α)
  | none => none
  | some result => some
      ⟨result.state, result.remaining, result.value, result.table, observations⟩

set_option maxRecDepth 100000 in
theorem map_attachCleanProbeObservations_runCleanFromTable_of_probeFree
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hprobeFree : computation.IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 0) :
    attachCleanProbeObservations observations <$>
        runCleanFromTable state fuel table computation =
      runObservedCleanFromTable observations state fuel table computation := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value =>
      simp [runCleanFromTable, runObservedCleanFromTable,
        attachCleanProbeObservations]
  | query_bind query next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hprobeFree
      cases query with
      | uniform n =>
          rw [runCleanFromTable, runObservedCleanFromTable,
            OracleComp.construct_query_bind, OracleComp.construct_query_bind,
            map_bind]
          apply bind_congr
          intro output
          exact ih output state fuel (hprobeFree.2 output)
      | hashOutput =>
          rw [runCleanFromTable, runObservedCleanFromTable,
            OracleComp.construct_query_bind, OracleComp.construct_query_bind,
            map_bind]
          apply bind_congr
          intro output
          exact ih output state fuel (hprobeFree.2 output)
      | ensure coordinate =>
          rw [runCleanFromTable, runObservedCleanFromTable,
            OracleComp.construct_query_bind, OracleComp.construct_query_bind]
          exact ih () (state.ensure coordinate) fuel (hprobeFree.2 ())
      | probe coordinate candidate =>
          simp [LazyRevealProbe.IsProbe] at hprobeFree
      | peek coordinate =>
          rw [runCleanFromTable, runObservedCleanFromTable,
            OracleComp.construct_query_bind, OracleComp.construct_query_bind]
          exact ih (state.values coordinate) state fuel (hprobeFree.2 _)
      | publish coordinate =>
          rw [runCleanFromTable, runObservedCleanFromTable,
            OracleComp.construct_query_bind, OracleComp.construct_query_bind]
          exact ih () (state.publish coordinate) fuel (hprobeFree.2 ())
      | reveal coordinate =>
          rw [runCleanFromTable, runObservedCleanFromTable,
            OracleComp.construct_query_bind, OracleComp.construct_query_bind]
          cases hvalue : state.values coordinate with
          | some output =>
              simp only [hvalue]
              exact ih output state fuel (hprobeFree.2 output)
          | none =>
              simp only [hvalue]
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : state.hitAt
                      (.chainStart lay tree leafIdx chainIdx) output
                  · simp [output, hhit, attachCleanProbeObservations]
                  · simp only [output, hhit, ↓reduceIte]
                    exact ih output
                      (state.materialize (.chainStart lay tree leafIdx chainIdx) output)
                      fuel (hprobeFree.2 output)
              | position position =>
                  rw [map_bind]
                  apply bind_congr
                  intro output
                  by_cases hhit : state.hitAt (.position position) output
                  · simp [hhit, attachCleanProbeObservations]
                  · simp only [hhit, ↓reduceIte]
                    exact ih output (state.materialize (.position position) output)
                      fuel (hprobeFree.2 output)

theorem runObservedCleanFromTable_reveal_query_bind
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) α) :
    runObservedCleanFromTable observations state fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.reveal coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next) =
      (match state.values coordinate with
      | some output =>
          runObservedCleanFromTable observations state fuel table (next output)
      | none =>
          match coordinate with
          | .chainStart lay tree leafIdx chainIdx =>
              let output := table ⟨lay, tree, leafIdx, chainIdx⟩
              if state.hitAt coordinate output then pure none
              else runObservedCleanFromTable observations
                (state.materialize coordinate output) fuel table (next output)
          | .position _ => do
              let output ← LazyRevealProbe.sampleHashOutput
              if state.hitAt coordinate output then pure none
              else
                runObservedCleanFromTable observations
                  (state.materialize coordinate output) fuel table (next output)) := by
  rw [runObservedCleanFromTable, OracleComp.construct_query_bind]
  cases coordinate <;> rfl

theorem runObservedCleanFromTable_bind
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (left : OracleComp (LazyRevealProbe.World Coordinate) α)
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β) :
    runObservedCleanFromTable observations state fuel table (left >>= next) =
      runObservedCleanFromTable observations state fuel table left >>= fun result =>
        match result with
        | none => pure none
        | some result =>
            runObservedCleanFromTable result.observations result.state result.remaining
              result.table (next result.value) := by
  induction left using OracleComp.inductionOn generalizing observations state fuel with
  | pure value => simp [runObservedCleanFromTable]
  | query_bind query continuation ih =>
      cases query with
      | uniform n =>
          rw [bind_assoc, runObservedCleanFromTable, OracleComp.construct_query_bind,
            runObservedCleanFromTable, OracleComp.construct_query_bind]
          simp only [bind_assoc]
          apply bind_congr
          intro output
          exact ih output observations state fuel
      | hashOutput =>
          rw [bind_assoc, runObservedCleanFromTable, OracleComp.construct_query_bind,
            runObservedCleanFromTable, OracleComp.construct_query_bind]
          simp only [bind_assoc]
          apply bind_congr
          intro output
          exact ih output observations state fuel
      | ensure coordinate =>
          rw [bind_assoc, runObservedCleanFromTable, OracleComp.construct_query_bind,
            runObservedCleanFromTable, OracleComp.construct_query_bind]
          exact ih () observations (state.ensure coordinate) fuel
      | probe coordinate candidate =>
          rw [bind_assoc, runObservedCleanFromTable_probe_query_bind,
            runObservedCleanFromTable_probe_query_bind]
          cases fuel with
          | zero => simp
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [hrevealed, ↓reduceIte]
                exact ih ()
                  (observations ++ [cleanProbeObservation state coordinate candidate])
                  state remaining
              · simp only [hrevealed, ↓reduceIte]
                exact ih ()
                  (observations ++ [cleanProbeObservation state coordinate candidate])
                  (state.addPending coordinate candidate) remaining
      | peek coordinate =>
          rw [bind_assoc, runObservedCleanFromTable, OracleComp.construct_query_bind,
            runObservedCleanFromTable, OracleComp.construct_query_bind]
          exact ih (state.values coordinate) observations state fuel
      | publish coordinate =>
          rw [bind_assoc, runObservedCleanFromTable, OracleComp.construct_query_bind,
            runObservedCleanFromTable, OracleComp.construct_query_bind]
          exact ih () observations (state.publish coordinate) fuel
      | reveal coordinate =>
          rw [bind_assoc, runObservedCleanFromTable_reveal_query_bind,
            runObservedCleanFromTable_reveal_query_bind]
          cases hvalue : state.values coordinate with
          | some output => exact ih output observations state fuel
          | none =>
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : state.hitAt
                      (.chainStart lay tree leafIdx chainIdx) output
                  · simp [output, hhit]
                  · simp only [output, hhit, ↓reduceIte]
                    exact ih output observations
                      (state.materialize (.chainStart lay tree leafIdx chainIdx) output) fuel
              | position position =>
                  simp only [bind_assoc]
                  apply bind_congr
                  intro output
                  by_cases hhit : state.hitAt (.position position) output
                  · simp [hhit]
                  · simp only [hhit, ↓reduceIte]
                    exact ih output observations
                      (state.materialize (.position position) output) fuel

theorem relTriple_graph_of_map_eq
    (left : ProbComp α) (right : ProbComp β) (project : α → β)
    (hproject : project <$> left = right) :
    RelTriple left right (fun leftOutput rightOutput =>
      project leftOutput = rightOutput) := by
  have hgraph : RelTriple left (project <$> left)
      (fun leftOutput rightOutput => project leftOutput = rightOutput) := by
    have hbase : RelTriple left left (fun leftOutput rightOutput =>
        project leftOutput = project rightOutput) := by
      apply relTriple_post_mono (relTriple_refl left)
      intro leftOutput rightOutput heq
      subst rightOutput
      rfl
    have hmapped : RelTriple (id <$> left) (project <$> left)
        (fun leftOutput rightOutput => project leftOutput = rightOutput) :=
      relTriple_map
        (R := fun leftOutput rightOutput => project leftOutput = rightOutput)
        (f := id) (g := project) hbase
    simpa using hmapped
  exact relTriple_of_evalDist_eq_right (congrArg evalDist hproject) hgraph

theorem relTriple_sampledSnapshot_privateWitnessPlan
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    RelTriple
      (sampledGranularAllDirectBoundaryNormalizedPrivateWitnessSnapshot adversary parameter
        ftsSecret fuel)
      (sampledGranularAllDirectBoundaryNormalizedPrivateWitnessPlan adversary parameter
        ftsSecret fuel)
      (fun snapshot plan => erasePrivateWitnessSnapshotOutput snapshot = plan) := by
  exact relTriple_graph_of_map_eq _ _ erasePrivateWitnessSnapshotOutput
    (map_erase_sampledGranularAllDirectBoundaryNormalizedPrivateWitnessSnapshot adversary
      parameter ftsSecret fuel)

theorem probEvent_root_le_observedFailure_add_delayed_of_relTriple
    (source : ProbComp PrivateWitnessSnapshotOutput)
    (observed : ProbComp (Option
      (ObservedCleanRunResult (RetainedGameResult × SplitHashCache))))
    (hrel : RelTriple source observed SnapshotObservedRootRel) :
    Pr[fun output =>
        WitnessFirstUsesSomeLayerRoot (erasePrivateWitnessSnapshotOutput output) | source] ≤
      Pr[= none | observed] +
        Pr[WitnessFirstUsesSomeDelayedLayerRootSnapshot | source] := by
  rw [← probEvent_eq_eq_probOutput]
  apply probEvent_le_failure_add_residual_of_relTriple source observed
    SnapshotObservedRootRel
    (fun output =>
      WitnessFirstUsesSomeLayerRoot (erasePrivateWitnessSnapshotOutput output))
    WitnessFirstUsesSomeDelayedLayerRootSnapshot (fun output => output = none) hrel
  intro sourceOutput observedOutput hrelation hroot hnotDelayed
  rcases hrelation with hfailure | hsuccess
  · exact hfailure
  · exact False.elim (hnotDelayed (hsuccess hroot))

theorem probEvent_root_map_erase_sampledSnapshot_eq
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[fun output =>
        WitnessFirstUsesSomeLayerRoot (erasePrivateWitnessSnapshotOutput output) |
      sampledGranularAllDirectBoundaryNormalizedPrivateWitnessSnapshot adversary parameter
        ftsSecret fuel] =
      Pr[WitnessFirstUsesSomeLayerRoot |
        sampledGranularAllDirectBoundaryNormalizedPrivateWitnessPlan adversary parameter
          ftsSecret fuel] := by
  calc
    _ = Pr[WitnessFirstUsesSomeLayerRoot |
        erasePrivateWitnessSnapshotOutput <$>
          sampledGranularAllDirectBoundaryNormalizedPrivateWitnessSnapshot adversary parameter
            ftsSecret fuel] := by
      rw [probEvent_map]
      exact OracleComp.probEvent_congr' (fun _ _ => Iff.rfl) rfl
    _ = _ := OracleComp.probEvent_congr' (fun _ _ => Iff.rfl)
      (congrArg evalDist
        (map_erase_sampledGranularAllDirectBoundaryNormalizedPrivateWitnessSnapshot adversary
          parameter ftsSecret fuel))

theorem probEvent_sampledPlan_root_le_observedFailure_add_delayed
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (hrel : RelTriple
      (sampledGranularAllDirectBoundaryNormalizedPrivateWitnessSnapshot adversary parameter
        ftsSecret fuel)
      (sampledObservedRootAwareClean adversary parameter ftsSecret fuel)
      SnapshotObservedRootRel) :
    Pr[WitnessFirstUsesSomeLayerRoot |
        sampledGranularAllDirectBoundaryNormalizedPrivateWitnessPlan adversary parameter
          ftsSecret fuel] ≤
      Pr[= none | sampledObservedRootAwareClean adversary parameter ftsSecret fuel] +
        Pr[WitnessFirstUsesSomeDelayedLayerRootSnapshot |
          sampledGranularAllDirectBoundaryNormalizedPrivateWitnessSnapshot adversary parameter
            ftsSecret fuel] := by
  rw [← probEvent_root_map_erase_sampledSnapshot_eq adversary parameter ftsSecret fuel]
  exact probEvent_root_le_observedFailure_add_delayed_of_relTriple _ _ hrel

end SphincsSecurity.Concrete.OtsProbeSimulation
