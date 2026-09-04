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

def PlannedProbeSnapshot.Before (snapshot : PlannedProbeSnapshot)
    (context : DeferredContext) : Prop :=
  snapshot.context.state.revealed ⊆ context.state.revealed ∧
    PrivateValuesLE snapshot.context context

def SnapshotsBefore (snapshots : List PlannedProbeSnapshot)
    (context : DeferredContext) : Prop :=
  ∀ snapshot ∈ snapshots, snapshot.Before context

theorem SnapshotsBefore.nil (context : DeferredContext) :
    SnapshotsBefore [] context := by
  simp [SnapshotsBefore]

theorem SnapshotsBefore.append_self
    {snapshots : List PlannedProbeSnapshot} {context : DeferredContext}
    (hbefore : SnapshotsBefore snapshots context) :
    SnapshotsBefore (snapshots ++ [⟨candidate, context⟩]) context := by
  intro snapshot hsnapshot
  simp only [List.mem_append, List.mem_singleton] at hsnapshot
  rcases hsnapshot with hold | rfl
  · exact hbefore snapshot hold
  · exact ⟨Finset.Subset.rfl, PrivateValuesLE.refl context⟩

theorem SnapshotsBefore.appendPlannedSnapshot
    {snapshots : List PlannedProbeSnapshot} {context : DeferredContext}
    (hbefore : SnapshotsBefore snapshots context) (candidate? : Option Probe) :
    SnapshotsBefore (appendPlannedSnapshot snapshots candidate? context) context := by
  cases candidate? with
  | none => exact hbefore
  | some candidate => exact hbefore.append_self

theorem SnapshotsBefore.trans
    {snapshots : List PlannedProbeSnapshot} {left right : DeferredContext}
    (hbefore : SnapshotsBefore snapshots left)
    (hrevealed : left.state.revealed ⊆ right.state.revealed)
    (hvalues : PrivateValuesLE left right) :
    SnapshotsBefore snapshots right := by
  intro snapshot hsnapshot
  have hsnapshot := hbefore snapshot hsnapshot
  exact ⟨hsnapshot.1.trans hrevealed, hsnapshot.2.trans hvalues⟩

set_option maxRecDepth 100000 in
theorem SnapshotsBefore.of_done_runDirectResolvedWitnessFromTable
    {snapshots : List PlannedProbeSnapshot}
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (hbefore : SnapshotsBefore snapshots context)
    (hresult : DirectWitnessResult.done result ∈ support
      (runDirectResolvedWitnessFromTable context fuel table computation)) :
    SnapshotsBefore snapshots result.context := by
  have hdetailed : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table computation) := by
    rw [← map_erase_runDirectResolvedWitnessFromTable computation context fuel table,
      support_map]
    exact ⟨DirectWitnessResult.done result, hresult, rfl⟩
  exact hbefore.trans
    (revealed_subset_done_of_mem_runDirectResolvedWitnessFromTable computation context fuel table
      result hresult)
    (privateValuesLE_of_done_runDirectResolvedDetailedFromTable computation context fuel table
      result hdetailed)

theorem PrivateValuesLE.canonicalize_right
    {left right : DeferredContext} (hle : PrivateValuesLE left right)
    (table : OtsSecretIndex → HashOutput) :
    PrivateValuesLE left (canonicalizeMaterializedValues table right) := by
  intro position output hvalue
  exact hle position output hvalue

theorem SnapshotsBefore.canonicalize_right
    {snapshots : List PlannedProbeSnapshot} {context : DeferredContext}
    (hbefore : SnapshotsBefore snapshots context)
    (table : OtsSecretIndex → HashOutput) :
    SnapshotsBefore snapshots (canonicalizeMaterializedValues table context) := by
  apply hbefore.trans
  · rw [canonicalizeMaterializedValues_revealed]
  · exact (PrivateValuesLE.refl context).canonicalize_right table

theorem SnapshotsBefore.revealed_subset_privateWitness
    {snapshots : List PlannedProbeSnapshot}
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (witness : PrivateHitWitness)
    (hbefore : SnapshotsBefore snapshots context)
    (hresult : DirectWitnessResult.stoppedPrivate witness ∈ support
      (runDirectResolvedWitnessFromTable context fuel table computation)) :
    ∀ snapshot ∈ snapshots,
      snapshot.context.state.revealed ⊆ witness.revealed := by
  intro snapshot hsnapshot
  exact (hbefore snapshot hsnapshot).1.trans
    (revealed_subset_privateWitness_of_mem_runDirectResolvedWitnessFromTable computation context
      fuel table witness hresult)

theorem SnapshotsBefore.privateValue_eq_privateWitness
    {snapshots : List PlannedProbeSnapshot}
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (witness : PrivateHitWitness)
    (hbefore : SnapshotsBefore snapshots context)
    (hresult : DirectWitnessResult.stoppedPrivate witness ∈ support
      (runDirectResolvedWitnessFromTable context fuel table computation))
    {snapshot : PlannedProbeSnapshot} (hsnapshot : snapshot ∈ snapshots)
    {output : HashOutput}
    (hvalue : snapshot.context.values witness.position = some output) :
    output = witness.output := by
  have hcurrent := (hbefore snapshot hsnapshot).2 witness.position output hvalue
  exact privateValue_eq_privateWitness_of_mem_runDirectResolvedWitnessFromTable computation
    context fuel table witness witness.position output hcurrent rfl hresult

set_option maxRecDepth 100000 in
theorem runDirectResolvedWitnessFromTable_bind
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (left : OracleComp (LazyRevealProbe.World Coordinate) α)
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β) :
    runDirectResolvedWitnessFromTable context fuel table (left >>= next) =
      runDirectResolvedWitnessFromTable context fuel table left >>= fun result =>
        match result with
        | .stoppedFuel => pure .stoppedFuel
        | .stoppedOrdinary => pure .stoppedOrdinary
        | .stoppedPrivate witness => pure (.stoppedPrivate witness)
        | .done result =>
            runDirectResolvedWitnessFromTable result.context result.remaining result.table
              (next result.value) := by
  induction left using OracleComp.inductionOn generalizing context fuel with
  | pure value => simp [runDirectResolvedWitnessFromTable]
  | query_bind input continuation ih =>
      cases input with
      | uniform n =>
          rw [bind_assoc, runDirectResolvedWitnessFromTable_uniform_query_bind,
            runDirectResolvedWitnessFromTable_uniform_query_bind]
          simp only [bind_assoc]
          apply bind_congr
          intro output
          exact ih output context fuel
      | hashOutput =>
          rw [bind_assoc, runDirectResolvedWitnessFromTable_hashOutput_query_bind,
            runDirectResolvedWitnessFromTable_hashOutput_query_bind]
          simp only [bind_assoc]
          apply bind_congr
          intro output
          exact ih output context fuel
      | ensure coordinate =>
          rw [bind_assoc, runDirectResolvedWitnessFromTable_ensure_query_bind,
            runDirectResolvedWitnessFromTable_ensure_query_bind]
          exact ih () { context with state := context.state.ensure coordinate } fuel
      | probe coordinate candidate =>
          rw [bind_assoc, runDirectResolvedWitnessFromTable_probe_query_bind,
            runDirectResolvedWitnessFromTable_probe_query_bind]
          cases fuel with
          | zero => simp
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · simp only [hrevealed, ↓reduceIte]
                exact ih () context remaining
              · simp only [hrevealed, ↓reduceIte]
                exact ih ()
                  { context with state := context.state.addPending coordinate candidate }
                  remaining
      | peek coordinate =>
          rw [bind_assoc, runDirectResolvedWitnessFromTable_peek_query_bind,
            runDirectResolvedWitnessFromTable_peek_query_bind]
          exact ih (context.state.values coordinate) context fuel
      | publish coordinate =>
          rw [bind_assoc, runDirectResolvedWitnessFromTable_publish_query_bind,
            runDirectResolvedWitnessFromTable_publish_query_bind]
          exact ih () { context with state := context.state.publish coordinate } fuel
      | reveal coordinate =>
          rw [bind_assoc, runDirectResolvedWitnessFromTable_reveal_query_bind,
            runDirectResolvedWitnessFromTable_reveal_query_bind]
          cases hvalue : context.state.values coordinate with
          | some output => exact ih output context fuel
          | none =>
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : context.state.hitAt
                      (.chainStart lay tree leafIdx chainIdx) output
                  · simp [output, hhit]
                  · simp only [output, hhit, ↓reduceIte]
                    exact ih output
                      { state := context.state.materialize
                          (.chainStart lay tree leafIdx chainIdx) output
                        values := context.values }
                      fuel
              | position position =>
                  cases hprivate : context.values position with
                  | some output =>
                      by_cases hhit : context.state.hitAt (.position position) output
                      · simp [hprivate, hhit]
                      · simp only [hprivate, hhit, ↓reduceIte]
                        exact ih output
                          { state := context.state.materialize (.position position) output
                            values := context.values }
                          fuel
                  | none =>
                      simp only [hprivate, bind_assoc]
                      apply bind_congr
                      intro output
                      by_cases hhit : context.state.hitAt (.position position) output
                      · simp [hhit]
                      · simp only [hhit, ↓reduceIte]
                        exact ih output
                          { state := context.state.materialize (.position position) output
                            values := context.values.install position output }
                          fuel

def DirectWitnessPublishedResult : DirectWitnessResult α → Prop
  | .stoppedFuel => True
  | .stoppedOrdinary => True
  | .stoppedPrivate witness =>
      Coordinate.position witness.position ∉ witness.revealed
  | .done result => PublishedValues result.context.state

def DirectWitnessPreservesPublished
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ context cache fuel table result,
    PublishedValues context.state →
    result ∈ support
      (runDirectResolvedWitnessFromTable context fuel table (computation.run cache)) →
    DirectWitnessPublishedResult result

theorem DirectWitnessPreservesPublished.result
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    (hpreserves : DirectWitnessPreservesPublished computation)
    (context : DeferredContext) (cache : SplitHashCache) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (result : DirectWitnessResult (α × SplitHashCache))
    (hpublished : PublishedValues context.state)
    (hresult : result ∈ support
      (runDirectResolvedWitnessFromTable context fuel table (computation.run cache))) :
    DirectWitnessPublishedResult result := by
  exact hpreserves context cache fuel table result hpublished hresult

theorem DirectWitnessPreservesPublished.pure (value : α) :
    DirectWitnessPreservesPublished
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) α) := by
  intro context cache fuel table result hpublished hresult
  simp [runDirectResolvedWitnessFromTable] at hresult
  subst result
  exact hpublished

theorem DirectWitnessPreservesPublished.bind
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hleft : DirectWitnessPreservesPublished left)
    (hnext : ∀ value, DirectWitnessPreservesPublished (next value)) :
    DirectWitnessPreservesPublished (left >>= next) := by
  intro context cache fuel table result hpublished hresult
  rw [StateT.run_bind, runDirectResolvedWitnessFromTable_bind,
    mem_support_bind_iff] at hresult
  obtain ⟨middle, hmiddle, hrest⟩ := hresult
  have hmiddlePublished := hleft context cache fuel table middle hpublished hmiddle
  cases middle with
  | stoppedFuel =>
      simp at hrest
      subst result
      trivial
  | stoppedOrdinary =>
      simp at hrest
      subst result
      trivial
  | stoppedPrivate witness =>
      simp at hrest
      subst result
      exact hmiddlePublished
  | done middle =>
      exact hnext middle.value.1 middle.context middle.value.2 middle.remaining middle.table
        result hmiddlePublished hrest

theorem directWitnessPreservesPublished_revealCoordinateOutput
    (coordinate : Coordinate) :
    DirectWitnessPreservesPublished (revealCoordinateOutput coordinate) := by
  intro context cache fuel table result hpublished hresult
  rw [revealCoordinateOutput_run, LazyRevealProbe.revealQuery,
    runDirectResolvedWitnessFromTable_reveal_query_bind] at hresult
  cases hvalue : context.state.values coordinate with
  | some output =>
      simp [hvalue, runDirectResolvedWitnessFromTable] at hresult
      subst result
      exact hpublished
  | none =>
      simp only [hvalue] at hresult
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          let output := table ⟨lay, tree, leafIdx, chainIdx⟩
          by_cases hhit : context.state.hitAt
              (.chainStart lay tree leafIdx chainIdx) output
          · simp [output, hhit] at hresult
            subst result
            trivial
          · simp [output, hhit, runDirectResolvedWitnessFromTable] at hresult
            subst result
            exact hpublished.materialize _ _
      | position position =>
          cases hprivate : context.values position with
          | some output =>
              by_cases hhit : context.state.hitAt (.position position) output
              · simp [hprivate, hhit] at hresult
                subst result
                exact hpublished.not_revealed_of_value_none hvalue
              · simp [hprivate, hhit, runDirectResolvedWitnessFromTable] at hresult
                subst result
                exact hpublished.materialize _ _
          | none =>
              simp only [hprivate, mem_support_bind_iff] at hresult
              obtain ⟨output, _houtput, hrest⟩ := hresult
              by_cases hhit : context.state.hitAt (.position position) output
              · simp [hhit] at hrest
                subst result
                trivial
              · simp [hhit, runDirectResolvedWitnessFromTable] at hrest
                subst result
                exact hpublished.materialize _ _

theorem directWitnessPreservesPublished_revealCoordinate
    (coordinate : Coordinate) :
    DirectWitnessPreservesPublished (revealCoordinate coordinate) := by
  unfold revealCoordinate
  exact (directWitnessPreservesPublished_revealCoordinateOutput coordinate).bind fun _ =>
    DirectWitnessPreservesPublished.pure _

set_option maxRecDepth 100000 in
theorem directWitnessPreservesPublished_revealCoordinateOutput_publish
    (coordinate : Coordinate) :
    DirectWitnessPreservesPublished (do
      let output ← revealCoordinateOutput coordinate
      publishCoordinate coordinate
      pure output) := by
  intro context cache fuel table result hpublished hresult
  rw [StateT.run_bind, runDirectResolvedWitnessFromTable_bind,
    mem_support_bind_iff] at hresult
  obtain ⟨middle, hmiddle, hrest⟩ := hresult
  have hmiddlePublished := directWitnessPreservesPublished_revealCoordinateOutput coordinate
    context cache fuel table middle hpublished hmiddle
  cases middle with
  | stoppedFuel =>
      simp at hrest
      subst result
      trivial
  | stoppedOrdinary =>
      simp at hrest
      subst result
      trivial
  | stoppedPrivate witness =>
      simp at hrest
      subst result
      exact hmiddlePublished
  | done middle =>
      have hdetailed : DirectDetailedResult.done middle ∈ support
          (runDirectResolvedDetailedFromTable context fuel table
            ((revealCoordinateOutput coordinate).run cache)) := by
        rw [← map_erase_runDirectResolvedWitnessFromTable
          ((revealCoordinateOutput coordinate).run cache) context fuel table,
          support_map]
        exact ⟨DirectWitnessResult.done middle, hmiddle, rfl⟩
      have hvalue :=
        value_of_done_runDirectResolvedDetailedFromTable_revealCoordinateOutput table coordinate
          context fuel cache middle hdetailed
      change result ∈ support
        (runDirectResolvedWitnessFromTable middle.context middle.remaining middle.table
          ((publishCoordinate coordinate >>= fun _ =>
            pure middle.value.1).run middle.value.2)) at hrest
      simp only [publishCoordinate, StateT.run_bind, StateT.run_liftM,
        StateT.run_pure, bind_assoc, pure_bind] at hrest
      rw [LazyRevealProbe.publishQuery,
        runDirectResolvedWitnessFromTable_publish_query_bind] at hrest
      simp [runDirectResolvedWitnessFromTable] at hrest
      subst result
      exact hmiddlePublished.publish_of_value coordinate middle.value.1 hvalue

theorem directWitnessPreservesPublished_revealPublishedCoordinate
    (coordinate : Coordinate) :
    DirectWitnessPreservesPublished (revealPublishedCoordinate coordinate) := by
  have hpreserves :=
    (directWitnessPreservesPublished_revealCoordinateOutput_publish coordinate).bind
      fun output => DirectWitnessPreservesPublished.pure (truncateHash output)
  simpa only [revealPublishedCoordinate, revealCoordinate, bind_assoc, pure_bind] using hpreserves

theorem directWitnessPreservesPublished_modify
    (update : SplitHashCache → SplitHashCache) :
    DirectWitnessPreservesPublished
      (modify update : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) Unit) := by
  intro context cache fuel table result hpublished hresult
  simp [StateT.run_modify, runDirectResolvedWitnessFromTable] at hresult
  subst result
  exact hpublished

theorem directWitnessPreservesPublished_splitHashQuery (key : SplitHashKey) :
    DirectWitnessPreservesPublished (splitHashQuery key) := by
  intro context cache fuel table result hpublished hresult
  rw [splitHashQuery_run_eq] at hresult
  cases hlookup : cache key with
  | some output =>
      rw [hlookup] at hresult
      simp [runDirectResolvedWitnessFromTable] at hresult
      subst result
      exact hpublished
  | none =>
      rw [hlookup] at hresult
      dsimp only at hresult
      rw [LazyRevealProbe.hashOutputQuery,
        runDirectResolvedWitnessFromTable_hashOutput_query_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨output, _houtput, hdone⟩ := hresult
      simp [runDirectResolvedWitnessFromTable] at hdone
      subst result
      exact hpublished

theorem directWitnessPreservesPublished_peekCoordinate
    (coordinate : Coordinate) :
    DirectWitnessPreservesPublished (peekCoordinate coordinate) := by
  intro context cache fuel table result hpublished hresult
  rw [peekCoordinate_run_eq, LazyRevealProbe.peekQuery,
    runDirectResolvedWitnessFromTable_peek_query_bind] at hresult
  simp [runDirectResolvedWitnessFromTable] at hresult
  subst result
  exact hpublished

theorem directWitnessPreservesPublished_ensureCoordinate
    (coordinate : Coordinate) :
    DirectWitnessPreservesPublished (ensureCoordinate coordinate) := by
  intro context cache fuel table result hpublished hresult
  unfold ensureCoordinate at hresult
  rw [StateT.run_liftM, LazyRevealProbe.ensureQuery,
    runDirectResolvedWitnessFromTable_ensure_query_bind] at hresult
  simp [runDirectResolvedWitnessFromTable] at hresult
  subst result
  change PublishedValues (context.state.ensure coordinate)
  simpa [PublishedValues, LazyRevealProbe.State.ensure] using hpublished

theorem directWitnessPreservesPublished_probe (candidate : Probe) :
    DirectWitnessPreservesPublished (probe candidate) := by
  intro context cache fuel table result hpublished hresult
  unfold probe at hresult
  rw [StateT.run_liftM, LazyRevealProbe.probeQuery,
    runDirectResolvedWitnessFromTable_probe_query_bind] at hresult
  cases fuel with
  | zero =>
      simp at hresult
      subst result
      trivial
  | succ remaining =>
      by_cases hrevealed : candidate.coordinate ∈ context.state.revealed
      · simp [hrevealed, runDirectResolvedWitnessFromTable] at hresult
        subst result
        exact hpublished
      · simp [hrevealed, runDirectResolvedWitnessFromTable] at hresult
        subst result
        change PublishedValues (context.state.addPending
          candidate.coordinate candidate.candidate)
        simpa [PublishedValues, LazyRevealProbe.State.addPending] using hpublished

theorem directWitnessPreservesPublished_sequenceFin {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcomponent : ∀ index, DirectWitnessPreservesPublished (computation index)) :
    DirectWitnessPreservesPublished (sequenceFin computation) := by
  induction n with
  | zero => simpa [sequenceFin] using DirectWitnessPreservesPublished.pure Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomponent 0).bind fun _ =>
        (ih (fun index : Fin n => computation index.succ)
          (fun index => hcomponent index.succ)).bind fun _ =>
            DirectWitnessPreservesPublished.pure _

theorem directWitnessPreservesPublished_splitUniformImpl (n : Nat) :
    DirectWitnessPreservesPublished (splitUniformImpl n) := by
  intro context cache fuel table result hpublished hresult
  change result ∈ support (runDirectResolvedWitnessFromTable context fuel table
    (LazyRevealProbe.uniformQuery n >>= fun output => pure (output, cache))) at hresult
  rw [LazyRevealProbe.uniformQuery,
    runDirectResolvedWitnessFromTable_uniform_query_bind,
    mem_support_bind_iff] at hresult
  obtain ⟨output, _houtput, hdone⟩ := hresult
  simp [runDirectResolvedWitnessFromTable] at hdone
  subst result
  exact hpublished

def DirectWitnessPreservesPublishedImpl {spec : OracleSpec ι}
    (impl : QueryImpl spec
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)))) : Prop :=
  ∀ query, DirectWitnessPreservesPublished (impl query)

theorem DirectWitnessPreservesPublishedImpl.simulateQ
    {spec : OracleSpec ι}
    {impl : QueryImpl spec
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)))}
    (himpl : DirectWitnessPreservesPublishedImpl impl)
    (computation : OracleComp spec α) :
    DirectWitnessPreservesPublished (simulateQ impl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact DirectWitnessPreservesPublished.pure value
  | query_bind query next ih =>
      rw [simulateQ_query_bind]
      exact (himpl query).bind ih

theorem directWitnessPreservesPublishedImpl_ordinaryHashImpl :
    DirectWitnessPreservesPublishedImpl ordinaryHashImpl :=
  fun input => directWitnessPreservesPublished_splitHashQuery (.ordinary input)

theorem directWitnessPreservesPublished_simulateQ_ordinaryHashImpl
    (computation : OracleComp HashSpec α) :
    DirectWitnessPreservesPublished (simulateQ ordinaryHashImpl computation) :=
  directWitnessPreservesPublishedImpl_ordinaryHashImpl.simulateQ computation

theorem directWitnessPreservesPublished_peekPositionValues : ∀ positions,
    DirectWitnessPreservesPublished (peekPositionValues positions)
  | [] => DirectWitnessPreservesPublished.pure _
  | position :: remaining => by
      rw [peekPositionValues]
      exact (directWitnessPreservesPublished_peekCoordinate (.position position)).bind
        fun value => match value with
        | none => DirectWitnessPreservesPublished.pure none
        | some _ => (directWitnessPreservesPublished_peekPositionValues remaining).bind
            fun values => match values with
            | none => DirectWitnessPreservesPublished.pure none
            | some values => DirectWitnessPreservesPublished.pure (some (_ :: values))

theorem directWitnessPreservesPublished_peekTableInput
    (parameter : PublicParameter) : ∀ coordinate,
    DirectWitnessPreservesPublished (peekTableInput parameter coordinate)
  | .chainStart _ _ _ _ => DirectWitnessPreservesPublished.pure none
  | .position position => by
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          simp only [peekTableInput]
          by_cases hstep : step.val = 0
          · rw [if_pos hstep]
            exact (directWitnessPreservesPublished_peekCoordinate
              (.chainStart lay tree leafIdx chainIdx)).bind fun value =>
                match value with
                | none => DirectWitnessPreservesPublished.pure none
                | some value => DirectWitnessPreservesPublished.pure (some
                    (tweakableHashInput parameter
                      (Position.chain lay tree leafIdx chainIdx step).domain
                      (digestBytes value)))
          · rw [if_neg hstep]
            exact (directWitnessPreservesPublished_peekPositionValues
              (Position.chain lay tree leafIdx chainIdx step).children).bind fun value =>
                match value with
                | none => DirectWitnessPreservesPublished.pure none
                | some values => DirectWitnessPreservesPublished.pure (some
                    (tweakableHashInput parameter
                      (Position.chain lay tree leafIdx chainIdx step).domain
                      (values.flatMap digestBytes)))
      | leaf lay tree leafIdx =>
          simp only [peekTableInput]
          exact (directWitnessPreservesPublished_peekPositionValues
            (Position.leaf lay tree leafIdx).children).bind fun value =>
              match value with
              | none => DirectWitnessPreservesPublished.pure none
              | some values => DirectWitnessPreservesPublished.pure (some
                  (tweakableHashInput parameter (Position.leaf lay tree leafIdx).domain
                    (values.flatMap digestBytes)))
      | node lay tree level nodeIdx =>
          simp only [peekTableInput]
          exact (directWitnessPreservesPublished_peekPositionValues
            (Position.node lay tree level nodeIdx).children).bind fun value =>
              match value with
              | none => DirectWitnessPreservesPublished.pure none
              | some values => DirectWitnessPreservesPublished.pure (some
                  (tweakableHashInput parameter (Position.node lay tree level nodeIdx).domain
                    (values.flatMap digestBytes)))
      | ftsLeaf index tree leafIdx =>
          simp only [peekTableInput]
          exact (directWitnessPreservesPublished_peekPositionValues
            (Position.ftsLeaf index tree leafIdx).children).bind fun value =>
              match value with
              | none => DirectWitnessPreservesPublished.pure none
              | some values => DirectWitnessPreservesPublished.pure (some
                  (tweakableHashInput parameter (Position.ftsLeaf index tree leafIdx).domain
                    (values.flatMap digestBytes)))
      | ftsNode index tree level nodeIdx =>
          simp only [peekTableInput]
          exact (directWitnessPreservesPublished_peekPositionValues
            (Position.ftsNode index tree level nodeIdx).children).bind fun value =>
              match value with
              | none => DirectWitnessPreservesPublished.pure none
              | some values => DirectWitnessPreservesPublished.pure (some
                  (tweakableHashInput parameter
                    (Position.ftsNode index tree level nodeIdx).domain
                    (values.flatMap digestBytes)))
      | ftsRoots index =>
          simp only [peekTableInput]
          exact (directWitnessPreservesPublished_peekPositionValues
            (Position.ftsRoots index).children).bind fun value =>
              match value with
              | none => DirectWitnessPreservesPublished.pure none
              | some values => DirectWitnessPreservesPublished.pure (some
                  (tweakableHashInput parameter (Position.ftsRoots index).domain
                    (values.flatMap digestBytes)))
theorem directWitnessPreservesPublished_resolveKnownInput
    (parameter : PublicParameter) (coordinate : Coordinate) (input : HashInput) :
    DirectWitnessPreservesPublished (resolveKnownInput parameter coordinate input) := by
  unfold resolveKnownInput
  exact (directWitnessPreservesPublished_peekTableInput parameter coordinate).bind fun known =>
    match known with
    | none => directWitnessPreservesPublished_splitHashQuery (.ordinary input)
    | some knownInput => by
        by_cases heq : knownInput = input
        · simp only [heq, ↓reduceIte]
          exact (directWitnessPreservesPublished_revealCoordinateOutput_publish coordinate).bind
            fun output => (directWitnessPreservesPublished_modify fun cache =>
              Function.update cache (.ordinary input) (some output)).bind fun _ =>
                DirectWitnessPreservesPublished.pure output
        · simp only [heq, ↓reduceIte]
          exact directWitnessPreservesPublished_splitHashQuery (.ordinary input)

theorem directWitnessPreservesPublished_executeCandidate?
    (candidate? : Option Probe) :
    DirectWitnessPreservesPublished (executeCandidate? candidate?) := by
  cases candidate? with
  | none => exact DirectWitnessPreservesPublished.pure ()
  | some candidate => exact directWitnessPreservesPublished_probe candidate

theorem directWitnessPreservesPublished_probingHashQueryAfterPlan
    (parameter : PublicParameter) (input : HashInput) (plan : PlannedHashQuery) :
    DirectWitnessPreservesPublished
      (probingHashQueryAfterPlan parameter input plan) := by
  unfold probingHashQueryAfterPlan executePlannedHashQuery
  exact (directWitnessPreservesPublished_executeCandidate? plan.candidate?).bind fun _ =>
    match plan.action with
    | .ordinary => directWitnessPreservesPublished_splitHashQuery (.ordinary input)
    | .resolve coordinate =>
        directWitnessPreservesPublished_resolveKnownInput parameter coordinate input

theorem directWitnessPreservesPublished_ensureFullChain
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    DirectWitnessPreservesPublished (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  exact (directWitnessPreservesPublished_sequenceFin _ fun step =>
    directWitnessPreservesPublished_ensureCoordinate
      (.position (.chain lay tree leafIdx chainIdx step))).bind fun _ =>
        DirectWitnessPreservesPublished.pure ()

theorem directWitnessPreservesPublished_ensureChainPrefix
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (digit : Digit) :
    DirectWitnessPreservesPublished
      (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  unfold ensureChainPrefix
  exact (directWitnessPreservesPublished_sequenceFin _ fun step => by
    split
    · exact directWitnessPreservesPublished_ensureCoordinate
        (.position (.chain lay tree leafIdx chainIdx step))
    · exact DirectWitnessPreservesPublished.pure ()).bind fun _ =>
        DirectWitnessPreservesPublished.pure ()

theorem directWitnessPreservesPublished_ensureOtsLeaf
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    DirectWitnessPreservesPublished (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  exact (directWitnessPreservesPublished_sequenceFin _ fun chainIdx =>
    directWitnessPreservesPublished_ensureFullChain lay tree leafIdx chainIdx).bind fun _ =>
      directWitnessPreservesPublished_ensureCoordinate (.position (.leaf lay tree leafIdx))

theorem directWitnessPreservesPublished_ensureTreeNode
    (lay : Layer) (tree : TreeIndex) : ∀ level nodeIdx,
    DirectWitnessPreservesPublished (ensureTreeNode lay tree level nodeIdx)
  | 0, nodeIdx => by
      rw [ensureTreeNode]
      exact directWitnessPreservesPublished_ensureOtsLeaf lay tree (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      exact (directWitnessPreservesPublished_ensureTreeNode lay tree level
        (2 * nodeIdx)).bind fun _ =>
          (directWitnessPreservesPublished_ensureTreeNode lay tree level
            (2 * nodeIdx + 1)).bind fun _ => by
              split
              · exact directWitnessPreservesPublished_ensureCoordinate _
              · exact DirectWitnessPreservesPublished.pure ()

theorem directWitnessPreservesPublished_maskedTreeNode
    (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat) :
    DirectWitnessPreservesPublished (maskedTreeNode lay tree level nodeIdx) := by
  cases level with
  | zero =>
      rw [maskedTreeNode]
      exact (directWitnessPreservesPublished_ensureTreeNode lay tree 0 nodeIdx).bind fun _ =>
        directWitnessPreservesPublished_revealCoordinate _
  | succ current =>
      rw [maskedTreeNode]
      exact (directWitnessPreservesPublished_ensureTreeNode lay tree (current + 1)
        nodeIdx).bind fun _ => by
          by_cases hlevel : current < maxLayerHeight
          · rw [dif_pos hlevel]
            exact directWitnessPreservesPublished_revealCoordinate _
          · rw [dif_neg hlevel]
            exact DirectWitnessPreservesPublished.pure 0

theorem directWitnessPreservesPublished_maskedTreeRoot
    (lay : Layer) (tree : TreeIndex) :
    DirectWitnessPreservesPublished (maskedTreeRoot lay tree) :=
  directWitnessPreservesPublished_maskedTreeNode lay tree (layerHeight lay) 0

theorem directWitnessPreservesPublished_ensureTreePath
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    DirectWitnessPreservesPublished (ensureTreePath lay tree leafIdx) := by
  unfold ensureTreePath
  exact (directWitnessPreservesPublished_sequenceFin _ fun level => by
    split
    · exact directWitnessPreservesPublished_ensureTreeNode lay tree level.val
        (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
    · exact DirectWitnessPreservesPublished.pure ()).bind fun _ =>
        DirectWitnessPreservesPublished.pure ()

theorem directWitnessPreservesPublished_maskedPublishedTreeRoot :
    DirectWitnessPreservesPublished maskedPublishedTreeRoot := by
  unfold maskedPublishedTreeRoot
  exact (directWitnessPreservesPublished_ensureTreeNode topLayer rootTree
    (layerHeight topLayer) 0).bind fun _ =>
      directWitnessPreservesPublished_revealPublishedCoordinate
        (.position (.node topLayer rootTree
          ⟨layerHeight topLayer - 1, by norm_num [layerHeight, topLayer, maxLayerHeight]⟩ 0))

theorem directWitnessPreservesPublished_maskedLayerMessage
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) :
    DirectWitnessPreservesPublished (maskedLayerMessage parameter ftsSecret index lay) := by
  unfold maskedLayerMessage
  split
  · exact directWitnessPreservesPublished_maskedTreeRoot _ _
  · exact directWitnessPreservesPublished_simulateQ_ordinaryHashImpl _

theorem directWitnessPreservesPublished_maskedOtsSignFrom
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest) : ∀ attempts counter,
    DirectWitnessPreservesPublished
      (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
  | 0, _ => DirectWitnessPreservesPublished.pure none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom]
      exact (directWitnessPreservesPublished_simulateQ_ordinaryHashImpl _).bind fun encoded =>
        match encoded with
        | none => directWitnessPreservesPublished_maskedOtsSignFrom parameter lay tree leafIdx
            message attempts (counter + 1)
        | some encoding =>
            (directWitnessPreservesPublished_sequenceFin _ fun chainIdx =>
              directWitnessPreservesPublished_ensureChainPrefix lay tree leafIdx chainIdx
                (encoding chainIdx)).bind fun _ => DirectWitnessPreservesPublished.pure _

theorem directWitnessPreservesPublished_maskedOtsSign
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest) :
    DirectWitnessPreservesPublished
      (maskedOtsSign parameter lay tree leafIdx message) :=
  directWitnessPreservesPublished_maskedOtsSignFrom parameter lay tree leafIdx message
    encodingAttemptLimit 0

theorem directWitnessPreservesPublished_maskedSignLayer
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) :
    DirectWitnessPreservesPublished (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayer
  exact (directWitnessPreservesPublished_maskedLayerMessage parameter ftsSecret index lay).bind
    fun message =>
      (directWitnessPreservesPublished_maskedOtsSign parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) message).bind fun result =>
          match result with
          | none => DirectWitnessPreservesPublished.pure none
          | some _ =>
              (directWitnessPreservesPublished_ensureTreePath lay (treeIndexAt index lay)
                (leafIndexAt index lay)).bind fun _ => DirectWitnessPreservesPublished.pure _

theorem directWitnessPreservesPublished_revealLayerValues
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit) :
    DirectWitnessPreservesPublished (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  exact (directWitnessPreservesPublished_sequenceFin _ fun chainIdx =>
    directWitnessPreservesPublished_revealPublishedCoordinate
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx
        (encoding chainIdx))).bind fun _ =>
          (directWitnessPreservesPublished_sequenceFin _ fun level => by
            split
            · cases hlevelValue : level.val with
              | zero => exact directWitnessPreservesPublished_revealPublishedCoordinate _
              | succ current =>
                  rw [show current + 1 = Nat.succ current by omega]
                  change DirectWitnessPreservesPublished
                    (if hlevel : current < maxLayerHeight then
                      revealPublishedCoordinate (.position (.node lay (treeIndexAt index lay)
                        ⟨current, hlevel⟩ (leafOfNat
                          (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
                    else pure 0)
                  by_cases hlevel : current < maxLayerHeight
                  · rw [dif_pos hlevel]
                    exact directWitnessPreservesPublished_revealPublishedCoordinate _
                  · rw [dif_neg hlevel]
                    exact DirectWitnessPreservesPublished.pure 0
            · exact DirectWitnessPreservesPublished.pure 0).bind fun _ =>
                  DirectWitnessPreservesPublished.pure _

theorem directWitnessPreservesPublished_ordinarySignDigestLoop
    (secretKey : SecretKey) (attempts : Nat) (message : Message) :
    DirectWitnessPreservesPublished
      (simulateQ ordinaryRomImpl (signDigestLoop attempts secretKey message)) := by
  induction attempts with
  | zero =>
      rw [signDigestLoop, simulateQ_pure]
      exact DirectWitnessPreservesPublished.pure none
  | succ attempts ih =>
      rw [signDigestLoop, simulateQ_bind]
      have hrandomness : DirectWitnessPreservesPublished
          (simulateQ ordinaryRomImpl (liftM sampleRandomness)) := by
        rw [ordinaryRomImpl, QueryImpl.simulateQ_add_liftM_left]
        exact (show DirectWitnessPreservesPublishedImpl splitUniformImpl from
          fun n => directWitnessPreservesPublished_splitUniformImpl n).simulateQ
            sampleRandomness
      exact hrandomness.bind fun randomness => by
        rw [simulateQ_bind]
        have hattempt : DirectWitnessPreservesPublished
            (simulateQ ordinaryRomImpl
              (liftM (signAttempt secretKey message randomness :
                OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf)))))) := by
          rw [ordinaryRomImpl, QueryImpl.simulateQ_add_liftM_right]
          exact directWitnessPreservesPublished_simulateQ_ordinaryHashImpl _
        exact hattempt.bind fun attempt => by
          cases attempt with
          | none => exact ih
          | some selected => exact DirectWitnessPreservesPublished.pure _

theorem directWitnessPreservesPublished_maskedSignAfterDigest
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    DirectWitnessPreservesPublished
      (maskedSignAfterDigest parameter ftsSecret randomness index leaves) := by
  unfold maskedSignAfterDigest
  exact (directWitnessPreservesPublished_simulateQ_ordinaryHashImpl _).bind fun _ =>
    (directWitnessPreservesPublished_sequenceFin _ fun lay =>
      directWitnessPreservesPublished_maskedSignLayer parameter ftsSecret index lay).bind
        fun layers => match traverseOption layers with
        | none => DirectWitnessPreservesPublished.pure none
        | some parts => (directWitnessPreservesPublished_sequenceFin _ fun lay =>
            directWitnessPreservesPublished_revealLayerValues index lay (parts lay).2).bind
              fun _ => DirectWitnessPreservesPublished.pure _

theorem directWitnessPreservesPublished_maskedSign
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message) :
    DirectWitnessPreservesPublished (maskedSign parameter root ftsSecret message) := by
  unfold maskedSign
  exact (directWitnessPreservesPublished_ordinarySignDigestLoop
    (⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩ : SecretKey) digestAttemptLimit
      message).bind fun selected => match selected with
        | none => DirectWitnessPreservesPublished.pure none
        | some data => directWitnessPreservesPublished_maskedSignAfterDigest parameter ftsSecret
            data.1 data.2.1 data.2.2

def SourceSnapshotStopInvariant (output : PrivateWitnessSnapshotOutput) : Prop :=
  ∀ witness, output.1 = some witness →
    Coordinate.position witness.position ∉ witness.revealed ∧
      ∀ snapshot ∈ output.2,
        snapshot.context.state.revealed ⊆ witness.revealed ∧
          ∀ value, snapshot.context.values witness.position = some value →
            value = witness.output

theorem sourceSnapshotStopInvariant_none
    (snapshots : List PlannedProbeSnapshot) :
    SourceSnapshotStopInvariant (none, snapshots) := by
  intro witness hwitness
  simp at hwitness

theorem sourceSnapshotStopInvariant_privateHitWitnessOf
    {snapshots : List PlannedProbeSnapshot} {context : DeferredContext}
    (hbefore : SnapshotsBefore snapshots context)
    (hpublished : PublishedValues context.state)
    (hhit : PrivateStructuralHit context) :
    SourceSnapshotStopInvariant
      (some (privateHitWitnessOf context hhit), snapshots) := by
  intro witness hwitness
  have hwitnessEq : witness = privateHitWitnessOf context hhit := Option.some.inj hwitness.symm
  subst witness
  have hspec := privateHitWitnessOf_spec context hhit
  constructor
  · exact hpublished.not_revealed_of_value_none hspec.1
  · intro snapshot hsnapshot
    have hsnapshotBefore := hbefore snapshot hsnapshot
    constructor
    · simpa [privateHitWitnessOf] using hsnapshotBefore.1
    · intro value hvalue
      have hcurrent := hsnapshotBefore.2 _ value hvalue
      exact Option.some.inj (hcurrent.symm.trans hspec.2.1)

set_option maxRecDepth 100000 in
theorem sourceSnapshotStopInvariant_stoppedPrivate
    {snapshots : List PlannedProbeSnapshot}
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (witness : PrivateHitWitness)
    (hbefore : SnapshotsBefore snapshots context)
    (hhidden : Coordinate.position witness.position ∉ witness.revealed)
    (hresult : DirectWitnessResult.stoppedPrivate witness ∈ support
      (runDirectResolvedWitnessFromTable context fuel table computation)) :
    SourceSnapshotStopInvariant (some witness, snapshots) := by
  intro selected hselected
  have heq : selected = witness := Option.some.inj hselected.symm
  subst selected
  refine ⟨hhidden, ?_⟩
  intro snapshot hsnapshot
  constructor
  · exact hbefore.revealed_subset_privateWitness computation context fuel table witness hresult
      snapshot hsnapshot
  · intro value hvalue
    exact hbefore.privateValue_eq_privateWitness computation context fuel table witness hresult
      hsnapshot hvalue

set_option maxRecDepth 100000 in
theorem sourceSnapshotStopInvariant_of_mem_runDirectWitnessSnapshotObserve
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (snapshots : List PlannedProbeSnapshot) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hbefore : SnapshotsBefore snapshots context)
    (hpreserves : ∀ result,
      result ∈ support
        (runDirectResolvedWitnessFromTable context fuel table computation) →
      DirectWitnessPublishedResult result)
    (hobserve : ∀ result output,
      DirectWitnessResult.done result ∈ support
        (runDirectResolvedWitnessFromTable context fuel table computation) →
      SnapshotsBefore snapshots result.context →
      PublishedValues result.context.state →
      output ∈ support
        (observe result.context result.remaining result.value snapshots) →
      SourceSnapshotStopInvariant output)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (runDirectWitnessSnapshotObserve observe snapshots context fuel table computation)) :
    SourceSnapshotStopInvariant output := by
  unfold runDirectWitnessSnapshotObserve at houtput
  rw [mem_support_bind_iff] at houtput
  obtain ⟨result, hresult, hfinish⟩ := houtput
  have hresultPublished := hpreserves result hresult
  cases result with
  | stoppedFuel =>
      simp [finishDirectWitnessSnapshotObserve] at hfinish
      subst output
      exact sourceSnapshotStopInvariant_none snapshots
  | stoppedOrdinary =>
      simp [finishDirectWitnessSnapshotObserve] at hfinish
      subst output
      exact sourceSnapshotStopInvariant_none snapshots
  | stoppedPrivate witness =>
      simp [finishDirectWitnessSnapshotObserve] at hfinish
      subst output
      exact sourceSnapshotStopInvariant_stoppedPrivate computation context fuel table witness
        hbefore hresultPublished hresult
  | done result =>
      apply hobserve result output hresult
      · exact hbefore.of_done_runDirectResolvedWitnessFromTable computation context fuel table
          result hresult
      · exact hresultPublished
      · simpa [finishDirectWitnessSnapshotObserve] using hfinish

theorem sourceSnapshotStopInvariant_of_mem_classifyDirectWitnessSnapshotObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (context : DeferredContext) (fuel : Nat) (value : α)
    (snapshots : List PlannedProbeSnapshot)
    (hbefore : SnapshotsBefore snapshots context)
    (hpublished : PublishedValues context.state)
    (hobserve : ∀ output ∈ support (observe context fuel value snapshots),
      SourceSnapshotStopInvariant output)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (classifyDirectWitnessSnapshotObserve table observe context fuel value snapshots)) :
    SourceSnapshotStopInvariant output := by
  classical
  unfold classifyDirectWitnessSnapshotObserve at houtput
  by_cases hhit : PrivateStructuralHit context
  · simp [hhit] at houtput
    subst output
    exact sourceSnapshotStopInvariant_privateHitWitnessOf hbefore hpublished hhit
  · simp only [hhit, ↓reduceDIte] at houtput
    by_cases hcompletable : DeferredCompletable table context
    · exact hobserve output (by simpa [hcompletable] using houtput)
    · simp [hcompletable] at houtput
      subst output
      exact sourceSnapshotStopInvariant_none snapshots

theorem sourceSnapshotStopInvariant_of_mem_canonicalizeDirectWitnessSnapshotObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (context : DeferredContext) (fuel : Nat) (value : α)
    (snapshots : List PlannedProbeSnapshot)
    (hbefore : SnapshotsBefore snapshots context)
    (hpublished : PublishedValues context.state)
    (hobserve : ∀ output ∈ support
      (observe (canonicalizeMaterializedValues table context) fuel value snapshots),
      SourceSnapshotStopInvariant output)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (canonicalizeDirectWitnessSnapshotObserve table observe context fuel value snapshots)) :
    SourceSnapshotStopInvariant output := by
  classical
  let canonical := canonicalizeMaterializedValues table context
  have hcanonicalBefore : SnapshotsBefore snapshots canonical :=
    hbefore.canonicalize_right table
  have hcanonicalPublished : PublishedValues canonical.state :=
    hpublished.to_canonicalizedMaterializedValues
  unfold canonicalizeDirectWitnessSnapshotObserve at houtput
  by_cases hhit : PrivateStructuralHit canonical
  · simp [canonical, hhit] at houtput
    subst output
    exact sourceSnapshotStopInvariant_privateHitWitnessOf hcanonicalBefore hcanonicalPublished
      hhit
  · simp only [canonical, hhit, ↓reduceDIte, hpublished, ↓reduceIte] at houtput
    exact sourceSnapshotStopInvariant_of_mem_classifyDirectWitnessSnapshotObserve table observe
      canonical fuel value snapshots hcanonicalBefore hcanonicalPublished hobserve output houtput

theorem sourceSnapshotStopInvariant_of_mem_retainedResolvedFinalization
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache)
    (snapshots : List PlannedProbeSnapshot)
    (hbefore : SnapshotsBefore snapshots context)
    (hpublished : PublishedValues context.state)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (retainedResolvedFinalizationPrivateWitnessSnapshotObserve table root context fuel value
        snapshots)) :
    SourceSnapshotStopInvariant output := by
  classical
  unfold retainedResolvedFinalizationPrivateWitnessSnapshotObserve at houtput
  by_cases hhit : PrivateStructuralHit context
  · simp [hhit] at houtput
    subst output
    exact sourceSnapshotStopInvariant_privateHitWitnessOf hbefore hpublished hhit
  · simp [hhit] at houtput
    subst output
    exact sourceSnapshotStopInvariant_none snapshots

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem sourceSnapshotStopInvariant_of_mem_directDetailedBoundaryNormalized
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List PlannedProbeSnapshot → ProbComp PrivateWitnessSnapshotOutput)
    (snapshots : List PlannedProbeSnapshot) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hbefore : SnapshotsBefore snapshots context)
    (hpublished : PublishedValues context.state)
    (hobserve : ∀ nextContext remaining value nextSnapshots,
      SnapshotsBefore nextSnapshots nextContext → PublishedValues nextContext.state →
      ∀ output ∈ support (observe nextContext remaining value nextSnapshots),
        SourceSnapshotStopInvariant output)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve parameter root ftsSecret
        computation observe snapshots context fuel table cache)) :
    SourceSnapshotStopInvariant output := by
  induction computation using OracleComp.inductionOn generalizing
      snapshots context fuel cache output with
  | pure value =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve,
        OracleComp.construct_pure] at houtput
      exact hobserve context fuel (value, cache) snapshots hbefore hpublished output houtput
  | query_bind query next ih =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve,
        OracleComp.construct_query_bind] at houtput
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              refine sourceSnapshotStopInvariant_of_mem_runDirectWitnessSnapshotObserve _
                snapshots context fuel table ((splitUniformImpl n).run cache) hbefore ?_ ?_
                  output houtput
              · intro result hresult
                exact directWitnessPreservesPublished_splitUniformImpl n context cache fuel table
                  result hpublished hresult
              · intro result nextOutput hresult hnextBefore hnextPublished hnext
                apply sourceSnapshotStopInvariant_of_mem_canonicalizeDirectWitnessSnapshotObserve
                  table _ result.context result.remaining result.value snapshots hnextBefore
                  hnextPublished _ nextOutput hnext
                intro finalOutput hfinal
                exact ih result.value.1 snapshots
                  (canonicalizeMaterializedValues table result.context) result.remaining
                  result.value.2 (hnextBefore.canonicalize_right table)
                  hnextPublished.to_canonicalizedMaterializedValues finalOutput hfinal
          | inr input =>
              let plan := purePlanProbingHashQuery parameter input context.state
              let nextSnapshots := appendPlannedSnapshot snapshots
                (rootAwarePlannedCandidate? parameter input context.state) context
              have hnextBefore : SnapshotsBefore nextSnapshots context :=
                hbefore.appendPlannedSnapshot _
              refine sourceSnapshotStopInvariant_of_mem_runDirectWitnessSnapshotObserve _
                nextSnapshots context fuel table
                ((probingHashQueryAfterPlan parameter input plan).run cache) hnextBefore ?_ ?_
                  output houtput
              · intro result hresult
                exact directWitnessPreservesPublished_probingHashQueryAfterPlan parameter input plan
                  context cache fuel table result hpublished hresult
              · intro result nextOutput hresult hlaterBefore hlaterPublished hnext
                apply sourceSnapshotStopInvariant_of_mem_canonicalizeDirectWitnessSnapshotObserve
                  table _ result.context result.remaining result.value nextSnapshots hlaterBefore
                  hlaterPublished _ nextOutput hnext
                intro finalOutput hfinal
                exact ih result.value.1 nextSnapshots
                  (canonicalizeMaterializedValues table result.context) result.remaining
                  result.value.2 (hlaterBefore.canonicalize_right table)
                  hlaterPublished.to_canonicalizedMaterializedValues finalOutput hfinal
      | inr message =>
          refine sourceSnapshotStopInvariant_of_mem_runDirectWitnessSnapshotObserve _ snapshots
            context fuel table ((maskedSign parameter root ftsSecret message).run cache) hbefore
              ?_ ?_ output houtput
          · intro result hresult
            exact directWitnessPreservesPublished_maskedSign parameter root ftsSecret message
              context cache fuel table result hpublished hresult
          · intro result nextOutput hresult hnextBefore hnextPublished hnext
            apply sourceSnapshotStopInvariant_of_mem_canonicalizeDirectWitnessSnapshotObserve
              table _ result.context result.remaining result.value snapshots hnextBefore
              hnextPublished _ nextOutput hnext
            intro finalOutput hfinal
            exact ih result.value.1 snapshots
              (canonicalizeMaterializedValues table result.context) result.remaining result.value.2
              (hnextBefore.canonicalize_right table)
              hnextPublished.to_canonicalizedMaterializedValues finalOutput hfinal

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem sourceSnapshotStopInvariant_of_mem_granularDetailedRetainedRest
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (snapshots : List PlannedProbeSnapshot)
    (hbefore : SnapshotsBefore snapshots context)
    (hpublished : PublishedValues context.state)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve adversary parameter
        table ftsSecret context fuel value snapshots)) :
    SourceSnapshotStopInvariant output := by
  unfold granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve at houtput
  apply sourceSnapshotStopInvariant_of_mem_directDetailedBoundaryNormalized parameter value.1
    ftsSecret (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationPrivateWitnessSnapshotObserve table value.1)
    snapshots context fuel table value.2 hbefore hpublished _ output houtput
  intro nextContext remaining nextValue nextSnapshots hnextBefore hnextPublished finalOutput hfinal
  exact sourceSnapshotStopInvariant_of_mem_retainedResolvedFinalization table value.1 nextContext
    remaining nextValue nextSnapshots hnextBefore hnextPublished finalOutput hfinal

attribute [local irreducible] maskedPublishedTreeRoot in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem sourceSnapshotStopInvariant_of_mem_granularAll
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (granularAllDirectBoundaryNormalizedPrivateWitnessSnapshot adversary parameter table
        ftsSecret fuel)) :
    SourceSnapshotStopInvariant output := by
  let initialContext : DeferredContext :=
    { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      values := emptyDeferredStructuralValues }
  change output ∈ support (runDirectWitnessSnapshotObserve
    (granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve adversary parameter table
      ftsSecret) [] initialContext fuel table
    (maskedPublishedTreeRoot.run emptySplitHashCache)) at houtput
  have hbefore : SnapshotsBefore ([] : List PlannedProbeSnapshot) initialContext :=
    SnapshotsBefore.nil initialContext
  have hpreserves : DirectWitnessPreservesPublished maskedPublishedTreeRoot :=
    directWitnessPreservesPublished_maskedPublishedTreeRoot
  have hinitialPublished : PublishedValues initialContext.state := by
    exact publishedValues_empty
  let hpreservesResult := fun result =>
    hpreserves.result initialContext emptySplitHashCache fuel table result hinitialPublished
  have hobserve : ∀ result nextOutput,
      DirectWitnessResult.done result ∈ support
        (runDirectResolvedWitnessFromTable initialContext fuel table
          (maskedPublishedTreeRoot.run emptySplitHashCache)) →
      SnapshotsBefore [] result.context →
      PublishedValues result.context.state →
      nextOutput ∈ support
        (granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve adversary parameter
          table ftsSecret result.context result.remaining result.value []) →
      SourceSnapshotStopInvariant nextOutput := by
    intro result nextOutput _ hnextBefore hpublished hnext
    exact sourceSnapshotStopInvariant_of_mem_granularDetailedRetainedRest adversary parameter table
      ftsSecret result.context result.remaining result.value [] hnextBefore hpublished nextOutput
      hnext
  exact sourceSnapshotStopInvariant_of_mem_runDirectWitnessSnapshotObserve
    (observe := granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve adversary
      parameter table ftsSecret)
    (snapshots := []) (context := initialContext) (fuel := fuel) (table := table)
    (computation := maskedPublishedTreeRoot.run emptySplitHashCache)
    hbefore hpreservesResult hobserve output houtput

attribute [local irreducible]
  granularAllDirectBoundaryNormalizedPrivateWitnessSnapshot maskedPublishedTreeRoot in
set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem sourceSnapshotStopInvariant_of_mem_sampledGranularAll
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (sampledGranularAllDirectBoundaryNormalizedPrivateWitnessSnapshot adversary parameter
        ftsSecret fuel)) :
    SourceSnapshotStopInvariant output := by
  change output ∈ support (sampleOtsHashTable >>= fun table =>
    granularAllDirectBoundaryNormalizedPrivateWitnessSnapshot adversary parameter table ftsSecret
      fuel) at houtput
  rw [mem_support_bind_iff] at houtput
  obtain ⟨table, _htable, hrest⟩ := houtput
  exact sourceSnapshotStopInvariant_of_mem_granularAll adversary parameter table ftsSecret fuel
    output hrest

set_option maxRecDepth 100000 in
theorem selectedObservationHidden_of_sourceSnapshotStopInvariant
    {table : OtsSecretIndex → HashOutput}
    {source : PrivateWitnessSnapshotOutput}
    {observations : List CleanProbeObservation}
    (hsource : SourceSnapshotStopInvariant source)
    (haligned : SnapshotsObservedAt table source.2 observations) :
    ∀ witness
      (sourceOrdinal : Fin
        (erasePrivateWitnessSnapshotOutput source).2.length)
      (observationOrdinal : Fin observations.length),
      (erasePrivateWitnessSnapshotOutput source).1 = some witness →
      sourceOrdinal.val = observationOrdinal.val →
      firstPrivateWitnessOrdinal? witness
          (erasePrivateWitnessSnapshotOutput source).2 = some sourceOrdinal →
      (observations.get observationOrdinal).revealedAtProbe = false := by
  intro witness sourceOrdinal observationOrdinal hwitness hordinal hfirst
  have hwitnessSource : source.1 = some witness := by
    simpa [erasePrivateWitnessSnapshotOutput] using hwitness
  have hsourceFacts := hsource witness hwitnessSource
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
  let alignedObservationOrdinal : Fin observations.length :=
    ⟨snapshotOrdinal.val, hobservationLt⟩
  have halignedOrdinal : alignedObservationOrdinal = observationOrdinal := by
    apply Fin.ext
    exact hordinal
  have hpair := haligned.get snapshotOrdinal.isLt hobservationLt
  have hpair' : PlannedProbeSnapshot.ObservedAt table
      (source.2.get snapshotOrdinal) (observations.get observationOrdinal) := by
    simpa [alignedObservationOrdinal, halignedOrdinal] using hpair
  have hsourceProbe :
      (erasePrivateWitnessSnapshotOutput source).2.get sourceOrdinal =
        (source.2.get snapshotOrdinal).probe := by
    simp [erasePrivateWitnessSnapshotOutput, snapshotOrdinal]
  have hmatch := privateWitnessAtOrdinal_of_firstPrivateWitnessOrdinal?_eq_some hfirst
  unfold PrivateWitnessAtOrdinal at hmatch
  rw [hsourceProbe] at hmatch
  have hcoordinate : (observations.get observationOrdinal).coordinate =
      Coordinate.position witness.position := by
    have hprobe : (observations.get observationOrdinal).toProbe =
        (source.2.get snapshotOrdinal).probe := by
      exact hpair'.1
    exact congrArg Probe.coordinate hprobe |>.trans hmatch.1
  have hsnapshotHidden : Coordinate.position witness.position ∉
      (source.2.get snapshotOrdinal).context.state.revealed := by
    intro hrevealed
    exact hsourceFacts.1
      ((hsourceFacts.2 (source.2.get snapshotOrdinal) (List.get_mem _ _)).1 hrevealed)
  rw [hpair'.2.2.1]
  simp only [decide_eq_false_iff_not]
  rwa [hcoordinate]

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

set_option maxRecDepth 100000 in
theorem witnessFirstUsesSomeDelayedLayerRootSnapshot_of_aligned_tracked_sourceInvariant
    {table : OtsSecretIndex → HashOutput}
    {source : PrivateWitnessSnapshotOutput}
    {result : ObservedCleanRunResult α}
    (hsource : SourceSnapshotStopInvariant source)
    (haligned : SnapshotsObservedAt table source.2 result.observations)
    (hfirst : WitnessFirstUsesSomeLayerRoot
      (erasePrivateWitnessSnapshotOutput source))
    (htracked : CleanProbeObservationsTrackedBy result.observations result.state)
    (hstored : ∀ witness,
      (erasePrivateWitnessSnapshotOutput source).1 = some witness →
        result.state.values (Coordinate.position witness.position) = some witness.output) :
    WitnessFirstUsesSomeDelayedLayerRootSnapshot source := by
  exact witnessFirstUsesSomeDelayedLayerRootSnapshot_of_aligned_tracked haligned hfirst htracked
    hstored (selectedObservationHidden_of_sourceSnapshotStopInvariant hsource haligned)

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
