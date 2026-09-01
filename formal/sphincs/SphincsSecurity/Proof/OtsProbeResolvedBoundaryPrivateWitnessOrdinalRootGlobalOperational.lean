import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalCoupling

/-!
# Operational global root coupling

The adaptive induction in this file has a deliberately small successful postcondition. Source
chronology and comparison observation tracking are unary support invariants, so the two-run kernel
only carries snapshot alignment and the final value at a retained private witness.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def SnapshotObservedValueRel
    (table : OtsSecretIndex → HashOutput)
    (source : PrivateWitnessSnapshotOutput)
    (observed : Option
      (ObservedCleanRunResult (RetainedGameResult × SplitHashCache))) : Prop :=
  observed = none ∨
    ∃ result, observed = some result ∧
      SnapshotsObservedAt table source.2 result.observations ∧
      ∀ witness, source.1 = some witness →
        result.state.values (.position witness.position) = some witness.output

theorem SnapshotObservedValueRel.to_rootRel
    {table : OtsSecretIndex → HashOutput}
    {source : PrivateWitnessSnapshotOutput}
    {observed : Option
      (ObservedCleanRunResult (RetainedGameResult × SplitHashCache))}
    (hrelation : SnapshotObservedValueRel table source observed)
    (hsource : SourceSnapshotStopInvariant source)
    (htracked : ∀ result, observed = some result →
      CleanProbeObservationsTrackedBy result.observations result.state) :
    SnapshotObservedRootRel source observed := by
  rcases hrelation with hfailed | ⟨result, hresult, haligned, hstored⟩
  · exact Or.inl hfailed
  · right
    intro hfirst
    subst observed
    exact witnessFirstUsesSomeDelayedLayerRootSnapshot_of_aligned_tracked_sourceInvariant
      hsource haligned hfirst (htracked result rfl) (by
        intro witness hwitness
        exact hstored witness (by simpa [erasePrivateWitnessSnapshotOutput] using hwitness))

theorem relTriple_snapshotObservedRoot_of_valueRel
    {table : OtsSecretIndex → HashOutput}
    {source : ProbComp PrivateWitnessSnapshotOutput}
    {observed : ProbComp (Option
      (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)))}
    (hrelation : RelTriple source observed (SnapshotObservedValueRel table))
    (hsource : ∀ output ∈ support source, SourceSnapshotStopInvariant output)
    (htracked : ∀ output ∈ support observed, ∀ result, output = some result →
      CleanProbeObservationsTrackedBy result.observations result.state) :
    RelTriple source observed SnapshotObservedRootRel := by
  have hleft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hrelation
      SourceSnapshotStopInvariant hsource
  have hboth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
  apply relTriple_post_mono hboth
  intro left right hfacts
  exact hfacts.1.1.to_rootRel hfacts.1.2 fun result hresult =>
    htracked right hfacts.2 result hresult

def DirectWitnessMaterializedStableRunEq
    (table : OtsSecretIndex → HashOutput) :
    DirectWitnessResult (α × SplitHashCache) →
      DirectDetailedResult (α × SplitHashCache) → Prop
  | .stoppedPrivate witness, .done right =>
      (right.context.state.values (.position witness.position) = some witness.output ∧
        right.context = directDeferredContext right.context.state) ∨
        OrdinaryMaterializedDoomedRun table right
  | .stoppedPrivate _, _ => True
  | .stoppedOrdinary, .stopped .privateStructuralHit => False
  | .stoppedOrdinary, .stopped _ => True
  | .stoppedOrdinary, .done right => OrdinaryMaterializedDoomedRun table right
  | .stoppedFuel, .stopped .ordinaryHit => True
  | .stoppedFuel, .stopped .fuelExhausted => True
  | .stoppedFuel, .done right => OrdinaryMaterializedDoomedRun table right
  | .stoppedFuel, _ => False
  | .done _, .stopped .privateStructuralHit => False
  | .done _, .stopped _ => True
  | .done left, .done right =>
      OrdinaryMaterializedRunEq table left right ∨
        OrdinaryMaterializedDoomedRun table right

theorem DirectWitnessMaterializedStableRunEq.erase
    {table : OtsSecretIndex → HashOutput}
    {left : DirectWitnessResult (α × SplitHashCache)}
    {right : DirectDetailedResult (α × SplitHashCache)}
    (hrelation : DirectWitnessMaterializedStableRunEq table left right) :
    DirectDetailedOrdinaryStableRunEq table left.erase right := by
  cases left with
  | stoppedFuel =>
      cases right with
      | stopped reason => cases reason <;> exact hrelation
      | done result => exact hrelation
  | stoppedOrdinary =>
      cases right with
      | stopped reason => cases reason <;> exact hrelation
      | done result => exact hrelation
  | stoppedPrivate witness => trivial
  | done left =>
      cases right with
      | stopped reason => cases reason <;> exact hrelation
      | done right => exact hrelation

def WitnessMaterializedStableCouplesBetween
    (table : OtsSecretIndex → HashOutput)
    (left right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ leftContext rightContext leftFuel rightFuel leftCache rightCache,
    FinalizationContextLE table leftContext rightContext →
    leftFuel ≤ rightFuel →
    ordinaryQueryCache leftCache = ordinaryQueryCache rightCache →
    leftContext.state.revealed = rightContext.state.revealed →
    LazyRevealProbe.ValuesLE leftContext.state rightContext.state →
    PublishedValues leftContext.state →
    rightContext = directDeferredContext rightContext.state →
    RelTriple
      (runDirectResolvedWitnessFromTable leftContext leftFuel table (left.run leftCache))
      (runDirectResolvedDetailedFromTable rightContext rightFuel table (right.run rightCache))
      (DirectWitnessMaterializedStableRunEq table)

abbrev WitnessMaterializedStableCouples
    (table : OtsSecretIndex → HashOutput)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  WitnessMaterializedStableCouplesBetween table computation computation

theorem WitnessMaterializedStableCouplesBetween.toDetailed
    {table : OtsSecretIndex → HashOutput}
    {left right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    (hcouples : WitnessMaterializedStableCouplesBetween table left right) :
    OrdinaryMaterializedStableCouplesBetween table left right := by
  intro leftContext rightContext leftFuel rightFuel leftCache rightCache hcontext hfuel
    hcache hrevealed hvalues hpublished hrightMaterialized
  have hrun := hcouples leftContext rightContext leftFuel rightFuel leftCache rightCache hcontext
    hfuel hcache hrevealed hvalues hpublished hrightMaterialized
  rw [← map_erase_runDirectResolvedWitnessFromTable
    (left.run leftCache) leftContext leftFuel table]
  have hbind := relTriple_bind hrun fun leftResult rightResult hrelation =>
    relTriple_pure_pure (b := rightResult) hrelation.erase
  simpa using hbind

theorem witnessMaterializedStableCouples_pure
    (table : OtsSecretIndex → HashOutput) (value : α) :
    WitnessMaterializedStableCouples table
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) α) := by
  intro left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache hrevealed
    hvalues hpublished hrightMaterialized
  rw [StateT.run_pure, StateT.run_pure,
    runDirectResolvedDetailedFromTable_pure]
  simp only [runDirectResolvedWitnessFromTable]
  apply relTriple_pure_pure
  left
  exact
    { value_eq := rfl
      context_le := hcontext
      remaining_le := hfuel
      left_table := rfl
      right_table := rfl
      cache_eq := hcache
      revealed_eq := hrevealed
      values_le := hvalues
      left_published := hpublished
      right_materialized := hrightMaterialized }

set_option maxRecDepth 100000 in
theorem valuesLE_of_done_runDirectResolvedDetailedFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table computation)) :
    LazyRevealProbe.ValuesLE context.state result.context.state := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runDirectResolvedDetailedFromTable] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact LazyRevealProbe.ValuesLE.refl context.state
  | query_bind query next ih =>
      cases query with
      | uniform n =>
          rw [runDirectResolvedDetailedFromTable_uniform_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output context fuel htail
      | hashOutput =>
          rw [runDirectResolvedDetailedFromTable_hashOutput_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output context fuel htail
      | ensure coordinate =>
          rw [runDirectResolvedDetailedFromTable_ensure_query_bind] at hresult
          exact (LazyRevealProbe.valuesLE_ensure context.state coordinate).trans
            (ih () { context with state := context.state.ensure coordinate } fuel hresult)
      | probe coordinate candidate =>
          rw [runDirectResolvedDetailedFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · simp only [hrevealed, ↓reduceIte] at hresult
                exact ih () context remaining hresult
              · simp only [hrevealed, ↓reduceIte] at hresult
                exact (LazyRevealProbe.valuesLE_addPending context.state coordinate candidate).trans
                  (ih () { context with state := context.state.addPending coordinate candidate }
                    remaining hresult)
      | peek coordinate =>
          rw [runDirectResolvedDetailedFromTable_peek_query_bind] at hresult
          exact ih (context.state.values coordinate) context fuel hresult
      | publish coordinate =>
          rw [runDirectResolvedDetailedFromTable_publish_query_bind] at hresult
          exact (LazyRevealProbe.valuesLE_publish context.state coordinate).trans
            (ih () { context with state := context.state.publish coordinate } fuel hresult)
      | reveal coordinate =>
          rw [runDirectResolvedDetailedFromTable_reveal_query_bind] at hresult
          cases hvalue : context.state.values coordinate with
          | some output =>
              simp only [hvalue] at hresult
              exact ih output context fuel hresult
          | none =>
              simp only [hvalue] at hresult
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : context.state.hitAt
                      (.chainStart lay tree leafIdx chainIdx) output
                  · simp [output, hhit] at hresult
                  · simp only [output, hhit, ↓reduceIte] at hresult
                    exact (LazyRevealProbe.valuesLE_materialize_of_none context.state
                      (.chainStart lay tree leafIdx chainIdx) output hvalue).trans
                        (ih output
                          { state := context.state.materialize
                              (.chainStart lay tree leafIdx chainIdx) output
                            values := context.values }
                          fuel hresult)
              | position position =>
                  cases hprivate : context.values position with
                  | some output =>
                      by_cases hhit : context.state.hitAt (.position position) output
                      · simp [hprivate, hhit] at hresult
                      · simp only [hprivate, hhit, ↓reduceIte] at hresult
                        exact (LazyRevealProbe.valuesLE_materialize_of_none context.state
                          (.position position) output hvalue).trans
                            (ih output
                              { state := context.state.materialize (.position position) output
                                values := context.values }
                              fuel hresult)
                  | none =>
                      simp only [hprivate, mem_support_bind_iff] at hresult
                      obtain ⟨output, _houtput, htail⟩ := hresult
                      by_cases hhit : context.state.hitAt (.position position) output
                      · simp [hhit] at htail
                      · simp only [hhit, ↓reduceIte] at htail
                        exact (LazyRevealProbe.valuesLE_materialize_of_none context.state
                          (.position position) output hvalue).trans
                            (ih output
                              { state := context.state.materialize (.position position) output
                                values := context.values.install position output }
                              fuel htail)

set_option maxRecDepth 100000 in
theorem relTriple_pure_stoppedPrivate_run_of_materialized_value
    (relationTable runnerTable : OtsSecretIndex → HashOutput)
    (witness : PrivateHitWitness)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate)
      (α × SplitHashCache))
    (hvalue : state.values (.position witness.position) = some witness.output) :
    RelTriple
      (pure (.stoppedPrivate witness) :
        ProbComp (DirectWitnessResult (α × SplitHashCache)))
      (runDirectResolvedDetailedFromTable (directDeferredContext state) fuel runnerTable computation)
      (DirectWitnessMaterializedStableRunEq relationTable) := by
  have hbase := relTriple_true
    (pure (.stoppedPrivate witness) :
      ProbComp (DirectWitnessResult (α × SplitHashCache)))
    (runDirectResolvedDetailedFromTable (directDeferredContext state) fuel runnerTable computation)
  have hleft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun result => result ∈ support
        (pure (.stoppedPrivate witness) :
          ProbComp (DirectWitnessResult (α × SplitHashCache))))
      (fun result hresult => hresult)
  have hboth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
  apply relTriple_post_mono hboth
  intro leftResult rightResult hrelation
  have hleft : leftResult = .stoppedPrivate witness := by
    simpa using hrelation.1.2
  subst leftResult
  have hmaterialized := directDetailedMaterialized_of_mem_runDirectResolvedDetailedFromTable
    computation state fuel runnerTable rightResult hrelation.2
  cases rightResult with
  | stopped reason =>
      cases reason with
      | privateStructuralHit => exact False.elim hmaterialized
      | ordinaryHit => trivial
      | fuelExhausted => trivial
  | done result =>
      left
      exact ⟨valuesLE_of_done_runDirectResolvedDetailedFromTable computation
          (directDeferredContext state) fuel runnerTable result hrelation.2
            (.position witness.position) witness.output hvalue,
        hmaterialized⟩

set_option maxRecDepth 100000 in
theorem relTriple_any_run_of_materializedDoomed_witness
    (table : OtsSecretIndex → HashOutput)
    (leftRun : ProbComp (DirectWitnessResult (α × SplitHashCache)))
    (rightComputation : OracleComp (LazyRevealProbe.World Coordinate)
      (α × SplitHashCache))
    (right : DeferredContext) (rightFuel : Nat)
    (hrightDoomed : DoomedResolvedContext table right)
    (hrightMaterialized : right = directDeferredContext right.state) :
    RelTriple leftRun
      (runDirectResolvedDetailedFromTable right rightFuel table rightComputation)
      (DirectWitnessMaterializedStableRunEq table) := by
  have hbase := relTriple_true leftRun
    (runDirectResolvedDetailedFromTable right rightFuel table rightComputation)
  have hboth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hbase
  apply relTriple_post_mono hboth
  intro leftResult rightResult hrelation
  have hrightShape : DirectDetailedMaterialized rightResult := by
    have hrightSupport := hrelation.2
    rw [hrightMaterialized] at hrightSupport
    exact directDetailedMaterialized_of_mem_runDirectResolvedDetailedFromTable
      rightComputation right.state rightFuel table rightResult hrightSupport
  cases rightResult with
  | stopped reason =>
      cases reason with
      | privateStructuralHit => exact False.elim hrightShape
      | ordinaryHit =>
          cases leftResult <;> trivial
      | fuelExhausted =>
          cases leftResult <;> trivial
  | done rightResult =>
      have hdoomed := finalizationDoomedRun_of_mem_runDirectResolvedDetailedFromTable table
        rightComputation right rightFuel rightResult hrightDoomed hrelation.2
      have hrightDoomedRun : OrdinaryMaterializedDoomedRun table rightResult :=
        ⟨hdoomed, hrightShape⟩
      cases leftResult with
      | stoppedFuel => exact hrightDoomedRun
      | stoppedOrdinary => exact hrightDoomedRun
      | stoppedPrivate witness => exact Or.inr hrightDoomedRun
      | done leftResult => exact Or.inr hrightDoomedRun

theorem relTriple_any_pure_nonprivateStop_witness
    (table : OtsSecretIndex → HashOutput)
    (leftRun : ProbComp (DirectWitnessResult (α × SplitHashCache)))
    (reason : DirectStopReason) (hreason : reason ≠ .privateStructuralHit) :
    RelTriple leftRun
      (pure (.stopped reason) :
        ProbComp (DirectDetailedResult (α × SplitHashCache)))
      (DirectWitnessMaterializedStableRunEq table) := by
  have hbase := relTriple_true leftRun
    (pure (.stopped reason) :
      ProbComp (DirectDetailedResult (α × SplitHashCache)))
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hbase
  apply relTriple_post_mono hsupported
  intro leftResult rightResult hrelation
  have hright : rightResult = .stopped reason := by
    simpa using hrelation.2
  subst rightResult
  cases reason with
  | privateStructuralHit => contradiction
  | ordinaryHit => cases leftResult <;> trivial
  | fuelExhausted => cases leftResult <;> trivial

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedWitness_detailed_bind_stable
    (table : OtsSecretIndex → HashOutput)
    (left right : OracleComp (LazyRevealProbe.World Coordinate) (α × SplitHashCache))
    (leftNext rightNext : α → SplitHashCache →
      OracleComp (LazyRevealProbe.World Coordinate) (β × SplitHashCache))
    (leftContext rightContext : DeferredContext) (leftFuel rightFuel : Nat)
    (hleft : RelTriple
      (runDirectResolvedWitnessFromTable leftContext leftFuel table left)
      (runDirectResolvedDetailedFromTable rightContext rightFuel table right)
      (DirectWitnessMaterializedStableRunEq table))
    (hclean : ∀ (leftResult rightResult :
      ResolvedRunResult (α × SplitHashCache)),
      OrdinaryMaterializedRunEq table leftResult rightResult →
      RelTriple
        (runDirectResolvedWitnessFromTable leftResult.context leftResult.remaining
          leftResult.table (leftNext leftResult.value.1 leftResult.value.2))
        (runDirectResolvedDetailedFromTable rightResult.context rightResult.remaining
          rightResult.table (rightNext rightResult.value.1 rightResult.value.2))
        (DirectWitnessMaterializedStableRunEq table)) :
    RelTriple
      (runDirectResolvedWitnessFromTable leftContext leftFuel table
        (left >>= fun value => leftNext value.1 value.2))
      (runDirectResolvedDetailedFromTable rightContext rightFuel table
        (right >>= fun value => rightNext value.1 value.2))
      (DirectWitnessMaterializedStableRunEq table) := by
  rw [runDirectResolvedWitnessFromTable_bind,
    runDirectResolvedDetailedFromTable_bind]
  apply relTriple_bind hleft
  intro leftResult rightResult hrelation
  cases leftResult with
  | stoppedFuel =>
      cases rightResult with
      | stopped rightReason =>
          cases rightReason with
          | privateStructuralHit => contradiction
          | ordinaryHit => exact relTriple_pure_pure trivial
          | fuelExhausted => exact relTriple_pure_pure trivial
      | done rightResult =>
          simp only
          rw [hrelation.1.1]
          exact relTriple_any_run_of_materializedDoomed_witness table
            (pure .stoppedFuel)
            (rightNext rightResult.value.1 rightResult.value.2)
            rightResult.context rightResult.remaining hrelation.1.2 hrelation.2
  | stoppedOrdinary =>
      cases rightResult with
      | stopped rightReason =>
          cases rightReason with
          | privateStructuralHit => contradiction
          | ordinaryHit => exact relTriple_pure_pure trivial
          | fuelExhausted => exact relTriple_pure_pure trivial
      | done rightResult =>
          simp only
          rw [hrelation.1.1]
          exact relTriple_any_run_of_materializedDoomed_witness table
            (pure .stoppedOrdinary)
            (rightNext rightResult.value.1 rightResult.value.2)
            rightResult.context rightResult.remaining hrelation.1.2 hrelation.2
  | stoppedPrivate witness =>
      cases rightResult with
      | stopped rightReason => exact relTriple_pure_pure trivial
      | done rightResult =>
          rcases hrelation with hstored | hdoomed
          · simp only
            rw [hstored.2]
            exact relTriple_pure_stoppedPrivate_run_of_materialized_value table
              rightResult.table witness rightResult.context.state rightResult.remaining
              (rightNext rightResult.value.1 rightResult.value.2) hstored.1
          · simp only
            rw [hdoomed.1.1]
            exact relTriple_any_run_of_materializedDoomed_witness table
              (pure (.stoppedPrivate witness))
              (rightNext rightResult.value.1 rightResult.value.2)
              rightResult.context rightResult.remaining hdoomed.1.2 hdoomed.2
  | done leftResult =>
      cases rightResult with
      | stopped rightReason =>
          cases rightReason with
          | privateStructuralHit => contradiction
          | ordinaryHit =>
              exact relTriple_any_pure_nonprivateStop_witness table _ .ordinaryHit (by decide)
          | fuelExhausted =>
              exact relTriple_any_pure_nonprivateStop_witness table _ .fuelExhausted (by decide)
      | done rightResult =>
          rcases hrelation with hcleanRelation | hdoomedRelation
          · exact hclean leftResult rightResult hcleanRelation
          · simp only
            rw [hdoomedRelation.1.1]
            exact relTriple_any_run_of_materializedDoomed_witness table
              (runDirectResolvedWitnessFromTable leftResult.context leftResult.remaining
                leftResult.table (leftNext leftResult.value.1 leftResult.value.2))
              (rightNext rightResult.value.1 rightResult.value.2)
              rightResult.context rightResult.remaining hdoomedRelation.1.2 hdoomedRelation.2

theorem WitnessMaterializedStableCouples.bind
    {table : OtsSecretIndex → HashOutput}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hleft : WitnessMaterializedStableCouples table left)
    (hnext : ∀ value, WitnessMaterializedStableCouples table (next value)) :
    WitnessMaterializedStableCouples table (left >>= next) := by
  intro leftContext rightContext leftFuel rightFuel leftCache rightCache hcontext hfuel hcache
    hrevealed hvalues hpublished hrightMaterialized
  rw [StateT.run_bind, StateT.run_bind]
  apply relTriple_runDirectResolvedWitness_detailed_bind_stable table
    (left.run leftCache) (left.run rightCache)
    (fun value cache => (next value).run cache)
    (fun value cache => (next value).run cache)
    leftContext rightContext leftFuel rightFuel
  · exact hleft leftContext rightContext leftFuel rightFuel leftCache rightCache hcontext hfuel
      hcache hrevealed hvalues hpublished hrightMaterialized
  · intro leftResult rightResult hrelation
    rw [hrelation.left_table, hrelation.right_table, ← hrelation.value_eq]
    exact hnext leftResult.value.1 leftResult.context rightResult.context
      leftResult.remaining rightResult.remaining leftResult.value.2 rightResult.value.2
      hrelation.context_le hrelation.remaining_le hrelation.cache_eq hrelation.revealed_eq
      hrelation.values_le hrelation.left_published hrelation.right_materialized

theorem witnessMaterializedStableCouples_ensureCoordinate
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) :
    WitnessMaterializedStableCouples table (ensureCoordinate coordinate) := by
  intro left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache hrevealed
    hvalues hpublished hrightMaterialized
  unfold ensureCoordinate
  rw [StateT.run_liftM, StateT.run_liftM, LazyRevealProbe.ensureQuery,
    runDirectResolvedWitnessFromTable_ensure_query_bind,
    runDirectResolvedDetailedFromTable_ensure_query_bind,
    runDirectResolvedDetailedFromTable_pure]
  simp only [runDirectResolvedWitnessFromTable]
  apply relTriple_pure_pure
  left
  exact
    { value_eq := rfl
      context_le := hcontext.ensure coordinate
      remaining_le := hfuel
      left_table := rfl
      right_table := rfl
      cache_eq := hcache
      revealed_eq := by
        simpa [LazyRevealProbe.State.ensure] using hrevealed
      values_le := by
        intro other output hvalue
        exact hvalues other output hvalue
      left_published := by
        simpa [PublishedValues, LazyRevealProbe.State.ensure] using hpublished
      right_materialized := by
        rw [hrightMaterialized]
        simp [directDeferredContext, directDeferredValues_ensure] }

theorem witnessMaterializedStableCouples_sequenceFin
    {table : OtsSecretIndex → HashOutput} {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcomponent : ∀ index,
      WitnessMaterializedStableCouples table (computation index)) :
    WitnessMaterializedStableCouples table (sequenceFin computation) := by
  induction n with
  | zero =>
      simpa [sequenceFin] using
        (witnessMaterializedStableCouples_pure table Fin.elim0 :
          WitnessMaterializedStableCouples table
            (pure Fin.elim0 : StateT SplitHashCache
              (OracleComp (LazyRevealProbe.World Coordinate)) (Fin 0 → α)))
  | succ n ih =>
      rw [sequenceFin]
      apply (hcomponent 0).bind
      intro head
      apply (ih (fun index : Fin n => computation index.succ)
        (fun index => hcomponent index.succ)).bind
      intro tail
      exact witnessMaterializedStableCouples_pure table
        (Fin.cases head tail : Fin (n + 1) → α)

set_option maxRecDepth 100000 in
theorem witnessMaterializedStableCouples_splitHashQuery_ordinary
    (table : OtsSecretIndex → HashOutput) (input : HashInput) :
    WitnessMaterializedStableCouples table
      (splitHashQuery (.ordinary input)) := by
  intro left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache hrevealed
    hvalues hpublished hrightMaterialized
  rw [splitHashQuery_run_eq, splitHashQuery_run_eq]
  have hcacheAt : leftCache (.ordinary input) = rightCache (.ordinary input) :=
    congrFun hcache input
  cases hlookup : leftCache (.ordinary input) with
  | some output =>
      have hright : rightCache (.ordinary input) = some output := by
        rw [← hcacheAt]
        exact hlookup
      simp only [hright]
      exact witnessMaterializedStableCouples_pure table output left right leftFuel rightFuel
        leftCache rightCache hcontext hfuel hcache hrevealed hvalues hpublished
          hrightMaterialized
  | none =>
      have hright : rightCache (.ordinary input) = none := by
        rw [← hcacheAt]
        exact hlookup
      simp only [hright]
      rw [LazyRevealProbe.hashOutputQuery,
        runDirectResolvedWitnessFromTable_hashOutput_query_bind,
        runDirectResolvedDetailedFromTable_hashOutput_query_bind]
      apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
      intro leftOutput rightOutput houtput
      subst rightOutput
      simp only [runDirectResolvedWitnessFromTable,
        runDirectResolvedDetailedFromTable]
      apply relTriple_pure_pure
      left
      exact
        { value_eq := rfl
          context_le := hcontext
          remaining_le := hfuel
          left_table := rfl
          right_table := rfl
          cache_eq := by
            rw [ordinaryQueryCache_update, ordinaryQueryCache_update, hcache]
          revealed_eq := hrevealed
          values_le := hvalues
          left_published := hpublished
          right_materialized := hrightMaterialized }

theorem witnessMaterializedStableCouples_ordinaryHashImpl
    (table : OtsSecretIndex → HashOutput) (input : HashInput) :
    WitnessMaterializedStableCouples table (ordinaryHashImpl input) :=
  witnessMaterializedStableCouples_splitHashQuery_ordinary table input

theorem witnessMaterializedStableCouples_splitUniformImpl
    (table : OtsSecretIndex → HashOutput) (n : unifSpec.Domain) :
    WitnessMaterializedStableCouples table (splitUniformImpl n) := by
  intro left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache hrevealed
    hvalues hpublished hrightMaterialized
  unfold splitUniformImpl
  rw [StateT.run_liftM, StateT.run_liftM, LazyRevealProbe.uniformQuery,
    runDirectResolvedWitnessFromTable_uniform_query_bind,
    runDirectResolvedDetailedFromTable_uniform_query_bind]
  apply relTriple_bind (relTriple_refl
    (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
  intro leftOutput rightOutput houtput
  subst rightOutput
  exact witnessMaterializedStableCouples_pure table leftOutput left right leftFuel rightFuel
    leftCache rightCache hcontext hfuel hcache hrevealed hvalues hpublished
      hrightMaterialized

theorem witnessMaterializedStableCouples_simulateQ
    {table : OtsSecretIndex → HashOutput} {spec : OracleSpec ι}
    (impl : QueryImpl spec
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))))
    (hquery : ∀ query, WitnessMaterializedStableCouples table (impl query))
    (computation : OracleComp spec α) :
    WitnessMaterializedStableCouples table (simulateQ impl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure]
      exact witnessMaterializedStableCouples_pure table value
  | query_bind query next ih =>
      rw [simulateQ_query_bind]
      exact (hquery query).bind fun output => ih output

theorem runDirectResolvedWitnessFromTable_revealCoordinateOutput_of_value
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (output : HashOutput)
    (hvalue : context.state.values coordinate = some output) :
    runDirectResolvedWitnessFromTable context fuel table
        ((revealCoordinateOutput coordinate).run cache) =
      pure (.done ⟨context, fuel,
        (output, Function.update cache (.hidden coordinate) (some output)), table⟩) := by
  unfold revealCoordinateOutput
  rw [StateT.run_bind, runDirectResolvedWitnessFromTable_bind]
  simp only [StateT.run_liftM]
  rw [LazyRevealProbe.revealQuery,
    runDirectResolvedWitnessFromTable_reveal_query_bind, hvalue]
  simp [StateT.run_modify, runDirectResolvedWitnessFromTable]

theorem runDirectResolvedWitnessFromTable_revealCoordinateOutput_position_of_private
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (output : HashOutput)
    (hhidden : context.state.values (.position position) = none)
    (hprivate : context.values position = some output) :
    runDirectResolvedWitnessFromTable context fuel table
        ((revealCoordinateOutput (.position position)).run cache) =
      if context.state.hitAt (.position position) output then
        pure (.stoppedPrivate ⟨position, output, context.state.revealed⟩)
      else
        pure (.done ⟨
          { state := context.state.materialize (.position position) output
            values := context.values },
          fuel,
          (output, Function.update cache (.hidden (.position position)) (some output)),
          table⟩) := by
  unfold revealCoordinateOutput
  rw [StateT.run_bind, runDirectResolvedWitnessFromTable_bind]
  simp only [StateT.run_liftM]
  rw [LazyRevealProbe.revealQuery,
    runDirectResolvedWitnessFromTable_reveal_query_bind]
  by_cases hhit : context.state.hitAt (.position position) output <;>
    simp [hhidden, hprivate, hhit, StateT.run_modify,
      runDirectResolvedWitnessFromTable]

theorem runDirectResolvedWitnessFromTable_revealCoordinateOutput_position_of_fresh
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hhidden : context.state.values (.position position) = none)
    (hprivate : context.values position = none) :
    runDirectResolvedWitnessFromTable context fuel table
        ((revealCoordinateOutput (.position position)).run cache) = (do
      let output ← LazyRevealProbe.sampleHashOutput
      if context.state.hitAt (.position position) output then
        pure .stoppedOrdinary
      else
        pure (.done ⟨
          { state := context.state.materialize (.position position) output
            values := context.values.install position output },
          fuel,
          (output, Function.update cache (.hidden (.position position)) (some output)),
          table⟩)) := by
  unfold revealCoordinateOutput
  rw [StateT.run_bind, runDirectResolvedWitnessFromTable_bind]
  simp only [StateT.run_liftM]
  rw [LazyRevealProbe.revealQuery,
    runDirectResolvedWitnessFromTable_reveal_query_bind]
  simp [hhidden, hprivate, StateT.run_modify, runDirectResolvedWitnessFromTable]
  apply bind_congr
  intro output
  by_cases hhit : context.state.hitAt (.position position) output <;> simp [hhit]

set_option maxRecDepth 100000 in
theorem witnessMaterializedStableCouples_revealCoordinateOutput_position
    (table : OtsSecretIndex → HashOutput) (position : Position) :
    WitnessMaterializedStableCouples table
      (revealCoordinateOutput (.position position)) := by
  intro left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache hrevealed
    hvalues hpublished hrightMaterialized
  cases hleftValue : left.state.values (.position position) with
  | some output =>
      have hrightValue : right.state.values (.position position) = some output :=
        hvalues (.position position) output hleftValue
      rw [runDirectResolvedWitnessFromTable_revealCoordinateOutput_of_value table
          (.position position) left leftFuel leftCache output hleftValue,
        runDirectResolvedDetailedFromTable_revealCoordinateOutput_of_value table
          (.position position) right rightFuel rightCache output hrightValue]
      apply relTriple_pure_pure
      left
      exact
        { value_eq := rfl
          context_le := hcontext
          remaining_le := hfuel
          left_table := rfl
          right_table := rfl
          cache_eq := by
            rw [ordinaryQueryCache_update_hidden, ordinaryQueryCache_update_hidden, hcache]
          revealed_eq := hrevealed
          values_le := hvalues
          left_published := hpublished
          right_materialized := hrightMaterialized }
  | none =>
      cases hrightValue : right.state.values (.position position) with
      | some output =>
          have hprivate := hcontext.view.privateValue_of_left_hidden_of_right_materialized
            position output hleftValue hrightValue
          rw [runDirectResolvedWitnessFromTable_revealCoordinateOutput_position_of_private
              table position left leftFuel leftCache output hleftValue hprivate,
            runDirectResolvedDetailedFromTable_revealCoordinateOutput_of_value table
              (.position position) right rightFuel rightCache output hrightValue]
          by_cases hhit : left.state.hitAt (.position position) output
          · simp only [hhit, ↓reduceIte]
            apply relTriple_pure_pure
            left
            exact ⟨hrightValue, hrightMaterialized⟩
          · simp only [hhit, ↓reduceIte]
            apply relTriple_pure_pure
            left
            exact
              { value_eq := rfl
                context_le := hcontext.materialize_position_left position output
                  hleftValue hprivate
                remaining_le := hfuel
                left_table := rfl
                right_table := rfl
                cache_eq := by
                  rw [ordinaryQueryCache_update_hidden, ordinaryQueryCache_update_hidden, hcache]
                revealed_eq := by
                  simpa [LazyRevealProbe.State.materialize] using hrevealed
                values_le := hvalues.materialize_left (.position position) output hrightValue
                left_published := hpublished.materialize (.position position) output
                right_materialized := hrightMaterialized }
      | none =>
          have hrightPrivate : right.values position = none := by
            rw [hrightMaterialized]
            simpa [directDeferredContext, directDeferredValues] using hrightValue
          have hleftPositionValue : left.positionValue position = none := by
            change resolvedCompletionValue table left (.position position) = none
            rw [hcontext.view.valueEq]
            simp [resolvedCompletionValue, DeferredContext.positionValue, hrightValue,
              hrightPrivate]
          have hleftPrivate : left.values position = none := by
            simpa [DeferredContext.positionValue, hleftValue] using hleftPositionValue
          rw [runDirectResolvedWitnessFromTable_revealCoordinateOutput_position_of_fresh
              table position left leftFuel leftCache hleftValue hleftPrivate,
            runDirectResolvedDetailedFromTable_revealCoordinateOutput_position_of_fresh
              table position right rightFuel rightCache hrightValue hrightPrivate]
          apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
          intro leftOutput rightOutput houtput
          subst rightOutput
          by_cases hleftHit : left.state.hitAt (.position position) leftOutput
          · have hresolvedNone :
                resolvedCompletionValue table left (.position position) = none := by
              simpa [resolvedCompletionValue] using hleftPositionValue
            have hrightHit : right.state.hitAt (.position position) leftOutput := by
              unfold LazyRevealProbe.State.hitAt at hleftHit ⊢
              exact hcontext.view.pendingLE (.position position) hresolvedNone hleftHit
            simp only [hleftHit, hrightHit, ↓reduceIte]
            exact relTriple_pure_pure trivial
          · by_cases hrightHit : right.state.hitAt (.position position) leftOutput
            · simp only [hleftHit, hrightHit, ↓reduceIte]
              exact relTriple_pure_pure trivial
            · simp only [hleftHit, hrightHit, ↓reduceIte]
              apply relTriple_pure_pure
              left
              exact
                { value_eq := rfl
                  context_le := hcontext.materialize_position_both position leftOutput
                  remaining_le := hfuel
                  left_table := rfl
                  right_table := rfl
                  cache_eq := by
                    rw [ordinaryQueryCache_update_hidden, ordinaryQueryCache_update_hidden,
                      hcache]
                  revealed_eq := by
                    simpa [LazyRevealProbe.State.materialize] using hrevealed
                  values_le := hvalues.materialize_both (.position position) leftOutput
                  left_published := hpublished.materialize (.position position) leftOutput
                  right_materialized := by
                    rw [hrightMaterialized]
                    simp [directDeferredContext, directDeferredValues_materialize_position] }

theorem witnessMaterializedStableCouples_revealPosition
    (table : OtsSecretIndex → HashOutput) (position : Position) :
    WitnessMaterializedStableCouples table (revealPosition position) := by
  unfold revealPosition revealCoordinate
  exact (witnessMaterializedStableCouples_revealCoordinateOutput_position table position).bind
    fun output => witnessMaterializedStableCouples_pure table (truncateHash output)

theorem runDirectResolvedWitnessFromTable_revealCoordinateOutput_chainStart_of_missing
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hmissing : context.state.values index.coordinate = none) :
    runDirectResolvedWitnessFromTable context fuel table
        ((revealCoordinateOutput index.coordinate).run cache) =
      if context.state.hitAt index.coordinate (table index) then
        pure .stoppedOrdinary
      else
        pure (.done ⟨
          { context with
            state := context.state.materialize index.coordinate (table index) },
          fuel,
          (table index, Function.update cache (.hidden index.coordinate) (some (table index))),
          table⟩) := by
  rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
  change context.state.values (.chainStart lay tree leafIdx chainIdx) = none at hmissing
  unfold revealCoordinateOutput
  rw [StateT.run_bind, runDirectResolvedWitnessFromTable_bind]
  simp only [StateT.run_liftM]
  rw [LazyRevealProbe.revealQuery,
    runDirectResolvedWitnessFromTable_reveal_query_bind]
  by_cases hhit : context.state.hitAt
      (.chainStart lay tree leafIdx chainIdx) (table ⟨lay, tree, leafIdx, chainIdx⟩) <;>
    simp [OtsSecretIndex.coordinate, hmissing, hhit, StateT.run_modify,
      runDirectResolvedWitnessFromTable]

set_option maxRecDepth 100000 in
theorem witnessMaterializedStableCouples_revealCoordinateOutput_chainStart
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex) :
    WitnessMaterializedStableCouples table
      (revealCoordinateOutput index.coordinate) := by
  intro left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache hrevealed
    hvalues hpublished hrightMaterialized
  cases hleftValue : left.state.values index.coordinate with
  | some output =>
      have hrightValue : right.state.values index.coordinate = some output :=
        hvalues index.coordinate output hleftValue
      rw [runDirectResolvedWitnessFromTable_revealCoordinateOutput_of_value table
          index.coordinate left leftFuel leftCache output hleftValue,
        runDirectResolvedDetailedFromTable_revealCoordinateOutput_of_value table
          index.coordinate right rightFuel rightCache output hrightValue]
      apply relTriple_pure_pure
      left
      exact
        { value_eq := rfl
          context_le := hcontext
          remaining_le := hfuel
          left_table := rfl
          right_table := rfl
          cache_eq := by
            rw [ordinaryQueryCache_update_hidden, ordinaryQueryCache_update_hidden, hcache]
          revealed_eq := hrevealed
          values_le := hvalues
          left_published := hpublished
          right_materialized := hrightMaterialized }
  | none =>
      have hleftMiss : ¬left.state.hitAt index.coordinate (table index) :=
        hcontext.leftCompletable.not_hitAt_chainStart index
      rw [runDirectResolvedWitnessFromTable_revealCoordinateOutput_chainStart_of_missing
        table index left leftFuel leftCache hleftValue, if_neg hleftMiss]
      cases hrightValue : right.state.values index.coordinate with
      | some output =>
          have houtput : output = table index :=
            hcontext.view.rightStarts index output hrightValue
          subst output
          rw [runDirectResolvedDetailedFromTable_revealCoordinateOutput_of_value table
            index.coordinate right rightFuel rightCache (table index) hrightValue]
          apply relTriple_pure_pure
          left
          exact
            { value_eq := rfl
              context_le := hcontext.materialize_chainStart_left index
              remaining_le := hfuel
              left_table := rfl
              right_table := rfl
              cache_eq := by
                rw [ordinaryQueryCache_update_hidden, ordinaryQueryCache_update_hidden, hcache]
              revealed_eq := by
                simpa [LazyRevealProbe.State.materialize] using hrevealed
              values_le := hvalues.materialize_left index.coordinate (table index) hrightValue
              left_published := hpublished.materialize index.coordinate (table index)
              right_materialized := hrightMaterialized }
      | none =>
          have hrightMiss : ¬right.state.hitAt index.coordinate (table index) :=
            hcontext.rightCompletable.not_hitAt_chainStart index
          rw [runDirectResolvedDetailedFromTable_revealCoordinateOutput_chainStart_of_missing
            table index right rightFuel rightCache hrightValue, if_neg hrightMiss]
          apply relTriple_pure_pure
          left
          exact
            { value_eq := rfl
              context_le := hcontext.materialize_chainStart_both index
              remaining_le := hfuel
              left_table := rfl
              right_table := rfl
              cache_eq := by
                rw [ordinaryQueryCache_update_hidden, ordinaryQueryCache_update_hidden, hcache]
              revealed_eq := by
                simpa [LazyRevealProbe.State.materialize] using hrevealed
              values_le := hvalues.materialize_both index.coordinate (table index)
              left_published := hpublished.materialize index.coordinate (table index)
              right_materialized := by
                rw [hrightMaterialized]
                simp [directDeferredContext, directDeferredValues_materialize_chainStart] }

theorem witnessMaterializedStableCouples_revealCoordinate
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) :
    WitnessMaterializedStableCouples table (revealCoordinate coordinate) := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      unfold revealCoordinate
      exact (witnessMaterializedStableCouples_revealCoordinateOutput_chainStart table
        ⟨lay, tree, leafIdx, chainIdx⟩).bind fun output =>
          witnessMaterializedStableCouples_pure table (truncateHash output)
  | position position =>
      exact witnessMaterializedStableCouples_revealPosition table position

theorem witnessMaterializedStableCouples_revealCoordinateOutput
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) :
    WitnessMaterializedStableCouples table (revealCoordinateOutput coordinate) := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      exact witnessMaterializedStableCouples_revealCoordinateOutput_chainStart table
        ⟨lay, tree, leafIdx, chainIdx⟩
  | position position =>
      exact witnessMaterializedStableCouples_revealCoordinateOutput_position table position

theorem witnessMaterializedStableCouples_ordinaryRomImpl
    (table : OtsSecretIndex → HashOutput) (query : OracleWorld.Domain) :
    WitnessMaterializedStableCouples table (ordinaryRomImpl query) := by
  cases query with
  | inl n => exact witnessMaterializedStableCouples_splitUniformImpl table n
  | inr input => exact witnessMaterializedStableCouples_ordinaryHashImpl table input

end SphincsSecurity.Concrete.OtsProbeSimulation
