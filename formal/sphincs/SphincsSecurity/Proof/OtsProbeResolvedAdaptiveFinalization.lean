import SphincsSecurity.Proof.OtsProbeResolvedSignerFinalization

/-!
# Finalization equivalence through adaptive execution

The chronological and delayed signers leave different coordinates materialized. This file tracks
their common clean completion semantics through the adaptive random-oracle handler, while treating
a context with no clean completion as terminally doomed.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def FinalizationDoomedRun (table : OtsSecretIndex → HashOutput) :
    Option (ResolvedRunResult α) → Prop
  | none => True
  | some result =>
      result.table = table ∧ DoomedResolvedContext table result.context

def FinalizationAdaptiveRunEq (table : OtsSecretIndex → HashOutput) :
    Option (ResolvedRunResult (α × SplitHashCache)) →
      Option (ResolvedRunResult (α × SplitHashCache)) → Prop :=
  fun left right =>
    FinalizationMaterializedRunEq table left right ∨
      (FinalizationDoomedRun table left ∧ FinalizationDoomedRun table right)

def MaterializedValuesEq :
    Option (ResolvedRunResult (α × SplitHashCache)) →
      Option (ResolvedRunResult (α × SplitHashCache)) → Prop
  | none, none => True
  | some left, some right => left.context.state.values = right.context.state.values
  | _, _ => False

def FinalizationSynchronizedRunEq (table : OtsSecretIndex → HashOutput) :
    Option (ResolvedRunResult (α × SplitHashCache)) →
      Option (ResolvedRunResult (α × SplitHashCache)) → Prop :=
  fun left right =>
    (FinalizationMaterializedRunEq table left right ∧ MaterializedValuesEq left right) ∨
      (FinalizationDoomedRun table left ∧ FinalizationDoomedRun table right)

def FinalizationSynchronizedCouples (table : OtsSecretIndex → HashOutput)
    (left right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ leftContext rightContext fuel leftCache rightCache,
    FinalizationContextEq table (some leftContext) (some rightContext) →
    leftContext.state.values = rightContext.state.values →
    ordinaryQueryCache leftCache = ordinaryQueryCache rightCache →
    leftContext.state.revealed = rightContext.state.revealed →
    RelTriple
      (runResolvedFromTable leftContext fuel table (left.run leftCache))
      (runResolvedFromTable rightContext fuel table (right.run rightCache))
      (FinalizationSynchronizedRunEq table)

theorem FinalizationAdaptiveRunEq.symm
    {table : OtsSecretIndex → HashOutput}
    {left right : Option (ResolvedRunResult (α × SplitHashCache))}
    (hrelation : FinalizationAdaptiveRunEq table left right) :
    FinalizationAdaptiveRunEq table right left := by
  rcases hrelation with hclean | hdoomed
  · left
    cases left with
    | none =>
        cases right with
        | none => trivial
        | some right => simp [FinalizationMaterializedRunEq] at hclean
    | some left =>
        cases right with
        | none => simp [FinalizationMaterializedRunEq] at hclean
        | some right =>
            rcases hclean with
              ⟨hvalue, hcontext, hfuel, hleftTable, hrightTable, hcache, hrevealed⟩
            rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
            have hrightCompletable : DeferredCompletable table right.context := by
              rcases hleftCompletable with ⟨completion, hcompletion⟩
              exact ⟨completion, (hview.deferredCompletion_iff completion).mp hcompletion⟩
            exact ⟨hvalue.symm,
              ⟨hview.symm, hrightValid, hleftValid, hrightCompletable⟩,
              hfuel.symm, hrightTable, hleftTable, hcache.symm, hrevealed.symm⟩
  · exact Or.inr ⟨hdoomed.2, hdoomed.1⟩

def FinalizationAdaptiveCouples (table : OtsSecretIndex → HashOutput)
    (left right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ leftContext rightContext fuel leftCache rightCache,
    FinalizationContextEq table (some leftContext) (some rightContext) →
    ordinaryQueryCache leftCache = ordinaryQueryCache rightCache →
    leftContext.state.revealed = rightContext.state.revealed →
    RelTriple
      (runResolvedFromTable leftContext fuel table (left.run leftCache))
      (runResolvedFromTable rightContext fuel table (right.run rightCache))
      (FinalizationAdaptiveRunEq table)

theorem finalizationDoomedRun_of_mem_runResolvedFromTable
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (result : ResolvedRunResult α)
    (hdoomed : DoomedResolvedContext table context)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table computation)) :
    FinalizationDoomedRun table (some result) := by
  have hcore := resolvedCore_of_mem_runResolvedFromTable computation context fuel table result
    hdoomed.1 hdoomed.2.1 hresult
  exact ⟨hcore.1, hcore.2.1, hcore.2.2,
    not_deferredCompletable_of_mem_runResolvedFromTable computation context fuel table result
      hdoomed.1 hdoomed.2.1 hresult hdoomed.2.2⟩

theorem relTriple_runResolvedFromTable_of_finalizationDoomed
    (table : OtsSecretIndex → HashOutput)
    (leftComputation : OracleComp (LazyRevealProbe.World Coordinate) (α × SplitHashCache))
    (rightComputation : OracleComp (LazyRevealProbe.World Coordinate) (α × SplitHashCache))
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (hleftDoomed : DoomedResolvedContext table left)
    (hrightDoomed : DoomedResolvedContext table right) :
    RelTriple
      (runResolvedFromTable left leftFuel table leftComputation)
      (runResolvedFromTable right rightFuel table rightComputation)
      (FinalizationAdaptiveRunEq table) := by
  have hbase := relTriple_true
    (runResolvedFromTable left leftFuel table leftComputation)
    (runResolvedFromTable right rightFuel table rightComputation)
  have hleft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun result => result ∈ support
        (runResolvedFromTable left leftFuel table leftComputation))
      (fun result hresult => hresult)
  have hboth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
  apply relTriple_post_mono hboth
  intro leftResult rightResult hrelation
  right
  constructor
  · cases leftResult with
    | none => trivial
    | some result =>
        exact finalizationDoomedRun_of_mem_runResolvedFromTable table leftComputation left leftFuel
          result hleftDoomed hrelation.1.2
  · cases rightResult with
    | none => trivial
    | some result =>
        exact finalizationDoomedRun_of_mem_runResolvedFromTable table rightComputation right rightFuel
          result hrightDoomed hrelation.2

theorem relTriple_pure_none_runResolvedFromTable_of_finalizationDoomed
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) (α × SplitHashCache))
    (context : DeferredContext) (fuel : Nat)
    (hdoomed : DoomedResolvedContext table context) :
    RelTriple
      (pure none : ProbComp
        (Option (ResolvedRunResult (α × SplitHashCache))))
      (runResolvedFromTable context fuel table computation)
      (FinalizationAdaptiveRunEq table) := by
  have hbase := relTriple_true
    (pure none : ProbComp (Option (ResolvedRunResult (α × SplitHashCache))))
    (runResolvedFromTable context fuel table computation)
  have hleft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun result => result ∈ support
        (pure none : ProbComp (Option (ResolvedRunResult (α × SplitHashCache)))))
      (fun result hresult => hresult)
  have hboth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
  apply relTriple_post_mono hboth
  intro leftResult rightResult hrelation
  have hleftResult : leftResult = none := by simpa using hrelation.1.2
  subst leftResult
  right
  refine ⟨trivial, ?_⟩
  cases rightResult with
  | none => trivial
  | some result =>
      exact finalizationDoomedRun_of_mem_runResolvedFromTable table computation context fuel
        result hdoomed hrelation.2

theorem relTriple_runResolvedFromTable_pure_none_of_finalizationDoomed
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) (α × SplitHashCache))
    (context : DeferredContext) (fuel : Nat)
    (hdoomed : DoomedResolvedContext table context) :
    RelTriple
      (runResolvedFromTable context fuel table computation)
      (pure none : ProbComp
        (Option (ResolvedRunResult (α × SplitHashCache))))
      (FinalizationAdaptiveRunEq table) := by
  apply relTriple_post_mono
    (relTriple_symm
      (relTriple_pure_none_runResolvedFromTable_of_finalizationDoomed table computation context
        fuel hdoomed))
  intro leftResult rightResult hrelation
  exact hrelation.symm

theorem relTriple_runResolvedFromTable_of_finalizationDoomed_synchronized
    (table : OtsSecretIndex → HashOutput)
    (leftComputation : OracleComp (LazyRevealProbe.World Coordinate) (α × SplitHashCache))
    (rightComputation : OracleComp (LazyRevealProbe.World Coordinate) (α × SplitHashCache))
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (hleftDoomed : DoomedResolvedContext table left)
    (hrightDoomed : DoomedResolvedContext table right) :
    RelTriple
      (runResolvedFromTable left leftFuel table leftComputation)
      (runResolvedFromTable right rightFuel table rightComputation)
      (FinalizationSynchronizedRunEq table) := by
  have hbase := relTriple_true
    (runResolvedFromTable left leftFuel table leftComputation)
    (runResolvedFromTable right rightFuel table rightComputation)
  have hleft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun result => result ∈ support
        (runResolvedFromTable left leftFuel table leftComputation))
      (fun result hresult => hresult)
  have hboth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
  apply relTriple_post_mono hboth
  intro leftResult rightResult hrelation
  right
  constructor
  · cases leftResult with
    | none => trivial
    | some result =>
        exact finalizationDoomedRun_of_mem_runResolvedFromTable table leftComputation left
          leftFuel result hleftDoomed hrelation.1.2
  · cases rightResult with
    | none => trivial
    | some result =>
        exact finalizationDoomedRun_of_mem_runResolvedFromTable table rightComputation right
          rightFuel result hrightDoomed hrelation.2

theorem relTriple_pure_none_runResolvedFromTable_of_finalizationDoomed_synchronized
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) (α × SplitHashCache))
    (context : DeferredContext) (fuel : Nat)
    (hdoomed : DoomedResolvedContext table context) :
    RelTriple
      (pure none : ProbComp
        (Option (ResolvedRunResult (α × SplitHashCache))))
      (runResolvedFromTable context fuel table computation)
      (FinalizationSynchronizedRunEq table) := by
  have hbase := relTriple_true
    (pure none : ProbComp (Option (ResolvedRunResult (α × SplitHashCache))))
    (runResolvedFromTable context fuel table computation)
  have hleft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun result => result ∈ support
        (pure none : ProbComp (Option (ResolvedRunResult (α × SplitHashCache)))))
      (fun result hresult => hresult)
  have hboth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
  apply relTriple_post_mono hboth
  intro leftResult rightResult hrelation
  have hleftResult : leftResult = none := by simpa using hrelation.1.2
  subst leftResult
  right
  refine ⟨trivial, ?_⟩
  cases rightResult with
  | none => trivial
  | some result =>
      exact finalizationDoomedRun_of_mem_runResolvedFromTable table computation context fuel
        result hdoomed hrelation.2

theorem relTriple_runResolvedFromTable_pure_none_of_finalizationDoomed_synchronized
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) (α × SplitHashCache))
    (context : DeferredContext) (fuel : Nat)
    (hdoomed : DoomedResolvedContext table context) :
    RelTriple
      (runResolvedFromTable context fuel table computation)
      (pure none : ProbComp
        (Option (ResolvedRunResult (α × SplitHashCache))))
      (FinalizationSynchronizedRunEq table) := by
  apply relTriple_post_mono
    (relTriple_symm
      (relTriple_pure_none_runResolvedFromTable_of_finalizationDoomed_synchronized table
        computation context fuel hdoomed))
  intro leftResult rightResult hrelation
  rcases hrelation with hclean | hdoomed
  · cases leftResult with
    | none =>
        cases rightResult with
        | none => exact Or.inl ⟨trivial, trivial⟩
        | some rightResult => simp [FinalizationMaterializedRunEq] at hclean
    | some leftResult =>
        cases rightResult with
        | none => simp [FinalizationMaterializedRunEq] at hclean
        | some rightResult =>
            rcases hclean.1 with
              ⟨hvalue, hcontext, hfuel, hleftTable, hrightTable, hcache, hrevealed⟩
            rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
            have hleftCompletable' : DeferredCompletable table leftResult.context := by
              rcases hleftCompletable with ⟨completion, hcompletion⟩
              exact ⟨completion, (hview.deferredCompletion_iff completion).mp hcompletion⟩
            left
            exact ⟨⟨hvalue.symm,
              ⟨hview.symm, hrightValid, hleftValid, hleftCompletable'⟩,
              hfuel.symm, hrightTable, hleftTable, hcache.symm, hrevealed.symm⟩,
              hclean.2.symm⟩
  · exact Or.inr ⟨hdoomed.2, hdoomed.1⟩

theorem FinalizationMaterializedCouples.toAdaptive
    {table : OtsSecretIndex → HashOutput}
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    (hcomputation : FinalizationMaterializedCouples table computation) :
    FinalizationAdaptiveCouples table computation computation := by
  intro left right fuel leftCache rightCache hcontext hcache hrevealed
  apply relTriple_post_mono
    (hcomputation left right fuel leftCache rightCache hcontext hcache hrevealed)
  intro leftResult rightResult hrelation
  exact Or.inl hrelation

theorem FinalizationSynchronizedRunEq.toAdaptive
    {table : OtsSecretIndex → HashOutput}
    {left right : Option (ResolvedRunResult (α × SplitHashCache))}
    (hrelation : FinalizationSynchronizedRunEq table left right) :
    FinalizationAdaptiveRunEq table left right := by
  rcases hrelation with hclean | hdoomed
  · exact Or.inl hclean.1
  · exact Or.inr hdoomed

theorem finalizationSynchronizedCouples_pure
    (table : OtsSecretIndex → HashOutput) (value : α) :
    FinalizationSynchronizedCouples table
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) α)
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) α) := by
  intro left right fuel leftCache rightCache hcontext hvalues hcache hrevealed
  simp [StateT.run_pure, runResolvedFromTable, FinalizationSynchronizedRunEq,
    FinalizationMaterializedRunEq, MaterializedValuesEq, hcontext, hvalues, hcache, hrevealed]

theorem finalizationSynchronizedCouples_peekCoordinate
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) :
    FinalizationSynchronizedCouples table (peekCoordinate coordinate)
      (peekCoordinate coordinate) := by
  intro left right fuel leftCache rightCache hcontext hvalues hcache hrevealed
  cases hleftValue : left.state.values coordinate with
  | none =>
      have hrightValue : right.state.values coordinate = none := by
        rw [← hvalues]
        exact hleftValue
      rw [runResolvedFromTable_peekCoordinate_of_none left fuel table leftCache coordinate
          hleftValue,
        runResolvedFromTable_peekCoordinate_of_none right fuel table rightCache coordinate
          hrightValue]
      apply relTriple_pure_pure
      left
      exact ⟨⟨rfl, hcontext, rfl, rfl, rfl, hcache, hrevealed⟩, hvalues⟩
  | some output =>
      have hrightValue : right.state.values coordinate = some output := by
        rw [← hvalues]
        exact hleftValue
      rw [runResolvedFromTable_peekCoordinate_of_value left fuel table leftCache coordinate output
          hleftValue,
        runResolvedFromTable_peekCoordinate_of_value right fuel table rightCache coordinate output
          hrightValue]
      apply relTriple_pure_pure
      left
      exact ⟨⟨rfl, hcontext, rfl, rfl, rfl, hcache, hrevealed⟩, hvalues⟩

theorem finalizationSynchronizedCouples_ensureCoordinate
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) :
    FinalizationSynchronizedCouples table (ensureCoordinate coordinate)
      (ensureCoordinate coordinate) := by
  intro left right fuel leftCache rightCache hcontext hvalues hcache hrevealed
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  unfold ensureCoordinate
  simp only [StateT.run_liftM, LazyRevealProbe.ensureQuery, runResolvedFromTable]
  apply relTriple_pure_pure
  left
  exact ⟨⟨rfl,
    ⟨hview.ensure coordinate, hleftValid.ensure coordinate,
      hrightValid.ensure coordinate, hleftCompletable.ensure coordinate⟩,
    rfl, rfl, rfl, hcache, hrevealed⟩, hvalues⟩

theorem finalizationSynchronizedCouples_publishCoordinate
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) :
    FinalizationSynchronizedCouples table (publishCoordinate coordinate)
      (publishCoordinate coordinate) := by
  intro left right fuel leftCache rightCache hcontext hvalues hcache hrevealed
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  unfold publishCoordinate
  rw [StateT.run_liftM, StateT.run_liftM, LazyRevealProbe.publishQuery,
    runResolvedFromTable_publish_query_bind,
    runResolvedFromTable_publish_query_bind]
  apply relTriple_pure_pure
  left
  exact ⟨⟨rfl,
    ⟨hview.publish coordinate, hleftValid.publish coordinate,
      hrightValid.publish coordinate, hleftCompletable.publish coordinate⟩,
    rfl, rfl, rfl, hcache, by
      simpa [LazyRevealProbe.State.publish] using congrArg (insert coordinate) hrevealed⟩,
    hvalues⟩

theorem finalizationSynchronizedCouples_splitHashQuery_ordinary
    (table : OtsSecretIndex → HashOutput) (input : HashInput) :
    FinalizationSynchronizedCouples table (splitHashQuery (.ordinary input))
      (splitHashQuery (.ordinary input)) := by
  intro left right fuel leftCache rightCache hcontext hvalues hcache hrevealed
  rw [splitHashQuery_run_eq, splitHashQuery_run_eq]
  have hcacheAt : leftCache (.ordinary input) = rightCache (.ordinary input) :=
    congrFun hcache input
  cases hlookup : leftCache (.ordinary input) with
  | some output =>
      have hright : rightCache (.ordinary input) = some output := by
        rw [← hcacheAt]
        exact hlookup
      simp only [hright]
      simp [runResolvedFromTable, FinalizationSynchronizedRunEq,
        FinalizationMaterializedRunEq, MaterializedValuesEq, hcontext, hvalues, hcache,
        hrevealed]
  | none =>
      have hright : rightCache (.ordinary input) = none := by
        rw [← hcacheAt]
        exact hlookup
      simp only [hright]
      rw [LazyRevealProbe.hashOutputQuery,
        runResolvedFromTable_hashOutput_query_bind,
        runResolvedFromTable_hashOutput_query_bind]
      apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
      intro leftOutput rightOutput houtput
      subst rightOutput
      simp only [runResolvedFromTable]
      apply relTriple_pure_pure
      left
      refine ⟨⟨rfl, hcontext, rfl, rfl, rfl, ?_, hrevealed⟩, hvalues⟩
      rw [ordinaryQueryCache_update, ordinaryQueryCache_update, hcache]

theorem finalizationSynchronizedCouples_ordinaryHashImpl
    (table : OtsSecretIndex → HashOutput) (input : HashInput) :
    FinalizationSynchronizedCouples table (ordinaryHashImpl input)
      (ordinaryHashImpl input) :=
  finalizationSynchronizedCouples_splitHashQuery_ordinary table input

set_option maxRecDepth 100000 in
theorem finalizationSynchronizedCouples_revealPosition
    (table : OtsSecretIndex → HashOutput) (position : Position) :
    FinalizationSynchronizedCouples table (revealPosition position)
      (revealPosition position) := by
  intro left right fuel leftCache rightCache hcontext hvalues hcache hrevealed
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  rw [runResolvedFromTable_revealPosition, runResolvedFromTable_revealPosition]
  have hresolved := relTriple_resolveDeferredReveal_of_finalizationViewEq table position left
    right hview hleftValid hrightValid hleftCompletable
  have hresolvedLeft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hresolved
      (fun result => result ∈ support (resolveDeferredReveal table position left))
      (fun result hresult => hresult)
  have hresolvedBoth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hresolvedLeft
  apply relTriple_bind hresolvedBoth
  intro leftResolved rightResolved hrelation
  rcases hrelation with ⟨⟨hrelation, hleftSupport⟩, hrightSupport⟩
  cases leftResolved with
  | none =>
      cases rightResolved with
      | none =>
          simp [FinalizationSynchronizedRunEq, FinalizationMaterializedRunEq,
            MaterializedValuesEq]
      | some rightResolved => simp [FinalizationResolutionEq] at hrelation
  | some leftResolved =>
      cases rightResolved with
      | none => simp [FinalizationResolutionEq] at hrelation
      | some rightResolved =>
          have hleftMaterializedCompletable : DeferredCompletable table
              (materializeResolvedPosition left position leftResolved) := by
            rcases hrelation.2.2.2.2 with ⟨completion, hcompletion⟩
            exact ⟨completion,
              (deferredCompletion_materializeResolvedReveal_iff position leftResolved
                hleftValid hview.leftStarts hleftSupport).mpr hcompletion⟩
          have hrightRawCompletable :
              DeferredCompletable table rightResolved.toDeferredContext := by
            rcases hrelation.2.2.2.2 with ⟨completion, hcompletion⟩
            exact ⟨completion,
              (hrelation.2.1.deferredCompletion_iff completion).mp hcompletion⟩
          have hrightMaterializedCompletable : DeferredCompletable table
              (materializeResolvedPosition right position rightResolved) := by
            rcases hrightRawCompletable with ⟨completion, hcompletion⟩
            exact ⟨completion,
              (deferredCompletion_materializeResolvedReveal_iff position rightResolved
                hrightValid hview.rightStarts hrightSupport).mpr hcompletion⟩
          have hleftMaterializedView := finalizationViewEq_materializeResolvedReveal position
            leftResolved hleftValid hview.leftStarts hleftSupport
              hleftMaterializedCompletable
          have hrightMaterializedView := finalizationViewEq_materializeResolvedReveal position
            rightResolved hrightValid hview.rightStarts hrightSupport
              hrightMaterializedCompletable
          have hleftResultValid := hleftValid.of_resolveDeferredReveal table position
            leftResolved hleftSupport
          have hrightResultValid := hrightValid.of_resolveDeferredReveal table position
            rightResolved hrightSupport
          have hleftStateValues := resolveDeferredReveal_preserves_state_values table position
            left leftResolved hleftSupport
          have hrightStateValues := resolveDeferredReveal_preserves_state_values table position
            right rightResolved hrightSupport
          have hleftResolvedValue := resolveDeferredReveal_resolves table position left
            leftResolved hleftSupport
          have hrightResolvedValue := resolveDeferredReveal_resolves table position right
            rightResolved hrightSupport
          have hleftMaterializedValid :
              (materializeResolvedPosition left position leftResolved).Valid :=
            hleftValid.materializeResolvedPosition_of position leftResolved hleftResultValid
              hleftStateValues hleftResolvedValue
          have hrightMaterializedValid :
              (materializeResolvedPosition right position rightResolved).Valid :=
            hrightValid.materializeResolvedPosition_of position rightResolved hrightResultValid
              hrightStateValues hrightResolvedValue
          apply relTriple_pure_pure
          left
          refine ⟨⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩, ?_⟩
          · simpa using congrArg truncateHash hrelation.1
          · exact ⟨hleftMaterializedView.trans
                (hrelation.2.1.trans hrightMaterializedView.symm),
              hleftMaterializedValid, hrightMaterializedValid,
              hleftMaterializedCompletable⟩
          · rw [ordinaryQueryCache_update_hidden, ordinaryQueryCache_update_hidden,
              hcache]
          · simpa [materializeResolvedPosition, LazyRevealProbe.State.materialize]
              using hrevealed
          · change Function.update left.state.values (.position position)
                (some leftResolved.output) =
              Function.update right.state.values (.position position)
                (some rightResolved.output)
            rw [hrelation.1, hvalues]

set_option maxRecDepth 100000 in
theorem finalizationSynchronizedCouples_revealPositionOutput
    (table : OtsSecretIndex → HashOutput) (position : Position) :
    FinalizationSynchronizedCouples table
      (revealCoordinateOutput (.position position))
      (revealCoordinateOutput (.position position)) := by
  intro left right fuel leftCache rightCache hcontext hvalues hcache hrevealed
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  rw [runResolvedFromTable_revealCoordinateOutput,
    runResolvedFromTable_revealCoordinateOutput]
  simp only
  have hresolved := relTriple_resolveDeferredReveal_of_finalizationViewEq table position left
    right hview hleftValid hrightValid hleftCompletable
  have hresolvedLeft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hresolved
      (fun result => result ∈ support (resolveDeferredReveal table position left))
      (fun result hresult => hresult)
  have hresolvedBoth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hresolvedLeft
  apply relTriple_bind hresolvedBoth
  intro leftResolved rightResolved hrelation
  rcases hrelation with ⟨⟨hrelation, hleftSupport⟩, hrightSupport⟩
  cases leftResolved with
  | none =>
      cases rightResolved with
      | none =>
          simp [FinalizationSynchronizedRunEq, FinalizationMaterializedRunEq,
            MaterializedValuesEq]
      | some rightResolved => simp [FinalizationResolutionEq] at hrelation
  | some leftResolved =>
      cases rightResolved with
      | none => simp [FinalizationResolutionEq] at hrelation
      | some rightResolved =>
          have hleftMaterializedCompletable : DeferredCompletable table
              (materializeResolvedPosition left position leftResolved) := by
            rcases hrelation.2.2.2.2 with ⟨completion, hcompletion⟩
            exact ⟨completion,
              (deferredCompletion_materializeResolvedReveal_iff position leftResolved
                hleftValid hview.leftStarts hleftSupport).mpr hcompletion⟩
          have hrightRawCompletable :
              DeferredCompletable table rightResolved.toDeferredContext := by
            rcases hrelation.2.2.2.2 with ⟨completion, hcompletion⟩
            exact ⟨completion,
              (hrelation.2.1.deferredCompletion_iff completion).mp hcompletion⟩
          have hrightMaterializedCompletable : DeferredCompletable table
              (materializeResolvedPosition right position rightResolved) := by
            rcases hrightRawCompletable with ⟨completion, hcompletion⟩
            exact ⟨completion,
              (deferredCompletion_materializeResolvedReveal_iff position rightResolved
                hrightValid hview.rightStarts hrightSupport).mpr hcompletion⟩
          have hleftMaterializedView := finalizationViewEq_materializeResolvedReveal position
            leftResolved hleftValid hview.leftStarts hleftSupport
              hleftMaterializedCompletable
          have hrightMaterializedView := finalizationViewEq_materializeResolvedReveal position
            rightResolved hrightValid hview.rightStarts hrightSupport
              hrightMaterializedCompletable
          have hleftResultValid := hleftValid.of_resolveDeferredReveal table position
            leftResolved hleftSupport
          have hrightResultValid := hrightValid.of_resolveDeferredReveal table position
            rightResolved hrightSupport
          have hleftStateValues := resolveDeferredReveal_preserves_state_values table position
            left leftResolved hleftSupport
          have hrightStateValues := resolveDeferredReveal_preserves_state_values table position
            right rightResolved hrightSupport
          have hleftResolvedValue := resolveDeferredReveal_resolves table position left
            leftResolved hleftSupport
          have hrightResolvedValue := resolveDeferredReveal_resolves table position right
            rightResolved hrightSupport
          have hleftMaterializedValid :
              (materializeResolvedPosition left position leftResolved).Valid :=
            hleftValid.materializeResolvedPosition_of position leftResolved hleftResultValid
              hleftStateValues hleftResolvedValue
          have hrightMaterializedValid :
              (materializeResolvedPosition right position rightResolved).Valid :=
            hrightValid.materializeResolvedPosition_of position rightResolved hrightResultValid
              hrightStateValues hrightResolvedValue
          apply relTriple_pure_pure
          left
          refine ⟨⟨hrelation.1, ?_, rfl, rfl, rfl, ?_, ?_⟩, ?_⟩
          · exact ⟨hleftMaterializedView.trans
                (hrelation.2.1.trans hrightMaterializedView.symm),
              hleftMaterializedValid, hrightMaterializedValid,
              hleftMaterializedCompletable⟩
          · rw [ordinaryQueryCache_update_hidden, ordinaryQueryCache_update_hidden,
              hcache]
          · simpa [materializeResolvedPosition, LazyRevealProbe.State.materialize]
              using hrevealed
          · change Function.update left.state.values (.position position)
                (some leftResolved.output) =
              Function.update right.state.values (.position position)
                (some rightResolved.output)
            rw [hrelation.1, hvalues]

set_option maxRecDepth 100000 in
theorem finalizationSynchronizedCouples_revealChainStart
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex) :
    FinalizationSynchronizedCouples table
      (revealChainStart index.lay index.tree index.leafIdx index.chainIdx)
      (revealChainStart index.lay index.tree index.leafIdx index.chainIdx) := by
  intro left right fuel leftCache rightCache hcontext hvalues hcache hrevealed
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  rw [revealChainStart, runResolvedFromTable_revealCoordinate,
    runResolvedFromTable_revealCoordinate]
  have hresolved := relTriple_resolveDeferredChainStart_of_finalizationViewEq table index left
    right hview hleftValid hrightValid hleftCompletable
  have hresolvedLeft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hresolved
      (fun result => result ∈ support
        (pure (resolveDeferredChainStart table index left) :
          ProbComp (Option DeferredResolution)))
      (fun result hresult => hresult)
  have hresolvedBoth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hresolvedLeft
  apply relTriple_bind hresolvedBoth
  intro leftResolved rightResolved hrelation
  rcases hrelation with ⟨⟨hrelation, hleftSupport⟩, hrightSupport⟩
  cases leftResolved with
  | none =>
      cases rightResolved with
      | none =>
          simp [FinalizationSynchronizedRunEq, FinalizationMaterializedRunEq,
            MaterializedValuesEq]
      | some rightResolved => simp [FinalizationResolutionEq] at hrelation
  | some leftResolved =>
      cases rightResolved with
      | none => simp [FinalizationResolutionEq] at hrelation
      | some rightResolved =>
          have hleftResult :
              resolveDeferredChainStart table index left = some leftResolved := by
            simpa using hleftSupport.symm
          have hrightResult :
              resolveDeferredChainStart table index right = some rightResolved := by
            simpa using hrightSupport.symm
          have hleftMaterializedCompletable :=
            hleftCompletable.materializeResolvedChainStart hview.leftStarts index leftResolved
              hleftResult
          have hrightCompletable : DeferredCompletable table right := by
            rcases hleftCompletable with ⟨completion, hcompletion⟩
            exact ⟨completion, (hview.deferredCompletion_iff completion).mp hcompletion⟩
          have hrightMaterializedCompletable :=
            hrightCompletable.materializeResolvedChainStart hview.rightStarts index
              rightResolved hrightResult
          have hleftMaterializedView :=
            finalizationViewEq_materializeResolvedChainStart index leftResolved hleftValid
              hview.leftStarts hleftResult hleftMaterializedCompletable
          have hrightMaterializedView :=
            finalizationViewEq_materializeResolvedChainStart index rightResolved hrightValid
              hview.rightStarts hrightResult hrightMaterializedCompletable
          have hleftMaterializedValid :
              (materializeResolvedChainStart left index leftResolved).Valid := by
            unfold materializeResolvedChainStart
            rw [resolveDeferredChainStart_deferred_values_eq table index left leftResolved
              hleftResult]
            rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
            exact hleftValid.materialize_chainStart lay tree leafIdx chainIdx leftResolved.output
          have hrightMaterializedValid :
              (materializeResolvedChainStart right index rightResolved).Valid := by
            unfold materializeResolvedChainStart
            rw [resolveDeferredChainStart_deferred_values_eq table index right rightResolved
              hrightResult]
            rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
            exact hrightValid.materialize_chainStart lay tree leafIdx chainIdx
              rightResolved.output
          apply relTriple_pure_pure
          left
          refine ⟨⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩, ?_⟩
          · simpa using congrArg truncateHash hrelation.1
          · exact ⟨hleftMaterializedView.trans
                (hrelation.2.1.trans hrightMaterializedView.symm),
              hleftMaterializedValid, hrightMaterializedValid,
              hleftMaterializedCompletable⟩
          · rw [ordinaryQueryCache_update_hidden, ordinaryQueryCache_update_hidden,
              hcache]
          · simpa [materializeResolvedChainStart, LazyRevealProbe.State.materialize]
              using hrevealed
          · change Function.update left.state.values index.coordinate
                (some leftResolved.output) =
              Function.update right.state.values index.coordinate
                (some rightResolved.output)
            rw [hrelation.1, hvalues]

theorem finalizationSynchronizedCouples_revealCoordinate
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) :
    FinalizationSynchronizedCouples table (revealCoordinate coordinate)
      (revealCoordinate coordinate) := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      exact finalizationSynchronizedCouples_revealChainStart table
        ⟨lay, tree, leafIdx, chainIdx⟩
  | position position =>
      exact finalizationSynchronizedCouples_revealPosition table position

theorem DeferredCompletion.addPending_of_avoids
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput} (coordinate : Coordinate)
    (candidate : Digest) (hcompletion : DeferredCompletion table context completion)
    (havoids : truncateHash (completion coordinate) ≠ candidate) :
    DeferredCompletion table
      { context with state := context.state.addPending coordinate candidate } completion := by
  refine ⟨hcompletion.1, hcompletion.2.1, ?_, hcompletion.2.2.2⟩
  intro other otherCandidate hmember
  simp only [LazyRevealProbe.State.addPending, Finset.mem_insert] at hmember
  rcases hmember with hnew | hold
  · rcases hnew with ⟨rfl, rfl⟩
    exact havoids
  · exact hcompletion.2.2.1 other otherCandidate hold

theorem FinalizationViewEq.addPending_of_completable
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewEq table left right) (coordinate : Coordinate)
    (candidate : Digest)
    (hleftCompletable : DeferredCompletable table
      { left with state := left.state.addPending coordinate candidate })
    (hrightCompletable : DeferredCompletable table
      { right with state := right.state.addPending coordinate candidate }) :
    FinalizationViewEq table
      { left with state := left.state.addPending coordinate candidate }
      { right with state := right.state.addPending coordinate candidate } := by
  refine ⟨hview.leftConsistent.addPending coordinate candidate,
    hview.rightConsistent.addPending coordinate candidate,
    hview.leftStarts.addPending coordinate candidate,
    hview.rightStarts.addPending coordinate candidate, hview.valueEq, ?_, ?_, ?_⟩
  · intro other output hvalue hhit
    obtain ⟨completion, hcompletion⟩ := hleftCompletable
    have houtput := hcompletion.eq_resolvedCompletionValue other output hvalue
    have havoids := hcompletion.2.2.1
    unfold LazyRevealProbe.State.hitAt at hhit
    rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit
    exact havoids other (truncateHash output) hhit (by rw [houtput])
  · intro other output hvalue hhit
    obtain ⟨completion, hcompletion⟩ := hrightCompletable
    have houtput := hcompletion.eq_resolvedCompletionValue other output hvalue
    have havoids := hcompletion.2.2.1
    unfold LazyRevealProbe.State.hitAt at hhit
    rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit
    exact havoids other (truncateHash output) hhit (by rw [houtput])
  · intro other hvalue
    have hvalueBase : resolvedCompletionValue table left other = none := hvalue
    ext digest
    rw [LazyRevealProbe.State.mem_pendingAt_iff,
      LazyRevealProbe.State.mem_pendingAt_iff]
    simp only [LazyRevealProbe.State.addPending, Finset.mem_insert]
    have hbase : (other, digest) ∈ left.state.pending ↔
        (other, digest) ∈ right.state.pending := by
      rw [← LazyRevealProbe.State.mem_pendingAt_iff,
        ← LazyRevealProbe.State.mem_pendingAt_iff,
        hview.pendingEq other hvalueBase]
    tauto

theorem deferredCompletable_addPending_iff_of_finalizationViewEq
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewEq table left right) (coordinate : Coordinate)
    (candidate : Digest) :
    DeferredCompletable table
        { left with state := left.state.addPending coordinate candidate } ↔
      DeferredCompletable table
        { right with state := right.state.addPending coordinate candidate } := by
  constructor
  · rintro ⟨completion, hcompletion⟩
    have hleftBase := hcompletion.of_addPending coordinate candidate
    have hrightBase := (hview.deferredCompletion_iff completion).mp hleftBase
    have havoids := hcompletion.2.2.1 coordinate candidate (by
      simp [LazyRevealProbe.State.addPending])
    exact ⟨completion, hrightBase.addPending_of_avoids coordinate candidate havoids⟩
  · rintro ⟨completion, hcompletion⟩
    have hrightBase := hcompletion.of_addPending coordinate candidate
    have hleftBase := (hview.deferredCompletion_iff completion).mpr hrightBase
    have havoids := hcompletion.2.2.1 coordinate candidate (by
      simp [LazyRevealProbe.State.addPending])
    exact ⟨completion, hleftBase.addPending_of_avoids coordinate candidate havoids⟩

theorem finalizationAdaptiveCouples_probe
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (candidate : Digest) :
    FinalizationAdaptiveCouples table (probe ⟨coordinate, candidate⟩)
      (probe ⟨coordinate, candidate⟩) := by
  intro left right fuel leftCache rightCache hcontext hcache hrevealed
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  unfold probe
  rw [StateT.run_liftM, StateT.run_liftM, LazyRevealProbe.probeQuery,
    runResolvedFromTable_probe_query_bind, runResolvedFromTable_probe_query_bind]
  cases fuel with
  | zero =>
      apply relTriple_pure_pure
      exact Or.inl trivial
  | succ remaining =>
      by_cases hleftRevealed : coordinate ∈ left.state.revealed
      · have hrightRevealed : coordinate ∈ right.state.revealed := by
          rw [← hrevealed]
          exact hleftRevealed
        simp only [hleftRevealed, hrightRevealed, ↓reduceIte, runResolvedFromTable]
        apply relTriple_pure_pure
        exact Or.inl ⟨rfl, ⟨hview, hleftValid, hrightValid, hleftCompletable⟩,
          rfl, rfl, rfl, hcache, hrevealed⟩
      · have hrightRevealed : coordinate ∉ right.state.revealed := by
          rwa [← hrevealed]
        simp only [hleftRevealed, hrightRevealed, ↓reduceIte, runResolvedFromTable]
        let left' : DeferredContext :=
          { left with state := left.state.addPending coordinate candidate }
        let right' : DeferredContext :=
          { right with state := right.state.addPending coordinate candidate }
        have hcompletableIff := deferredCompletable_addPending_iff_of_finalizationViewEq hview
          coordinate candidate
        by_cases hleft' : DeferredCompletable table left'
        · have hright' : DeferredCompletable table right' := hcompletableIff.mp hleft'
          obtain ⟨leftCompletion, hleftCompletion⟩ := hleft'
          obtain ⟨rightCompletion, hrightCompletion⟩ := hright'
          have hleftCompletable' : DeferredCompletable table left' :=
            ⟨leftCompletion, hleftCompletion⟩
          have hrightCompletable' : DeferredCompletable table right' :=
            ⟨rightCompletion, hrightCompletion⟩
          have hleftValid' : left'.Valid := ⟨
            hleftValid.valuesConsistent.addPending coordinate candidate, by
              intro other output hvalue hhit
              unfold LazyRevealProbe.State.hitAt at hhit
              rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit
              exact hleftCompletion.2.2.1 other (truncateHash output) hhit
                (by rw [hleftCompletion.1 other output hvalue])⟩
          have hrightValid' : right'.Valid := ⟨
            hrightValid.valuesConsistent.addPending coordinate candidate, by
              intro other output hvalue hhit
              unfold LazyRevealProbe.State.hitAt at hhit
              rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit
              exact hrightCompletion.2.2.1 other (truncateHash output) hhit
                (by rw [hrightCompletion.1 other output hvalue])⟩
          apply relTriple_pure_pure
          left
          exact ⟨rfl,
            ⟨hview.addPending_of_completable coordinate candidate hleftCompletable'
                hrightCompletable',
              hleftValid', hrightValid', hleftCompletable'⟩,
            rfl, rfl, rfl, hcache, hrevealed⟩
        · have hright' : ¬DeferredCompletable table right' := by
            rwa [← hcompletableIff]
          apply relTriple_pure_pure
          right
          exact ⟨⟨rfl, hleftValid.valuesConsistent.addPending coordinate candidate,
              hview.leftStarts.addPending coordinate candidate, hleft'⟩,
            ⟨rfl, hrightValid.valuesConsistent.addPending coordinate candidate,
              hview.rightStarts.addPending coordinate candidate, hright'⟩⟩

theorem finalizationSynchronizedCouples_probe
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (candidate : Digest) :
    FinalizationSynchronizedCouples table (probe ⟨coordinate, candidate⟩)
      (probe ⟨coordinate, candidate⟩) := by
  intro left right fuel leftCache rightCache hcontext hvalues hcache hrevealed
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  unfold probe
  rw [StateT.run_liftM, StateT.run_liftM, LazyRevealProbe.probeQuery,
    runResolvedFromTable_probe_query_bind, runResolvedFromTable_probe_query_bind]
  cases fuel with
  | zero =>
      apply relTriple_pure_pure
      exact Or.inl ⟨trivial, trivial⟩
  | succ remaining =>
      by_cases hleftRevealed : coordinate ∈ left.state.revealed
      · have hrightRevealed : coordinate ∈ right.state.revealed := by
          rw [← hrevealed]
          exact hleftRevealed
        simp only [hleftRevealed, hrightRevealed, ↓reduceIte, runResolvedFromTable]
        apply relTriple_pure_pure
        left
        exact ⟨⟨rfl, ⟨hview, hleftValid, hrightValid, hleftCompletable⟩,
          rfl, rfl, rfl, hcache, hrevealed⟩, hvalues⟩
      · have hrightRevealed : coordinate ∉ right.state.revealed := by
          rwa [← hrevealed]
        simp only [hleftRevealed, hrightRevealed, ↓reduceIte, runResolvedFromTable]
        let left' : DeferredContext :=
          { left with state := left.state.addPending coordinate candidate }
        let right' : DeferredContext :=
          { right with state := right.state.addPending coordinate candidate }
        have hcompletableIff := deferredCompletable_addPending_iff_of_finalizationViewEq hview
          coordinate candidate
        by_cases hleft' : DeferredCompletable table left'
        · have hright' : DeferredCompletable table right' := hcompletableIff.mp hleft'
          obtain ⟨leftCompletion, hleftCompletion⟩ := hleft'
          obtain ⟨rightCompletion, hrightCompletion⟩ := hright'
          have hleftCompletable' : DeferredCompletable table left' :=
            ⟨leftCompletion, hleftCompletion⟩
          have hrightCompletable' : DeferredCompletable table right' :=
            ⟨rightCompletion, hrightCompletion⟩
          have hleftValid' : left'.Valid := ⟨
            hleftValid.valuesConsistent.addPending coordinate candidate, by
              intro other output hvalue hhit
              unfold LazyRevealProbe.State.hitAt at hhit
              rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit
              exact hleftCompletion.2.2.1 other (truncateHash output) hhit
                (by rw [hleftCompletion.1 other output hvalue])⟩
          have hrightValid' : right'.Valid := ⟨
            hrightValid.valuesConsistent.addPending coordinate candidate, by
              intro other output hvalue hhit
              unfold LazyRevealProbe.State.hitAt at hhit
              rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit
              exact hrightCompletion.2.2.1 other (truncateHash output) hhit
                (by rw [hrightCompletion.1 other output hvalue])⟩
          apply relTriple_pure_pure
          left
          refine ⟨⟨rfl,
            ⟨hview.addPending_of_completable coordinate candidate hleftCompletable'
                hrightCompletable',
              hleftValid', hrightValid', hleftCompletable'⟩,
            rfl, rfl, rfl, hcache, hrevealed⟩, ?_⟩
          exact hvalues
        · have hright' : ¬DeferredCompletable table right' := by
            rwa [← hcompletableIff]
          apply relTriple_pure_pure
          right
          exact ⟨⟨rfl, hleftValid.valuesConsistent.addPending coordinate candidate,
              hview.leftStarts.addPending coordinate candidate, hleft'⟩,
            ⟨rfl, hrightValid.valuesConsistent.addPending coordinate candidate,
              hview.rightStarts.addPending coordinate candidate, hright'⟩⟩

theorem FinalizationAdaptiveCouples.bind
    {table : OtsSecretIndex → HashOutput}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {leftNext : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    {rightNext : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hleft : FinalizationAdaptiveCouples table left right)
    (hnext : ∀ value, FinalizationAdaptiveCouples table (leftNext value) (rightNext value)) :
    FinalizationAdaptiveCouples table (left >>= leftNext) (right >>= rightNext) := by
  intro leftContext rightContext fuel leftCache rightCache hcontext hcache hrevealed
  rw [StateT.run_bind, StateT.run_bind, runResolvedFromTable_bind,
    runResolvedFromTable_bind]
  apply relTriple_bind
    (hleft leftContext rightContext fuel leftCache rightCache hcontext hcache hrevealed)
  intro leftResult rightResult hrelation
  rcases hrelation with hclean | hdoomed
  · cases leftResult with
    | none =>
        cases rightResult with
        | none => simp [FinalizationAdaptiveRunEq, FinalizationMaterializedRunEq]
        | some rightResult => simp [FinalizationMaterializedRunEq] at hclean
    | some leftResult =>
        cases rightResult with
        | none => simp [FinalizationMaterializedRunEq] at hclean
        | some rightResult =>
            rcases leftResult with ⟨leftContext, leftFuel, leftValue, leftTable⟩
            rcases rightResult with ⟨rightContext, rightFuel, rightValue, rightTable⟩
            rcases leftValue with ⟨leftOutput, leftCache⟩
            rcases rightValue with ⟨rightOutput, rightCache⟩
            simp only [FinalizationMaterializedRunEq] at hclean
            rcases hclean with
              ⟨houtput, hcontext, hfuel, hleftTable, hrightTable, hcache, hrevealed⟩
            subst rightOutput
            subst rightFuel
            subst leftTable
            subst rightTable
            exact hnext leftOutput leftContext rightContext leftFuel leftCache rightCache
              hcontext hcache hrevealed
  · cases leftResult with
    | none =>
        cases rightResult with
        | none => simp [FinalizationAdaptiveRunEq, FinalizationDoomedRun]
        | some rightResult =>
            simp only
            rw [hdoomed.2.1]
            exact relTriple_pure_none_runResolvedFromTable_of_finalizationDoomed table
              ((rightNext rightResult.value.1).run rightResult.value.2)
              rightResult.context rightResult.remaining hdoomed.2.2
    | some leftResult =>
        cases rightResult with
        | none =>
            simp only
            rw [hdoomed.1.1]
            exact relTriple_runResolvedFromTable_pure_none_of_finalizationDoomed table
              ((leftNext leftResult.value.1).run leftResult.value.2)
              leftResult.context leftResult.remaining hdoomed.1.2
        | some rightResult =>
            have hleftTable := hdoomed.1.1
            have hrightTable := hdoomed.2.1
            simp only
            rw [hleftTable, hrightTable]
            exact relTriple_runResolvedFromTable_of_finalizationDoomed table
              ((leftNext leftResult.value.1).run leftResult.value.2)
              ((rightNext rightResult.value.1).run rightResult.value.2)
              leftResult.context rightResult.context leftResult.remaining rightResult.remaining
              hdoomed.1.2 hdoomed.2.2

theorem FinalizationSynchronizedCouples.bind
    {table : OtsSecretIndex → HashOutput}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {leftNext : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    {rightNext : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hleft : FinalizationSynchronizedCouples table left right)
    (hnext : ∀ value,
      FinalizationSynchronizedCouples table (leftNext value) (rightNext value)) :
    FinalizationSynchronizedCouples table (left >>= leftNext) (right >>= rightNext) := by
  intro leftContext rightContext fuel leftCache rightCache hcontext hvalues hcache hrevealed
  rw [StateT.run_bind, StateT.run_bind, runResolvedFromTable_bind,
    runResolvedFromTable_bind]
  apply relTriple_bind
    (hleft leftContext rightContext fuel leftCache rightCache hcontext hvalues hcache hrevealed)
  intro leftResult rightResult hrelation
  rcases hrelation with hclean | hdoomed
  · cases leftResult with
    | none =>
        cases rightResult with
        | none => simp [FinalizationSynchronizedRunEq, FinalizationMaterializedRunEq,
            MaterializedValuesEq]
        | some rightResult => simp [FinalizationMaterializedRunEq] at hclean
    | some leftResult =>
        cases rightResult with
        | none => simp [FinalizationMaterializedRunEq] at hclean
        | some rightResult =>
            rcases leftResult with ⟨leftContext, leftFuel, leftValue, leftTable⟩
            rcases rightResult with ⟨rightContext, rightFuel, rightValue, rightTable⟩
            rcases leftValue with ⟨leftOutput, leftCache⟩
            rcases rightValue with ⟨rightOutput, rightCache⟩
            simp only [FinalizationMaterializedRunEq, MaterializedValuesEq] at hclean
            rcases hclean.1 with
              ⟨houtput, hcontext, hfuel, hleftTable, hrightTable, hcache, hrevealed⟩
            subst rightOutput
            subst rightFuel
            subst leftTable
            subst rightTable
            exact hnext leftOutput leftContext rightContext leftFuel leftCache rightCache
              hcontext hclean.2 hcache hrevealed
  · cases leftResult with
    | none =>
        cases rightResult with
        | none => simp [FinalizationSynchronizedRunEq, FinalizationDoomedRun]
        | some rightResult =>
            simp only
            rw [hdoomed.2.1]
            exact relTriple_pure_none_runResolvedFromTable_of_finalizationDoomed_synchronized
              table ((rightNext rightResult.value.1).run rightResult.value.2)
                rightResult.context rightResult.remaining hdoomed.2.2
    | some leftResult =>
        cases rightResult with
        | none =>
            simp only
            rw [hdoomed.1.1]
            exact relTriple_runResolvedFromTable_pure_none_of_finalizationDoomed_synchronized
              table ((leftNext leftResult.value.1).run leftResult.value.2)
                leftResult.context leftResult.remaining hdoomed.1.2
        | some rightResult =>
            have hleftTable := hdoomed.1.1
            have hrightTable := hdoomed.2.1
            simp only
            rw [hleftTable, hrightTable]
            exact relTriple_runResolvedFromTable_of_finalizationDoomed_synchronized table
              ((leftNext leftResult.value.1).run leftResult.value.2)
              ((rightNext rightResult.value.1).run rightResult.value.2)
              leftResult.context rightResult.context leftResult.remaining rightResult.remaining
              hdoomed.1.2 hdoomed.2.2

theorem finalizationSynchronizedCouples_splitUniformImpl
    (table : OtsSecretIndex → HashOutput) (n : Nat) :
    FinalizationSynchronizedCouples table (splitUniformImpl n) (splitUniformImpl n) := by
  intro left right fuel leftCache rightCache hcontext hvalues hcache hrevealed
  unfold splitUniformImpl
  rw [StateT.run_liftM, StateT.run_liftM, LazyRevealProbe.uniformQuery,
    runResolvedFromTable_uniform_query_bind,
    runResolvedFromTable_uniform_query_bind]
  apply relTriple_bind (relTriple_refl
    (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
  intro leftOutput rightOutput houtput
  subst rightOutput
  apply relTriple_pure_pure
  left
  exact ⟨⟨rfl, hcontext, rfl, rfl, rfl, hcache, hrevealed⟩, hvalues⟩

theorem finalizationSynchronizedCouples_ordinaryRomImpl
    (table : OtsSecretIndex → HashOutput) (query : OracleWorld.Domain) :
    FinalizationSynchronizedCouples table (ordinaryRomImpl query)
      (ordinaryRomImpl query) := by
  cases query with
  | inl n => exact finalizationSynchronizedCouples_splitUniformImpl table n
  | inr input => exact finalizationSynchronizedCouples_ordinaryHashImpl table input

theorem finalizationSynchronizedCouples_simulateQ
    {table : OtsSecretIndex → HashOutput} {spec : OracleSpec ι}
    (leftImpl rightImpl : QueryImpl spec
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))))
    (hquery : ∀ query,
      FinalizationSynchronizedCouples table (leftImpl query) (rightImpl query))
    (computation : OracleComp spec α) :
    FinalizationSynchronizedCouples table
      (simulateQ leftImpl computation) (simulateQ rightImpl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure]
      exact finalizationSynchronizedCouples_pure table value
  | query_bind query next ih =>
      rw [simulateQ_query_bind, simulateQ_query_bind]
      exact (hquery query).bind fun output => ih output

theorem finalizationSynchronizedCouples_peekPositionValues
    (table : OtsSecretIndex → HashOutput) : ∀ positions,
    FinalizationSynchronizedCouples table (peekPositionValues positions)
      (peekPositionValues positions)
  | [] => finalizationSynchronizedCouples_pure table (some [])
  | position :: remaining => by
      rw [peekPositionValues]
      apply (finalizationSynchronizedCouples_peekCoordinate table (.position position)).bind
      intro value
      cases value with
      | none => exact finalizationSynchronizedCouples_pure table none
      | some value =>
          apply (finalizationSynchronizedCouples_peekPositionValues table remaining).bind
          intro values
          cases values with
          | none => exact finalizationSynchronizedCouples_pure table none
          | some values =>
              exact finalizationSynchronizedCouples_pure table (some (value :: values))

theorem finalizationSynchronizedCouples_peekTableInput
    (table : OtsSecretIndex → HashOutput) (parameter : PublicParameter) : ∀ coordinate,
    FinalizationSynchronizedCouples table (peekTableInput parameter coordinate)
      (peekTableInput parameter coordinate)
  | .chainStart _ _ _ _ => finalizationSynchronizedCouples_pure table none
  | .position (.chain lay tree leafIdx chainIdx step) => by
      simp only [peekTableInput]
      by_cases hstep : step.val = 0
      · rw [if_pos hstep]
        apply (finalizationSynchronizedCouples_peekCoordinate table
          (.chainStart lay tree leafIdx chainIdx)).bind
        intro value
        cases value with
        | none => exact finalizationSynchronizedCouples_pure table none
        | some value =>
            simp only
            exact finalizationSynchronizedCouples_pure table
              (some (tweakableHashInput parameter
                (Position.chain lay tree leafIdx chainIdx step).domain (digestBytes value)))
      · rw [if_neg hstep]
        apply (finalizationSynchronizedCouples_peekPositionValues table
          (Position.chain lay tree leafIdx chainIdx step).children).bind
        intro values
        cases values with
        | none =>
            simp only
            exact finalizationSynchronizedCouples_pure table none
        | some values =>
            simp only
            exact finalizationSynchronizedCouples_pure table
              (some (tweakableHashInput parameter
                (Position.chain lay tree leafIdx chainIdx step).domain
                (values.flatMap digestBytes)))
  | .position (.leaf lay tree leafIdx) => by
      unfold peekTableInput
      apply (finalizationSynchronizedCouples_peekPositionValues table
        (Position.leaf lay tree leafIdx).children).bind
      intro values
      cases values with
      | none =>
          simp only
          exact finalizationSynchronizedCouples_pure table none
      | some values =>
          simp only
          exact finalizationSynchronizedCouples_pure table
            (some (tweakableHashInput parameter (Position.leaf lay tree leafIdx).domain
              (values.flatMap digestBytes)))
  | .position (.node lay tree level nodeIdx) => by
      unfold peekTableInput
      apply (finalizationSynchronizedCouples_peekPositionValues table
        (Position.node lay tree level nodeIdx).children).bind
      intro values
      cases values with
      | none =>
          simp only
          exact finalizationSynchronizedCouples_pure table none
      | some values =>
          simp only
          exact finalizationSynchronizedCouples_pure table
            (some (tweakableHashInput parameter (Position.node lay tree level nodeIdx).domain
              (values.flatMap digestBytes)))
  | .position (.ftsLeaf index tree leafIdx) => by
      unfold peekTableInput
      apply (finalizationSynchronizedCouples_peekPositionValues table
        (Position.ftsLeaf index tree leafIdx).children).bind
      intro values
      cases values with
      | none =>
          simp only
          exact finalizationSynchronizedCouples_pure table none
      | some values =>
          simp only
          exact finalizationSynchronizedCouples_pure table
            (some (tweakableHashInput parameter (Position.ftsLeaf index tree leafIdx).domain
              (values.flatMap digestBytes)))
  | .position (.ftsNode index tree level nodeIdx) => by
      unfold peekTableInput
      apply (finalizationSynchronizedCouples_peekPositionValues table
        (Position.ftsNode index tree level nodeIdx).children).bind
      intro values
      cases values with
      | none =>
          simp only
          exact finalizationSynchronizedCouples_pure table none
      | some values =>
          simp only
          exact finalizationSynchronizedCouples_pure table
            (some (tweakableHashInput parameter (Position.ftsNode index tree level nodeIdx).domain
              (values.flatMap digestBytes)))
  | .position (.ftsRoots index) => by
      unfold peekTableInput
      apply (finalizationSynchronizedCouples_peekPositionValues table
        (Position.ftsRoots index).children).bind
      intro values
      cases values with
      | none =>
          simp only
          exact finalizationSynchronizedCouples_pure table none
      | some values =>
          simp only
          exact finalizationSynchronizedCouples_pure table
            (some (tweakableHashInput parameter (Position.ftsRoots index).domain
              (values.flatMap digestBytes)))

theorem finalizationSynchronizedCouples_cacheOrdinary
    (table : OtsSecretIndex → HashOutput) (input : HashInput) (output : HashOutput) :
    FinalizationSynchronizedCouples table
      (modify fun cache : SplitHashCache =>
        Function.update cache (.ordinary input) (some output))
      (modify fun cache : SplitHashCache =>
        Function.update cache (.ordinary input) (some output)) := by
  intro left right fuel leftCache rightCache hcontext hvalues hcache hrevealed
  simp only [StateT.run_modify, runResolvedFromTable]
  apply relTriple_pure_pure
  left
  refine ⟨⟨rfl, hcontext, rfl, rfl, rfl, ?_, hrevealed⟩, hvalues⟩
  rw [ordinaryQueryCache_update, ordinaryQueryCache_update, hcache]

theorem finalizationSynchronizedCouples_resolveKnownInput
    (table : OtsSecretIndex → HashOutput) (parameter : PublicParameter)
    (position : Position) (input : HashInput) :
    FinalizationSynchronizedCouples table
      (resolveKnownInput parameter (.position position) input)
      (resolveKnownInput parameter (.position position) input) := by
  unfold resolveKnownInput
  apply (finalizationSynchronizedCouples_peekTableInput table parameter
    (.position position)).bind
  intro knownInput
  cases knownInput with
  | none => exact finalizationSynchronizedCouples_splitHashQuery_ordinary table input
  | some knownInput =>
      simp only
      by_cases hknown : knownInput = input
      · rw [if_pos hknown]
        apply (finalizationSynchronizedCouples_revealPositionOutput table position).bind
        intro output
        apply (finalizationSynchronizedCouples_publishCoordinate table
          (.position position)).bind
        intro _
        apply (finalizationSynchronizedCouples_cacheOrdinary table input output).bind
        intro _
        exact finalizationSynchronizedCouples_pure table output
      · rw [if_neg hknown]
        exact finalizationSynchronizedCouples_splitHashQuery_ordinary table input

theorem finalizationSynchronizedCouples_resolveKnownInputCoordinate
    (table : OtsSecretIndex → HashOutput) (parameter : PublicParameter)
    (coordinate : Coordinate) (input : HashInput) :
    FinalizationSynchronizedCouples table
      (resolveKnownInput parameter coordinate input)
      (resolveKnownInput parameter coordinate input) := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      unfold resolveKnownInput
      simp only [peekTableInput, pure_bind]
      exact finalizationSynchronizedCouples_splitHashQuery_ordinary table input
  | position position =>
      exact finalizationSynchronizedCouples_resolveKnownInput table parameter position input

theorem finalizationSynchronizedCouples_probeFirstMissingInputCoordinate
    (table : OtsSecretIndex → HashOutput) (input : HashInput) :
    ∀ slot coordinates,
      FinalizationSynchronizedCouples table
        (probeFirstMissingInputCoordinate input slot coordinates)
        (probeFirstMissingInputCoordinate input slot coordinates)
  | _, [] => finalizationSynchronizedCouples_pure table ()
  | slot, coordinate :: remaining => by
      rw [probeFirstMissingInputCoordinate]
      apply (finalizationSynchronizedCouples_peekCoordinate table coordinate).bind
      intro value
      cases value with
      | none =>
          exact finalizationSynchronizedCouples_probe table coordinate
            (slotDigest slot input)
      | some _ =>
          exact finalizationSynchronizedCouples_probeFirstMissingInputCoordinate table input
            (slot + 1) remaining

theorem finalizationSynchronizedCouples_prepareLeafInputProbe
    (table : OtsSecretIndex → HashOutput) (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    FinalizationSynchronizedCouples table
      (prepareLeafInputProbe input candidate lay tree leafIdx)
      (prepareLeafInputProbe input candidate lay tree leafIdx) := by
  unfold prepareLeafInputProbe
  apply (finalizationSynchronizedCouples_peekCoordinate table candidate.coordinate).bind
  intro value
  cases value with
  | none =>
      exact finalizationSynchronizedCouples_probe table candidate.coordinate
        candidate.candidate
  | some _ =>
      exact finalizationSynchronizedCouples_probeFirstMissingInputCoordinate table input 0
        ((Position.leaf lay tree leafIdx).children.map Coordinate.position)

theorem finalizationSynchronizedCouples_probingHashQuery
    (table : OtsSecretIndex → HashOutput) (parameter : PublicParameter)
    (input : HashInput) :
    FinalizationSynchronizedCouples table (probingHashQuery parameter input)
      (probingHashQuery parameter input) := by
  unfold probingHashQuery
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      cases hposition : decodePosition? parameter input with
      | none =>
          apply (finalizationSynchronizedCouples_probe table candidate.coordinate
            candidate.candidate).bind
          intro _
          exact finalizationSynchronizedCouples_resolveKnownInputCoordinate table parameter
            candidate.outputCoordinate input
      | some position =>
          cases position with
          | leaf lay tree leafIdx =>
              apply (finalizationSynchronizedCouples_prepareLeafInputProbe table input candidate
                lay tree leafIdx).bind
              intro _
              exact finalizationSynchronizedCouples_resolveKnownInputCoordinate table parameter
                candidate.outputCoordinate input
          | chain lay tree leafIdx chainIdx step =>
              apply (finalizationSynchronizedCouples_probe table candidate.coordinate
                candidate.candidate).bind
              intro _
              exact finalizationSynchronizedCouples_resolveKnownInputCoordinate table parameter
                candidate.outputCoordinate input
          | node lay tree level nodeIdx =>
              apply (finalizationSynchronizedCouples_probe table candidate.coordinate
                candidate.candidate).bind
              intro _
              exact finalizationSynchronizedCouples_resolveKnownInputCoordinate table parameter
                candidate.outputCoordinate input
          | ftsLeaf index tree leafIdx =>
              apply (finalizationSynchronizedCouples_probe table candidate.coordinate
                candidate.candidate).bind
              intro _
              exact finalizationSynchronizedCouples_resolveKnownInputCoordinate table parameter
                candidate.outputCoordinate input
          | ftsNode index tree level nodeIdx =>
              apply (finalizationSynchronizedCouples_probe table candidate.coordinate
                candidate.candidate).bind
              intro _
              exact finalizationSynchronizedCouples_resolveKnownInputCoordinate table parameter
                candidate.outputCoordinate input
          | ftsRoots index =>
              apply (finalizationSynchronizedCouples_probe table candidate.coordinate
                candidate.candidate).bind
              intro _
              exact finalizationSynchronizedCouples_resolveKnownInputCoordinate table parameter
                candidate.outputCoordinate input
  | none =>
      cases hposition : decodePosition? parameter input with
      | none =>
          exact finalizationSynchronizedCouples_splitHashQuery_ordinary table input
      | some position =>
          cases position with
          | chain lay tree leafIdx chainIdx step =>
              exact finalizationSynchronizedCouples_resolveKnownInput table parameter
                (.chain lay tree leafIdx chainIdx step) input
          | leaf lay tree leafIdx =>
              exact finalizationSynchronizedCouples_resolveKnownInput table parameter
                (.leaf lay tree leafIdx) input
          | node lay tree level nodeIdx =>
              apply (finalizationSynchronizedCouples_probeFirstMissingInputCoordinate table input
                0 ((Position.node lay tree level nodeIdx).children.map
                  Coordinate.position)).bind
              intro _
              exact finalizationSynchronizedCouples_resolveKnownInput table parameter
                (.node lay tree level nodeIdx) input
          | ftsLeaf index tree leafIdx =>
              exact finalizationSynchronizedCouples_splitHashQuery_ordinary table input
          | ftsNode index tree level nodeIdx =>
              exact finalizationSynchronizedCouples_splitHashQuery_ordinary table input
          | ftsRoots index =>
              exact finalizationSynchronizedCouples_splitHashQuery_ordinary table input

theorem finalizationSynchronizedCouples_probingRomImpl
    (table : OtsSecretIndex → HashOutput) (parameter : PublicParameter)
    (query : OracleWorld.Domain) :
    FinalizationSynchronizedCouples table (probingRomImpl parameter query)
      (probingRomImpl parameter query) := by
  cases query with
  | inl n => exact finalizationSynchronizedCouples_splitUniformImpl table n
  | inr input => exact finalizationSynchronizedCouples_probingHashQuery table parameter input

theorem finalizationSynchronizedCouples_probingRom
    (table : OtsSecretIndex → HashOutput) (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) :
    FinalizationSynchronizedCouples table
      (simulateQ (probingRomImpl parameter) computation)
      (simulateQ (probingRomImpl parameter) computation) :=
  finalizationSynchronizedCouples_simulateQ (probingRomImpl parameter)
    (probingRomImpl parameter)
    (finalizationSynchronizedCouples_probingRomImpl table parameter) computation

theorem finalizationAdaptiveCouples_pure
    (table : OtsSecretIndex → HashOutput) (value : α) :
    FinalizationAdaptiveCouples table
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) α)
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) α) :=
  (finalizationMaterializedCouples_pure table value).toAdaptive

theorem finalizationAdaptiveCouples_simulateQ
    {table : OtsSecretIndex → HashOutput} {spec : OracleSpec ι}
    (leftImpl rightImpl : QueryImpl spec
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))))
    (hquery : ∀ query,
      FinalizationAdaptiveCouples table (leftImpl query) (rightImpl query))
    (computation : OracleComp spec α) :
    FinalizationAdaptiveCouples table
      (simulateQ leftImpl computation) (simulateQ rightImpl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure]
      exact finalizationAdaptiveCouples_pure table value
  | query_bind query next ih =>
      rw [simulateQ_query_bind, simulateQ_query_bind]
      exact (hquery query).bind fun output => ih output

theorem finalizationAdaptiveCouples_ordinaryRomImpl
    (table : OtsSecretIndex → HashOutput) (query : OracleWorld.Domain) :
    FinalizationAdaptiveCouples table (ordinaryRomImpl query) (ordinaryRomImpl query) :=
  (finalizationMaterializedCouples_ordinaryRomImpl table query).toAdaptive

theorem finalizationAdaptiveCouples_ensureCoordinate
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) :
    FinalizationAdaptiveCouples table (ensureCoordinate coordinate)
      (ensureCoordinate coordinate) :=
  (finalizationMaterializedCouples_ensureCoordinate table coordinate).toAdaptive

theorem finalizationAdaptiveCouples_revealCoordinate
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) :
    FinalizationAdaptiveCouples table (revealCoordinate coordinate)
      (revealCoordinate coordinate) :=
  (finalizationMaterializedCouples_revealCoordinate table coordinate).toAdaptive

theorem finalizationAdaptiveCouples_publishCoordinate
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) :
    FinalizationAdaptiveCouples table (publishCoordinate coordinate)
      (publishCoordinate coordinate) :=
  (finalizationMaterializedCouples_publishCoordinate table coordinate).toAdaptive

theorem relTriple_finishResolvedRunIsNone_of_finalizationAdaptiveRunEq
    (table : OtsSecretIndex → HashOutput)
    (left right : Option (ResolvedRunResult (α × SplitHashCache)))
    (hrelation : FinalizationAdaptiveRunEq table left right) :
    RelTriple (finishResolvedRunIsNone left) (finishResolvedRunIsNone right)
      (EqRel Bool) := by
  rcases hrelation with hclean | hdoomed
  · exact relTriple_finishResolvedRunIsNone_of_finalizationMaterializedRunEq table left right
      hclean
  · cases left with
    | none =>
        cases right with
        | none => exact relTriple_pure_pure rfl
        | some right =>
            have hrightTable := hdoomed.2.1
            have hrightDoomed :
                ¬DeferredCompletable right.table right.context := by
              rw [hrightTable]
              exact hdoomed.2.2.2.2
            rw [finishResolvedRunIsNone, finishResolvedRunIsNone,
              finishResolvedRun_of_not_deferredCompletable right hrightDoomed]
            simp [finishResolvedRun]
            rfl
    | some left =>
        have hleftTable := hdoomed.1.1
        have hleftDoomed : ¬DeferredCompletable left.table left.context := by
          rw [hleftTable]
          exact hdoomed.1.2.2.2
        cases right with
        | none =>
            rw [finishResolvedRunIsNone, finishResolvedRunIsNone,
              finishResolvedRun_of_not_deferredCompletable left hleftDoomed]
            simp [finishResolvedRun]
            rfl
        | some right =>
            have hrightTable := hdoomed.2.1
            have hrightDoomed :
                ¬DeferredCompletable right.table right.context := by
              rw [hrightTable]
              exact hdoomed.2.2.2.2
            rw [finishResolvedRunIsNone, finishResolvedRunIsNone,
              finishResolvedRun_of_not_deferredCompletable left hleftDoomed,
              finishResolvedRun_of_not_deferredCompletable right hrightDoomed]
            exact relTriple_pure_pure rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
