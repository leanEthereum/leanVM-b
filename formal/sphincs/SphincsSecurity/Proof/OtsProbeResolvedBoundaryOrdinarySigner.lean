import SphincsSecurity.Proof.OtsProbeResolvedBoundaryOrdinaryRefinement

/-!
# Directional ordinary refinement through the signer

The general boundary relation permits a successful left run to retain a private structural hit.
That alternative is needed after a probing hash query, but it is not stable under an arbitrary
bind. The signer-local relation below removes only that successful latent-hit alternative. A
stopped private hit remains admissible, and a materialized right run may still be doomed.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def DirectDetailedOrdinaryStableRunEq (table : OtsSecretIndex → HashOutput) :
    DirectDetailedResult (α × SplitHashCache) →
      DirectDetailedResult (α × SplitHashCache) → Prop
  | .stopped .privateStructuralHit, _ => True
  | .stopped .ordinaryHit, .stopped .privateStructuralHit => False
  | .stopped .ordinaryHit, .stopped _ => True
  | .stopped .ordinaryHit, .done right =>
      OrdinaryMaterializedDoomedRun table right
  | .stopped .fuelExhausted, .stopped .ordinaryHit => True
  | .stopped .fuelExhausted, .stopped .fuelExhausted => True
  | .stopped .fuelExhausted, .done right =>
      OrdinaryMaterializedDoomedRun table right
  | .stopped .fuelExhausted, _ => False
  | .done _, .stopped .privateStructuralHit => False
  | .done _, .stopped _ => True
  | .done left, .done right =>
      OrdinaryMaterializedRunEq table left right ∨
        OrdinaryMaterializedDoomedRun table right

theorem DirectDetailedOrdinaryStableRunEq.toOrdinary
    {table : OtsSecretIndex → HashOutput}
    {left right : DirectDetailedResult (α × SplitHashCache)}
    (hrelation : DirectDetailedOrdinaryStableRunEq table left right) :
    DirectDetailedOrdinaryRunEq table left right := by
  cases left with
  | stopped leftReason =>
      cases leftReason with
      | privateStructuralHit => trivial
      | ordinaryHit =>
          cases right with
          | stopped rightReason => cases rightReason <;> exact hrelation
          | done _ => exact hrelation
      | fuelExhausted =>
          cases right with
          | stopped rightReason => cases rightReason <;> exact hrelation
          | done _ => exact hrelation
  | done leftResult =>
      cases right with
      | stopped rightReason => cases rightReason <;> exact hrelation
      | done rightResult =>
          rcases hrelation with hclean | hdoomed
          · exact Or.inl hclean
          · exact Or.inr (Or.inr hdoomed)

theorem relTriple_stable_to_ordinary
    {table : OtsSecretIndex → HashOutput}
    {left right : ProbComp (DirectDetailedResult (α × SplitHashCache))}
    (hrelation : RelTriple left right
      (DirectDetailedOrdinaryStableRunEq table)) :
    RelTriple left right (DirectDetailedOrdinaryRunEq table) := by
  apply relTriple_post_mono hrelation
  intro leftResult rightResult
  exact DirectDetailedOrdinaryStableRunEq.toOrdinary

theorem relTriple_pure_privateStructuralHit_any_stable
    (table : OtsSecretIndex → HashOutput)
    (rightRun : ProbComp (DirectDetailedResult (α × SplitHashCache))) :
    RelTriple
      (pure (.stopped .privateStructuralHit) :
        ProbComp (DirectDetailedResult (α × SplitHashCache)))
      rightRun (DirectDetailedOrdinaryStableRunEq table) := by
  have hbase := relTriple_true
    (pure (.stopped .privateStructuralHit) :
      ProbComp (DirectDetailedResult (α × SplitHashCache))) rightRun
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun result => result ∈ support
        (pure (.stopped .privateStructuralHit) :
          ProbComp (DirectDetailedResult (α × SplitHashCache))))
      (fun result hresult => hresult)
  apply relTriple_post_mono hsupported
  intro leftResult _ hrelation
  have hleft : leftResult = .stopped .privateStructuralHit := by
    simpa using hrelation.2
  subst leftResult
  trivial

theorem relTriple_any_pure_nonprivateStop_stable
    (table : OtsSecretIndex → HashOutput)
    (leftRun : ProbComp (DirectDetailedResult (α × SplitHashCache)))
    (reason : DirectStopReason) (hreason : reason ≠ .privateStructuralHit) :
    RelTriple leftRun
      (pure (.stopped reason) :
        ProbComp (DirectDetailedResult (α × SplitHashCache)))
      (DirectDetailedOrdinaryStableRunEq table) := by
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
  | ordinaryHit => cases leftResult with
    | stopped leftReason => cases leftReason <;> trivial
    | done _ => trivial
  | fuelExhausted => cases leftResult with
    | stopped leftReason => cases leftReason <;> trivial
    | done _ => trivial

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_of_right_materializedDoomed_stable
    (table : OtsSecretIndex → HashOutput)
    (leftRun : ProbComp (DirectDetailedResult (α × SplitHashCache)))
    (rightComputation :
      OracleComp (LazyRevealProbe.World Coordinate) (α × SplitHashCache))
    (right : DeferredContext) (rightFuel : Nat)
    (hrightDoomed : DoomedResolvedContext table right)
    (hrightMaterialized : right = directDeferredContext right.state) :
    RelTriple
      leftRun
      (runDirectResolvedDetailedFromTable right rightFuel table rightComputation)
      (DirectDetailedOrdinaryStableRunEq table) := by
  have hbase := relTriple_true leftRun
    (runDirectResolvedDetailedFromTable right rightFuel table rightComputation)
  have hleft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun result => result ∈ support leftRun)
      (fun result hresult => hresult)
  have hboth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
  apply relTriple_post_mono hboth
  intro leftResult rightResult hrelation
  have hrightShape : DirectDetailedMaterialized rightResult := by
    have hsupport := hrelation.2
    rw [hrightMaterialized] at hsupport
    exact directDetailedMaterialized_of_mem_runDirectResolvedDetailedFromTable
      rightComputation right.state rightFuel table rightResult hsupport
  cases rightResult with
  | stopped reason =>
      cases reason with
      | privateStructuralHit => exact False.elim hrightShape
      | ordinaryHit =>
          cases leftResult with
          | stopped leftReason => cases leftReason <;> trivial
          | done _ => trivial
      | fuelExhausted =>
          cases leftResult with
          | stopped leftReason => cases leftReason <;> trivial
          | done _ => trivial
  | done rightResult =>
      have hdoomed :=
        finalizationDoomedRun_of_mem_runDirectResolvedDetailedFromTable table
          rightComputation right rightFuel rightResult hrightDoomed hrelation.2
      have hmaterialized := hrightShape
      cases leftResult with
      | stopped reason =>
          cases reason with
          | privateStructuralHit => trivial
          | ordinaryHit => exact ⟨hdoomed, hmaterialized⟩
          | fuelExhausted => exact ⟨hdoomed, hmaterialized⟩
      | done _ =>
          right
          exact ⟨hdoomed, hmaterialized⟩

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_bind_stable
    (table : OtsSecretIndex → HashOutput)
    (left right : OracleComp (LazyRevealProbe.World Coordinate) (α × SplitHashCache))
    (leftNext rightNext : α → SplitHashCache →
      OracleComp (LazyRevealProbe.World Coordinate) (β × SplitHashCache))
    (leftContext rightContext : DeferredContext) (leftFuel rightFuel : Nat)
    (hleft : RelTriple
      (runDirectResolvedDetailedFromTable leftContext leftFuel table left)
      (runDirectResolvedDetailedFromTable rightContext rightFuel table right)
      (DirectDetailedOrdinaryStableRunEq table))
    (hclean : ∀ (leftResult rightResult :
      ResolvedRunResult (α × SplitHashCache)),
      OrdinaryMaterializedRunEq table leftResult rightResult →
      RelTriple
        (runDirectResolvedDetailedFromTable leftResult.context leftResult.remaining
          leftResult.table (leftNext leftResult.value.1 leftResult.value.2))
        (runDirectResolvedDetailedFromTable rightResult.context rightResult.remaining
          rightResult.table (rightNext rightResult.value.1 rightResult.value.2))
        (DirectDetailedOrdinaryStableRunEq table)) :
    RelTriple
      (runDirectResolvedDetailedFromTable leftContext leftFuel table
        (left >>= fun value => leftNext value.1 value.2))
      (runDirectResolvedDetailedFromTable rightContext rightFuel table
        (right >>= fun value => rightNext value.1 value.2))
      (DirectDetailedOrdinaryStableRunEq table) := by
  rw [runDirectResolvedDetailedFromTable_bind,
    runDirectResolvedDetailedFromTable_bind]
  apply relTriple_bind hleft
  intro leftResult rightResult hrelation
  cases leftResult with
  | stopped leftReason =>
      cases leftReason with
      | privateStructuralHit =>
          exact relTriple_pure_privateStructuralHit_any_stable table _
      | ordinaryHit =>
          cases rightResult with
          | stopped rightReason =>
              cases rightReason with
              | privateStructuralHit => contradiction
              | ordinaryHit => exact relTriple_pure_pure trivial
              | fuelExhausted => exact relTriple_pure_pure trivial
          | done rightResult =>
              simp only
              rw [hrelation.1.1]
              exact relTriple_runDirectResolvedDetailed_of_right_materializedDoomed_stable table
                (pure (.stopped .ordinaryHit))
                (rightNext rightResult.value.1 rightResult.value.2)
                rightResult.context rightResult.remaining hrelation.1.2 hrelation.2
      | fuelExhausted =>
          cases rightResult with
          | stopped rightReason =>
              cases rightReason with
              | privateStructuralHit => contradiction
              | ordinaryHit => exact relTriple_pure_pure trivial
              | fuelExhausted => exact relTriple_pure_pure trivial
          | done rightResult =>
              simp only
              rw [hrelation.1.1]
              exact relTriple_runDirectResolvedDetailed_of_right_materializedDoomed_stable table
                (pure (.stopped .fuelExhausted))
                (rightNext rightResult.value.1 rightResult.value.2)
                rightResult.context rightResult.remaining hrelation.1.2 hrelation.2
  | done leftResult =>
      cases rightResult with
      | stopped rightReason =>
          cases rightReason with
          | privateStructuralHit => contradiction
          | ordinaryHit =>
              exact relTriple_any_pure_nonprivateStop_stable table _ .ordinaryHit (by decide)
          | fuelExhausted =>
              exact relTriple_any_pure_nonprivateStop_stable table _ .fuelExhausted (by decide)
      | done rightResult =>
          rcases hrelation with hcleanRelation | hdoomedRelation
          · exact hclean leftResult rightResult hcleanRelation
          · simp only
            rw [hdoomedRelation.1.1]
            exact relTriple_runDirectResolvedDetailed_of_right_materializedDoomed_stable table
              (runDirectResolvedDetailedFromTable leftResult.context leftResult.remaining
                leftResult.table (leftNext leftResult.value.1 leftResult.value.2))
              (rightNext rightResult.value.1 rightResult.value.2)
              rightResult.context rightResult.remaining hdoomedRelation.1.2
                hdoomedRelation.2

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_bind_with_support_stable
    (table : OtsSecretIndex → HashOutput)
    (left right : OracleComp (LazyRevealProbe.World Coordinate) (α × SplitHashCache))
    (leftNext rightNext : α → SplitHashCache →
      OracleComp (LazyRevealProbe.World Coordinate) (β × SplitHashCache))
    (leftContext rightContext : DeferredContext) (leftFuel rightFuel : Nat)
    (hleft : RelTriple
      (runDirectResolvedDetailedFromTable leftContext leftFuel table left)
      (runDirectResolvedDetailedFromTable rightContext rightFuel table right)
      (DirectDetailedOrdinaryStableRunEq table))
    (hclean : ∀ (leftResult rightResult :
      ResolvedRunResult (α × SplitHashCache)),
      DirectDetailedResult.done leftResult ∈ support
        (runDirectResolvedDetailedFromTable leftContext leftFuel table left) →
      DirectDetailedResult.done rightResult ∈ support
        (runDirectResolvedDetailedFromTable rightContext rightFuel table right) →
      OrdinaryMaterializedRunEq table leftResult rightResult →
      RelTriple
        (runDirectResolvedDetailedFromTable leftResult.context leftResult.remaining
          leftResult.table (leftNext leftResult.value.1 leftResult.value.2))
        (runDirectResolvedDetailedFromTable rightResult.context rightResult.remaining
          rightResult.table (rightNext rightResult.value.1 rightResult.value.2))
        (DirectDetailedOrdinaryStableRunEq table)) :
    RelTriple
      (runDirectResolvedDetailedFromTable leftContext leftFuel table
        (left >>= fun value => leftNext value.1 value.2))
      (runDirectResolvedDetailedFromTable rightContext rightFuel table
        (right >>= fun value => rightNext value.1 value.2))
      (DirectDetailedOrdinaryStableRunEq table) := by
  rw [runDirectResolvedDetailedFromTable_bind,
    runDirectResolvedDetailedFromTable_bind]
  have hleftWithSupport :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hleft
      (fun result => result ∈ support
        (runDirectResolvedDetailedFromTable leftContext leftFuel table left))
      (fun result hresult => hresult)
  have hbothWithSupport :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleftWithSupport
  apply relTriple_bind hbothWithSupport
  intro leftResult rightResult hrelation
  rcases hrelation with ⟨⟨hrelation, hleftSupport⟩, hrightSupport⟩
  cases leftResult with
  | stopped leftReason =>
      cases leftReason with
      | privateStructuralHit =>
          exact relTriple_pure_privateStructuralHit_any_stable table _
      | ordinaryHit =>
          cases rightResult with
          | stopped rightReason =>
              cases rightReason with
              | privateStructuralHit => contradiction
              | ordinaryHit => exact relTriple_pure_pure trivial
              | fuelExhausted => exact relTriple_pure_pure trivial
          | done rightResult =>
              simp only
              rw [hrelation.1.1]
              exact relTriple_runDirectResolvedDetailed_of_right_materializedDoomed_stable table
                (pure (.stopped .ordinaryHit))
                (rightNext rightResult.value.1 rightResult.value.2)
                rightResult.context rightResult.remaining hrelation.1.2 hrelation.2
      | fuelExhausted =>
          cases rightResult with
          | stopped rightReason =>
              cases rightReason with
              | privateStructuralHit => contradiction
              | ordinaryHit => exact relTriple_pure_pure trivial
              | fuelExhausted => exact relTriple_pure_pure trivial
          | done rightResult =>
              simp only
              rw [hrelation.1.1]
              exact relTriple_runDirectResolvedDetailed_of_right_materializedDoomed_stable table
                (pure (.stopped .fuelExhausted))
                (rightNext rightResult.value.1 rightResult.value.2)
                rightResult.context rightResult.remaining hrelation.1.2 hrelation.2
  | done leftResult =>
      cases rightResult with
      | stopped rightReason =>
          cases rightReason with
          | privateStructuralHit => contradiction
          | ordinaryHit =>
              exact relTriple_any_pure_nonprivateStop_stable table _ .ordinaryHit (by decide)
          | fuelExhausted =>
              exact relTriple_any_pure_nonprivateStop_stable table _ .fuelExhausted (by decide)
      | done rightResult =>
          rcases hrelation with hcleanRelation | hdoomedRelation
          · exact hclean leftResult rightResult hleftSupport hrightSupport hcleanRelation
          · simp only
            rw [hdoomedRelation.1.1]
            exact relTriple_runDirectResolvedDetailed_of_right_materializedDoomed_stable table
              (runDirectResolvedDetailedFromTable leftResult.context leftResult.remaining
                leftResult.table (leftNext leftResult.value.1 leftResult.value.2))
              (rightNext rightResult.value.1 rightResult.value.2)
              rightResult.context rightResult.remaining hdoomedRelation.1.2
                hdoomedRelation.2

def OrdinaryMaterializedStableCouples (table : OtsSecretIndex → HashOutput)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ left right leftFuel rightFuel leftCache rightCache,
    FinalizationContextLE table left right →
    leftFuel ≤ rightFuel →
    ordinaryQueryCache leftCache = ordinaryQueryCache rightCache →
    left.state.revealed = right.state.revealed →
    LazyRevealProbe.ValuesLE left.state right.state →
    PublishedValues left.state →
    right = directDeferredContext right.state →
    RelTriple
      (runDirectResolvedDetailedFromTable left leftFuel table
        (computation.run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        (computation.run rightCache))
      (DirectDetailedOrdinaryStableRunEq table)

theorem ordinaryMaterializedStableCouples_pure
    (table : OtsSecretIndex → HashOutput) (value : α) :
    OrdinaryMaterializedStableCouples table
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) α) := by
  intro left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache hrevealed
    hvalues hpublished hrightMaterialized
  rw [StateT.run_pure, StateT.run_pure,
    runDirectResolvedDetailedFromTable_pure,
    runDirectResolvedDetailedFromTable_pure]
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

theorem OrdinaryMaterializedStableCouples.bind
    {table : OtsSecretIndex → HashOutput}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hleft : OrdinaryMaterializedStableCouples table left)
    (hnext : ∀ value, OrdinaryMaterializedStableCouples table (next value)) :
    OrdinaryMaterializedStableCouples table (left >>= next) := by
  intro leftContext rightContext leftFuel rightFuel leftCache rightCache hcontext hfuel hcache
    hrevealed hvalues hpublished hrightMaterialized
  rw [StateT.run_bind, StateT.run_bind]
  apply relTriple_runDirectResolvedDetailed_bind_stable table
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

theorem FinalizationViewLE.ensure
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewLE table left right) (coordinate : Coordinate) :
    FinalizationViewLE table
      { left with state := left.state.ensure coordinate }
      { right with state := right.state.ensure coordinate } where
  leftConsistent := hview.leftConsistent.ensure coordinate
  rightConsistent := hview.rightConsistent.ensure coordinate
  leftStarts := hview.leftStarts
  rightStarts := hview.rightStarts
  valueEq := hview.valueEq
  leftClean := hview.leftClean
  rightClean := hview.rightClean
  pendingLE := hview.pendingLE

theorem FinalizationContextLE.ensure
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextLE table left right) (coordinate : Coordinate) :
    FinalizationContextLE table
      { left with state := left.state.ensure coordinate }
      { right with state := right.state.ensure coordinate } where
  view := hcontext.view.ensure coordinate
  leftValid := hcontext.leftValid.ensure coordinate
  rightValid := hcontext.rightValid.ensure coordinate
  rightCompletable := hcontext.rightCompletable.ensure coordinate

theorem ordinaryMaterializedStableCouples_ensureCoordinate
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) :
    OrdinaryMaterializedStableCouples table (ensureCoordinate coordinate) := by
  intro left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache hrevealed
    hvalues hpublished hrightMaterialized
  unfold ensureCoordinate
  rw [StateT.run_liftM, StateT.run_liftM, LazyRevealProbe.ensureQuery,
    runDirectResolvedDetailedFromTable_ensure_query_bind,
    runDirectResolvedDetailedFromTable_ensure_query_bind,
    runDirectResolvedDetailedFromTable_pure,
    runDirectResolvedDetailedFromTable_pure]
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

theorem ordinaryMaterializedStableCouples_sequenceFin
    {table : OtsSecretIndex → HashOutput} {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcomponent : ∀ index,
      OrdinaryMaterializedStableCouples table (computation index)) :
    OrdinaryMaterializedStableCouples table (sequenceFin computation) := by
  induction n with
  | zero =>
      simpa [sequenceFin] using
        (ordinaryMaterializedStableCouples_pure table Fin.elim0 :
          OrdinaryMaterializedStableCouples table
            (pure Fin.elim0 : StateT SplitHashCache
              (OracleComp (LazyRevealProbe.World Coordinate)) (Fin 0 → α)))
  | succ n ih =>
      rw [sequenceFin]
      apply (hcomponent 0).bind
      intro head
      apply (ih (fun index : Fin n => computation index.succ)
        (fun index => hcomponent index.succ)).bind
      intro tail
      exact ordinaryMaterializedStableCouples_pure table
        (Fin.cases head tail : Fin (n + 1) → α)

set_option maxRecDepth 100000 in
theorem ordinaryMaterializedStableCouples_splitHashQuery_ordinary
    (table : OtsSecretIndex → HashOutput) (input : HashInput) :
    OrdinaryMaterializedStableCouples table
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
      exact ordinaryMaterializedStableCouples_pure table output left right leftFuel rightFuel
        leftCache rightCache hcontext hfuel hcache hrevealed hvalues hpublished
          hrightMaterialized
  | none =>
      have hright : rightCache (.ordinary input) = none := by
        rw [← hcacheAt]
        exact hlookup
      simp only [hright]
      rw [LazyRevealProbe.hashOutputQuery,
        runDirectResolvedDetailedFromTable_hashOutput_query_bind,
        runDirectResolvedDetailedFromTable_hashOutput_query_bind]
      apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
      intro leftOutput rightOutput houtput
      subst rightOutput
      simp only [runDirectResolvedDetailedFromTable]
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

theorem ordinaryMaterializedStableCouples_ordinaryHashImpl
    (table : OtsSecretIndex → HashOutput) (input : HashInput) :
    OrdinaryMaterializedStableCouples table (ordinaryHashImpl input) :=
  ordinaryMaterializedStableCouples_splitHashQuery_ordinary table input

theorem ordinaryMaterializedStableCouples_splitUniformImpl
    (table : OtsSecretIndex → HashOutput) (n : unifSpec.Domain) :
    OrdinaryMaterializedStableCouples table (splitUniformImpl n) := by
  intro left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache hrevealed
    hvalues hpublished hrightMaterialized
  unfold splitUniformImpl
  rw [StateT.run_liftM, StateT.run_liftM, LazyRevealProbe.uniformQuery,
    runDirectResolvedDetailedFromTable_uniform_query_bind,
    runDirectResolvedDetailedFromTable_uniform_query_bind]
  apply relTriple_bind (relTriple_refl
    (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
  intro leftOutput rightOutput houtput
  subst rightOutput
  exact ordinaryMaterializedStableCouples_pure table leftOutput left right leftFuel rightFuel
    leftCache rightCache hcontext hfuel hcache hrevealed hvalues hpublished
      hrightMaterialized

theorem ordinaryMaterializedStableCouples_simulateQ
    {table : OtsSecretIndex → HashOutput} {spec : OracleSpec ι}
    (impl : QueryImpl spec
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))))
    (hquery : ∀ query, OrdinaryMaterializedStableCouples table (impl query))
    (computation : OracleComp spec α) :
    OrdinaryMaterializedStableCouples table (simulateQ impl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure]
      exact ordinaryMaterializedStableCouples_pure table value
  | query_bind query next ih =>
      rw [simulateQ_query_bind]
      exact (hquery query).bind fun output => ih output

set_option maxRecDepth 100000 in
theorem ordinaryMaterializedStableCouples_revealCoordinateOutput_position
    (table : OtsSecretIndex → HashOutput) (position : Position) :
    OrdinaryMaterializedStableCouples table
      (revealCoordinateOutput (.position position)) := by
  intro left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache hrevealed
    hvalues hpublished hrightMaterialized
  cases hleftValue : left.state.values (.position position) with
  | some output =>
      have hrightValue : right.state.values (.position position) = some output :=
        hvalues (.position position) output hleftValue
      rw [runDirectResolvedDetailedFromTable_revealCoordinateOutput_of_value table
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
          rw [runDirectResolvedDetailedFromTable_revealCoordinateOutput_position_of_private
              table position left leftFuel leftCache output hleftValue hprivate,
            runDirectResolvedDetailedFromTable_revealCoordinateOutput_of_value table
              (.position position) right rightFuel rightCache output hrightValue]
          by_cases hhit : left.state.hitAt (.position position) output
          · simp only [hhit, ↓reduceIte]
            exact relTriple_pure_pure trivial
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
          rw [runDirectResolvedDetailedFromTable_revealCoordinateOutput_position_of_fresh
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

theorem ordinaryMaterializedStableCouples_revealPosition
    (table : OtsSecretIndex → HashOutput) (position : Position) :
    OrdinaryMaterializedStableCouples table (revealPosition position) := by
  unfold revealPosition revealCoordinate
  exact (ordinaryMaterializedStableCouples_revealCoordinateOutput_position table position).bind
    fun output => ordinaryMaterializedStableCouples_pure table (truncateHash output)

theorem DeferredCompletable.materialize_chainStart_value
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hcompletable : DeferredCompletable table context) (index : OtsSecretIndex) :
    DeferredCompletable table
      { context with
        state := context.state.materialize index.coordinate (table index) } := by
  rcases hcompletable with ⟨completion, hcompletion⟩
  refine ⟨completion, ?_, hcompletion.2.1, ?_, hcompletion.2.2.2⟩
  · intro coordinate output hvalue
    by_cases heq : coordinate = index.coordinate
    · subst coordinate
      have houtput : output = table index := by
        simpa [LazyRevealProbe.State.materialize] using hvalue.symm
      rw [houtput]
      exact hcompletion.2.2.2 index
    · apply hcompletion.1 coordinate output
      simpa [LazyRevealProbe.State.materialize, Function.update_of_ne heq] using hvalue
  · intro coordinate candidate hmember
    apply hcompletion.2.2.1 coordinate candidate
    change (coordinate, candidate) ∈ context.state.pendingAway index.coordinate at hmember
    exact (Finset.mem_filter.1 hmember).1

set_option maxRecDepth 100000 in
theorem FinalizationViewLE.materialize_chainStart_left
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewLE table left right) (index : OtsSecretIndex) :
    FinalizationViewLE table
      { left with state := left.state.materialize index.coordinate (table index) } right := by
  let materialized : DeferredContext :=
    { left with state := left.state.materialize index.coordinate (table index) }
  have hresolved : resolvedCompletionValue table materialized =
      resolvedCompletionValue table left := by
    funext coordinate
    cases coordinate with
    | chainStart => rfl
    | position position =>
        simp [materialized, resolvedCompletionValue, DeferredContext.positionValue,
          LazyRevealProbe.State.materialize, OtsSecretIndex.coordinate]
  refine
    { leftConsistent := ?_
      rightConsistent := hview.rightConsistent
      leftStarts := hview.leftStarts.materialize_start index
      rightStarts := hview.rightStarts
      valueEq := hresolved.trans hview.valueEq
      leftClean := ?_
      rightClean := hview.rightClean
      pendingLE := ?_ }
  · intro position output hvalue
    apply hview.leftConsistent position output
    simpa [materialized, LazyRevealProbe.State.materialize, OtsSecretIndex.coordinate] using
      hvalue
  · intro coordinate output hvalue
    have horiginal : resolvedCompletionValue table left coordinate = some output := by
      rw [← hresolved]
      exact hvalue
    by_cases heq : coordinate = index.coordinate
    · subst coordinate
      change ¬(left.state.clearPending index.coordinate).hitAt index.coordinate output
      exact not_hitAt_clearPending_self left.state index.coordinate output
    · change ¬(left.state.clearPending index.coordinate).hitAt coordinate output
      exact (hitAt_clearPending_of_ne left.state index.coordinate coordinate output heq).not.mpr
        (hview.leftClean coordinate output horiginal)
  · intro coordinate hvalue candidate hcandidate
    have horiginal : resolvedCompletionValue table left coordinate = none := by
      rw [← hresolved]
      exact hvalue
    have hne : coordinate ≠ index.coordinate := by
      intro heq
      subst coordinate
      rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
      change some (table ⟨lay, tree, leafIdx, chainIdx⟩) = none at hvalue
      contradiction
    have hbase : candidate ∈ left.state.pendingAt coordinate := by
      change candidate ∈
        (left.state.clearPending index.coordinate).pendingAt coordinate at hcandidate
      rw [pendingAt_clearPending_of_ne left.state index.coordinate coordinate hne] at hcandidate
      exact hcandidate
    exact hview.pendingLE coordinate horiginal hbase

set_option maxRecDepth 100000 in
theorem FinalizationViewLE.materialize_chainStart_right
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewLE table left right) (index : OtsSecretIndex) :
    FinalizationViewLE table left
      { right with state := right.state.materialize index.coordinate (table index) } := by
  let materialized : DeferredContext :=
    { right with state := right.state.materialize index.coordinate (table index) }
  have hresolved : resolvedCompletionValue table materialized =
      resolvedCompletionValue table right := by
    funext coordinate
    cases coordinate with
    | chainStart => rfl
    | position position =>
        simp [materialized, resolvedCompletionValue, DeferredContext.positionValue,
          LazyRevealProbe.State.materialize, OtsSecretIndex.coordinate]
  refine
    { leftConsistent := hview.leftConsistent
      rightConsistent := ?_
      leftStarts := hview.leftStarts
      rightStarts := hview.rightStarts.materialize_start index
      valueEq := hview.valueEq.trans hresolved.symm
      leftClean := hview.leftClean
      rightClean := ?_
      pendingLE := ?_ }
  · intro position output hvalue
    apply hview.rightConsistent position output
    simpa [materialized, LazyRevealProbe.State.materialize, OtsSecretIndex.coordinate] using
      hvalue
  · intro coordinate output hvalue
    have horiginal : resolvedCompletionValue table right coordinate = some output := by
      rw [← hresolved]
      exact hvalue
    by_cases heq : coordinate = index.coordinate
    · subst coordinate
      change ¬(right.state.clearPending index.coordinate).hitAt index.coordinate output
      exact not_hitAt_clearPending_self right.state index.coordinate output
    · change ¬(right.state.clearPending index.coordinate).hitAt coordinate output
      exact (hitAt_clearPending_of_ne right.state index.coordinate coordinate output heq).not.mpr
        (hview.rightClean coordinate output horiginal)
  · intro coordinate hvalue candidate hcandidate
    have hne : coordinate ≠ index.coordinate := by
      intro heq
      subst coordinate
      rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
      change some (table ⟨lay, tree, leafIdx, chainIdx⟩) = none at hvalue
      contradiction
    have hrightValue : resolvedCompletionValue table right coordinate = none := by
      rw [← hview.valueEq]
      exact hvalue
    have hleftValue : resolvedCompletionValue table left coordinate = none := by
      exact hvalue
    have hbase := hview.pendingLE coordinate hleftValue hcandidate
    change candidate ∈
      (right.state.clearPending index.coordinate).pendingAt coordinate
    rw [pendingAt_clearPending_of_ne right.state index.coordinate coordinate hne]
    exact hbase

theorem FinalizationContextLE.materialize_chainStart_left
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextLE table left right) (index : OtsSecretIndex) :
    FinalizationContextLE table
      { left with state := left.state.materialize index.coordinate (table index) } right where
  view := hcontext.view.materialize_chainStart_left index
  leftValid := by
    rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
    exact hcontext.leftValid.materialize_chainStart lay tree leafIdx chainIdx
      (table ⟨lay, tree, leafIdx, chainIdx⟩)
  rightValid := hcontext.rightValid
  rightCompletable := hcontext.rightCompletable

theorem FinalizationContextLE.materialize_chainStart_right
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextLE table left right) (index : OtsSecretIndex) :
    FinalizationContextLE table left
      { right with state := right.state.materialize index.coordinate (table index) } where
  view := hcontext.view.materialize_chainStart_right index
  leftValid := hcontext.leftValid
  rightValid := by
    rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
    exact hcontext.rightValid.materialize_chainStart lay tree leafIdx chainIdx
      (table ⟨lay, tree, leafIdx, chainIdx⟩)
  rightCompletable := hcontext.rightCompletable.materialize_chainStart_value index

theorem FinalizationContextLE.materialize_chainStart_both
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextLE table left right) (index : OtsSecretIndex) :
    FinalizationContextLE table
      { left with state := left.state.materialize index.coordinate (table index) }
      { right with state := right.state.materialize index.coordinate (table index) } :=
  (hcontext.materialize_chainStart_left index).materialize_chainStart_right index

theorem runDirectResolvedDetailedFromTable_revealCoordinateOutput_chainStart_of_missing
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hmissing : context.state.values index.coordinate = none) :
    runDirectResolvedDetailedFromTable context fuel table
        ((revealCoordinateOutput index.coordinate).run cache) =
      if context.state.hitAt index.coordinate (table index) then
        pure (.stopped .ordinaryHit)
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
  rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind]
  simp only [StateT.run_liftM]
  rw [LazyRevealProbe.revealQuery,
    runDirectResolvedDetailedFromTable_reveal_query_bind]
  by_cases hhit : context.state.hitAt
      (.chainStart lay tree leafIdx chainIdx) (table ⟨lay, tree, leafIdx, chainIdx⟩) <;>
    simp [OtsSecretIndex.coordinate, hmissing, hhit, StateT.run_modify,
      runDirectResolvedDetailedFromTable]

set_option maxRecDepth 100000 in
theorem ordinaryMaterializedStableCouples_revealCoordinateOutput_chainStart
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex) :
    OrdinaryMaterializedStableCouples table
      (revealCoordinateOutput index.coordinate) := by
  intro left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache hrevealed
    hvalues hpublished hrightMaterialized
  cases hleftValue : left.state.values index.coordinate with
  | some output =>
      have hrightValue : right.state.values index.coordinate = some output :=
        hvalues index.coordinate output hleftValue
      rw [runDirectResolvedDetailedFromTable_revealCoordinateOutput_of_value table
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
      rw [runDirectResolvedDetailedFromTable_revealCoordinateOutput_chainStart_of_missing
        table index left leftFuel leftCache hleftValue, if_neg hleftMiss]
      cases hrightValue : right.state.values index.coordinate with
      | some output =>
          have houtput : output = table index := by
            exact hcontext.view.rightStarts index output hrightValue
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

theorem ordinaryMaterializedStableCouples_revealCoordinate
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) :
    OrdinaryMaterializedStableCouples table (revealCoordinate coordinate) := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      unfold revealCoordinate
      exact (ordinaryMaterializedStableCouples_revealCoordinateOutput_chainStart table
        ⟨lay, tree, leafIdx, chainIdx⟩).bind fun output =>
          ordinaryMaterializedStableCouples_pure table (truncateHash output)
  | position position =>
      exact ordinaryMaterializedStableCouples_revealPosition table position

theorem ordinaryMaterializedStableCouples_revealCoordinateOutput
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) :
    OrdinaryMaterializedStableCouples table (revealCoordinateOutput coordinate) := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      exact ordinaryMaterializedStableCouples_revealCoordinateOutput_chainStart table
        ⟨lay, tree, leafIdx, chainIdx⟩
  | position position =>
      exact ordinaryMaterializedStableCouples_revealCoordinateOutput_position table position

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_publishCoordinate_then_pure_stable
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (value : α) (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hleftValue : ∃ output, left.state.values coordinate = some output)
    (hrightMaterialized : right = directDeferredContext right.state) :
    RelTriple
      (runDirectResolvedDetailedFromTable left leftFuel table
        ((publishCoordinate coordinate >>= fun _ => pure value).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((publishCoordinate coordinate >>= fun _ => pure value).run rightCache))
      (DirectDetailedOrdinaryStableRunEq table) := by
  obtain ⟨output, hleftValue⟩ := hleftValue
  have hrightValue : right.state.values coordinate = some output :=
    hvalues coordinate output hleftValue
  unfold publishCoordinate
  rw [StateT.run_bind, StateT.run_bind]
  simp only [StateT.run_liftM]
  simp only [StateT.run_pure, bind_assoc, pure_bind]
  unfold LazyRevealProbe.publishQuery
  rw [runDirectResolvedDetailedFromTable_publish_query_bind,
    runDirectResolvedDetailedFromTable_publish_query_bind]
  rw [runDirectResolvedDetailedFromTable_pure,
    runDirectResolvedDetailedFromTable_pure]
  apply relTriple_pure_pure
  left
  exact
    { value_eq := rfl
      context_le := hcontext.publish coordinate
      remaining_le := hfuel
      left_table := rfl
      right_table := rfl
      cache_eq := hcache
      revealed_eq := by
        simpa [LazyRevealProbe.State.publish] using congrArg (insert coordinate) hrevealed
      values_le := by
        intro other otherOutput hvalue
        exact hvalues other otherOutput hvalue
      left_published := hpublished.publish_of_value coordinate output hleftValue
      right_materialized := by
        rw [hrightMaterialized]
        simp [directDeferredContext, directDeferredValues_publish] }

set_option maxRecDepth 100000 in
theorem value_of_done_runDirectResolvedDetailedFromTable_revealCoordinateOutput
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (result : ResolvedRunResult (HashOutput × SplitHashCache))
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table
        ((revealCoordinateOutput coordinate).run cache))) :
    result.context.state.values coordinate = some result.value.1 := by
  cases hvalue : context.state.values coordinate with
  | some output =>
      rw [runDirectResolvedDetailedFromTable_revealCoordinateOutput_of_value table
        coordinate context fuel cache output hvalue] at hresult
      simp at hresult
      subst result
      exact hvalue
  | none =>
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
          have hmissing : context.state.values index.coordinate = none := by
            simpa [index, OtsSecretIndex.coordinate] using hvalue
          change DirectDetailedResult.done result ∈ support
            (runDirectResolvedDetailedFromTable context fuel table
              ((revealCoordinateOutput index.coordinate).run cache)) at hresult
          rw [runDirectResolvedDetailedFromTable_revealCoordinateOutput_chainStart_of_missing
            table index context fuel cache hmissing] at hresult
          by_cases hhit : context.state.hitAt index.coordinate (table index)
          · simp [hhit] at hresult
          · simp [hhit] at hresult
            subst result
            simp [LazyRevealProbe.State.materialize, index, OtsSecretIndex.coordinate]
      | position position =>
          cases hprivate : context.values position with
          | some output =>
              rw [runDirectResolvedDetailedFromTable_revealCoordinateOutput_position_of_private
                table position context fuel cache output hvalue hprivate] at hresult
              by_cases hhit : context.state.hitAt (.position position) output
              · simp [hhit] at hresult
              · simp [hhit] at hresult
                subst result
                simp [LazyRevealProbe.State.materialize]
          | none =>
              rw [runDirectResolvedDetailedFromTable_revealCoordinateOutput_position_of_fresh
                table position context fuel cache hvalue hprivate,
                mem_support_bind_iff] at hresult
              obtain ⟨output, _houtput, hrest⟩ := hresult
              by_cases hhit : context.state.hitAt (.position position) output
              · simp [hhit] at hrest
              · simp [hhit] at hrest
                subst result
                simp [LazyRevealProbe.State.materialize]

set_option maxRecDepth 100000 in
theorem ordinaryMaterializedStableCouples_revealPublishedCoordinate
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) :
    OrdinaryMaterializedStableCouples table (revealPublishedCoordinate coordinate) := by
  intro left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache hrevealed
    hvalues hpublished hrightMaterialized
  unfold revealPublishedCoordinate revealCoordinate
  simp only [bind_assoc, pure_bind]
  rw [StateT.run_bind, StateT.run_bind]
  apply relTriple_runDirectResolvedDetailed_bind_with_support_stable table
    ((revealCoordinateOutput coordinate).run leftCache)
    ((revealCoordinateOutput coordinate).run rightCache)
    (fun output cache =>
      ((publishCoordinate coordinate >>= fun _ => pure (truncateHash output)).run cache))
    (fun output cache =>
      ((publishCoordinate coordinate >>= fun _ => pure (truncateHash output)).run cache))
    left right leftFuel rightFuel
  · exact ordinaryMaterializedStableCouples_revealCoordinateOutput table coordinate
      left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache hrevealed hvalues
        hpublished hrightMaterialized
  · intro leftResult rightResult hleftSupport _hrightSupport hrelation
    have hleftValue :=
      value_of_done_runDirectResolvedDetailedFromTable_revealCoordinateOutput table coordinate
        left leftFuel leftCache leftResult hleftSupport
    rw [hrelation.left_table, hrelation.right_table, ← hrelation.value_eq]
    exact relTriple_runDirectResolvedDetailed_publishCoordinate_then_pure_stable table
      coordinate (truncateHash leftResult.value.1) leftResult.context rightResult.context
      leftResult.remaining rightResult.remaining leftResult.value.2 rightResult.value.2
      hrelation.context_le hrelation.remaining_le hrelation.cache_eq hrelation.revealed_eq
      hrelation.values_le hrelation.left_published ⟨leftResult.value.1, hleftValue⟩
      hrelation.right_materialized

theorem ordinaryMaterializedStableCouples_ordinaryRomImpl
    (table : OtsSecretIndex → HashOutput) (query : OracleWorld.Domain) :
    OrdinaryMaterializedStableCouples table (ordinaryRomImpl query) := by
  cases query with
  | inl n => exact ordinaryMaterializedStableCouples_splitUniformImpl table n
  | inr input => exact ordinaryMaterializedStableCouples_ordinaryHashImpl table input

theorem ordinaryMaterializedStableCouples_ensureFullChain
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    OrdinaryMaterializedStableCouples table
      (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  apply (ordinaryMaterializedStableCouples_sequenceFin
    (fun step : ChainStep =>
      ensureCoordinate (.position (.chain lay tree leafIdx chainIdx step)))
    (fun step => ordinaryMaterializedStableCouples_ensureCoordinate table
      (.position (.chain lay tree leafIdx chainIdx step)))).bind
  intro _
  exact ordinaryMaterializedStableCouples_pure table ()

theorem ordinaryMaterializedStableCouples_ensureOtsLeaf
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    OrdinaryMaterializedStableCouples table (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  apply (ordinaryMaterializedStableCouples_sequenceFin
    (fun chainIdx : ChainIndex => ensureFullChain lay tree leafIdx chainIdx)
    (fun chainIdx => ordinaryMaterializedStableCouples_ensureFullChain table lay tree leafIdx
      chainIdx)).bind
  intro _
  exact ordinaryMaterializedStableCouples_ensureCoordinate table
    (.position (.leaf lay tree leafIdx))

theorem ordinaryMaterializedStableCouples_ensureTreeNode
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx,
      OrdinaryMaterializedStableCouples table (ensureTreeNode lay tree level nodeIdx)
  | 0, nodeIdx =>
      ordinaryMaterializedStableCouples_ensureOtsLeaf table lay tree (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      apply (ordinaryMaterializedStableCouples_ensureTreeNode table lay tree level
        (2 * nodeIdx)).bind
      intro _
      apply (ordinaryMaterializedStableCouples_ensureTreeNode table lay tree level
        (2 * nodeIdx + 1)).bind
      intro _
      by_cases hlevel : level < maxLayerHeight
      · rw [dif_pos hlevel]
        exact ordinaryMaterializedStableCouples_ensureCoordinate table
          (.position (.node lay tree ⟨level, hlevel⟩ (leafOfNat nodeIdx)))
      · rw [dif_neg hlevel]
        exact ordinaryMaterializedStableCouples_pure table ()

theorem ordinaryMaterializedStableCouples_maskedTreeNode
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (level nodeIdx : Nat) :
    OrdinaryMaterializedStableCouples table (maskedTreeNode lay tree level nodeIdx) := by
  unfold maskedTreeNode
  apply (ordinaryMaterializedStableCouples_ensureTreeNode table lay tree level nodeIdx).bind
  intro _
  cases level with
  | zero =>
      exact ordinaryMaterializedStableCouples_revealPosition table
        (.leaf lay tree (leafOfNat nodeIdx))
  | succ current =>
      by_cases hlevel : current < maxLayerHeight
      · simp only [hlevel, ↓reduceDIte]
        exact ordinaryMaterializedStableCouples_revealPosition table
          (.node lay tree ⟨current, hlevel⟩ (leafOfNat nodeIdx))
      · simp only [hlevel, ↓reduceDIte]
        exact ordinaryMaterializedStableCouples_pure table 0

theorem ordinaryMaterializedStableCouples_maskedTreeRoot
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) :
    OrdinaryMaterializedStableCouples table (maskedTreeRoot lay tree) := by
  unfold maskedTreeRoot
  exact ordinaryMaterializedStableCouples_maskedTreeNode table lay tree (layerHeight lay) 0

theorem ordinaryMaterializedStableCouples_ensureChainPrefix
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (digit : Digit) :
    OrdinaryMaterializedStableCouples table
      (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  unfold ensureChainPrefix
  apply (ordinaryMaterializedStableCouples_sequenceFin
    (fun step : ChainStep =>
      if step.val < digit.val then
        ensureCoordinate (.position (.chain lay tree leafIdx chainIdx step))
      else pure ())
    (fun step => by
      by_cases hstep : step.val < digit.val
      · rw [if_pos hstep]
        exact ordinaryMaterializedStableCouples_ensureCoordinate table
          (.position (.chain lay tree leafIdx chainIdx step))
      · rw [if_neg hstep]
        exact ordinaryMaterializedStableCouples_pure table ())).bind
  intro _
  exact ordinaryMaterializedStableCouples_pure table ()

theorem ordinaryMaterializedStableCouples_ensureTreePath
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    OrdinaryMaterializedStableCouples table (ensureTreePath lay tree leafIdx) := by
  unfold ensureTreePath
  apply (ordinaryMaterializedStableCouples_sequenceFin
    (fun level : Fin maxLayerHeight =>
      if level.val < layerHeight lay then
        ensureTreeNode lay tree level.val
          (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
      else pure ())
    (fun level => by
      by_cases hlevel : level.val < layerHeight lay
      · rw [if_pos hlevel]
        exact ordinaryMaterializedStableCouples_ensureTreeNode table lay tree level.val
          (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
      · rw [if_neg hlevel]
        exact ordinaryMaterializedStableCouples_pure table ())).bind
  intro _
  exact ordinaryMaterializedStableCouples_pure table ()

theorem ordinaryMaterializedStableCouples_maskedOtsSignFrom
    (table : OtsSecretIndex → HashOutput) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    ∀ attempts counter,
      OrdinaryMaterializedStableCouples table
        (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
  | 0, counter => by
      rw [maskedOtsSignFrom]
      exact ordinaryMaterializedStableCouples_pure table none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom]
      have hencoded := ordinaryMaterializedStableCouples_simulateQ ordinaryHashImpl
        (ordinaryMaterializedStableCouples_ordinaryHashImpl table)
        (encode parameter lay tree leafIdx message
          (BitVec.ofNat counterBits counter))
      apply hencoded.bind
      intro encoded
      cases encoded with
      | none =>
          exact ordinaryMaterializedStableCouples_maskedOtsSignFrom table parameter lay tree
            leafIdx message attempts (counter + 1)
      | some encoding =>
          apply (ordinaryMaterializedStableCouples_sequenceFin
            (fun chainIdx => ensureChainPrefix lay tree leafIdx chainIdx
              (encoding chainIdx))
            (fun chainIdx => ordinaryMaterializedStableCouples_ensureChainPrefix table lay tree
              leafIdx chainIdx (encoding chainIdx))).bind
          intro _
          exact ordinaryMaterializedStableCouples_pure table
            (some (BitVec.ofNat counterBits counter, encoding))

theorem ordinaryMaterializedStableCouples_maskedOtsSign
    (table : OtsSecretIndex → HashOutput) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    OrdinaryMaterializedStableCouples table
      (maskedOtsSign parameter lay tree leafIdx message) :=
  ordinaryMaterializedStableCouples_maskedOtsSignFrom table parameter lay tree leafIdx message
    encodingAttemptLimit 0

theorem ordinaryMaterializedStableCouples_maskedLayerMessage
    (table : OtsSecretIndex → HashOutput) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay : Layer) :
    OrdinaryMaterializedStableCouples table
      (maskedLayerMessage parameter ftsSecret index lay) := by
  unfold maskedLayerMessage
  by_cases hbelow : lay.val + 1 < numLayers
  · rw [dif_pos hbelow]
    exact ordinaryMaterializedStableCouples_maskedTreeRoot table ⟨lay.val + 1, hbelow⟩
      (treeIndexAt index ⟨lay.val + 1, hbelow⟩)
  · rw [dif_neg hbelow]
    exact ordinaryMaterializedStableCouples_simulateQ ordinaryHashImpl
      (ordinaryMaterializedStableCouples_ordinaryHashImpl table)
      (ftsKey parameter index (ftsSecret index))

theorem ordinaryMaterializedStableCouples_maskedSignLayer
    (table : OtsSecretIndex → HashOutput) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay : Layer) :
    OrdinaryMaterializedStableCouples table
      (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayer
  apply (ordinaryMaterializedStableCouples_maskedLayerMessage table parameter ftsSecret index
    lay).bind
  intro message
  apply (ordinaryMaterializedStableCouples_maskedOtsSign table parameter lay
    (treeIndexAt index lay) (leafIndexAt index lay) message).bind
  intro selected
  cases selected with
  | none => exact ordinaryMaterializedStableCouples_pure table none
  | some selected =>
      apply (ordinaryMaterializedStableCouples_ensureTreePath table lay
        (treeIndexAt index lay) (leafIndexAt index lay)).bind
      intro _
      exact ordinaryMaterializedStableCouples_pure table (some selected)

set_option maxRecDepth 100000 in
theorem ordinaryMaterializedStableCouples_revealLayerValues
    (table : OtsSecretIndex → HashOutput) (index : Index) (lay : Layer)
    (encoding : ChainIndex → Digit) :
    OrdinaryMaterializedStableCouples table (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  apply (ordinaryMaterializedStableCouples_sequenceFin
    (fun chainIdx : ChainIndex =>
      revealPublishedCoordinate
        (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay)
          chainIdx (encoding chainIdx)))
    (fun chainIdx => ordinaryMaterializedStableCouples_revealPublishedCoordinate table
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay)
        chainIdx (encoding chainIdx)))).bind
  intro values
  apply (ordinaryMaterializedStableCouples_sequenceFin
    (fun level : Fin maxLayerHeight =>
      if level.val < layerHeight lay then
        match level.val with
        | 0 => revealPublishedCoordinate (.position (.leaf lay (treeIndexAt index lay)
            (leafOfNat (Nat.xor (leafIndexAt index lay).val 1))))
        | current + 1 =>
            if hcurrent : current < maxLayerHeight then
              revealPublishedCoordinate (.position (.node lay (treeIndexAt index lay)
                ⟨current, hcurrent⟩ (leafOfNat
                  (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
            else pure 0
      else pure 0)
    (fun level => by
      by_cases hinLayer : level.val < layerHeight lay
      · rw [if_pos hinLayer]
        cases hvalue : level.val with
        | zero =>
            exact ordinaryMaterializedStableCouples_revealPublishedCoordinate table
              (.position (.leaf lay (treeIndexAt index lay)
                (leafOfNat (Nat.xor (leafIndexAt index lay).val 1))))
        | succ current =>
            have hcurrent : current < maxLayerHeight := by
              have := level.isLt
              omega
            simp only
            rw [dif_pos hcurrent]
            exact ordinaryMaterializedStableCouples_revealPublishedCoordinate table
              (.position (.node lay (treeIndexAt index lay) ⟨current, hcurrent⟩
                (leafOfNat
                  (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
      · rw [if_neg hinLayer]
        exact ordinaryMaterializedStableCouples_pure table 0)).bind
  intro path
  exact ordinaryMaterializedStableCouples_pure table (values, path)

set_option maxRecDepth 100000 in
theorem ordinaryMaterializedStableCouples_maskedSignAfterDigest
    (table : OtsSecretIndex → HashOutput) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    OrdinaryMaterializedStableCouples table
      (maskedSignAfterDigest parameter ftsSecret randomness index leaves) := by
  unfold maskedSignAfterDigest
  apply (ordinaryMaterializedStableCouples_simulateQ ordinaryHashImpl
    (ordinaryMaterializedStableCouples_ordinaryHashImpl table)
    (ftsOpen parameter index leaves (ftsSecret index))).bind
  intro ftsPath
  apply (ordinaryMaterializedStableCouples_sequenceFin
    (fun lay : Layer => maskedSignLayer parameter ftsSecret index lay)
    (fun lay => ordinaryMaterializedStableCouples_maskedSignLayer table parameter ftsSecret
      index lay)).bind
  intro layers
  cases hparts : traverseOption layers with
  | none => exact ordinaryMaterializedStableCouples_pure table none
  | some parts =>
      apply (ordinaryMaterializedStableCouples_sequenceFin
        (fun lay : Layer => revealLayerValues index lay (parts lay).2)
        (fun lay => ordinaryMaterializedStableCouples_revealLayerValues table index lay
          (parts lay).2)).bind
      intro revealed
      let signature : Signature :=
        { randomness := randomness
          ftsSecret := fun tree => ftsSecret index tree (leaves (ftsIndexOf tree))
          ftsPath := ftsPath
          counter := fun lay => (parts lay).1
          chainValue := fun lay => (revealed lay).1
          authPath := flattenPaths fun lay => (revealed lay).2 }
      exact ordinaryMaterializedStableCouples_pure table (some signature)

set_option maxRecDepth 100000 in
theorem ordinaryMaterializedStableCouples_maskedSign
    (table : OtsSecretIndex → HashOutput) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message) :
    OrdinaryMaterializedStableCouples table
      (maskedSign parameter root ftsSecret message) := by
  unfold maskedSign
  apply (ordinaryMaterializedStableCouples_simulateQ ordinaryRomImpl
    (ordinaryMaterializedStableCouples_ordinaryRomImpl table)
    (signDigestLoop digestAttemptLimit
      ⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩ message)).bind
  intro selected
  cases selected with
  | none => exact ordinaryMaterializedStableCouples_pure table none
  | some data =>
      exact ordinaryMaterializedStableCouples_maskedSignAfterDigest table parameter ftsSecret
        data.1 data.2.1 data.2.2

theorem ordinaryMaterializedStableCouples_maskedSigningImpl
    (table : OtsSecretIndex → HashOutput) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message) :
    OrdinaryMaterializedStableCouples table
      (maskedSigningImpl parameter root ftsSecret message) :=
  ordinaryMaterializedStableCouples_maskedSign table parameter root ftsSecret message

end SphincsSecurity.Concrete.OtsProbeSimulation
