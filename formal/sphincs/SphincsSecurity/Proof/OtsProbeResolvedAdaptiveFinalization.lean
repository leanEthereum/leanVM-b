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
