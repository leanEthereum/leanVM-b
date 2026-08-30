import SphincsSecurity.Proof.OtsProbeResolvedBoundaryOrdinary

/-!
# One-sided ordinary boundary refinement

The canonical side can spend a probe at an unpublished structural value which the materialized
side can already read. A miss preserves finalization semantics while consuming one unit of fuel;
a hit is exactly the private structural outcome and imposes no ordinary-failure obligation.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem FinalizationViewEq.addPending_left_of_resolved
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewEq table left right)
    (coordinate : Coordinate) (candidate : Digest) (output : HashOutput)
    (hvalue : resolvedCompletionValue table left coordinate = some output)
    (hmiss : truncateHash output ≠ candidate) :
    FinalizationViewEq table
      { left with state := left.state.addPending coordinate candidate } right := by
  refine
    { leftConsistent := hview.leftConsistent.addPending coordinate candidate
      rightConsistent := hview.rightConsistent
      leftStarts := hview.leftStarts.addPending coordinate candidate
      rightStarts := hview.rightStarts
      valueEq := hview.valueEq
      leftClean := ?_
      rightClean := hview.rightClean
      pendingEq := ?_ }
  · intro other otherOutput hotherValue hhit
    by_cases heq : other = coordinate
    · subst other
      have houtput : otherOutput = output := by
        change resolvedCompletionValue table left coordinate = some otherOutput at hotherValue
        rw [hvalue] at hotherValue
        exact (Option.some.inj hotherValue).symm
      subst otherOutput
      rw [hitAt_addPending_self_iff] at hhit
      exact hhit.elim (hview.leftClean coordinate output hvalue) hmiss
    · have hhitBase : left.state.hitAt other otherOutput := by
        rw [hitAt_addPending_of_ne left.state coordinate other candidate otherOutput (Ne.symm heq)]
          at hhit
        exact hhit
      exact hview.leftClean other otherOutput hotherValue hhitBase
  · intro other hnone
    have hne : other ≠ coordinate := by
      intro heq
      subst other
      change resolvedCompletionValue table left coordinate = none at hnone
      rw [hvalue] at hnone
      contradiction
    calc
      (left.state.addPending coordinate candidate).pendingAt other =
          left.state.pendingAt other := by
        ext digest
        simp [LazyRevealProbe.State.pendingAt, LazyRevealProbe.State.addPending, hne]
      _ = right.state.pendingAt other := hview.pendingEq other hnone

theorem FinalizationContextEq.addPending_left_of_resolved
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextEq table (some left) (some right))
    (coordinate : Coordinate) (candidate : Digest) (output : HashOutput)
    (hvalue : resolvedCompletionValue table left coordinate = some output)
    (hmiss : truncateHash output ≠ candidate) :
    FinalizationContextEq table
      (some { left with state := left.state.addPending coordinate candidate })
      (some right) := by
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  obtain ⟨completion, hcompletion⟩ := hleftCompletable
  have hcompletionOutput : completion coordinate = output :=
    hcompletion.eq_resolvedCompletionValue coordinate output hvalue
  have hcompletion' : DeferredCompletion table
      { left with state := left.state.addPending coordinate candidate } completion :=
    hcompletion.addPending_of_avoids coordinate candidate (by
      rwa [hcompletionOutput])
  have hleftCompletable' : DeferredCompletable table
      { left with state := left.state.addPending coordinate candidate } :=
    ⟨completion, hcompletion'⟩
  exact
    ⟨hview.addPending_left_of_resolved coordinate candidate output hvalue hmiss,
      hleftValid.addPending_of_completable coordinate candidate hleftCompletable',
      hrightValid, hleftCompletable'⟩

structure FinalizationViewLE (table : OtsSecretIndex → HashOutput)
    (left right : DeferredContext) : Prop where
  leftConsistent : left.ValuesConsistent
  rightConsistent : right.ValuesConsistent
  leftStarts : StartTableAgrees left.state table
  rightStarts : StartTableAgrees right.state table
  valueEq : resolvedCompletionValue table left = resolvedCompletionValue table right
  leftClean : ∀ coordinate output,
    resolvedCompletionValue table left coordinate = some output →
      ¬left.state.hitAt coordinate output
  rightClean : ∀ coordinate output,
    resolvedCompletionValue table right coordinate = some output →
      ¬right.state.hitAt coordinate output
  pendingLE : ∀ coordinate,
    resolvedCompletionValue table left coordinate = none →
      left.state.pendingAt coordinate ⊆ right.state.pendingAt coordinate

theorem FinalizationViewLE.of_eq
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewEq table left right) :
    FinalizationViewLE table left right where
  leftConsistent := hview.leftConsistent
  rightConsistent := hview.rightConsistent
  leftStarts := hview.leftStarts
  rightStarts := hview.rightStarts
  valueEq := hview.valueEq
  leftClean := hview.leftClean
  rightClean := hview.rightClean
  pendingLE coordinate hnone := by
    rw [hview.pendingEq coordinate hnone]

theorem FinalizationViewLE.refl
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hvalid : context.Valid) (hstarts : StartTableAgrees context.state table)
    (hclean : ∀ coordinate output,
      resolvedCompletionValue table context coordinate = some output →
        ¬context.state.hitAt coordinate output) :
    FinalizationViewLE table context context :=
  FinalizationViewLE.of_eq
    (FinalizationViewEq.refl table context hvalid hstarts hclean)

theorem FinalizationViewLE.trans
    {table : OtsSecretIndex → HashOutput} {left middle right : DeferredContext}
    (hleft : FinalizationViewLE table left middle)
    (hright : FinalizationViewLE table middle right) :
    FinalizationViewLE table left right := by
  refine
    { leftConsistent := hleft.leftConsistent
      rightConsistent := hright.rightConsistent
      leftStarts := hleft.leftStarts
      rightStarts := hright.rightStarts
      valueEq := hleft.valueEq.trans hright.valueEq
      leftClean := hleft.leftClean
      rightClean := hright.rightClean
      pendingLE := ?_ }
  intro coordinate hvalue candidate hcandidate
  have hmiddleValue : resolvedCompletionValue table middle coordinate = none := by
    rw [← hleft.valueEq]
    exact hvalue
  exact hright.pendingLE coordinate hmiddleValue
    (hleft.pendingLE coordinate hvalue hcandidate)

theorem FinalizationViewLE.deferredCompletion_left
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewLE table left right)
    (completion : Coordinate → HashOutput)
    (hcompletion : DeferredCompletion table right completion) :
    DeferredCompletion table left completion := by
  refine ⟨?_, ?_, ?_, hcompletion.2.2.2⟩
  · intro coordinate output hvalue
    have hleftValue : resolvedCompletionValue table left coordinate = some output := by
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          have houtput := hview.leftStarts
            ⟨lay, tree, leafIdx, chainIdx⟩ output hvalue
          simp [resolvedCompletionValue, houtput]
      | position position =>
          simp [resolvedCompletionValue, DeferredContext.positionValue, hvalue]
    have hrightValue : resolvedCompletionValue table right coordinate = some output := by
      rw [← hview.valueEq]
      exact hleftValue
    exact hcompletion.eq_resolvedCompletionValue coordinate output hrightValue
  · intro position output hvalue
    have hleftValue : resolvedCompletionValue table left (.position position) =
        some output := by
      unfold resolvedCompletionValue DeferredContext.positionValue
      cases hstate : left.state.values (.position position) with
      | some cached =>
          have hsame := hview.leftConsistent position cached hstate
          rw [hsame] at hvalue
          have hcached : cached = output := Option.some.inj hvalue
          simp [hstate, hcached]
      | none => simpa [hstate] using hvalue
    have hrightValue : resolvedCompletionValue table right (.position position) =
        some output := by
      rw [← hview.valueEq]
      exact hleftValue
    exact hcompletion.eq_resolvedCompletionValue (.position position) output hrightValue
  · intro coordinate candidate hmember
    cases hvalue : resolvedCompletionValue table left coordinate with
    | some output =>
        have hrightValue : resolvedCompletionValue table right coordinate = some output := by
          rw [← hview.valueEq]
          exact hvalue
        have hcompletionOutput : completion coordinate = output :=
          hcompletion.eq_resolvedCompletionValue coordinate output hrightValue
        intro hhit
        apply hview.leftClean coordinate output hvalue
        unfold LazyRevealProbe.State.hitAt
        rw [LazyRevealProbe.State.mem_pendingAt_iff]
        have hcandidate : candidate = truncateHash output := by
          rw [← hhit, hcompletionOutput]
        simpa [hcandidate] using hmember
    | none =>
        have hrightValue : resolvedCompletionValue table right coordinate = none := by
          rw [← hview.valueEq]
          exact hvalue
        have hleftPending : candidate ∈ left.state.pendingAt coordinate :=
          (LazyRevealProbe.State.mem_pendingAt_iff left.state coordinate candidate).2 hmember
        have hrightPending : candidate ∈ right.state.pendingAt coordinate :=
          hview.pendingLE coordinate hvalue hleftPending
        exact hcompletion.2.2.1 coordinate candidate
          ((LazyRevealProbe.State.mem_pendingAt_iff right.state coordinate candidate).1
            hrightPending)

structure FinalizationContextLE (table : OtsSecretIndex → HashOutput)
    (left right : DeferredContext) : Prop where
  view : FinalizationViewLE table left right
  leftValid : left.Valid
  rightValid : right.Valid
  rightCompletable : DeferredCompletable table right

theorem FinalizationContextLE.of_eq
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextEq table (some left) (some right)) :
    FinalizationContextLE table left right := by
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  obtain ⟨completion, hcompletion⟩ := hleftCompletable
  exact
    { view := FinalizationViewLE.of_eq hview
      leftValid := hleftValid
      rightValid := hrightValid
      rightCompletable :=
        ⟨completion, (hview.deferredCompletion_iff completion).mp hcompletion⟩ }

theorem FinalizationContextLE.leftCompletable
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextLE table left right) :
    DeferredCompletable table left := by
  obtain ⟨completion, hcompletion⟩ := hcontext.rightCompletable
  exact ⟨completion, hcontext.view.deferredCompletion_left completion hcompletion⟩

theorem FinalizationViewLE.not_rightCompletable_of_not_leftCompletable
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewLE table left right)
    (hleft : ¬DeferredCompletable table left) :
    ¬DeferredCompletable table right := by
  rintro ⟨completion, hcompletion⟩
  exact hleft ⟨completion, hview.deferredCompletion_left completion hcompletion⟩

theorem FinalizationViewLE.addPending_right_of_completable
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewLE table left right) (coordinate : Coordinate)
    (candidate : Digest)
    (hcompletable : DeferredCompletable table
      { right with state := right.state.addPending coordinate candidate }) :
    FinalizationViewLE table left
      { right with state := right.state.addPending coordinate candidate } := by
  refine
    { leftConsistent := hview.leftConsistent
      rightConsistent := hview.rightConsistent.addPending coordinate candidate
      leftStarts := hview.leftStarts
      rightStarts := hview.rightStarts.addPending coordinate candidate
      valueEq := hview.valueEq
      leftClean := hview.leftClean
      rightClean := ?_
      pendingLE := ?_ }
  · intro other output hvalue hhit
    obtain ⟨completion, hcompletion⟩ := hcompletable
    have houtput := hcompletion.eq_resolvedCompletionValue other output hvalue
    have havoids := hcompletion.2.2.1
    unfold LazyRevealProbe.State.hitAt at hhit
    rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit
    exact havoids other (truncateHash output) hhit (by rw [houtput])
  · intro other hvalue digest hdigest
    have hbase := hview.pendingLE other hvalue hdigest
    rw [LazyRevealProbe.State.mem_pendingAt_iff] at hbase ⊢
    simp only [LazyRevealProbe.State.addPending, Finset.mem_insert]
    exact Or.inr hbase

theorem FinalizationContextLE.addPending_right_of_completable
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextLE table left right)
    (coordinate : Coordinate) (candidate : Digest)
    (hcompletable : DeferredCompletable table
      { right with state := right.state.addPending coordinate candidate }) :
    FinalizationContextLE table left
      { right with state := right.state.addPending coordinate candidate } where
  view := hcontext.view.addPending_right_of_completable coordinate candidate hcompletable
  leftValid := hcontext.leftValid
  rightValid := hcontext.rightValid.addPending_of_completable
    coordinate candidate hcompletable
  rightCompletable := hcompletable

theorem FinalizationViewLE.addPending_left_of_resolved
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewLE table left right)
    (coordinate : Coordinate) (candidate : Digest) (output : HashOutput)
    (hvalue : resolvedCompletionValue table left coordinate = some output)
    (hmiss : truncateHash output ≠ candidate) :
    FinalizationViewLE table
      { left with state := left.state.addPending coordinate candidate } right := by
  refine
    { leftConsistent := hview.leftConsistent.addPending coordinate candidate
      rightConsistent := hview.rightConsistent
      leftStarts := hview.leftStarts.addPending coordinate candidate
      rightStarts := hview.rightStarts
      valueEq := hview.valueEq
      leftClean := ?_
      rightClean := hview.rightClean
      pendingLE := ?_ }
  · intro other otherOutput hotherValue hhit
    by_cases heq : other = coordinate
    · subst other
      have houtput : otherOutput = output := by
        change resolvedCompletionValue table left coordinate = some otherOutput at hotherValue
        rw [hvalue] at hotherValue
        exact (Option.some.inj hotherValue).symm
      subst otherOutput
      rw [hitAt_addPending_self_iff] at hhit
      exact hhit.elim (hview.leftClean coordinate output hvalue) hmiss
    · have hhitBase : left.state.hitAt other otherOutput := by
        rw [hitAt_addPending_of_ne left.state coordinate other candidate otherOutput
          (Ne.symm heq)] at hhit
        exact hhit
      exact hview.leftClean other otherOutput hotherValue hhitBase
  · intro other hnone digest hdigest
    have hne : other ≠ coordinate := by
      intro heq
      subst other
      change resolvedCompletionValue table left coordinate = none at hnone
      rw [hvalue] at hnone
      contradiction
    have hbase : digest ∈ left.state.pendingAt other := by
      have hpending :
          (left.state.addPending coordinate candidate).pendingAt other =
            left.state.pendingAt other := by
        ext otherCandidate
        simp [LazyRevealProbe.State.pendingAt, LazyRevealProbe.State.addPending, hne]
      rw [← hpending]
      exact hdigest
    exact hview.pendingLE other hnone hbase

theorem FinalizationContextLE.addPending_left_of_resolved
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextLE table left right)
    (coordinate : Coordinate) (candidate : Digest) (output : HashOutput)
    (hvalue : resolvedCompletionValue table left coordinate = some output)
    (hmiss : truncateHash output ≠ candidate) :
    FinalizationContextLE table
      { left with state := left.state.addPending coordinate candidate } right := by
  obtain ⟨completion, hcompletion⟩ := hcontext.leftCompletable
  have hcompletionOutput : completion coordinate = output :=
    hcompletion.eq_resolvedCompletionValue coordinate output hvalue
  have hcompletion' : DeferredCompletion table
      { left with state := left.state.addPending coordinate candidate } completion :=
    hcompletion.addPending_of_avoids coordinate candidate (by
      rwa [hcompletionOutput])
  exact
    { view := hcontext.view.addPending_left_of_resolved
        coordinate candidate output hvalue hmiss
      leftValid := hcontext.leftValid.addPending_of_completable coordinate candidate
        ⟨completion, hcompletion'⟩
      rightValid := hcontext.rightValid
      rightCompletable := hcontext.rightCompletable }

theorem FinalizationViewLE.addPending_both_of_right_completable
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewLE table left right)
    (coordinate : Coordinate) (candidate : Digest)
    (hrightCompletable : DeferredCompletable table
      { right with state := right.state.addPending coordinate candidate }) :
    FinalizationViewLE table
      { left with state := left.state.addPending coordinate candidate }
      { right with state := right.state.addPending coordinate candidate } := by
  obtain ⟨completion, hrightCompletion⟩ := hrightCompletable
  have hrightBase := hrightCompletion.of_addPending coordinate candidate
  have hleftBase := hview.deferredCompletion_left completion hrightBase
  have havoids := hrightCompletion.2.2.1 coordinate candidate (by
    simp [LazyRevealProbe.State.addPending])
  have hleftCompletion :=
    hleftBase.addPending_of_avoids coordinate candidate havoids
  refine
    { leftConsistent := hview.leftConsistent.addPending coordinate candidate
      rightConsistent := hview.rightConsistent.addPending coordinate candidate
      leftStarts := hview.leftStarts.addPending coordinate candidate
      rightStarts := hview.rightStarts.addPending coordinate candidate
      valueEq := hview.valueEq
      leftClean := ?_
      rightClean := ?_
      pendingLE := ?_ }
  · intro other output hvalue hhit
    have houtput := hleftCompletion.eq_resolvedCompletionValue other output hvalue
    unfold LazyRevealProbe.State.hitAt at hhit
    rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit
    exact hleftCompletion.2.2.1 other (truncateHash output) hhit (by rw [houtput])
  · intro other output hvalue hhit
    have houtput := hrightCompletion.eq_resolvedCompletionValue other output hvalue
    unfold LazyRevealProbe.State.hitAt at hhit
    rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit
    exact hrightCompletion.2.2.1 other (truncateHash output) hhit (by rw [houtput])
  · intro other hvalue digest hdigest
    rw [LazyRevealProbe.State.mem_pendingAt_iff] at hdigest ⊢
    simp only [LazyRevealProbe.State.addPending, Finset.mem_insert] at hdigest ⊢
    rcases hdigest with hnew | hold
    · exact Or.inl hnew
    · right
      rw [← LazyRevealProbe.State.mem_pendingAt_iff] at hold ⊢
      exact hview.pendingLE other hvalue hold

theorem FinalizationContextLE.addPending_both_of_right_completable
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextLE table left right)
    (coordinate : Coordinate) (candidate : Digest)
    (hrightCompletable : DeferredCompletable table
      { right with state := right.state.addPending coordinate candidate }) :
    FinalizationContextLE table
      { left with state := left.state.addPending coordinate candidate }
      { right with state := right.state.addPending coordinate candidate } := by
  have hview := hcontext.view.addPending_both_of_right_completable
    coordinate candidate hrightCompletable
  have hleftCompletable : DeferredCompletable table
      { left with state := left.state.addPending coordinate candidate } := by
    obtain ⟨completion, hcompletion⟩ := hrightCompletable
    exact ⟨completion, hview.deferredCompletion_left completion hcompletion⟩
  exact
    { view := hview
      leftValid := hcontext.leftValid.addPending_of_completable coordinate candidate
        hleftCompletable
      rightValid := hcontext.rightValid.addPending_of_completable coordinate candidate
        hrightCompletable
      rightCompletable := hrightCompletable }

theorem FinalizationViewLE.privateValue_of_left_hidden_of_right_materialized
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewLE table left right) (position : Position)
    (output : HashOutput)
    (hleft : left.state.values (.position position) = none)
    (hright : right.state.values (.position position) = some output) :
    left.values position = some output := by
  have hposition : left.positionValue position = some output := by
    change resolvedCompletionValue table left (.position position) = some output
    rw [hview.valueEq]
    simp [resolvedCompletionValue, DeferredContext.positionValue, hright]
  simpa [DeferredContext.positionValue, hleft] using hposition

structure OrdinaryMaterializedRunEq (table : OtsSecretIndex → HashOutput)
    (left right : ResolvedRunResult (α × SplitHashCache)) : Prop where
  value_eq : left.value.1 = right.value.1
  context_le : FinalizationContextLE table left.context right.context
  remaining_le : left.remaining ≤ right.remaining
  left_table : left.table = table
  right_table : right.table = table
  cache_eq : ordinaryQueryCache left.value.2 = ordinaryQueryCache right.value.2
  revealed_eq : left.context.state.revealed = right.context.state.revealed
  values_le : LazyRevealProbe.ValuesLE left.context.state right.context.state
  left_published : PublishedValues left.context.state

def DirectDetailedOrdinaryRunEq (table : OtsSecretIndex → HashOutput) :
    DirectDetailedResult (α × SplitHashCache) →
      DirectDetailedResult (α × SplitHashCache) → Prop
  | .stopped .privateStructuralHit, _ => True
  | .stopped .ordinaryHit, .stopped .ordinaryHit => True
  | .stopped .ordinaryHit, .done right =>
      FinalizationDoomedRun table (some right)
  | .stopped .ordinaryHit, _ => False
  | .stopped .fuelExhausted, _ => False
  | .done _, .stopped .ordinaryHit => True
  | .done _, .stopped _ => False
  | .done left, .done right =>
      OrdinaryMaterializedRunEq table left right ∨
        PrivateStructuralHit left.context ∨
        FinalizationDoomedRun table (some right)

theorem relTriple_runDirectResolvedDetailed_pure_of_ordinaryMaterialized
    (table : OtsSecretIndex → HashOutput) (value : α)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state) :
    RelTriple
      (runDirectResolvedDetailedFromTable left leftFuel table
        ((pure value : StateT SplitHashCache
          (OracleComp (LazyRevealProbe.World Coordinate)) α).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((pure value : StateT SplitHashCache
          (OracleComp (LazyRevealProbe.World Coordinate)) α).run rightCache))
      (DirectDetailedOrdinaryRunEq table) := by
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
      left_published := hpublished }

theorem runDirectResolvedDetailedFromTable_peek_query
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (context : DeferredContext) (fuel : Nat) :
    runDirectResolvedDetailedFromTable context fuel table
        (liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.peek coordinate))) =
      pure (.done ⟨context, fuel, context.state.values coordinate, table⟩) := by
  rw [← bind_pure
    (liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
      (.peek coordinate)))]
  rw [runDirectResolvedDetailedFromTable_peek_query_bind,
    runDirectResolvedDetailedFromTable_pure]

theorem runDirectResolvedDetailedFromTable_peekCoordinate
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    runDirectResolvedDetailedFromTable context fuel table
        ((peekCoordinate coordinate).run cache) =
      pure (.done ⟨context, fuel,
        (truncateHash <$> context.state.values coordinate, cache), table⟩) := by
  unfold peekCoordinate
  rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind]
  simp only [StateT.run_liftM]
  unfold LazyRevealProbe.peekQuery
  rw [runDirectResolvedDetailedFromTable_bind,
    runDirectResolvedDetailedFromTable_peek_query]
  simp [runDirectResolvedDetailedFromTable_pure]

theorem runDirectResolvedDetailedFromTable_probeFirstMissingInputCoordinate_cons
    (table : OtsSecretIndex → HashOutput) (input : HashInput) (slot : Nat)
    (coordinate : Coordinate) (remaining : List Coordinate)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    runDirectResolvedDetailedFromTable context fuel table
        ((probeFirstMissingInputCoordinate input slot
          (coordinate :: remaining)).run cache) =
      match context.state.values coordinate with
      | none =>
          runDirectResolvedDetailedFromTable context fuel table
            ((probe ⟨coordinate, slotDigest slot input⟩).run cache)
      | some _ =>
          runDirectResolvedDetailedFromTable context fuel table
            ((probeFirstMissingInputCoordinate input (slot + 1) remaining).run cache) := by
  rw [probeFirstMissingInputCoordinate, StateT.run_bind,
    runDirectResolvedDetailedFromTable_bind]
  rw [runDirectResolvedDetailedFromTable_peekCoordinate]
  cases context.state.values coordinate <;> simp

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_pure_probe_right
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (candidate : Digest)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : leftFuel + 1 ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMissing : right.state.values coordinate = none) :
    RelTriple
      (runDirectResolvedDetailedFromTable left leftFuel table
        ((pure () : StateT SplitHashCache
          (OracleComp (LazyRevealProbe.World Coordinate)) Unit).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((probe ⟨coordinate, candidate⟩).run rightCache))
      (DirectDetailedOrdinaryRunEq table) := by
  obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (by omega : rightFuel ≠ 0)
  unfold probe
  rw [StateT.run_pure, StateT.run_liftM]
  unfold LazyRevealProbe.probeQuery
  simp only
  rw [runDirectResolvedDetailedFromTable_pure,
    runDirectResolvedDetailedFromTable_probe_query_bind]
  have hrightNotRevealed : coordinate ∉ right.state.revealed := by
    intro hrightRevealed
    have hleftRevealed : coordinate ∈ left.state.revealed := by
      rw [hrevealed]
      exact hrightRevealed
    have hleftKnown := hpublished coordinate hleftRevealed
    cases hleftValue : left.state.values coordinate with
    | none => exact hleftKnown hleftValue
    | some output =>
        have hrightValue := hvalues coordinate output hleftValue
        rw [hrightMissing] at hrightValue
        contradiction
  simp only [hrightNotRevealed, ↓reduceIte]
  rw [runDirectResolvedDetailedFromTable_pure]
  apply relTriple_pure_pure
  let nextRight : DeferredContext :=
    { right with state := right.state.addPending coordinate candidate }
  by_cases hcompletable : DeferredCompletable table nextRight
  · left
    exact
      { value_eq := rfl
        context_le := hcontext.addPending_right_of_completable
          coordinate candidate hcompletable
        remaining_le := by
          show leftFuel ≤ remaining
          omega
        left_table := rfl
        right_table := rfl
        cache_eq := hcache
        revealed_eq := hrevealed
        values_le := hvalues
        left_published := hpublished }
  · right
    right
    exact ⟨rfl, hcontext.view.rightConsistent.addPending coordinate candidate,
      hcontext.view.rightStarts.addPending coordinate candidate, hcompletable⟩

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_pure_probeFirstMissing_right
    (table : OtsSecretIndex → HashOutput) (input : HashInput) :
    ∀ (slot : Nat) (coordinates : List Coordinate)
      (left right : DeferredContext) (leftFuel rightFuel : Nat)
      (leftCache rightCache : SplitHashCache),
      FinalizationContextLE table left right →
      leftFuel + 1 ≤ rightFuel →
      ordinaryQueryCache leftCache = ordinaryQueryCache rightCache →
      left.state.revealed = right.state.revealed →
      LazyRevealProbe.ValuesLE left.state right.state →
      PublishedValues left.state →
      RelTriple
        (runDirectResolvedDetailedFromTable left leftFuel table
          ((pure () : StateT SplitHashCache
            (OracleComp (LazyRevealProbe.World Coordinate)) Unit).run leftCache))
        (runDirectResolvedDetailedFromTable right rightFuel table
          ((probeFirstMissingInputCoordinate input slot coordinates).run rightCache))
        (DirectDetailedOrdinaryRunEq table)
  | slot, [], left, right, leftFuel, rightFuel, leftCache, rightCache,
      hcontext, hfuel, hcache, hrevealed, hvalues, hpublished => by
      simpa [probeFirstMissingInputCoordinate] using
        (relTriple_runDirectResolvedDetailed_pure_of_ordinaryMaterialized table ()
          left right leftFuel rightFuel leftCache rightCache hcontext (by omega)
          hcache hrevealed hvalues hpublished)
  | slot, coordinate :: remaining, left, right, leftFuel, rightFuel,
      leftCache, rightCache, hcontext, hfuel, hcache, hrevealed, hvalues,
      hpublished => by
      rw [runDirectResolvedDetailedFromTable_probeFirstMissingInputCoordinate_cons]
      cases hrightValue : right.state.values coordinate with
      | none =>
          exact relTriple_runDirectResolvedDetailed_pure_probe_right table coordinate
            (slotDigest slot input) left right leftFuel rightFuel leftCache rightCache
              hcontext hfuel hcache hrevealed hvalues hpublished hrightValue
      | some output =>
          exact relTriple_runDirectResolvedDetailed_pure_probeFirstMissing_right table input
            (slot + 1) remaining left right leftFuel rightFuel leftCache rightCache
              hcontext hfuel hcache hrevealed hvalues hpublished

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_probe_aligned
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (candidate : Digest)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : 0 < leftFuel ∧ leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state) :
    RelTriple
      (runDirectResolvedDetailedFromTable left leftFuel table
        ((probe ⟨coordinate, candidate⟩).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((probe ⟨coordinate, candidate⟩).run rightCache))
      (DirectDetailedOrdinaryRunEq table) := by
  obtain ⟨leftRemaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (by omega : leftFuel ≠ 0)
  obtain ⟨rightRemaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (by omega : rightFuel ≠ 0)
  unfold probe
  rw [StateT.run_liftM, StateT.run_liftM]
  unfold LazyRevealProbe.probeQuery
  simp only
  rw [runDirectResolvedDetailedFromTable_probe_query_bind,
    runDirectResolvedDetailedFromTable_probe_query_bind]
  by_cases hleftRevealed : coordinate ∈ left.state.revealed
  · have hrightRevealed : coordinate ∈ right.state.revealed := by
      rw [← hrevealed]
      exact hleftRevealed
    simp only [hleftRevealed, hrightRevealed, ↓reduceIte]
    exact relTriple_runDirectResolvedDetailed_pure_of_ordinaryMaterialized table ()
      left right leftRemaining rightRemaining leftCache rightCache hcontext
        (by omega) hcache hrevealed hvalues hpublished
  · have hrightRevealed : coordinate ∉ right.state.revealed := by
      rwa [← hrevealed]
    simp only [hleftRevealed, hrightRevealed, ↓reduceIte]
    let nextLeft : DeferredContext :=
      { left with state := left.state.addPending coordinate candidate }
    let nextRight : DeferredContext :=
      { right with state := right.state.addPending coordinate candidate }
    by_cases hcompletable : DeferredCompletable table nextRight
    · have hnext := hcontext.addPending_both_of_right_completable
        coordinate candidate hcompletable
      have hnextPublished : PublishedValues nextLeft.state := by
        simpa [nextLeft, PublishedValues, LazyRevealProbe.State.addPending] using hpublished
      exact relTriple_runDirectResolvedDetailed_pure_of_ordinaryMaterialized table ()
        nextLeft nextRight leftRemaining rightRemaining leftCache rightCache hnext
          (by omega) hcache hrevealed hvalues hnextPublished
    · rw [runDirectResolvedDetailedFromTable_pure,
        runDirectResolvedDetailedFromTable_pure]
      apply relTriple_pure_pure
      right
      right
      exact ⟨rfl, hcontext.view.rightConsistent.addPending coordinate candidate,
        hcontext.view.rightStarts.addPending coordinate candidate, hcompletable⟩

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_privateHit_pure_probeFirstMissing_right
    (table : OtsSecretIndex → HashOutput) (input : HashInput) :
    ∀ (slot : Nat) (coordinates : List Coordinate)
      (left right : DeferredContext) (leftFuel rightFuel : Nat)
      (leftCache rightCache : SplitHashCache),
      PrivateStructuralHit left →
      leftFuel + 1 ≤ rightFuel →
      RelTriple
        (runDirectResolvedDetailedFromTable left leftFuel table
          ((pure () : StateT SplitHashCache
            (OracleComp (LazyRevealProbe.World Coordinate)) Unit).run leftCache))
        (runDirectResolvedDetailedFromTable right rightFuel table
          ((probeFirstMissingInputCoordinate input slot coordinates).run rightCache))
        (DirectDetailedOrdinaryRunEq table)
  | slot, [], left, right, leftFuel, rightFuel, leftCache, rightCache,
      hprivate, hfuel => by
      rw [StateT.run_pure, runDirectResolvedDetailedFromTable_pure]
      simp only [probeFirstMissingInputCoordinate, StateT.run_pure,
        runDirectResolvedDetailedFromTable_pure]
      apply relTriple_pure_pure
      right
      left
      exact hprivate
  | slot, coordinate :: remaining, left, right, leftFuel, rightFuel,
      leftCache, rightCache, hprivate, hfuel => by
      rw [runDirectResolvedDetailedFromTable_probeFirstMissingInputCoordinate_cons]
      cases hrightValue : right.state.values coordinate with
      | some output =>
          exact
            relTriple_runDirectResolvedDetailed_privateHit_pure_probeFirstMissing_right
              table input (slot + 1) remaining left right leftFuel rightFuel
                leftCache rightCache hprivate hfuel
      | none =>
          obtain ⟨rightRemaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
            (by omega : rightFuel ≠ 0)
          unfold probe
          rw [StateT.run_pure, StateT.run_liftM]
          unfold LazyRevealProbe.probeQuery
          simp only
          rw [runDirectResolvedDetailedFromTable_pure,
            runDirectResolvedDetailedFromTable_probe_query_bind]
          by_cases hrevealed : coordinate ∈ right.state.revealed <;>
            simp only [hrevealed, ↓reduceIte] <;>
            rw [runDirectResolvedDetailedFromTable_pure] <;>
            apply relTriple_pure_pure <;>
            right <;> left <;> exact hprivate

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_probe_private_position_probeFirstMissing_right
    (table : OtsSecretIndex → HashOutput) (input : HashInput) (slot : Nat)
    (coordinates : List Coordinate) (position : Position)
    (candidate : Digest) (output : HashOutput)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : 0 < leftFuel ∧ leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hhidden : left.state.values (.position position) = none)
    (hprivate : left.values position = some output) :
    RelTriple
      (runDirectResolvedDetailedFromTable left leftFuel table
        ((probe ⟨.position position, candidate⟩).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((probeFirstMissingInputCoordinate input slot coordinates).run rightCache))
      (DirectDetailedOrdinaryRunEq table) := by
  obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (by omega : leftFuel ≠ 0)
  unfold probe
  rw [StateT.run_liftM]
  unfold LazyRevealProbe.probeQuery
  simp only
  rw [runDirectResolvedDetailedFromTable_probe_query_bind]
  have hleftNotRevealed : Coordinate.position position ∉ left.state.revealed := by
    intro hrevealedPosition
    exact (hpublished (.position position) hrevealedPosition) hhidden
  simp only [hleftNotRevealed, ↓reduceIte]
  let nextLeft : DeferredContext :=
    { left with state := left.state.addPending (.position position) candidate }
  by_cases hhit : truncateHash output = candidate
  · have hprivateHit : PrivateStructuralHit nextLeft :=
      (privateStructuralHit_addPending_iff left position output candidate
        (not_privateStructuralHit_of_deferredCompletable hcontext.leftCompletable)
        hhidden hprivate).2 hhit
    exact
      relTriple_runDirectResolvedDetailed_privateHit_pure_probeFirstMissing_right
        table input slot coordinates nextLeft right remaining rightFuel leftCache rightCache
          hprivateHit (by omega)
  · have hnext := hcontext.addPending_left_of_resolved
      (.position position) candidate output (by
        change left.positionValue position = some output
        simp [DeferredContext.positionValue, hhidden, hprivate]) hhit
    have hnextPublished : PublishedValues nextLeft.state := by
      simpa [nextLeft, PublishedValues, LazyRevealProbe.State.addPending] using hpublished
    exact relTriple_runDirectResolvedDetailed_pure_probeFirstMissing_right table input
      slot coordinates nextLeft right remaining rightFuel leftCache rightCache hnext
        (by omega) hcache hrevealed hvalues hnextPublished

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_probeFirstMissing_positions
    (table : OtsSecretIndex → HashOutput) (input : HashInput) :
    ∀ (slot : Nat) (positions : List Position)
      (left right : DeferredContext) (leftFuel rightFuel : Nat)
      (leftCache rightCache : SplitHashCache),
      FinalizationContextLE table left right →
      0 < leftFuel → leftFuel ≤ rightFuel →
      ordinaryQueryCache leftCache = ordinaryQueryCache rightCache →
      left.state.revealed = right.state.revealed →
      LazyRevealProbe.ValuesLE left.state right.state →
      PublishedValues left.state →
      RelTriple
        (runDirectResolvedDetailedFromTable left leftFuel table
          ((probeFirstMissingInputCoordinate input slot
            (positions.map Coordinate.position)).run leftCache))
        (runDirectResolvedDetailedFromTable right rightFuel table
          ((probeFirstMissingInputCoordinate input slot
            (positions.map Coordinate.position)).run rightCache))
        (DirectDetailedOrdinaryRunEq table)
  | slot, [], left, right, leftFuel, rightFuel, leftCache, rightCache,
      hcontext, hpositive, hfuel, hcache, hrevealed, hvalues, hpublished => by
      simpa [probeFirstMissingInputCoordinate] using
        (relTriple_runDirectResolvedDetailed_pure_of_ordinaryMaterialized table ()
          left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache
            hrevealed hvalues hpublished)
  | slot, position :: remaining, left, right, leftFuel, rightFuel,
      leftCache, rightCache, hcontext, hpositive, hfuel, hcache, hrevealed,
      hvalues, hpublished => by
      simp only [List.map_cons]
      rw [runDirectResolvedDetailedFromTable_probeFirstMissingInputCoordinate_cons,
        runDirectResolvedDetailedFromTable_probeFirstMissingInputCoordinate_cons]
      cases hleftValue : left.state.values (.position position) with
      | some leftOutput =>
          have hrightValue := hvalues (.position position) leftOutput hleftValue
          rw [hrightValue]
          exact relTriple_runDirectResolvedDetailed_probeFirstMissing_positions table input
            (slot + 1) remaining left right leftFuel rightFuel leftCache rightCache
              hcontext hpositive hfuel hcache hrevealed hvalues hpublished
      | none =>
          cases hrightValue : right.state.values (.position position) with
          | none =>
              exact relTriple_runDirectResolvedDetailed_probe_aligned table
                (.position position) (slotDigest slot input) left right leftFuel rightFuel
                  leftCache rightCache hcontext ⟨hpositive, hfuel⟩ hcache hrevealed
                    hvalues hpublished
          | some output =>
              have hprivate :=
                hcontext.view.privateValue_of_left_hidden_of_right_materialized
                  position output hleftValue hrightValue
              exact
                relTriple_runDirectResolvedDetailed_probe_private_position_probeFirstMissing_right
                  table input (slot + 1) (remaining.map Coordinate.position) position
                    (slotDigest slot input) output left right leftFuel rightFuel
                      leftCache rightCache hcontext ⟨hpositive, hfuel⟩ hcache hrevealed
                        hvalues hpublished hleftValue hprivate

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_probe_skip_private_position
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (candidate : Digest) (output : HashOutput)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : 0 < leftFuel ∧ leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hhidden : left.state.values (.position position) = none)
    (hprivate : left.values position = some output) :
    RelTriple
      (runDirectResolvedDetailedFromTable left leftFuel table
        ((probe ⟨.position position, candidate⟩).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((pure () : StateT SplitHashCache
          (OracleComp (LazyRevealProbe.World Coordinate)) Unit).run rightCache))
      (DirectDetailedOrdinaryRunEq table) := by
  obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : leftFuel ≠ 0)
  unfold probe
  rw [StateT.run_liftM, StateT.run_pure]
  unfold LazyRevealProbe.probeQuery
  simp only
  rw [runDirectResolvedDetailedFromTable_probe_query_bind,
    runDirectResolvedDetailedFromTable_pure]
  have hleftNotRevealed : Coordinate.position position ∉ left.state.revealed := by
    intro hrevealedPosition
    exact (hpublished (.position position) hrevealedPosition) hhidden
  simp only [hleftNotRevealed, ↓reduceIte]
  apply relTriple_pure_pure
  by_cases hhit : truncateHash output = candidate
  · right
    left
    exact (privateStructuralHit_addPending_iff left position output candidate
      (not_privateStructuralHit_of_deferredCompletable hcontext.leftCompletable)
      hhidden hprivate).2 hhit
  · left
    exact
      { value_eq := rfl
        context_le := hcontext.addPending_left_of_resolved
          (.position position) candidate output (by
            change left.positionValue position = some output
            simp [DeferredContext.positionValue, hhidden, hprivate]) hhit
        remaining_le := by
          show remaining ≤ rightFuel
          omega
        left_table := rfl
        right_table := rfl
        cache_eq := hcache
        revealed_eq := hrevealed
        values_le := hvalues
        left_published := hpublished }

end SphincsSecurity.Concrete.OtsProbeSimulation
