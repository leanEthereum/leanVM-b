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

structure OrdinaryMaterializedRunEq (table : OtsSecretIndex → HashOutput)
    (left right : ResolvedRunResult (α × SplitHashCache)) : Prop where
  value_eq : left.value.1 = right.value.1
  context_le : FinalizationContextLE table left.context right.context
  remaining_le : left.remaining ≤ right.remaining
  left_table : left.table = table
  right_table : right.table = table
  cache_eq : ordinaryQueryCache left.value.2 = ordinaryQueryCache right.value.2
  revealed_eq : left.context.state.revealed = right.context.state.revealed

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
        (FinalizationDoomedRun table (some left) ∧
          FinalizationDoomedRun table (some right))

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_probe_skip_private_position
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (candidate : Digest) (output : HashOutput)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hfuel : 0 < leftFuel ∧ leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
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
      (not_privateStructuralHit_of_deferredCompletable hcontext.2.2.2)
      hhidden hprivate).2 hhit
  · left
    exact
      { value_eq := rfl
        context_le := FinalizationContextLE.of_eq (hcontext.addPending_left_of_resolved
          (.position position) candidate output (by
            change left.positionValue position = some output
            simp [DeferredContext.positionValue, hhidden, hprivate]) hhit)
        remaining_le := by
          show remaining ≤ rightFuel
          omega
        left_table := rfl
        right_table := rfl
        cache_eq := hcache
        revealed_eq := hrevealed }

end SphincsSecurity.Concrete.OtsProbeSimulation
