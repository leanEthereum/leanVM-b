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

structure OrdinaryMaterializedRunEq (table : OtsSecretIndex → HashOutput)
    (left right : ResolvedRunResult (α × SplitHashCache)) : Prop where
  value_eq : left.value.1 = right.value.1
  context_eq : FinalizationContextEq table (some left.context) (some right.context)
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
        context_eq := hcontext.addPending_left_of_resolved
          (.position position) candidate output (by
            change left.positionValue position = some output
            simp [DeferredContext.positionValue, hhidden, hprivate]) hhit
        remaining_le := by
          show remaining ≤ rightFuel
          omega
        left_table := rfl
        right_table := rfl
        cache_eq := hcache
        revealed_eq := hrevealed }

end SphincsSecurity.Concrete.OtsProbeSimulation
