import SphincsSecurity.Proof.OtsProbeResolvedBoundaryOrdinaryAdaptive

/-!
# Probe-free private-boundary safety

A computation that issues no probes cannot create a private structural first fire. This supplies the signing-query case of the materialized private-boundary probability lift.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

def CanonicalPrivateSafeResult
    (table : OtsSecretIndex → HashOutput) : DirectDetailedResult α → Prop
  | .stopped .privateStructuralHit => False
  | .stopped _ => True
  | .done result =>
      ¬PrivateStructuralHit (canonicalizeMaterializedValues table result.context)

theorem canonicalPrivateClean_ensure
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (coordinate : Coordinate)
    (hclean : ¬PrivateStructuralHit
      (canonicalizeMaterializedValues table context)) :
    ¬PrivateStructuralHit
      (canonicalizeMaterializedValues table
        { context with state := context.state.ensure coordinate }) := by
  rintro ⟨position, output, hhidden, hprivate, hhit⟩
  apply hclean
  refine ⟨position, output, ?_, hprivate, ?_⟩
  · unfold canonicalizeMaterializedValues publicMaterializedValues at hhidden ⊢
    by_cases hrevealed : Coordinate.position position ∈ context.state.revealed
    · simp only [LazyRevealProbe.State.ensure, hrevealed, ↓reduceIte] at hhidden ⊢
      simpa [resolvedCompletionValue, DeferredContext.positionValue] using hhidden
    · simp [hrevealed]
  · simpa [canonicalizeMaterializedValues, LazyRevealProbe.State.ensure,
      LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt] using hhit

theorem canonicalPrivateClean_publish
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (coordinate : Coordinate)
    (hclean : ¬PrivateStructuralHit
      (canonicalizeMaterializedValues table context)) :
    ¬PrivateStructuralHit
      (canonicalizeMaterializedValues table
        { context with state := context.state.publish coordinate }) := by
  rintro ⟨position, output, hhidden, hprivate, hhit⟩
  apply hclean
  refine ⟨position, output, ?_, hprivate, ?_⟩
  · unfold canonicalizeMaterializedValues publicMaterializedValues at hhidden ⊢
    by_cases heq : Coordinate.position position = coordinate
    · subst coordinate
      change context.values position = some output at hprivate
      cases hstate : context.state.values (.position position) <;>
        simp [LazyRevealProbe.State.publish, resolvedCompletionValue,
          DeferredContext.positionValue, hprivate, hstate] at hhidden
    · by_cases hrevealed : Coordinate.position position ∈ context.state.revealed
      · simp only [LazyRevealProbe.State.publish, Finset.mem_insert, heq, hrevealed,
          ↓reduceIte] at hhidden ⊢
        simpa [resolvedCompletionValue, DeferredContext.positionValue] using hhidden
      · simp [hrevealed]
  · simpa [canonicalizeMaterializedValues, LazyRevealProbe.State.publish,
      LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt] using hhit

theorem canonicalPrivateClean_materialize
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (coordinate : Coordinate) (materialized : HashOutput)
    (values : DeferredStructuralValues)
    (hvalues : ∀ position, coordinate ≠ .position position →
      values position = context.values position)
    (hclean : ¬PrivateStructuralHit
      (canonicalizeMaterializedValues table context)) :
    ¬PrivateStructuralHit
      (canonicalizeMaterializedValues table
        { state := context.state.materialize coordinate materialized
          values := values }) := by
  rintro ⟨position, output, hhidden, hprivate, hhit⟩
  by_cases heq : coordinate = .position position
  · subst coordinate
    have hfalse := not_hitAt_clearPending_self context.state
      (.position position) output
    apply hfalse
    simpa [canonicalizeMaterializedValues, LazyRevealProbe.State.materialize,
      LazyRevealProbe.State.clearPending, LazyRevealProbe.State.hitAt,
      LazyRevealProbe.State.pendingAt] using hhit
  · apply hclean
    have hne : Coordinate.position position ≠ coordinate := fun hsame => heq hsame.symm
    refine ⟨position, output, ?_, ?_, ?_⟩
    · change publicMaterializedValues table
          { state := context.state.materialize coordinate materialized
            values := values }
          (.position position) = none at hhidden
      change publicMaterializedValues table context (.position position) = none
      unfold publicMaterializedValues at hhidden ⊢
      by_cases hrevealed : Coordinate.position position ∈ context.state.revealed
      · simp only [LazyRevealProbe.State.materialize, hrevealed, ↓reduceIte] at hhidden ⊢
        unfold resolvedCompletionValue DeferredContext.positionValue at hhidden ⊢
        simpa [LazyRevealProbe.State.materialize, Function.update_of_ne hne,
          hvalues position heq] using hhidden
      · simp [hrevealed]
    · change values position = some output at hprivate
      rw [hvalues position heq] at hprivate
      exact hprivate
    · have hsame := hitAt_clearPending_of_ne context.state coordinate
          (.position position) output hne
      apply hsame.mp
      simpa [canonicalizeMaterializedValues, LazyRevealProbe.State.materialize,
        LazyRevealProbe.State.clearPending, LazyRevealProbe.State.hitAt,
        LazyRevealProbe.State.pendingAt] using hhit

theorem privateClean_materialize
    (context : DeferredContext) (coordinate : Coordinate)
    (materialized : HashOutput) (values : DeferredStructuralValues)
    (hvalues : ∀ position, coordinate ≠ .position position →
      values position = context.values position)
    (hclean : ¬PrivateStructuralHit context) :
    ¬PrivateStructuralHit
      { state := context.state.materialize coordinate materialized
        values := values } := by
  rintro ⟨position, output, hhidden, hprivate, hhit⟩
  by_cases heq : coordinate = .position position
  · subst coordinate
    simp [LazyRevealProbe.State.materialize] at hhidden
  · apply hclean
    have hne : Coordinate.position position ≠ coordinate := fun hsame => heq hsame.symm
    refine ⟨position, output, ?_, ?_, ?_⟩
    · simpa [LazyRevealProbe.State.materialize, Function.update_of_ne hne] using hhidden
    · change values position = some output at hprivate
      rw [hvalues position heq] at hprivate
      exact hprivate
    · have hsame := hitAt_clearPending_of_ne context.state coordinate
          (.position position) output hne
      apply hsame.mp
      simpa [LazyRevealProbe.State.materialize, LazyRevealProbe.State.clearPending,
        LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt] using hhit

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem canonicalPrivateSafeResult_of_probeFree
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe 0)
    (hrawClean : ¬PrivateStructuralHit context)
    (hclean : ¬PrivateStructuralHit
      (canonicalizeMaterializedValues table context)) :
    ∀ result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table computation),
      CanonicalPrivateSafeResult table result := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      intro result hresult
      simp [runDirectResolvedDetailedFromTable_pure] at hresult
      subst result
      exact hclean
  | query_bind query next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      cases query with
      | uniform n =>
          rw [runDirectResolvedDetailedFromTable_uniform_query_bind]
          intro result hresult
          rw [mem_support_bind_iff] at hresult
          obtain ⟨output, houtput, hresult⟩ := hresult
          exact ih output context fuel
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output)
            hrawClean hclean result hresult
      | hashOutput =>
          rw [runDirectResolvedDetailedFromTable_hashOutput_query_bind]
          intro result hresult
          rw [mem_support_bind_iff] at hresult
          obtain ⟨output, houtput, hresult⟩ := hresult
          exact ih output context fuel
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output)
            hrawClean hclean result hresult
      | ensure coordinate =>
          rw [runDirectResolvedDetailedFromTable_ensure_query_bind]
          intro result hresult
          apply ih () { context with state := context.state.ensure coordinate } fuel
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 ())
            (by simpa [PrivateStructuralHit, LazyRevealProbe.State.ensure,
              LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt] using hrawClean)
            (canonicalPrivateClean_ensure table context coordinate hclean)
          · exact hresult
      | probe coordinate candidate =>
          exfalso
          simpa [LazyRevealProbe.IsProbe] using hbound.1
      | peek coordinate =>
          rw [runDirectResolvedDetailedFromTable_peek_query_bind]
          intro result hresult
          exact ih (context.state.values coordinate) context fuel
            (by simpa [LazyRevealProbe.IsProbe] using
              hbound.2 (context.state.values coordinate))
            hrawClean hclean result hresult
      | publish coordinate =>
          rw [runDirectResolvedDetailedFromTable_publish_query_bind]
          intro result hresult
          apply ih () { context with state := context.state.publish coordinate } fuel
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 ())
          · simpa [PrivateStructuralHit, LazyRevealProbe.State.publish,
              LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt] using hrawClean
          · exact canonicalPrivateClean_publish table context coordinate hclean
          · exact hresult
      | reveal coordinate =>
          rw [runDirectResolvedDetailedFromTable_reveal_query_bind]
          cases hstate : context.state.values coordinate with
          | some output =>
              intro result hresult
              exact ih output context fuel
                (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output)
                hrawClean hclean result hresult
          | none =>
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : context.state.hitAt
                      (.chainStart lay tree leafIdx chainIdx) output
                  · simp only [output, hhit, ↓reduceIte]
                    intro result hresult
                    simp only [support_pure, Set.mem_singleton_iff] at hresult
                    subst result
                    trivial
                  · simp only [output, hhit, ↓reduceIte]
                    intro result hresult
                    apply ih output
                      { state := context.state.materialize
                          (.chainStart lay tree leafIdx chainIdx) output
                        values := context.values }
                      fuel
                      (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output)
                    · apply privateClean_materialize context
                        (.chainStart lay tree leafIdx chainIdx) output context.values
                      · intro position _hne
                        rfl
                      · exact hrawClean
                    · apply canonicalPrivateClean_materialize table context
                        (.chainStart lay tree leafIdx chainIdx) output context.values
                      · intro position _hne
                        rfl
                      · exact hclean
                    · exact hresult
              | position position =>
                  cases hprivate : context.values position with
                  | some output =>
                      by_cases hhit : context.state.hitAt (.position position) output
                      · exact False.elim
                          (hrawClean ⟨position, output, hstate, hprivate, hhit⟩)
                      · simp only [hprivate, hhit, ↓reduceIte]
                        intro result hresult
                        apply ih output
                          { state := context.state.materialize (.position position) output
                            values := context.values }
                          fuel
                          (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output)
                        · apply privateClean_materialize context (.position position) output
                            context.values
                          · intro other _hne
                            rfl
                          · exact hrawClean
                        · apply canonicalPrivateClean_materialize table context
                            (.position position) output context.values
                          · intro other _hne
                            rfl
                          · exact hclean
                        · exact hresult
                  | none =>
                      simp only [hprivate]
                      intro result hresult
                      rw [mem_support_bind_iff] at hresult
                      obtain ⟨output, houtput, hrest⟩ := hresult
                      by_cases hhit : context.state.hitAt (.position position) output
                      · simp only [hhit, ↓reduceIte, support_pure,
                          Set.mem_singleton_iff] at hrest
                        subst result
                        trivial
                      · simp only [hhit, ↓reduceIte] at hrest
                        apply ih output
                          { state := context.state.materialize (.position position) output
                            values := context.values.install position output }
                          fuel
                          (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output)
                        · apply privateClean_materialize context (.position position) output
                            (context.values.install position output)
                          · intro other hne
                            simp [DeferredStructuralValues.install,
                              Function.update_of_ne (fun heq => hne (congrArg Coordinate.position
                                heq.symm))]
                          · exact hrawClean
                        · apply canonicalPrivateClean_materialize table context
                            (.position position) output
                            (context.values.install position output)
                          · intro other hne
                            simp [DeferredStructuralValues.install,
                              Function.update_of_ne (fun heq => hne (congrArg Coordinate.position
                                heq.symm))]
                          · exact hclean
                        · exact hrest

set_option maxRecDepth 100000 in
theorem remaining_le_fuel_of_mem_support_runRaw_done
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (state finalState : LazyRevealProbe.State Coordinate)
    (fuel remaining : Nat) (value : α)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining value ∈
      support (LazyRevealProbe.runRaw state fuel computation)) :
    remaining ≤ fuel := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure result =>
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl⟩
      exact le_rfl
  | query_bind query next ih =>
      cases query with
      | uniform n =>
          rw [LazyRevealProbe.runRaw_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output state fuel hrest
      | hashOutput =>
          rw [LazyRevealProbe.runRaw_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output state fuel hrest
      | ensure coordinate =>
          rw [LazyRevealProbe.runRaw_ensure_query_bind] at hresult
          exact ih () (state.ensure coordinate) fuel hresult
      | probe coordinate candidate =>
          cases fuel with
          | zero => simp [LazyRevealProbe.runRaw_probe_query_bind] at hresult
          | succ nextFuel =>
              rw [LazyRevealProbe.runRaw_probe_query_bind] at hresult
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [hrevealed, ↓reduceIte] at hresult
                exact (ih () state nextFuel hresult).trans (Nat.le_succ nextFuel)
              · simp only [hrevealed, ↓reduceIte] at hresult
                exact (ih () (state.addPending coordinate candidate) nextFuel hresult).trans
                  (Nat.le_succ nextFuel)
      | peek coordinate =>
          rw [LazyRevealProbe.runRaw_peek_query_bind] at hresult
          exact ih (state.values coordinate) state fuel hresult
      | publish coordinate =>
          rw [LazyRevealProbe.runRaw_publish_query_bind] at hresult
          exact ih () (state.publish coordinate) fuel hresult
      | reveal coordinate =>
          rw [LazyRevealProbe.runRaw_reveal_query_bind] at hresult
          cases hvalue : state.values coordinate with
          | some output =>
              rw [hvalue] at hresult
              exact ih output state fuel hresult
          | none =>
              rw [hvalue] at hresult
              rw [mem_support_bind_iff] at hresult
              obtain ⟨output, _houtput, hrest⟩ := hresult
              by_cases hhit : state.hitAt coordinate output
              · simp [hhit] at hrest
              · simp only [hhit, ↓reduceIte] at hrest
                exact ih output (state.materialize coordinate output) fuel hrest

theorem remaining_le_fuel_of_done_runDirectResolvedDetailedFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table computation)) :
    result.remaining ≤ fuel := by
  apply remaining_le_fuel_of_mem_support_runRaw_done computation context.state
    result.context.state fuel result.remaining result.value
  exact raw_done_of_mem_runDirectResolvedFromTable computation context fuel table result
    (mem_support_runDirectResolvedFromTable_of_done_detailed computation context fuel table
      result hresult)

set_option maxRecDepth 100000 in
theorem probEvent_materializedPrivateStep_signing_le
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (nextObserve : DeferredContext → Nat →
      (Option Signature × SplitHashCache) → ProbComp Bool)
    (epsilon terminalBound : ℝ≥0∞)
    (hclean : ¬PrivateStructuralHit
      (canonicalizeMaterializedValues table context))
    (hcompletable : DeferredCompletable table context)
    (hcontinuation : ∀ result : ResolvedRunResult
        (Option Signature × SplitHashCache),
      DirectDetailedResult.done result ∈ support
        (runDirectResolvedDetailedFromTable context fuel table
          ((maskedExpandedAdversaryImpl parameter root ftsSecret
            (.inr message)).run cache)) →
      ¬PrivateStructuralHit
          (canonicalizeMaterializedValues table result.context) →
      DeferredCompletable table result.context →
      Pr[= true | nextObserve result.context result.remaining result.value] ≤
        (result.remaining : ℝ≥0∞) * epsilon + terminalBound) :
    Pr[= true |
      runDirectDetailedPrivateObserve
        (classifyCanonicalMaterializedPrivateObserve table nextObserve)
        context fuel table
        ((maskedExpandedAdversaryImpl parameter root ftsSecret
          (.inr message)).run cache)] ≤
      (fuel : ℝ≥0∞) * epsilon + terminalBound := by
  have hprobeFree :
      (((maskedExpandedAdversaryImpl parameter root ftsSecret
        (.inr message)).run cache).IsQueryBoundP
          LazyRevealProbe.IsProbe 0) := by
    simpa [maskedExpandedAdversaryImpl, maskedSigningImpl] using
      maskedSign_probeFree parameter root ftsSecret message cache
  have hrawClean : ¬PrivateStructuralHit context :=
    not_privateStructuralHit_of_deferredCompletable hcompletable
  rw [← probEvent_eq_eq_probOutput]
  unfold runDirectDetailedPrivateObserve
  apply probEvent_bind_le_of_forall_le
  intro result hresult
  have hsafe := canonicalPrivateSafeResult_of_probeFree
    ((maskedExpandedAdversaryImpl parameter root ftsSecret (.inr message)).run cache)
    context fuel table hprobeFree hrawClean hclean result hresult
  cases result with
  | stopped reason =>
      cases reason with
      | privateStructuralHit => exact False.elim hsafe
      | ordinaryHit => simp [finishDirectDetailedPrivateObserve]
      | fuelExhausted => simp [finishDirectDetailedPrivateObserve]
  | done result =>
      simp only [CanonicalPrivateSafeResult] at hsafe
      simp only [finishDirectDetailedPrivateObserve]
      unfold classifyCanonicalMaterializedPrivateObserve
      simp only [hsafe, ↓reduceIte]
      by_cases hnextCompletable : DeferredCompletable table result.context
      · simp only [hnextCompletable, ↓reduceIte]
        have hnext := hcontinuation result hresult hsafe hnextCompletable
        rw [← probEvent_eq_eq_probOutput] at hnext
        refine hnext.trans ?_
        gcongr
        exact_mod_cast
          remaining_le_fuel_of_done_runDirectResolvedDetailedFromTable
            ((maskedExpandedAdversaryImpl parameter root ftsSecret
              (.inr message)).run cache)
            context fuel table result hresult
      · simp [hnextCompletable]

end SphincsSecurity.Concrete.OtsProbeSimulation
