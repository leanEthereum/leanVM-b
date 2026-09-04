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

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem valid_of_done_runDirectResolvedDetailedFromTable_of_probeFree
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe 0)
    (hvalid : context.Valid)
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table computation)) :
    result.context.Valid := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runDirectResolvedDetailedFromTable_pure] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact hvalid
  | query_bind query next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      cases query with
      | uniform n =>
          rw [runDirectResolvedDetailedFromTable_uniform_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output context fuel
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output) hvalid hrest
      | hashOutput =>
          rw [runDirectResolvedDetailedFromTable_hashOutput_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output context fuel
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output) hvalid hrest
      | ensure coordinate =>
          rw [runDirectResolvedDetailedFromTable_ensure_query_bind] at hresult
          exact ih () { context with state := context.state.ensure coordinate } fuel
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 ())
            (hvalid.ensure coordinate) hresult
      | probe coordinate candidate =>
          exfalso
          simpa [LazyRevealProbe.IsProbe] using hbound.1
      | peek coordinate =>
          rw [runDirectResolvedDetailedFromTable_peek_query_bind] at hresult
          exact ih (context.state.values coordinate) context fuel
            (by simpa [LazyRevealProbe.IsProbe] using
              hbound.2 (context.state.values coordinate)) hvalid hresult
      | publish coordinate =>
          rw [runDirectResolvedDetailedFromTable_publish_query_bind] at hresult
          exact ih () { context with state := context.state.publish coordinate } fuel
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 ())
            (hvalid.publish coordinate) hresult
      | reveal coordinate =>
          rw [runDirectResolvedDetailedFromTable_reveal_query_bind] at hresult
          cases hstate : context.state.values coordinate with
          | some output =>
              rw [hstate] at hresult
              exact ih output context fuel
                (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output) hvalid hresult
          | none =>
              rw [hstate] at hresult
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : context.state.hitAt
                      (.chainStart lay tree leafIdx chainIdx) output
                  · simp [output, hhit] at hresult
                  · simp only [output, hhit, ↓reduceIte] at hresult
                    exact ih output
                      { state := context.state.materialize
                          (.chainStart lay tree leafIdx chainIdx) output
                        values := context.values }
                      fuel
                      (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output)
                      (hvalid.materialize_chainStart lay tree leafIdx chainIdx output) hresult
              | position position =>
                  simp only at hresult
                  cases hprivate : context.values position with
                  | some output =>
                      rw [hprivate] at hresult
                      by_cases hhit : context.state.hitAt (.position position) output
                      · simp [hhit] at hresult
                      · simp only [hhit, ↓reduceIte] at hresult
                        exact ih output
                          { state := context.state.materialize (.position position) output
                            values := context.values }
                          fuel
                          (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output)
                          (hvalid.materialize_position position output hprivate) hresult
                  | none =>
                      rw [hprivate, mem_support_bind_iff] at hresult
                      obtain ⟨output, _houtput, hrest⟩ := hresult
                      by_cases hhit : context.state.hitAt (.position position) output
                      · simp [hhit] at hrest
                      · simp only [hhit, ↓reduceIte] at hrest
                        have htemporary :
                            ({ state := context.state
                               values := context.values.install position output } :
                              DeferredContext).Valid := by
                          constructor
                          · intro other otherOutput hvalue
                            by_cases heq : other = position
                            · subst other
                              rw [hstate] at hvalue
                              contradiction
                            · simpa [DeferredStructuralValues.install,
                                Function.update_of_ne heq] using
                                hvalid.1 other otherOutput hvalue
                          · exact hvalid.2
                        have hnextValid :
                            ({ state := context.state.materialize (.position position) output
                               values := context.values.install position output } :
                              DeferredContext).Valid := by
                          apply htemporary.materialize_position position output
                          simp [DeferredStructuralValues.install]
                        exact ih output
                          { state := context.state.materialize (.position position) output
                            values := context.values.install position output }
                          fuel
                          (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output)
                          hnextValid hrest

theorem DeferredContext.Valid.addPending_of_value_none
    {context : DeferredContext} (hvalid : context.Valid)
    (coordinate : Coordinate) (candidate : Digest)
    (hvalue : context.state.values coordinate = none) :
    ({ context with state := context.state.addPending coordinate candidate } :
      DeferredContext).Valid := by
  constructor
  · exact hvalid.1
  · intro other output hother
    change context.state.values other = some output at hother
    by_cases heq : other = coordinate
    · subst other
      rw [hvalue] at hother
      contradiction
    · rw [hitAt_addPending_of_ne context.state coordinate other candidate output (Ne.symm heq)]
      exact hvalid.2 other output hother

set_option maxRecDepth 100000 in
theorem valid_of_done_runDirectResolvedDetailed_probe
    (candidate : Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (Unit × SplitHashCache))
    (hvalid : context.Valid)
    (hsafe : candidate.coordinate ∈ context.state.revealed ∨
      context.state.values candidate.coordinate = none)
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table
        ((probe candidate).run cache))) :
    result.context.Valid := by
  unfold probe at hresult
  rw [StateT.run_liftM, LazyRevealProbe.probeQuery,
    runDirectResolvedDetailedFromTable_probe_query_bind] at hresult
  cases fuel with
  | zero => simp at hresult
  | succ remaining =>
      by_cases hrevealed : candidate.coordinate ∈ context.state.revealed
      · simp only [hrevealed, ↓reduceIte,
          runDirectResolvedDetailedFromTable_pure] at hresult
        simp only [support_pure, Set.mem_singleton_iff,
          DirectDetailedResult.done.injEq] at hresult
        rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
        exact hvalid
      · simp only [hrevealed, ↓reduceIte,
          runDirectResolvedDetailedFromTable_pure] at hresult
        simp only [support_pure, Set.mem_singleton_iff,
          DirectDetailedResult.done.injEq] at hresult
        rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
        exact hvalid.addPending_of_value_none candidate.coordinate candidate.candidate
          (hsafe.resolve_left hrevealed)

set_option maxRecDepth 100000 in
theorem valid_of_done_runDirectResolvedDetailed_probeFirstMissingInputCoordinate
    (input : HashInput) (slot : Nat) (coordinates : List Coordinate)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (Unit × SplitHashCache))
    (hvalid : context.Valid)
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table
        ((probeFirstMissingInputCoordinate input slot coordinates).run cache))) :
    result.context.Valid := by
  induction coordinates generalizing slot with
  | nil =>
      simp [probeFirstMissingInputCoordinate,
        runDirectResolvedDetailedFromTable_pure] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact hvalid
  | cons coordinate remaining ih =>
      rw [runDirectResolvedDetailedFromTable_probeFirstMissingInputCoordinate_cons] at hresult
      cases hvalue : context.state.values coordinate with
      | none =>
          rw [hvalue] at hresult
          exact valid_of_done_runDirectResolvedDetailed_probe
            ⟨coordinate, slotDigest slot input⟩ context fuel table cache result hvalid
              (Or.inr hvalue) hresult
      | some output =>
          rw [hvalue] at hresult
          exact ih (slot + 1) hresult

set_option maxRecDepth 100000 in
theorem valid_of_done_runDirectResolvedDetailed_prepareLeafInputProbe
    (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (Unit × SplitHashCache))
    (hvalid : context.Valid)
    (hsafe : candidate.coordinate ∈ context.state.revealed ∨
      context.state.values candidate.coordinate = none)
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table
        ((prepareLeafInputProbe input candidate lay tree leafIdx).run cache))) :
    result.context.Valid := by
  rw [runDirectResolvedDetailedFromTable_prepareLeafInputProbe] at hresult
  cases hvalue : context.state.values candidate.coordinate with
  | none =>
      rw [hvalue] at hresult
      exact valid_of_done_runDirectResolvedDetailed_probe candidate context fuel table cache
        result hvalid hsafe hresult
  | some output =>
      rw [hvalue] at hresult
      exact valid_of_done_runDirectResolvedDetailed_probeFirstMissingInputCoordinate input 0
        ((Position.leaf lay tree leafIdx).children.map Coordinate.position)
        context fuel table cache result hvalid hresult

set_option maxRecDepth 100000 in
theorem valid_of_done_runDirectResolvedDetailed_bind_probeFree
    (left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (β × SplitHashCache))
    (hleft : ∀ middle : ResolvedRunResult (α × SplitHashCache),
      DirectDetailedResult.done middle ∈ support
        (runDirectResolvedDetailedFromTable context fuel table (left.run cache)) →
      middle.context.Valid)
    (hnext : ∀ value, ProbeFree (next value))
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table
        ((left >>= next).run cache))) :
    result.context.Valid := by
  rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
    mem_support_bind_iff] at hresult
  obtain ⟨middleResult, hmiddle, hrest⟩ := hresult
  cases middleResult with
  | stopped reason => simp at hrest
  | done middle =>
      exact valid_of_done_runDirectResolvedDetailedFromTable_of_probeFree
        ((next middle.value.1).run middle.value.2) middle.context middle.remaining
          middle.table result (hnext middle.value.1 middle.value.2)
            (hleft middle hmiddle) hrest

theorem probe_safe_of_chainValid
    (candidate : Probe) (parameter : PublicParameter) (input : HashInput)
    (context : DeferredContext)
    (hmatches : candidate.MatchesInput parameter input)
    (hchainValid : ChainState.ValidFor (fun _ => True) context.state) :
    candidate.coordinate ∈ context.state.revealed ∨
      context.state.values candidate.coordinate = none := by
  have hchain := candidate.isChainCoordinate_of_matchesInput hmatches
  cases hvalue : context.state.values candidate.coordinate with
  | none => exact Or.inr rfl
  | some output =>
      exact Or.inl ((hchainValid candidate.coordinate hchain).1 (by simp [hvalue]))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem valid_of_done_runDirectResolvedDetailed_probingHashQuery
    (parameter : PublicParameter) (input : HashInput)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (HashOutput × SplitHashCache))
    (hvalid : context.Valid)
    (hchainValid : ChainState.ValidFor (fun _ => True) context.state)
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table
        ((probingHashQuery parameter input).run cache))) :
    result.context.Valid := by
  unfold probingHashQuery at hresult
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      rw [hprobe] at hresult
      have hmatches := (decodeProbe?_eq_some_iff parameter input candidate).1 hprobe
      have hsafe := probe_safe_of_chainValid candidate parameter input context hmatches
        hchainValid
      cases hposition : decodePosition? parameter input with
      | none =>
          rw [hposition] at hresult
          apply valid_of_done_runDirectResolvedDetailed_bind_probeFree
            (left := probe candidate)
            (next := fun _ => resolveKnownInput parameter candidate.outputCoordinate input)
            context fuel table cache result
          · intro middle hmiddle
            exact valid_of_done_runDirectResolvedDetailed_probe candidate context fuel table
              cache middle hvalid hsafe hmiddle
          · intro _
            exact resolveKnownInput_probeFree parameter candidate.outputCoordinate input
          · exact hresult
      | some position =>
          rw [hposition] at hresult
          cases position with
          | leaf lay tree leafIdx =>
              apply valid_of_done_runDirectResolvedDetailed_bind_probeFree
                (left := prepareLeafInputProbe input candidate lay tree leafIdx)
                (next := fun _ => resolveKnownInput parameter candidate.outputCoordinate input)
                context fuel table cache result
              · intro middle hmiddle
                exact valid_of_done_runDirectResolvedDetailed_prepareLeafInputProbe input
                  candidate lay tree leafIdx context fuel table cache middle hvalid hsafe hmiddle
              · intro _
                exact resolveKnownInput_probeFree parameter candidate.outputCoordinate input
              · exact hresult
          | chain lay tree leafIdx chainIdx step =>
              apply valid_of_done_runDirectResolvedDetailed_bind_probeFree
                (left := probe candidate)
                (next := fun _ => resolveKnownInput parameter candidate.outputCoordinate input)
                context fuel table cache result
              · intro middle hmiddle
                exact valid_of_done_runDirectResolvedDetailed_probe candidate context fuel table
                  cache middle hvalid hsafe hmiddle
              · intro _
                exact resolveKnownInput_probeFree parameter candidate.outputCoordinate input
              · exact hresult
          | node lay tree level nodeIdx =>
              apply valid_of_done_runDirectResolvedDetailed_bind_probeFree
                (left := probe candidate)
                (next := fun _ => resolveKnownInput parameter candidate.outputCoordinate input)
                context fuel table cache result
              · intro middle hmiddle
                exact valid_of_done_runDirectResolvedDetailed_probe candidate context fuel table
                  cache middle hvalid hsafe hmiddle
              · intro _
                exact resolveKnownInput_probeFree parameter candidate.outputCoordinate input
              · exact hresult
          | ftsLeaf index tree leafIdx =>
              apply valid_of_done_runDirectResolvedDetailed_bind_probeFree
                (left := probe candidate)
                (next := fun _ => resolveKnownInput parameter candidate.outputCoordinate input)
                context fuel table cache result
              · intro middle hmiddle
                exact valid_of_done_runDirectResolvedDetailed_probe candidate context fuel table
                  cache middle hvalid hsafe hmiddle
              · intro _
                exact resolveKnownInput_probeFree parameter candidate.outputCoordinate input
              · exact hresult
          | ftsNode index tree level nodeIdx =>
              apply valid_of_done_runDirectResolvedDetailed_bind_probeFree
                (left := probe candidate)
                (next := fun _ => resolveKnownInput parameter candidate.outputCoordinate input)
                context fuel table cache result
              · intro middle hmiddle
                exact valid_of_done_runDirectResolvedDetailed_probe candidate context fuel table
                  cache middle hvalid hsafe hmiddle
              · intro _
                exact resolveKnownInput_probeFree parameter candidate.outputCoordinate input
              · exact hresult
          | ftsRoots index =>
              apply valid_of_done_runDirectResolvedDetailed_bind_probeFree
                (left := probe candidate)
                (next := fun _ => resolveKnownInput parameter candidate.outputCoordinate input)
                context fuel table cache result
              · intro middle hmiddle
                exact valid_of_done_runDirectResolvedDetailed_probe candidate context fuel table
                  cache middle hvalid hsafe hmiddle
              · intro _
                exact resolveKnownInput_probeFree parameter candidate.outputCoordinate input
              · exact hresult
  | none =>
      rw [hprobe] at hresult
      cases hposition : decodePosition? parameter input with
      | none =>
          rw [hposition] at hresult
          exact valid_of_done_runDirectResolvedDetailedFromTable_of_probeFree
            ((splitHashQuery (.ordinary input)).run cache) context fuel table result
              (splitHashQuery_probeFree (.ordinary input) cache) hvalid hresult
      | some position =>
          rw [hposition] at hresult
          cases position with
          | chain lay tree leafIdx chainIdx step =>
              exact valid_of_done_runDirectResolvedDetailedFromTable_of_probeFree
                ((resolveKnownInput parameter
                  (.position (.chain lay tree leafIdx chainIdx step)) input).run cache)
                context fuel table result
                (resolveKnownInput_probeFree parameter
                  (.position (.chain lay tree leafIdx chainIdx step)) input cache)
                hvalid hresult
          | leaf lay tree leafIdx =>
              exact valid_of_done_runDirectResolvedDetailedFromTable_of_probeFree
                ((resolveKnownInput parameter (.position (.leaf lay tree leafIdx)) input).run
                  cache)
                context fuel table result
                (resolveKnownInput_probeFree parameter (.position (.leaf lay tree leafIdx))
                  input cache)
                hvalid hresult
          | node lay tree level nodeIdx =>
              apply valid_of_done_runDirectResolvedDetailed_bind_probeFree
                (left := probeFirstMissingInputCoordinate input 0
                  ((Position.node lay tree level nodeIdx).children.map Coordinate.position))
                (next := fun _ =>
                  resolveKnownInput parameter (.position (.node lay tree level nodeIdx)) input)
                context fuel table cache result
              · intro middle hmiddle
                exact valid_of_done_runDirectResolvedDetailed_probeFirstMissingInputCoordinate
                  input 0
                  ((Position.node lay tree level nodeIdx).children.map Coordinate.position)
                  context fuel table cache middle hvalid hmiddle
              · intro _
                exact resolveKnownInput_probeFree parameter
                  (.position (.node lay tree level nodeIdx)) input
              · exact hresult
          | ftsLeaf index tree leafIdx =>
              exact valid_of_done_runDirectResolvedDetailedFromTable_of_probeFree
                ((splitHashQuery (.ordinary input)).run cache) context fuel table result
                  (splitHashQuery_probeFree (.ordinary input) cache) hvalid hresult
          | ftsNode index tree level nodeIdx =>
              exact valid_of_done_runDirectResolvedDetailedFromTable_of_probeFree
                ((splitHashQuery (.ordinary input)).run cache) context fuel table result
                  (splitHashQuery_probeFree (.ordinary input) cache) hvalid hresult
          | ftsRoots index =>
              exact valid_of_done_runDirectResolvedDetailedFromTable_of_probeFree
                ((splitHashQuery (.ordinary input)).run cache) context fuel table result
                  (splitHashQuery_probeFree (.ordinary input) cache) hvalid hresult

theorem not_privateStructuralHit_canonicalize_of_direct_valid
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hdirect : context = directDeferredContext context.state)
    (hvalid : context.Valid) :
    ¬PrivateStructuralHit (canonicalizeMaterializedValues table context) := by
  rintro ⟨position, output, _hhidden, hprivate, hhit⟩
  have hstate : context.state.values (.position position) = some output := by
    have hsame : context.values position =
        context.state.values (.position position) := by
      rw [hdirect]
      rfl
    change context.values position = some output at hprivate
    rw [hsame] at hprivate
    exact hprivate
  apply hvalid.2 (.position position) output hstate
  simpa [canonicalizeMaterializedValues, LazyRevealProbe.State.hitAt,
    LazyRevealProbe.State.pendingAt] using hhit

set_option maxRecDepth 100000 in
theorem direct_valid_chain_of_done_maskedExpandedAdversaryImpl
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (query : (OracleWorld + SigningSpec).Domain)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult
      ((OracleWorld + SigningSpec).Range query × SplitHashCache))
    (hdirect : context = directDeferredContext context.state)
    (hvalid : context.Valid)
    (hchainValid : ChainState.ValidFor (fun _ => True) context.state)
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table
        ((maskedExpandedAdversaryImpl parameter root ftsSecret query).run cache))) :
    result.context = directDeferredContext result.context.state ∧
      result.context.Valid ∧
      ChainState.ValidFor (fun _ => True) result.context.state := by
  have hoption := mem_support_runDirectResolvedFromTable_of_done_detailed
    ((maskedExpandedAdversaryImpl parameter root ftsSecret query).run cache)
    context fuel table result hresult
  have hresultDirect : result.context = directDeferredContext result.context.state := by
    have hshape := directDetailedMaterialized_of_mem_runDirectResolvedDetailedFromTable
      ((maskedExpandedAdversaryImpl parameter root ftsSecret query).run cache)
      context.state fuel table (.done result) (by
        rw [← hdirect]
        exact hresult)
    exact hshape
  have hresultValid : result.context.Valid := by
    cases query with
    | inl worldQuery =>
        cases worldQuery with
        | inl n =>
            exact valid_of_done_runDirectResolvedDetailedFromTable_of_probeFree
              ((maskedExpandedAdversaryImpl parameter root ftsSecret (.inl (.inl n))).run cache)
              context fuel table result
              (by
                simpa [maskedExpandedAdversaryImpl, probingRomImpl] using
                  splitUniformImpl_probeFree n cache)
              hvalid hresult
        | inr input =>
            change ResolvedRunResult (HashOutput × SplitHashCache) at result
            change DirectDetailedResult.done result ∈ support
              (runDirectResolvedDetailedFromTable context fuel table
                ((probingHashQuery parameter input).run cache)) at hresult
            exact valid_of_done_runDirectResolvedDetailed_probingHashQuery parameter input
              context fuel table cache result hvalid hchainValid hresult
    | inr message =>
        exact valid_of_done_runDirectResolvedDetailedFromTable_of_probeFree
          ((maskedExpandedAdversaryImpl parameter root ftsSecret (.inr message)).run cache)
          context fuel table result
          (by
            simpa [maskedExpandedAdversaryImpl, maskedSigningImpl] using
              maskedSign_probeFree parameter root ftsSecret message cache)
          hvalid hresult
  have hresultChain : ChainState.ValidFor (fun _ => True) result.context.state := by
    apply chainValid_of_mem_runDirectResolvedFromTable (fun _ => True)
      (maskedExpandedAdversaryImpl parameter root ftsSecret query)
      context fuel table cache result
      ((preservesChainValidImpl_maskedExpandedAdversaryImpl_true parameter root ftsSecret) query)
      hchainValid hoption
  exact ⟨hresultDirect, hresultValid, hresultChain⟩

set_option maxRecDepth 100000 in
theorem probEvent_materializedPrivateStep_le
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (query : (OracleWorld + SigningSpec).Domain)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (nextObserve : DeferredContext → Nat →
      ((OracleWorld + SigningSpec).Range query × SplitHashCache) → ProbComp Bool)
    (epsilon terminalBound : ℝ≥0∞)
    (hdirect : context = directDeferredContext context.state)
    (hvalid : context.Valid)
    (hchainValid : ChainState.ValidFor (fun _ => True) context.state)
    (hcontinuation : ∀ result : ResolvedRunResult
        ((OracleWorld + SigningSpec).Range query × SplitHashCache),
      DirectDetailedResult.done result ∈ support
        (runDirectResolvedDetailedFromTable context fuel table
          ((maskedExpandedAdversaryImpl parameter root ftsSecret query).run cache)) →
      result.context = directDeferredContext result.context.state →
      result.context.Valid →
      ChainState.ValidFor (fun _ => True) result.context.state →
      DeferredCompletable table result.context →
      Pr[= true | nextObserve result.context result.remaining result.value] ≤
        (result.remaining : ℝ≥0∞) * epsilon + terminalBound) :
    Pr[= true |
      runDirectDetailedPrivateObserve
        (classifyCanonicalMaterializedPrivateObserve table nextObserve)
        context fuel table
        ((maskedExpandedAdversaryImpl parameter root ftsSecret query).run cache)] ≤
      (fuel : ℝ≥0∞) * epsilon + terminalBound := by
  rw [← probEvent_eq_eq_probOutput]
  unfold runDirectDetailedPrivateObserve
  apply probEvent_bind_le_of_forall_le
  intro detailedResult hdetailed
  have hshape := directDetailedMaterialized_of_mem_runDirectResolvedDetailedFromTable
    ((maskedExpandedAdversaryImpl parameter root ftsSecret query).run cache)
    context.state fuel table detailedResult (by
      rw [← hdirect]
      exact hdetailed)
  cases detailedResult with
  | stopped reason =>
      cases reason with
      | privateStructuralHit => exact False.elim hshape
      | ordinaryHit => simp [finishDirectDetailedPrivateObserve]
      | fuelExhausted => simp [finishDirectDetailedPrivateObserve]
  | done result =>
      have hinvariants := direct_valid_chain_of_done_maskedExpandedAdversaryImpl
        parameter root ftsSecret query context fuel table cache result hdirect hvalid
          hchainValid hdetailed
      have hclean := not_privateStructuralHit_canonicalize_of_direct_valid table
        result.context hinvariants.1 hinvariants.2.1
      simp only [finishDirectDetailedPrivateObserve]
      unfold classifyCanonicalMaterializedPrivateObserve
      simp only [hclean, ↓reduceIte]
      by_cases hcompletable : DeferredCompletable table result.context
      · simp only [hcompletable, ↓reduceIte]
        have hnext := hcontinuation result hdetailed hinvariants.1 hinvariants.2.1
          hinvariants.2.2 hcompletable
        rw [← probEvent_eq_eq_probOutput] at hnext
        refine hnext.trans ?_
        gcongr
        exact_mod_cast
          remaining_le_fuel_of_done_runDirectResolvedDetailedFromTable
            ((maskedExpandedAdversaryImpl parameter root ftsSecret query).run cache)
            context fuel table result hdetailed
      · simp [hcompletable]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem probEvent_directDetailedBoundaryCanonicalMaterializedPrivateObserve_false_le_zero
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hdirect : context = directDeferredContext context.state)
    (hvalid : context.Valid)
    (hchainValid : ChainState.ValidFor (fun _ => True) context.state) :
    Pr[= true |
      directDetailedBoundaryCanonicalMaterializedPrivateObserve
        (maskedExpandedAdversaryImpl parameter root ftsSecret) computation
        (fun _ _ _ => pure false) context fuel table cache] ≤
      (fuel : ℝ≥0∞) * 0 + 0 := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache with
  | pure value =>
      simp [directDetailedBoundaryCanonicalMaterializedPrivateObserve]
  | query_bind query next ih =>
      rw [directDetailedBoundaryCanonicalMaterializedPrivateObserve,
        OracleComp.construct_query_bind]
      apply probEvent_materializedPrivateStep_le parameter root ftsSecret query context fuel
        table cache (epsilon := 0) (terminalBound := 0)
      · exact hdirect
      · exact hvalid
      · exact hchainValid
      · intro result hresult hresultDirect hresultValid hresultChain hcompletable
        exact ih result.value.1 result.context result.remaining result.value.2
          hresultDirect hresultValid hresultChain

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem probEvent_runDirectDetailedPrivateObserve_probeFree_le_zero
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hprobeFree : ProbeFree computation)
    (hpreservesChain : PreservesChainValid (fun _ => True) computation)
    (hdirect : context = directDeferredContext context.state)
    (hvalid : context.Valid)
    (hchainValid : ChainState.ValidFor (fun _ => True) context.state)
    (hobserve : ∀ result : ResolvedRunResult (α × SplitHashCache),
      DirectDetailedResult.done result ∈ support
        (runDirectResolvedDetailedFromTable context fuel table (computation.run cache)) →
      result.context = directDeferredContext result.context.state →
      result.context.Valid →
      ChainState.ValidFor (fun _ => True) result.context.state →
      Pr[= true | observe result.context result.remaining result.value] ≤ 0) :
    Pr[= true |
      runDirectDetailedPrivateObserve observe context fuel table (computation.run cache)] ≤ 0 := by
  rw [← probEvent_eq_eq_probOutput]
  unfold runDirectDetailedPrivateObserve
  apply probEvent_bind_le_of_forall_le
  intro detailedResult hdetailed
  have hshape := directDetailedMaterialized_of_mem_runDirectResolvedDetailedFromTable
    (computation.run cache) context.state fuel table detailedResult (by
      rw [← hdirect]
      exact hdetailed)
  cases detailedResult with
  | stopped reason =>
      cases reason with
      | privateStructuralHit => exact False.elim hshape
      | ordinaryHit => simp [finishDirectDetailedPrivateObserve]
      | fuelExhausted => simp [finishDirectDetailedPrivateObserve]
  | done result =>
      have hoption := mem_support_runDirectResolvedFromTable_of_done_detailed
        (computation.run cache) context fuel table result hdetailed
      have hresultValid :=
        valid_of_done_runDirectResolvedDetailedFromTable_of_probeFree
          (computation.run cache) context fuel table result (hprobeFree cache) hvalid hdetailed
      have hresultChain := chainValid_of_mem_runDirectResolvedFromTable
        (fun _ => True) computation context fuel table cache result hpreservesChain
        hchainValid hoption
      simp only [finishDirectDetailedPrivateObserve]
      have hnext := hobserve result hdetailed hshape hresultValid hresultChain
      rwa [← probEvent_eq_eq_probOutput] at hnext

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem probEvent_materializedCanonicalPrivateRetained_le_zero
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[= true |
      materializedCanonicalPrivateRetained adversary parameter table ftsSecret fuel] ≤ 0 := by
  change Pr[= true |
    runDirectDetailedPrivateObserve
      (materializedCanonicalPrivateRetainedRestObserve adversary parameter table ftsSecret)
      (directDeferredContext
        (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate))
      fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)] ≤ 0
  apply probEvent_runDirectDetailedPrivateObserve_probeFree_le_zero
    maskedPublishedTreeRoot
    (materializedCanonicalPrivateRetainedRestObserve adversary parameter table ftsSecret)
    (directDeferredContext
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate))
    fuel table emptySplitHashCache
  · exact maskedPublishedTreeRoot_probeFree
  · exact preservesChainValid_maskedPublishedTreeRoot_true
  · rfl
  · exact DeferredContext.valid_empty
  · exact ChainState.validFor_empty (fun _ => True)
  · intro result hresult hresultDirect hresultValid hresultChain
    unfold materializedCanonicalPrivateRetainedRestObserve
    simpa using
      (probEvent_directDetailedBoundaryCanonicalMaterializedPrivateObserve_false_le_zero
        parameter result.value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩)
        result.context result.remaining table result.value.2 hresultDirect hresultValid
          hresultChain)

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledMaterializedCanonicalPrivateRetained_le
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat) :
    Pr[= true |
      sampledMaterializedCanonicalPrivateRetained adversary parameter ftsSecret q] ≤
      (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  unfold sampledMaterializedCanonicalPrivateRetained
  rw [← probEvent_eq_eq_probOutput]
  have hzero : Pr[fun hit : Bool => hit = true | do
      let table ← sampleOtsHashTable
      materializedCanonicalPrivateRetained adversary parameter table ftsSecret q] ≤ 0 := by
    apply probEvent_bind_le_of_forall_le
    intro table _htable
    rw [probEvent_eq_eq_probOutput]
    exact probEvent_materializedCanonicalPrivateRetained_le_zero
      adversary parameter table ftsSecret q
  exact hzero.trans (by positivity)

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

set_option maxRecDepth 100000 in
theorem probEvent_granularPrivateStep_signing_le
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
      PublishedValues result.context.state →
      DeferredCompletable table
        (canonicalizeMaterializedValues table result.context) →
      Pr[= true |
          nextObserve (canonicalizeMaterializedValues table result.context)
            result.remaining result.value] ≤
        (result.remaining : ℝ≥0∞) * epsilon + terminalBound) :
    Pr[= true |
      runDirectDetailedPrivateObserve
        (canonicalizeDirectDetailedPrivateObserve table nextObserve)
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
      unfold canonicalizeDirectDetailedPrivateObserve
      simp only [hsafe, ↓reduceIte]
      by_cases hpublished : PublishedValues result.context.state
      · simp only [hpublished, ↓reduceIte]
        unfold classifyDirectDetailedPrivateObserve
        simp only [hsafe, ↓reduceIte]
        by_cases hnextCompletable : DeferredCompletable table
            (canonicalizeMaterializedValues table result.context)
        · simp only [hnextCompletable, ↓reduceIte]
          have hnext := hcontinuation result hresult hpublished hnextCompletable
          rw [← probEvent_eq_eq_probOutput] at hnext
          refine hnext.trans ?_
          gcongr
          exact_mod_cast
            remaining_le_fuel_of_done_runDirectResolvedDetailedFromTable
              ((maskedExpandedAdversaryImpl parameter root ftsSecret
                (.inr message)).run cache)
              context fuel table result hresult
        · simp [hnextCompletable]
      · simp [hpublished]

end SphincsSecurity.Concrete.OtsProbeSimulation
