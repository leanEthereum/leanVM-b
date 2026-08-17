import XmssSecurity.RevealProbeOracleSimulation

open OracleComp OracleSpec

namespace XmssSecurity.RevealProbeOracleSimulation

variable {Source Target : Type}

def reindexImpl (embed : Source → Target) :
    QueryImpl (World Source) (OracleComp (World Target)) := fun input =>
  match input with
  | .uniform n => uniformQuery n
  | .probe index target => probeQuery (embed index) target
  | .reveal index => revealQuery (embed index)

noncomputable def reindex (embed : Source → Target)
    (computation : OracleComp (World Source) α) :
    OracleComp (World Target) α :=
  simulateQ (reindexImpl embed) computation

@[simp]
theorem reindex_pure (embed : Source → Target) (value : α) :
    reindex embed (pure value : OracleComp (World Source) α) = pure value := rfl

theorem reindex_bind (embed : Source → Target)
    (computation : OracleComp (World Source) α)
    (next : α → OracleComp (World Source) β) :
    reindex embed (computation >>= next) =
      reindex embed computation >>= fun value => reindex embed (next value) := by
  exact simulateQ_bind (reindexImpl embed) computation next

@[simp]
theorem reindex_uniformQuery (embed : Source → Target) (n : Nat) :
    reindex embed (uniformQuery n : OracleComp (World Source) (Fin (n + 1))) =
      uniformQuery n := by
  simp [reindex, uniformQuery, reindexImpl]

@[simp]
theorem reindex_probeQuery (embed : Source → Target)
    (index : Source) (target : Digest) :
    reindex embed (probeQuery index target) =
      probeQuery (embed index) target := by
  simp [reindex, probeQuery, reindexImpl]

@[simp]
theorem reindex_revealQuery (embed : Source → Target) (index : Source) :
    reindex embed (revealQuery index) = revealQuery (embed index) := by
  simp [reindex, revealQuery, reindexImpl]

theorem reindex_isProbeQueryBoundP
    (embed : Source → Target)
    (computation : OracleComp (World Source) α) (bound : Nat)
    (hbound : computation.IsQueryBoundP IsProbeQuery bound) :
    (reindex embed computation).IsQueryBoundP IsProbeQuery bound := by
  induction computation using OracleComp.inductionOn generalizing bound with
  | pure value => trivial
  | query_bind input next ih =>
      rw [reindex, simulateQ_query_bind]
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      cases input with
      | uniform n =>
          change Fin (n + 1) → OracleComp (World Source) α at next
          change (uniformQuery n >>= fun output => reindex embed (next output))
            |>.IsQueryBoundP IsProbeQuery bound
          rw [uniformQuery]
          rw [OracleComp.isQueryBoundP_query_bind_iff]
          constructor
          · simp [IsProbeQuery]
          · intro output
            exact ih output bound (by
              simpa [IsProbeQuery] using hbound.2 output)
      | probe index target =>
          change Unit → OracleComp (World Source) α at next
          change (probeQuery (embed index) target >>= fun output =>
              reindex embed (next output))
            |>.IsQueryBoundP IsProbeQuery bound
          rw [probeQuery]
          rw [OracleComp.isQueryBoundP_query_bind_iff]
          constructor
          · simpa [IsProbeQuery] using hbound.1
          · intro output
            exact ih output (bound - 1) (by
              simpa [IsProbeQuery] using hbound.2 output)
      | reveal index =>
          change Digest → OracleComp (World Source) α at next
          change (revealQuery (embed index) >>= fun output =>
              reindex embed (next output))
            |>.IsQueryBoundP IsProbeQuery bound
          rw [revealQuery]
          rw [OracleComp.isQueryBoundP_query_bind_iff]
          constructor
          · simp [IsProbeQuery]
          · intro output
            exact ih output bound (by
              simpa [IsProbeQuery] using hbound.2 output)

def mapObservedAction (embed : Source → Target) :
    ObservedAction Source → ObservedAction Target
  | .probe index target => .probe (embed index) target
  | .reveal index value => .reveal (embed index) value

def mapActionTrace (embed : Source → Target) (trace : ActionTrace Source) :
    ActionTrace Target :=
  trace.map (mapObservedAction embed)

theorem simulate_eagerTrace_reindex_run
    (embed : Source → Target) (table : Target → Digest)
    (computation : OracleComp (World Source) α) :
    (simulateQ (eagerTraceImpl table) (reindex embed computation)).run =
      (fun result => (result.1, mapActionTrace embed result.2)) <$>
        (simulateQ (eagerTraceImpl (table ∘ embed)) computation).run := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [reindex, mapActionTrace]
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          change Fin (n + 1) → OracleComp (World Source) α at next
          change (simulateQ (eagerTraceImpl table)
              (reindex embed (uniformQuery n >>= next))).run =
            (fun result => (result.1, mapActionTrace embed result.2)) <$>
              (simulateQ (eagerTraceImpl (table ∘ embed))
                (uniformQuery n >>= next)).run
          rw [reindex_bind, reindex_uniformQuery, simulateQ_bind,
            WriterT.run_bind', simulateQ_bind, WriterT.run_bind']
          simp only [uniformQuery, simulateQ_query,
            OracleQuery.input_query, OracleQuery.cont_query, eagerTraceImpl,
            QueryImpl.withTraceAppend_apply, eagerImpl, traceFragment,
            WriterT.run_monadLift', WriterT.run_tell, WriterT.run_bind',
            map_bind, bind_assoc, pure_bind]
          simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
            WriterT.run_pure', Prod.map_apply, List.nil_append, id_eq,
            Function.comp_apply]
          apply bind_congr
          intro output
          change Fin (n + 1) at output
          have hrec := ih output
          change (simulateQ ((eagerImpl table).withTraceAppend traceFragment)
              (reindex embed (next output))).run = _ at hrec
          rw [hrec]
          simp [mapActionTrace, map_eq_bind_pure_comp, bind_assoc]
          rfl
      | probe index target =>
          change Unit → OracleComp (World Source) α at next
          change (simulateQ (eagerTraceImpl table)
              (reindex embed (probeQuery index target >>= next))).run =
            (fun result => (result.1, mapActionTrace embed result.2)) <$>
              (simulateQ (eagerTraceImpl (table ∘ embed))
                (probeQuery index target >>= next)).run
          rw [reindex_bind, reindex_probeQuery, simulateQ_bind,
            WriterT.run_bind', simulateQ_bind, WriterT.run_bind']
          simp only [probeQuery, simulateQ_query,
            OracleQuery.input_query, OracleQuery.cont_query, eagerTraceImpl,
            QueryImpl.withTraceAppend_apply, eagerImpl, traceFragment,
            WriterT.run_monadLift', WriterT.run_tell, WriterT.run_bind',
            map_bind, bind_assoc, pure_bind]
          simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
            WriterT.run_pure', Prod.map_apply, id_eq, Function.comp_apply]
          have hrec := ih ()
          change (simulateQ ((eagerImpl table).withTraceAppend traceFragment)
              (reindex embed (next ()))).run = _ at hrec
          rw [hrec]
          simp [mapActionTrace, mapObservedAction,
            map_eq_bind_pure_comp, bind_assoc]
          rfl
      | reveal index =>
          change Digest → OracleComp (World Source) α at next
          change (simulateQ (eagerTraceImpl table)
              (reindex embed (revealQuery index >>= next))).run =
            (fun result => (result.1, mapActionTrace embed result.2)) <$>
              (simulateQ (eagerTraceImpl (table ∘ embed))
                (revealQuery index >>= next)).run
          rw [reindex_bind, reindex_revealQuery, simulateQ_bind,
            WriterT.run_bind', simulateQ_bind, WriterT.run_bind']
          simp only [revealQuery, simulateQ_query,
            OracleQuery.input_query, OracleQuery.cont_query, eagerTraceImpl,
            QueryImpl.withTraceAppend_apply, eagerImpl, traceFragment,
            WriterT.run_monadLift', WriterT.run_tell, WriterT.run_bind',
            map_bind, bind_assoc, pure_bind]
          simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
            WriterT.run_pure', Prod.map_apply, id_eq, Function.comp_apply]
          have hrec := ih (table (embed index))
          change (simulateQ ((eagerImpl table).withTraceAppend traceFragment)
              (reindex embed (next (table (embed index))))).run = _ at hrec
          rw [hrec]
          simp [mapActionTrace, mapObservedAction,
            map_eq_bind_pure_comp, bind_assoc]
          rfl

variable [Fintype Source] [DecidableEq Source]
  [Fintype Target] [DecidableEq Target]

def StatesCorrespond (embed : Source → Target)
    (source : AdaptiveRevealMonitor.State Source)
    (target : AdaptiveRevealMonitor.State Target) : Prop :=
  (∀ index,
      target.pending (embed index) = source.pending index ∧
      target.revealed (embed index) = source.revealed index) ∧
    ∀ index, index ∉ Set.range embed → target.pending index = ∅

omit [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target] in
theorem statesCorrespond_empty (embed : Source → Target) :
    StatesCorrespond embed AdaptiveRevealMonitor.State.empty
      AdaptiveRevealMonitor.State.empty := by
  constructor
  · intro index
    exact ⟨rfl, rfl⟩
  · intro index _
    rfl

omit [Fintype Source] [Fintype Target] in
theorem StatesCorrespond.addPending
    (embed : Source → Target) (hembed : Function.Injective embed)
    {source : AdaptiveRevealMonitor.State Source}
    {target : AdaptiveRevealMonitor.State Target}
    (hstates : StatesCorrespond embed source target)
    (index : Source) (digest : Digest) :
    StatesCorrespond embed (source.addPending index digest)
      (target.addPending (embed index) digest) := by
  classical
  constructor
  · intro candidate
    by_cases heq : candidate = index
    · subst candidate
      simp [AdaptiveRevealMonitor.State.addPending, hstates.1 index]
    · have hembedNe : embed candidate ≠ embed index := fun h => heq (hembed h)
      simp [AdaptiveRevealMonitor.State.addPending, heq, hembedNe,
        hstates.1 candidate]
  · intro candidate houtside
    have hne : candidate ≠ embed index := by
      intro heq
      exact houtside ⟨index, heq.symm⟩
    simp [AdaptiveRevealMonitor.State.addPending, hne,
      hstates.2 candidate houtside]

omit [Fintype Source] [Fintype Target] in
theorem StatesCorrespond.install
    (embed : Source → Target) (hembed : Function.Injective embed)
    {source : AdaptiveRevealMonitor.State Source}
    {target : AdaptiveRevealMonitor.State Target}
    (hstates : StatesCorrespond embed source target)
    (index : Source) (digest : Digest) :
    StatesCorrespond embed (source.install index digest)
      (target.install (embed index) digest) := by
  classical
  constructor
  · intro candidate
    by_cases heq : candidate = index
    · subst candidate
      simp [AdaptiveRevealMonitor.State.install]
    · have hembedNe : embed candidate ≠ embed index := fun h => heq (hembed h)
      simp [AdaptiveRevealMonitor.State.install, heq, hembedNe,
        hstates.1 candidate]
  · intro candidate houtside
    have hne : candidate ≠ embed index := by
      intro heq
      exact houtside ⟨index, heq.symm⟩
    simp [AdaptiveRevealMonitor.State.install, hne,
      hstates.2 candidate houtside]

omit [DecidableEq Source] in
theorem tableHits_eq_of_statesCorrespond
    (embed : Source → Target)
    (sourceTable : Source → Digest) (targetTable : Target → Digest)
    (htable : targetTable ∘ embed = sourceTable)
    {source : AdaptiveRevealMonitor.State Source}
    {target : AdaptiveRevealMonitor.State Target}
    (hstates : StatesCorrespond embed source target) :
    tableHits source sourceTable = tableHits target targetTable := by
  classical
  unfold tableHits
  simp only [decide_eq_decide]
  constructor
  · rintro ⟨index, hhit⟩
    exact ⟨embed index, by
      rw [hstates.1 index |>.1]
      change (targetTable ∘ embed) index ∈ source.pending index
      rw [congrFun htable index]
      exact hhit⟩
  · rintro ⟨index, hhit⟩
    by_cases hrange : index ∈ Set.range embed
    · obtain ⟨sourceIndex, rfl⟩ := hrange
      exact ⟨sourceIndex, by
        rw [hstates.1 sourceIndex |>.1] at hhit
        rw [← congrFun htable sourceIndex]
        exact hhit⟩
    · rw [hstates.2 index hrange] at hhit
      simp at hhit

theorem runObserved_mapActionTrace
    (embed : Source → Target) (hembed : Function.Injective embed)
    (sourceTable : Source → Digest) (targetTable : Target → Digest)
    (htable : targetTable ∘ embed = sourceTable)
    (source : AdaptiveRevealMonitor.State Source)
    (target : AdaptiveRevealMonitor.State Target)
    (hstates : StatesCorrespond embed source target)
    (trace : ActionTrace Source) :
    runObserved sourceTable source trace =
      runObserved targetTable target (mapActionTrace embed trace) := by
  induction trace generalizing source target with
  | nil =>
      exact tableHits_eq_of_statesCorrespond embed sourceTable targetTable
        htable hstates
  | cons action rest ih =>
      cases action with
      | probe index digest =>
          rw [mapActionTrace]
          simp only [List.map_cons, mapObservedAction, runObserved]
          have hreveal := hstates.1 index |>.2
          cases hsource : source.revealed index with
          | some value =>
              rw [← hreveal] at hsource
              rw [hsource]
              exact ih source target hstates
          | none =>
              rw [← hreveal] at hsource
              rw [hsource]
              exact ih (source.addPending index digest)
                (target.addPending (embed index) digest)
                (hstates.addPending embed hembed index digest)
      | reveal index value =>
          rw [mapActionTrace]
          simp only [List.map_cons, mapObservedAction, runObserved]
          have hreveal := hstates.1 index |>.2
          cases hsource : source.revealed index with
          | some digest =>
              rw [← hreveal] at hsource
              rw [hsource]
              exact ih source target hstates
          | none =>
              rw [← hreveal] at hsource
              rw [hsource]
              have hvalue : targetTable (embed index) = sourceTable index := by
                simpa [Function.comp_apply] using congrFun htable index
              rw [hvalue, hstates.1 index |>.1]
              by_cases hhit : sourceTable index ∈ source.pending index
              · simp [hhit]
              · simp only [hhit, ↓reduceIte]
                exact ih (source.install index (sourceTable index))
                  (target.install (embed index) (sourceTable index))
                  (hstates.install embed hembed index (sourceTable index))

theorem runObserved_empty_mapActionTrace
    (embed : Source → Target) (hembed : Function.Injective embed)
    (table : Target → Digest) (trace : ActionTrace Source) :
    runObserved (table ∘ embed) AdaptiveRevealMonitor.State.empty trace =
      runObserved table AdaptiveRevealMonitor.State.empty
        (mapActionTrace embed trace) := by
  exact runObserved_mapActionTrace embed hembed (table ∘ embed) table rfl
    AdaptiveRevealMonitor.State.empty AdaptiveRevealMonitor.State.empty
      (statesCorrespond_empty embed) trace

noncomputable local instance sourceSampleableTable :
    SampleableType (Source → Digest) :=
  SampleableType.ofFintype (Source → Digest)

noncomputable local instance targetSampleableTable :
    SampleableType (Target → Digest) :=
  SampleableType.ofFintype (Target → Digest)

theorem map_observed_eagerExperiment_reindex_eq
    (embed : Source → Target) (hembed : Function.Injective embed)
    (computation : OracleComp (World Source) α) :
    (fun result => runObserved result.1 AdaptiveRevealMonitor.State.empty
        result.2.2) <$>
      eagerExperiment (reindex embed computation) =
    (do
      let table ← eagerTableSample (Index := Target)
      let result ←
        (simulateQ (eagerTraceImpl (table ∘ embed)) computation).run
      pure (runObserved (table ∘ embed)
        AdaptiveRevealMonitor.State.empty result.2)) := by
  unfold eagerExperiment
  simp only [map_bind]
  apply bind_congr
  intro table
  rw [simulate_eagerTrace_reindex_run]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  apply bind_congr
  intro result
  exact congrArg pure
    (runObserved_empty_mapActionTrace embed hembed table result.2 |>.symm)

theorem evalDist_map_observed_eagerExperiment_reindex_eq
    (embed : Source → Target) (hembed : Function.Injective embed)
    (computation : OracleComp (World Source) α) :
    𝒟[(fun result => runObserved result.1
        AdaptiveRevealMonitor.State.empty result.2.2) <$>
      eagerExperiment (reindex embed computation)] =
    𝒟[(fun result => runObserved result.1
        AdaptiveRevealMonitor.State.empty result.2.2) <$>
      eagerExperiment computation] := by
  rw [map_observed_eagerExperiment_reindex_eq embed hembed computation]
  unfold eagerExperiment
  simp only [map_bind]
  let resume := fun table : Source → Digest => do
    let result ← (simulateQ (eagerTraceImpl table) computation).run
    pure (runObserved table AdaptiveRevealMonitor.State.empty result.2)
  change 𝒟[eagerTableSample (Index := Target) >>= fun table =>
      resume (table ∘ embed)] =
    𝒟[eagerTableSample (Index := Source) >>= resume]
  rw [← bind_map_left]
  have hrestrict :
      𝒟[(fun table : Target → Digest => table ∘ embed) <$>
          eagerTableSample (Index := Target)] =
        𝒟[eagerTableSample (Index := Source)] := by
    simpa [eagerTableSample] using
      evalDist_uniformSample_map_comp_injective (R := Digest) hembed
  rw [evalDist_bind, hrestrict, ← evalDist_bind]

theorem eagerExperiment_reindex_observedHit_probability_eq
    (embed : Source → Target) (hembed : Function.Injective embed)
    (computation : OracleComp (World Source) α) :
    Pr[ObservedHit | eagerExperiment (reindex embed computation)] =
      Pr[ObservedHit | eagerExperiment computation] := by
  change Pr[(fun result => runObserved result.1
      AdaptiveRevealMonitor.State.empty result.2.2 = true) |
    eagerExperiment (reindex embed computation)] = _
  change Pr[((· = true) ∘ fun result => runObserved result.1
      AdaptiveRevealMonitor.State.empty result.2.2) |
    eagerExperiment (reindex embed computation)] = _
  rw [← probEvent_map]
  change _ = Pr[((· = true) ∘ fun result => runObserved result.1
      AdaptiveRevealMonitor.State.empty result.2.2) |
    eagerExperiment computation]
  rw [← probEvent_map]
  exact probEvent_congr' (fun _ _ => Iff.rfl)
    (evalDist_map_observed_eagerExperiment_reindex_eq embed hembed computation)

end XmssSecurity.RevealProbeOracleSimulation
