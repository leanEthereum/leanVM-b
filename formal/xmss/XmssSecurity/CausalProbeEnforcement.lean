import XmssSecurity.CausalFilteredGame

open OracleComp OracleSpec

namespace XmssSecurity.RevealProbeOracleSimulation

variable {Index : Type} [Fintype Index] [DecidableEq Index]

def probeEnforcementImpl :
    QueryImpl (World Index) (StateT Nat (OracleComp (World Index))) :=
  fun input fuel =>
    match input with
    | .uniform n => do
        let output ← uniformQuery n
        pure (output, fuel)
    | .probe index target =>
        match fuel with
        | 0 => pure ((), 0)
        | remaining + 1 => do
            probeQuery index target
            pure ((), remaining)
    | .reveal index => do
        let value ← revealQuery index
        pure (value, fuel)

noncomputable def enforceProbeBound
    (fuel : Nat) (computation : OracleComp (World Index) α) :
    OracleComp (World Index) α :=
  Prod.fst <$> (simulateQ probeEnforcementImpl computation).run fuel

theorem simulate_probeEnforcementImpl_run_isProbeQueryBoundP
    (computation : OracleComp (World Index) α) (fuel : Nat) :
    (simulateQ probeEnforcementImpl computation).run fuel |>.IsQueryBoundP
      IsProbeQuery fuel := by
  induction computation using OracleComp.inductionOn generalizing fuel with
  | pure result => simp
  | query_bind input next ih =>
      rw [simulateQ_query_bind, StateT.run_bind]
      cases input with
      | uniform n =>
          change (uniformQuery n >>= fun output =>
            (simulateQ probeEnforcementImpl (next output)).run fuel)
              |>.IsQueryBoundP IsProbeQuery fuel
          rw [uniformQuery, OracleComp.isQueryBoundP_query_bind_iff]
          constructor
          · simp [IsProbeQuery]
          · intro output
            simpa [IsProbeQuery] using ih output fuel
      | probe index target =>
          cases fuel with
          | zero =>
              change (simulateQ probeEnforcementImpl (next ())).run 0
                |>.IsQueryBoundP IsProbeQuery 0
              exact ih () 0
          | succ remaining =>
              change (probeQuery index target >>= fun _ =>
                (simulateQ probeEnforcementImpl (next ())).run remaining)
                  |>.IsQueryBoundP IsProbeQuery (remaining + 1)
              rw [probeQuery, OracleComp.isQueryBoundP_query_bind_iff]
              constructor
              · simp [IsProbeQuery]
              · intro _
                simpa [IsProbeQuery] using ih () remaining
      | reveal index =>
          change (revealQuery index >>= fun value =>
            (simulateQ probeEnforcementImpl (next value)).run fuel)
              |>.IsQueryBoundP IsProbeQuery fuel
          rw [revealQuery, OracleComp.isQueryBoundP_query_bind_iff]
          constructor
          · simp [IsProbeQuery]
          · intro value
            simpa [IsProbeQuery] using ih value fuel

theorem enforceProbeBound_isProbeQueryBoundP
    (fuel : Nat) (computation : OracleComp (World Index) α) :
    (enforceProbeBound fuel computation).IsQueryBoundP IsProbeQuery fuel := by
  unfold enforceProbeBound
  apply (OracleComp.isQueryBoundP_map_iff _ _ fuel).2
  exact simulate_probeEnforcementImpl_run_isProbeQueryBoundP computation fuel

def enforceProbeTrace : Nat → ActionTrace Index → ActionTrace Index
  | _, [] => []
  | fuel, .reveal index value :: trace =>
      .reveal index value :: enforceProbeTrace fuel trace
  | 0, .probe _ _ :: trace => enforceProbeTrace 0 trace
  | fuel + 1, .probe index target :: trace =>
      .probe index target :: enforceProbeTrace fuel trace

theorem enforceProbeTrace_eq_self_of_count_le
    (trace : ActionTrace Index) (fuel : Nat)
    (hcount : observedProbeCount trace ≤ fuel) :
    enforceProbeTrace fuel trace = trace := by
  induction trace generalizing fuel with
  | nil => rfl
  | cons action trace ih =>
      cases action with
      | reveal index value =>
          simp only [observedProbeCount] at hcount
          simp only [enforceProbeTrace, List.cons.injEq, true_and]
          exact ih fuel hcount
      | probe index target =>
          cases fuel with
          | zero => simp [observedProbeCount] at hcount
          | succ fuel =>
              simp only [observedProbeCount, Nat.succ_le_succ_iff] at hcount
              simp only [enforceProbeTrace, List.cons.injEq, true_and]
              exact ih fuel hcount

theorem enforceProbeTrace_append_of_count_le
    (left right : ActionTrace Index) (fuel : Nat)
    (hcount : observedProbeCount left ≤ fuel) :
    enforceProbeTrace fuel (left ++ right) =
      left ++ enforceProbeTrace (fuel - observedProbeCount left) right := by
  induction left generalizing fuel with
  | nil => simp [observedProbeCount, enforceProbeTrace]
  | cons action left ih =>
      cases action with
      | reveal index value =>
          simp only [observedProbeCount] at hcount ⊢
          simp only [List.cons_append, enforceProbeTrace, List.cons.injEq,
            true_and]
          exact ih fuel hcount
      | probe index target =>
          cases fuel with
          | zero => simp [observedProbeCount] at hcount
          | succ fuel =>
              simp only [observedProbeCount, Nat.succ_le_succ_iff] at hcount
              simp only [List.cons_append, enforceProbeTrace, List.cons.injEq,
                true_and]
              rw [observedProbeCount, Nat.succ_sub_succ_eq_sub]
              exact ih fuel hcount

theorem enforceProbeTrace_append
    (left right : ActionTrace Index) (fuel : Nat) :
    enforceProbeTrace fuel (left ++ right) =
      enforceProbeTrace fuel left ++
        enforceProbeTrace (fuel - observedProbeCount left) right := by
  induction left generalizing fuel with
  | nil => simp [observedProbeCount, enforceProbeTrace]
  | cons action left ih =>
      cases action with
      | reveal index value =>
          simp only [List.cons_append, enforceProbeTrace, observedProbeCount,
            List.cons.injEq, true_and]
          exact ih fuel
      | probe index target =>
          cases fuel with
          | zero =>
              simp only [List.cons_append, enforceProbeTrace,
                Nat.zero_sub, observedProbeCount]
              simpa using ih 0
          | succ fuel =>
              simp only [List.cons_append, enforceProbeTrace,
                observedProbeCount, List.cons.injEq, true_and]
              rw [Nat.succ_sub_succ_eq_sub]
              exact ih fuel

theorem runObserved_eq_true_of_initial_tableHit
    (table : Index → Digest) (state : AdaptiveRevealMonitor.State Index)
    (trace : ActionTrace Index)
    (hhit : tableHits state table = true) :
    runObserved table state trace = true := by
  unfold tableHits at hhit
  simp only [decide_eq_true_eq] at hhit
  obtain ⟨index, hindex⟩ := hhit
  induction trace generalizing state index with
  | nil =>
      simp only [runObserved]
      unfold tableHits
      simp only [decide_eq_true_eq]
      exact ⟨index, hindex⟩
  | cons action trace ih =>
      cases action with
      | probe probeIndex target =>
          cases hrevealed : state.revealed probeIndex with
          | none =>
              rw [runObserved, hrevealed]
              apply ih (state.addPending probeIndex target) index
              by_cases heq : index = probeIndex
              · subst index
                simp [AdaptiveRevealMonitor.State.addPending, hindex]
              · simpa [AdaptiveRevealMonitor.State.addPending,
                  Function.update_of_ne heq] using hindex
          | some value =>
              rw [runObserved, hrevealed]
              exact ih state index hindex
      | reveal revealIndex value =>
          cases hrevealed : state.revealed revealIndex with
          | some revealedValue =>
              rw [runObserved, hrevealed]
              exact ih state index hindex
          | none =>
              rw [runObserved, hrevealed]
              by_cases hcontains : table revealIndex ∈ state.pending revealIndex
              · simp [hcontains]
              · rw [if_neg hcontains]
                apply ih (state.install revealIndex (table revealIndex)) index
                by_cases heq : index = revealIndex
                · subst index
                  exact False.elim (hcontains hindex)
                · simpa [AdaptiveRevealMonitor.State.install,
                    Function.update_of_ne heq] using hindex

theorem runObserved_append_eq_true_of_prefix
    (table : Index → Digest) (state : AdaptiveRevealMonitor.State Index)
    (trace suffix : ActionTrace Index)
    (hhit : runObserved table state trace = true) :
    runObserved table state (trace ++ suffix) = true := by
  induction trace generalizing state with
  | nil =>
      exact runObserved_eq_true_of_initial_tableHit table state suffix hhit
  | cons action trace ih =>
      cases action with
      | probe index target =>
          cases hrevealed : state.revealed index with
          | none =>
              rw [runObserved, hrevealed] at hhit
              rw [List.cons_append, runObserved, hrevealed]
              exact ih (state.addPending index target) hhit
          | some value =>
              rw [runObserved, hrevealed] at hhit
              rw [List.cons_append, runObserved, hrevealed]
              exact ih state hhit
      | reveal index value =>
          cases hrevealed : state.revealed index with
          | some revealedValue =>
              rw [runObserved, hrevealed] at hhit
              rw [List.cons_append, runObserved, hrevealed]
              exact ih state hhit
          | none =>
              rw [runObserved, hrevealed] at hhit
              rw [List.cons_append, runObserved, hrevealed]
              by_cases hcontains : table index ∈ state.pending index
              · simp [hcontains]
              · rw [if_neg hcontains] at hhit ⊢
                exact ih (state.install index (table index)) hhit

theorem runObserved_enforceProbeTrace_append_eq_true
    (table : Index → Digest) (state : AdaptiveRevealMonitor.State Index)
    (left right : ActionTrace Index) (fuel : Nat)
    (hcount : observedProbeCount left ≤ fuel)
    (hhit : runObserved table state left = true) :
    runObserved table state (enforceProbeTrace fuel (left ++ right)) = true := by
  rw [enforceProbeTrace_append_of_count_le left right fuel hcount]
  exact runObserved_append_eq_true_of_prefix table state left _ hhit

theorem runObserved_enforceProbeTrace_append_eq_true_of_prefix
    (table : Index → Digest) (state : AdaptiveRevealMonitor.State Index)
    (left right : ActionTrace Index) (fuel : Nat)
    (hhit : runObserved table state (enforceProbeTrace fuel left) = true) :
    runObserved table state (enforceProbeTrace fuel (left ++ right)) = true := by
  rw [enforceProbeTrace_append left right fuel]
  exact runObserved_append_eq_true_of_prefix table state
    (enforceProbeTrace fuel left) _ hhit

theorem simulate_eagerTrace_support_observedProbeCount_le
    (table : Index → Digest) (computation : OracleComp (World Index) α)
    (fuel : Nat) (hbound : computation.IsQueryBoundP IsProbeQuery fuel)
    (result : α × ActionTrace Index)
    (hresult : result ∈ support
      ((simulateQ (eagerTraceImpl table) computation).run)) :
    observedProbeCount result.2 ≤ fuel := by
  induction computation using OracleComp.inductionOn generalizing fuel result with
  | pure value =>
      simp only [simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      simp [observedProbeCount]
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [simulateQ_query_bind, WriterT.run_bind', mem_support_bind_iff]
        at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      cases input with
      | uniform n =>
          simp [eagerTraceImpl, eagerImpl, traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hhead
          obtain ⟨output, rfl⟩ := hhead
          rw [support_map] at htail
          obtain ⟨tail, htail, rfl⟩ := htail
          exact ih output fuel
            (by simpa [IsProbeQuery] using hbound.2 output) tail htail
      | probe index target =>
          cases fuel with
          | zero => simp [IsProbeQuery] at hbound
          | succ remaining =>
              simp [eagerTraceImpl, eagerImpl, traceFragment,
                QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hhead
              subst head
              rw [support_map] at htail
              obtain ⟨tail, htail, rfl⟩ := htail
              have htailCount := ih () remaining
                (by simpa [IsProbeQuery] using hbound.2 ()) tail htail
              simpa [Prod.map, observedProbeCount] using
                Nat.succ_le_succ htailCount
      | reveal index =>
          simp [eagerTraceImpl, eagerImpl, traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hhead
          subst head
          rw [support_map] at htail
          obtain ⟨tail, htail, rfl⟩ := htail
          exact ih (table index) fuel
            (by simpa [IsProbeQuery] using hbound.2 (table index)) tail htail

omit [Fintype Index] [DecidableEq Index] in
theorem simulate_eagerTrace_probeEnforcementImpl_run
    (table : Index → Digest)
    (computation : OracleComp (World Index) α) (fuel : Nat) :
    (simulateQ (eagerTraceImpl table)
      ((simulateQ probeEnforcementImpl computation).run fuel)).run =
        (fun result =>
          ((result.1, fuel - observedProbeCount result.2),
            enforceProbeTrace fuel result.2)) <$>
          (simulateQ (eagerTraceImpl table) computation).run := by
  induction computation using OracleComp.inductionOn generalizing fuel with
  | pure result => simp [observedProbeCount, enforceProbeTrace]
  | query_bind input next ih =>
      rw [simulateQ_query_bind, StateT.run_bind]
      cases input with
      | uniform n =>
          change
            (simulateQ (eagerTraceImpl table) (uniformQuery n >>= fun output =>
              (simulateQ probeEnforcementImpl (next output)).run fuel)).run =
            (fun result =>
              ((result.1, fuel - observedProbeCount result.2),
                enforceProbeTrace fuel result.2)) <$>
              (simulateQ (eagerTraceImpl table)
                (uniformQuery n >>= next)).run
          rw [simulateQ_bind, WriterT.run_bind', simulateQ_bind,
            WriterT.run_bind']
          simp [uniformQuery, eagerTraceImpl, eagerImpl, traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell]
          apply bind_congr
          intro output
          have hmap :
              Prod.map (id : (α × Nat) → α × Nat)
                  (fun trace : ActionTrace Index => trace) = id := by
            funext result
            cases result
            rfl
          rw [hmap, id_map]
          exact ih output fuel
      | probe index target =>
          cases fuel with
          | zero =>
              change
                (simulateQ (eagerTraceImpl table)
                  ((simulateQ probeEnforcementImpl (next ())).run 0)).run =
                (fun result =>
                  ((result.1, 0 - observedProbeCount result.2),
                    enforceProbeTrace 0 result.2)) <$>
                  (simulateQ (eagerTraceImpl table)
                    (probeQuery index target >>= next)).run
              rw [ih () 0]
              simp [probeQuery, eagerTraceImpl, eagerImpl, traceFragment,
                QueryImpl.withTraceAppend_apply, WriterT.run_tell,
                observedProbeCount, enforceProbeTrace]
          | succ remaining =>
              change
                (simulateQ (eagerTraceImpl table)
                  (probeQuery index target >>= fun _ =>
                    (simulateQ probeEnforcementImpl (next ())).run remaining)).run =
                (fun result =>
                  ((result.1, remaining + 1 - observedProbeCount result.2),
                    enforceProbeTrace (remaining + 1) result.2)) <$>
                  (simulateQ (eagerTraceImpl table)
                    (probeQuery index target >>= next)).run
              rw [simulateQ_bind, WriterT.run_bind', simulateQ_bind,
                WriterT.run_bind']
              simp [probeQuery, eagerTraceImpl, eagerImpl, traceFragment,
                QueryImpl.withTraceAppend_apply, WriterT.run_tell]
              change
                (Prod.map id
                  (fun trace => .probe index target :: trace)) <$>
                    (simulateQ (eagerTraceImpl table)
                      ((simulateQ probeEnforcementImpl (next ())).run
                        remaining)).run = _
              rw [ih () remaining]
              simp [observedProbeCount, enforceProbeTrace]
              rfl
      | reveal index =>
          change
            (simulateQ (eagerTraceImpl table)
              (revealQuery index >>= fun value =>
                (simulateQ probeEnforcementImpl (next value)).run fuel)).run =
            (fun result =>
              ((result.1, fuel - observedProbeCount result.2),
                enforceProbeTrace fuel result.2)) <$>
              (simulateQ (eagerTraceImpl table)
                (revealQuery index >>= next)).run
          rw [simulateQ_bind, WriterT.run_bind', simulateQ_bind,
            WriterT.run_bind']
          simp [revealQuery, eagerTraceImpl, eagerImpl, traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell]
          change
            (Prod.map id
              (fun trace => .reveal index (table index) :: trace)) <$>
                (simulateQ (eagerTraceImpl table)
                  ((simulateQ probeEnforcementImpl
                    (next (table index))).run fuel)).run = _
          rw [ih (table index) fuel]
          simp [observedProbeCount, enforceProbeTrace]
          rfl

omit [Fintype Index] [DecidableEq Index] in
theorem simulate_eagerTrace_enforceProbeBound
    (table : Index → Digest)
    (computation : OracleComp (World Index) α) (fuel : Nat) :
    (simulateQ (eagerTraceImpl table)
      (enforceProbeBound fuel computation)).run =
        (fun result => (result.1, enforceProbeTrace fuel result.2)) <$>
          (simulateQ (eagerTraceImpl table) computation).run := by
  unfold enforceProbeBound
  rw [simulateQ_map, WriterT.run_map',
    simulate_eagerTrace_probeEnforcementImpl_run]
  simp [Functor.map_map, Function.comp_def, Prod.map]

def enforceEagerResult
    (fuel : Nat)
    (result : (Index → Digest) × (α × ActionTrace Index)) :
    (Index → Digest) × (α × ActionTrace Index) :=
  (result.1, (result.2.1, enforceProbeTrace fuel result.2.2))

theorem enforceEagerResult_eq_self_of_count_le
    (fuel : Nat)
    (result : (Index → Digest) × (α × ActionTrace Index))
    (hcount : observedProbeCount result.2.2 ≤ fuel) :
    enforceEagerResult fuel result = result := by
  unfold enforceEagerResult
  rw [enforceProbeTrace_eq_self_of_count_le result.2.2 fuel hcount]

theorem observedHit_enforceEagerResult_iff_of_count_le
    (fuel : Nat)
    (result : (Index → Digest) × (α × ActionTrace Index))
    (hcount : observedProbeCount result.2.2 ≤ fuel) :
    ObservedHit (enforceEagerResult fuel result) ↔ ObservedHit result := by
  rw [enforceEagerResult_eq_self_of_count_le fuel result hcount]

theorem eagerExperiment_enforceProbeBound_eq_map
    (computation : OracleComp (World Index) α) (fuel : Nat) :
    eagerExperiment (enforceProbeBound fuel computation) =
      enforceEagerResult fuel <$> eagerExperiment computation := by
  unfold eagerExperiment
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  apply bind_congr
  intro table
  rw [simulate_eagerTrace_enforceProbeBound]
  rw [map_eq_bind_pure_comp]
  simp only [bind_assoc, pure_bind, Function.comp_apply,
    enforceEagerResult]

end XmssSecurity.RevealProbeOracleSimulation
