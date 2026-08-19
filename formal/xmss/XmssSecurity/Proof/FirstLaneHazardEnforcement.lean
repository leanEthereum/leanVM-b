import XmssSecurity.Proof.FirstLaneEagerSimulation
import XmssSecurity.Proof.RunObservedAppend

open OracleComp OracleSpec

namespace XmssSecurity.FirstLaneOracleSimulation

variable {Index : Type} [Fintype Index] [DecidableEq Index]

noncomputable def hazardEnforcementImpl :
    QueryImpl (World Index) (StateT Nat (OracleComp (World Index))) :=
  fun input fuel =>
    match input with
    | .uniform n => do
        let output ← uniformQuery n
        pure (output, fuel)
    | .encodingQuery epoch =>
        match fuel with
        | 0 => do
            let output ← liftProbComp uniformHashOutput
            pure (output, 0)
        | remaining + 1 => do
            let output ← encodingQuery epoch
            pure (output, remaining)
    | .encodingSignAttempt epoch => do
        let output ← encodingSignAttemptQuery epoch
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

noncomputable def enforceHazardBound
    (fuel : Nat) (computation : OracleComp (World Index) α) :
    OracleComp (World Index) α :=
  Prod.fst <$> (simulateQ hazardEnforcementImpl computation).run fuel

omit [Fintype Index] [DecidableEq Index] in
theorem liftProbComp_isHazardQueryBoundP (computation : ProbComp α) :
    (liftProbComp (Index := Index) computation).IsQueryBoundP
      IsHazardQuery 0 := by
  unfold liftProbComp
  apply OracleComp.IsQueryBoundP.simulateQ_of_step
    (p := fun _ : unifSpec.Domain => False)
    (q := IsHazardQuery)
    (OracleComp.isQueryBoundP_false computation 0)
  · intro input hfalse
    exact hfalse.elim
  · intro input _
    change (uniformQuery (Index := Index) input).IsQueryBoundP
      IsHazardQuery 0
    rw [uniformQuery, OracleComp.isQueryBoundP_query_iff]
    simp [IsHazardQuery]

omit [Fintype Index] [DecidableEq Index] in
theorem simulate_hazardEnforcementImpl_run_isHazardQueryBoundP
    (computation : OracleComp (World Index) α) (fuel : Nat) :
    (simulateQ hazardEnforcementImpl computation).run fuel |>.IsQueryBoundP
      IsHazardQuery fuel := by
  induction computation using OracleComp.inductionOn generalizing fuel with
  | pure result => simp
  | query_bind input next ih =>
      rw [simulateQ_query_bind, StateT.run_bind]
      cases input with
      | uniform n =>
          change (uniformQuery n >>= fun output =>
            (simulateQ hazardEnforcementImpl (next output)).run fuel)
              |>.IsQueryBoundP IsHazardQuery fuel
          rw [uniformQuery, OracleComp.isQueryBoundP_query_bind_iff]
          constructor
          · simp [IsHazardQuery]
          · intro output
            simpa [IsHazardQuery] using ih output fuel
      | encodingQuery epoch =>
          cases fuel with
          | zero =>
              change (liftProbComp uniformHashOutput >>= fun output =>
                (simulateQ hazardEnforcementImpl (next output)).run 0)
                  |>.IsQueryBoundP IsHazardQuery 0
              apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
                (liftProbComp_isHazardQueryBoundP uniformHashOutput)
              intro output _
              exact ih output 0
          | succ remaining =>
              change (encodingQuery epoch >>= fun output =>
                (simulateQ hazardEnforcementImpl (next output)).run remaining)
                  |>.IsQueryBoundP IsHazardQuery (remaining + 1)
              rw [encodingQuery, OracleComp.isQueryBoundP_query_bind_iff]
              constructor
              · simp [IsHazardQuery]
              · intro output
                simpa [IsHazardQuery] using ih output remaining
      | encodingSignAttempt epoch =>
          change (encodingSignAttemptQuery epoch >>= fun output =>
            (simulateQ hazardEnforcementImpl (next output)).run fuel)
              |>.IsQueryBoundP IsHazardQuery fuel
          rw [encodingSignAttemptQuery,
            OracleComp.isQueryBoundP_query_bind_iff]
          constructor
          · simp [IsHazardQuery]
          · intro output
            simpa [IsHazardQuery] using ih output fuel
      | probe index target =>
          cases fuel with
          | zero =>
              change (simulateQ hazardEnforcementImpl (next ())).run 0
                |>.IsQueryBoundP IsHazardQuery 0
              exact ih () 0
          | succ remaining =>
              change (probeQuery index target >>= fun _ =>
                (simulateQ hazardEnforcementImpl (next ())).run remaining)
                  |>.IsQueryBoundP IsHazardQuery (remaining + 1)
              rw [probeQuery, OracleComp.isQueryBoundP_query_bind_iff]
              constructor
              · simp [IsHazardQuery]
              · intro _
                simpa [IsHazardQuery] using ih () remaining
      | reveal index =>
          change (revealQuery index >>= fun value =>
            (simulateQ hazardEnforcementImpl (next value)).run fuel)
              |>.IsQueryBoundP IsHazardQuery fuel
          rw [revealQuery, OracleComp.isQueryBoundP_query_bind_iff]
          constructor
          · simp [IsHazardQuery]
          · intro value
            simpa [IsHazardQuery] using ih value fuel

omit [Fintype Index] [DecidableEq Index] in
theorem enforceHazardBound_isHazardQueryBoundP
    (fuel : Nat) (computation : OracleComp (World Index) α) :
    (enforceHazardBound fuel computation).IsQueryBoundP IsHazardQuery fuel := by
  unfold enforceHazardBound
  apply (OracleComp.isQueryBoundP_map_iff _ _ fuel).2
  exact simulate_hazardEnforcementImpl_run_isHazardQueryBoundP computation fuel

def enforceHazardTrace : Nat → ActionTrace Index → ActionTrace Index
  | _, [] => []
  | fuel, .encoding (.sign epoch output) :: trace =>
      .encoding (.sign epoch output) :: enforceHazardTrace fuel trace
  | fuel, .chain (.reveal index value) :: trace =>
      .chain (.reveal index value) :: enforceHazardTrace fuel trace
  | 0, .encoding (.query _ _) :: trace => enforceHazardTrace 0 trace
  | fuel + 1, .encoding (.query epoch output) :: trace =>
      .encoding (.query epoch output) :: enforceHazardTrace fuel trace
  | 0, .chain (.probe _ _) :: trace => enforceHazardTrace 0 trace
  | fuel + 1, .chain (.probe index target) :: trace =>
      .chain (.probe index target) :: enforceHazardTrace fuel trace

omit [Fintype Index] [DecidableEq Index] in
theorem enforceHazardTrace_eq_self_of_count_le
    (trace : ActionTrace Index) (fuel : Nat)
    (hcount : hazardCount trace ≤ fuel) :
    enforceHazardTrace fuel trace = trace := by
  induction trace generalizing fuel with
  | nil => rfl
  | cons action trace ih =>
      cases action with
      | encoding action =>
          cases action with
          | sign epoch output =>
              simp only [hazardCount] at hcount
              simp only [enforceHazardTrace, List.cons.injEq, true_and]
              exact ih fuel hcount
          | query epoch output =>
              cases fuel with
              | zero => simp [hazardCount] at hcount
              | succ fuel =>
                  simp only [hazardCount, Nat.succ_le_succ_iff] at hcount
                  simp only [enforceHazardTrace, List.cons.injEq, true_and]
                  exact ih fuel hcount
      | chain action =>
          cases action with
          | reveal index value =>
              simp only [hazardCount] at hcount
              simp only [enforceHazardTrace, List.cons.injEq, true_and]
              exact ih fuel hcount
          | probe index target =>
              cases fuel with
              | zero => simp [hazardCount] at hcount
              | succ fuel =>
                  simp only [hazardCount, Nat.succ_le_succ_iff] at hcount
                  simp only [enforceHazardTrace, List.cons.injEq, true_and]
                  exact ih fuel hcount

omit [Fintype Index] [DecidableEq Index] in
theorem enforceHazardTrace_append
    (fuel : Nat) (left right : ActionTrace Index) :
    enforceHazardTrace fuel (left ++ right) =
      enforceHazardTrace fuel left ++
        enforceHazardTrace (fuel - hazardCount left) right := by
  induction left generalizing fuel with
  | nil => simp [hazardCount, enforceHazardTrace]
  | cons action left ih =>
      cases action with
      | encoding action =>
          cases action with
          | sign epoch output =>
              simp [hazardCount, enforceHazardTrace, ih]
          | query epoch output =>
              cases fuel with
              | zero => simp [hazardCount, enforceHazardTrace, ih]
              | succ fuel => simp [hazardCount, enforceHazardTrace, ih]
      | chain action =>
          cases action with
          | reveal index value =>
              simp [hazardCount, enforceHazardTrace, ih]
          | probe index target =>
              cases fuel with
              | zero => simp [hazardCount, enforceHazardTrace, ih]
              | succ fuel => simp [hazardCount, enforceHazardTrace, ih]

omit [Fintype Index] [DecidableEq Index] in
theorem CappedEncodingMonitor.runObserved_append_eq_true_of_prefix
    (state : EncodingMonitor.State) (left right : EncodingActionTrace)
    (hhit : CappedEncodingMonitor.runObserved state left = true) :
    CappedEncodingMonitor.runObserved state (left ++ right) = true := by
  induction left generalizing state with
  | nil => simp [CappedEncodingMonitor.runObserved] at hhit
  | cons action left ih =>
      cases happly : CappedEncodingMonitor.State.applyObserved state action with
      | none => simp [CappedEncodingMonitor.runObserved, happly] at hhit
      | some result =>
          rcases result with ⟨nextState, hit⟩
          cases hit with
          | false =>
              simp only [List.cons_append,
                CappedEncodingMonitor.runObserved, happly,
                Bool.false_or] at hhit ⊢
              exact ih nextState hhit
          | true =>
              simp [List.cons_append, CappedEncodingMonitor.runObserved,
                happly]

theorem CombinedHit.append_of_prefix
    (table : Index → Digest) (left right : ActionTrace Index)
    (hhit : CombinedHit table left) : CombinedHit table (left ++ right) := by
  rcases hhit with hencoding | hchain
  · apply Or.inl
    rw [ActionTrace.encodingActions_append]
    exact CappedEncodingMonitor.runObserved_append_eq_true_of_prefix
      EncodingMonitor.State.empty left.encodingActions right.encodingActions
        hencoding
  · apply Or.inr
    rw [ActionTrace.chainActions_append]
    exact RevealProbeOracleSimulation.runObserved_append_eq_true_of_prefix
      table AdaptiveRevealMonitor.State.empty left.chainActions
        right.chainActions hchain

theorem CombinedHit.enforce_append_of_prefix
    (table : Index → Digest) (fuel : Nat)
    (left right : ActionTrace Index)
    (hhit : CombinedHit table (enforceHazardTrace fuel left)) :
    CombinedHit table (enforceHazardTrace fuel (left ++ right)) := by
  rw [enforceHazardTrace_append]
  exact CombinedHit.append_of_prefix table (enforceHazardTrace fuel left)
    (enforceHazardTrace (fuel - hazardCount left) right) hhit

omit [Fintype Index] [DecidableEq Index] in
theorem simulate_eagerTrace_hazardEnforcementImpl_run
    (table : Index → Digest)
    (computation : OracleComp (World Index) α) (fuel : Nat) :
    (simulateQ (eagerTraceImpl table)
      ((simulateQ hazardEnforcementImpl computation).run fuel)).run =
        (fun result =>
          ((result.1, fuel - hazardCount result.2),
            enforceHazardTrace fuel result.2)) <$>
          (simulateQ (eagerTraceImpl table) computation).run := by
  induction computation using OracleComp.inductionOn generalizing fuel with
  | pure result => simp [hazardCount, enforceHazardTrace]
  | query_bind input next ih =>
      rw [simulateQ_query_bind, StateT.run_bind]
      cases input with
      | uniform n =>
          change
            (simulateQ (eagerTraceImpl table) (uniformQuery n >>= fun output =>
              (simulateQ hazardEnforcementImpl (next output)).run fuel)).run =
            (fun result =>
              ((result.1, fuel - hazardCount result.2),
                enforceHazardTrace fuel result.2)) <$>
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
      | encodingQuery epoch =>
          cases fuel with
          | zero =>
              change
                (simulateQ (eagerTraceImpl table)
                  (liftProbComp uniformHashOutput >>= fun output =>
                    (simulateQ hazardEnforcementImpl (next output)).run 0)).run =
                (fun result =>
                  ((result.1, 0 - hazardCount result.2),
                    enforceHazardTrace 0 result.2)) <$>
                  (simulateQ (eagerTraceImpl table)
                    (encodingQuery epoch >>= next)).run
              rw [simulateQ_bind, WriterT.run_bind',
                simulate_eagerTrace_liftProbComp]
              simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
                Function.comp_apply]
              rw [simulateQ_bind, WriterT.run_bind']
              simp [encodingQuery, eagerTraceImpl, eagerImpl, traceFragment,
                QueryImpl.withTraceAppend_apply, WriterT.run_tell]
              apply bind_congr
              intro output
              have hmap :
                  Prod.map (id : (α × Nat) → α × Nat)
                      (fun trace : ActionTrace Index => trace) = id := by
                funext result
                cases result
                rfl
              rw [hmap]
              simp only [Function.comp_id, bind_pure]
              simp only [enforceHazardTrace]
              change
                (simulateQ (eagerTraceImpl table)
                  ((simulateQ hazardEnforcementImpl (next output)).run 0)).run =
                (fun result =>
                  ((result.1, 0),
                    enforceHazardTrace 0 result.2)) <$>
                  (simulateQ (eagerTraceImpl table) (next output)).run
              rw [ih output 0]
              simp
          | succ remaining =>
              change
                (simulateQ (eagerTraceImpl table)
                  (encodingQuery epoch >>= fun output =>
                    (simulateQ hazardEnforcementImpl (next output)).run
                      remaining)).run =
                (fun result =>
                  ((result.1, remaining + 1 - hazardCount result.2),
                    enforceHazardTrace (remaining + 1) result.2)) <$>
                  (simulateQ (eagerTraceImpl table)
                    (encodingQuery epoch >>= next)).run
              rw [simulateQ_bind, WriterT.run_bind', simulateQ_bind,
                WriterT.run_bind']
              simp [encodingQuery, eagerTraceImpl, eagerImpl, traceFragment,
                QueryImpl.withTraceAppend_apply, WriterT.run_tell]
              apply bind_congr
              intro output
              change
                (Prod.map id
                  (fun trace => .encoding (.query epoch output) :: trace)) <$>
                    (simulateQ (eagerTraceImpl table)
                      ((simulateQ hazardEnforcementImpl (next output)).run
                        remaining)).run = _
              rw [ih output remaining]
              simp [hazardCount, enforceHazardTrace]
              rfl
      | encodingSignAttempt epoch =>
          change
            (simulateQ (eagerTraceImpl table)
              (encodingSignAttemptQuery epoch >>= fun output =>
                (simulateQ hazardEnforcementImpl (next output)).run fuel)).run =
            (fun result =>
              ((result.1, fuel - hazardCount result.2),
                enforceHazardTrace fuel result.2)) <$>
              (simulateQ (eagerTraceImpl table)
                (encodingSignAttemptQuery epoch >>= next)).run
          rw [simulateQ_bind, WriterT.run_bind', simulateQ_bind,
            WriterT.run_bind']
          simp [encodingSignAttemptQuery, eagerTraceImpl, eagerImpl,
            traceFragment, QueryImpl.withTraceAppend_apply, WriterT.run_tell]
          apply bind_congr
          intro output
          change
            (Prod.map id
              (fun trace => .encoding (.sign epoch output) :: trace)) <$>
                (simulateQ (eagerTraceImpl table)
                  ((simulateQ hazardEnforcementImpl (next output)).run fuel)).run = _
          rw [ih output fuel]
          simp [hazardCount, enforceHazardTrace]
          rfl
      | probe index target =>
          cases fuel with
          | zero =>
              change
                (simulateQ (eagerTraceImpl table)
                  ((simulateQ hazardEnforcementImpl (next ())).run 0)).run =
                (fun result =>
                  ((result.1, 0 - hazardCount result.2),
                    enforceHazardTrace 0 result.2)) <$>
                  (simulateQ (eagerTraceImpl table)
                    (probeQuery index target >>= next)).run
              rw [ih () 0]
              simp [probeQuery, eagerTraceImpl, eagerImpl, traceFragment,
                QueryImpl.withTraceAppend_apply, WriterT.run_tell,
                enforceHazardTrace]
          | succ remaining =>
              change
                (simulateQ (eagerTraceImpl table)
                  (probeQuery index target >>= fun _ =>
                    (simulateQ hazardEnforcementImpl (next ())).run
                      remaining)).run =
                (fun result =>
                  ((result.1, remaining + 1 - hazardCount result.2),
                    enforceHazardTrace (remaining + 1) result.2)) <$>
                  (simulateQ (eagerTraceImpl table)
                    (probeQuery index target >>= next)).run
              rw [simulateQ_bind, WriterT.run_bind', simulateQ_bind,
                WriterT.run_bind']
              simp [probeQuery, eagerTraceImpl, eagerImpl, traceFragment,
                QueryImpl.withTraceAppend_apply, WriterT.run_tell]
              change
                (Prod.map id
                  (fun trace => .chain (.probe index target) :: trace)) <$>
                    (simulateQ (eagerTraceImpl table)
                      ((simulateQ hazardEnforcementImpl (next ())).run
                        remaining)).run = _
              rw [ih () remaining]
              simp [hazardCount, enforceHazardTrace]
              rfl
      | reveal index =>
          change
            (simulateQ (eagerTraceImpl table)
              (revealQuery index >>= fun value =>
                (simulateQ hazardEnforcementImpl (next value)).run fuel)).run =
            (fun result =>
              ((result.1, fuel - hazardCount result.2),
                enforceHazardTrace fuel result.2)) <$>
              (simulateQ (eagerTraceImpl table)
                (revealQuery index >>= next)).run
          rw [simulateQ_bind, WriterT.run_bind', simulateQ_bind,
            WriterT.run_bind']
          simp [revealQuery, eagerTraceImpl, eagerImpl, traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell]
          change
            (Prod.map id
              (fun trace => .chain (.reveal index (table index)) :: trace)) <$>
                (simulateQ (eagerTraceImpl table)
                  ((simulateQ hazardEnforcementImpl
                    (next (table index))).run fuel)).run = _
          rw [ih (table index) fuel]
          simp [hazardCount, enforceHazardTrace]
          rfl

omit [Fintype Index] [DecidableEq Index] in
theorem simulate_eagerTrace_enforceHazardBound
    (table : Index → Digest)
    (computation : OracleComp (World Index) α) (fuel : Nat) :
    (simulateQ (eagerTraceImpl table)
      (enforceHazardBound fuel computation)).run =
        (fun result => (result.1, enforceHazardTrace fuel result.2)) <$>
          (simulateQ (eagerTraceImpl table) computation).run := by
  unfold enforceHazardBound
  rw [simulateQ_map, WriterT.run_map',
    simulate_eagerTrace_hazardEnforcementImpl_run]
  simp [Functor.map_map, Prod.map]

def enforceEagerResult
    (fuel : Nat)
    (result : (Index → Digest) × (α × ActionTrace Index)) :
    (Index → Digest) × (α × ActionTrace Index) :=
  (result.1, (result.2.1, enforceHazardTrace fuel result.2.2))

omit [Fintype Index] [DecidableEq Index] in
theorem enforceEagerResult_eq_self_of_count_le
    (fuel : Nat)
    (result : (Index → Digest) × (α × ActionTrace Index))
    (hcount : hazardCount result.2.2 ≤ fuel) :
    enforceEagerResult fuel result = result := by
  unfold enforceEagerResult
  rw [enforceHazardTrace_eq_self_of_count_le result.2.2 fuel hcount]

theorem eagerExperiment_enforceHazardBound_eq_map
    (computation : OracleComp (World Index) α) (fuel : Nat) :
    eagerExperiment (enforceHazardBound fuel computation) =
      enforceEagerResult fuel <$> eagerExperiment computation := by
  unfold eagerExperiment
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  apply bind_congr
  intro table
  rw [simulate_eagerTrace_enforceHazardBound]
  rw [map_eq_bind_pure_comp]
  simp only [bind_assoc, pure_bind, Function.comp_apply, enforceEagerResult]

end XmssSecurity.FirstLaneOracleSimulation
