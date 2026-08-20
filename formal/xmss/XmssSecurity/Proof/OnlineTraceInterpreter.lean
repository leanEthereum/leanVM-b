import XmssSecurity.Proof.FirstLaneOnlineMonitor
import XmssSecurity.Proof.MarginalCoupling
import XmssSecurity.Proof.CacheAgreement
import VCVio.ProgramLogic.Relational.Quantitative

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.FirstLaneOracleSimulation

variable {Index : Type} [Fintype Index] [DecidableEq Index]

noncomputable def OnlineState.observe
    (table : Index → Digest) (state : OnlineState Index) :
    ObservedAction Index → Except Bool (OnlineState Index)
  | .encoding (.query epoch output) =>
      match state.fuel with
      | 0 => .error (RevealProbeOracleSimulation.tableHits state.chain table)
      | remaining + 1 =>
          match state.encoding with
          | none => .ok { state with fuel := remaining }
          | some encoding =>
              match CappedEncodingMonitor.State.applyObserved encoding
                  (.query epoch output) with
              | none => .ok { state with encoding := none, fuel := remaining }
              | some (next, hit) =>
                  if hit then .error true
                  else .ok { state with encoding := some next, fuel := remaining }
  | .encoding (.sign epoch output) =>
      match state.encoding with
      | none => .ok state
      | some encoding =>
          match CappedEncodingMonitor.State.applyObserved encoding
              (.sign epoch output) with
          | none => .ok { state with encoding := none }
          | some (next, hit) =>
              if hit then .error true
              else .ok { state with encoding := some next }
  | .chain (.probe index target) =>
      match state.fuel with
      | 0 => .error (RevealProbeOracleSimulation.tableHits state.chain table)
      | remaining + 1 =>
          match state.chain.revealed index with
          | some _ => .ok { state with fuel := remaining }
          | none => .ok { state with
              chain := state.chain.addPending index target
              fuel := remaining }
  | .chain (.reveal index _value) =>
      match state.chain.revealed index with
      | some _ => .ok state
      | none =>
          let value := table index
          if value ∈ state.chain.pending index then .error true
          else .ok { state with chain := state.chain.install index value }

noncomputable def OnlineState.observeAll
    (table : Index → Digest) :
    OnlineState Index → ActionTrace Index → Except Bool (OnlineState Index)
  | state, [] => .ok state
  | state, action :: rest =>
      (state.observe table action).bind fun next => next.observeAll table rest

theorem OnlineState.observeAll_append
    (table : Index → Digest) (state : OnlineState Index)
    (left right : ActionTrace Index) :
    state.observeAll table (left ++ right) =
      (state.observeAll table left).bind fun next =>
        next.observeAll table right := by
  induction left generalizing state with
  | nil => rfl
  | cons action left ih =>
      simp only [List.cons_append, OnlineState.observeAll]
      cases state.observe table action with
      | error error => rfl
      | ok next => exact ih next

theorem OnlineState.observe_preserves_stateAgrees
    (table : Index → Digest) (state next : OnlineState Index)
    (action : ObservedAction Index)
    (hagrees : RevealProbeOracleSimulation.StateAgrees table state.chain)
    (hnext : state.observe table action = .ok next) :
    RevealProbeOracleSimulation.StateAgrees table next.chain := by
  rcases action with action | action
  · rcases action with ⟨epoch, output⟩ | ⟨epoch, output⟩
    · cases state with
      | mk encoding chain fuel =>
          cases fuel with
          | zero => simp [OnlineState.observe] at hnext
          | succ remaining =>
              cases encoding with
              | none =>
                  simp [OnlineState.observe] at hnext
                  subst next
                  exact hagrees
              | some encoding =>
                  cases happly : CappedEncodingMonitor.State.applyObserved
                      encoding (.query epoch output) with
                  | none =>
                      simp [OnlineState.observe, happly] at hnext
                      subst next
                      exact hagrees
                  | some result =>
                      rcases result with ⟨encoding, hit⟩
                      cases hit with
                      | false =>
                          simp [OnlineState.observe, happly] at hnext
                          subst next
                          exact hagrees
                      | true => simp [OnlineState.observe, happly] at hnext
    · cases state with
      | mk encoding chain fuel =>
          cases encoding with
          | none =>
              simp [OnlineState.observe] at hnext
              subst next
              exact hagrees
          | some encoding =>
              cases happly : CappedEncodingMonitor.State.applyObserved
                  encoding (.sign epoch output) with
              | none =>
                  simp [OnlineState.observe, happly] at hnext
                  subst next
                  exact hagrees
              | some result =>
                  rcases result with ⟨encoding, hit⟩
                  cases hit with
                  | false =>
                      simp [OnlineState.observe, happly] at hnext
                      subst next
                      exact hagrees
                  | true => simp [OnlineState.observe, happly] at hnext
  · rcases action with ⟨index, target⟩ | ⟨index, value⟩
    · cases state with
      | mk encoding chain fuel =>
          cases fuel with
          | zero => simp [OnlineState.observe] at hnext
          | succ remaining =>
              cases hrevealed : chain.revealed index with
              | none =>
                  simp [OnlineState.observe, hrevealed] at hnext
                  subst next
                  exact hagrees
              | some value =>
                  simp [OnlineState.observe, hrevealed] at hnext
                  subst next
                  exact hagrees
    · cases state with
      | mk encoding chain fuel =>
          cases hrevealed : chain.revealed index with
          | some value =>
              simp [OnlineState.observe, hrevealed] at hnext
              subst next
              exact hagrees
          | none =>
              by_cases hhit : table index ∈ chain.pending index
              · simp [OnlineState.observe, hrevealed, hhit] at hnext
              · have hinstalled := hagrees.install index
                simp [OnlineState.observe, hrevealed, hhit] at hnext
                subst next
                exact hinstalled

theorem OnlineState.observeAll_preserves_stateAgrees
    (table : Index → Digest) (state next : OnlineState Index)
    (trace : ActionTrace Index)
    (hagrees : RevealProbeOracleSimulation.StateAgrees table state.chain)
    (hnext : state.observeAll table trace = .ok next) :
    RevealProbeOracleSimulation.StateAgrees table next.chain := by
  induction trace generalizing state with
  | nil =>
      simp [OnlineState.observeAll] at hnext
      subst next
      exact hagrees
  | cons action trace ih =>
      simp only [OnlineState.observeAll] at hnext
      cases haction : state.observe table action with
      | error error =>
          rw [haction] at hnext
          cases hnext
      | ok middle =>
          rw [haction] at hnext
          change middle.observeAll table trace = .ok next at hnext
          exact ih middle
            (state.observe_preserves_stateAgrees table middle action hagrees
              haction) hnext

noncomputable def observedResult
    (table : Index → Digest) (state : OnlineState Index)
    (result : α × ActionTrace Index) : Except Bool (α × OnlineState Index) :=
  (state.observeAll table result.2).map fun next => (result.1, next)

theorem observedResult_append_error
    (table : Index → Digest) (state : OnlineState Index)
    (tracePrefix suffix : ActionTrace Index) (value : α) (error : Bool)
    (hprefix : state.observeAll table tracePrefix = .error error) :
    observedResult table state (value, tracePrefix ++ suffix) = .error error := by
  rw [observedResult, OnlineState.observeAll_append, hprefix]
  rfl

theorem observedResult_append_ok
    (table : Index → Digest) (state next : OnlineState Index)
    (tracePrefix suffix : ActionTrace Index) (value : α)
    (hprefix : state.observeAll table tracePrefix = .ok next) :
    observedResult table state (value, tracePrefix ++ suffix) =
      observedResult table next (value, suffix) := by
  rw [observedResult, OnlineState.observeAll_append, hprefix]
  rfl

theorem evalDist_map_const_probComp
    (computation : ProbComp α) (value : β) :
    evalDist ((fun _ => value) <$> computation) =
      evalDist (pure value : ProbComp β) := by
  apply evalDist_ext
  intro output
  simp

theorem onlineImpl_query_run_eq_observedResult
    (table : Index → Digest) (input : (World Index).Domain)
    (state : OnlineState Index)
    (hagrees : RevealProbeOracleSimulation.StateAgrees table state.chain) :
    evalDist ((onlineImpl table input).run state).run =
      evalDist (observedResult table state <$>
        (eagerTraceImpl table input).run) := by
  cases input with
  | uniform n =>
      rw [onlineImpl_uniform_run]
      simp [eagerTraceImpl, eagerImpl,
        QueryImpl.withTraceAppend_apply, traceFragment, observedResult,
        OnlineState.observeAll, Except.map]
  | encodingQuery epoch =>
      cases state with
      | mk encoding chain fuel =>
          cases fuel with
          | zero =>
              rw [onlineImpl_encodingQuery_zero_run]
              simp [eagerTraceImpl,
                eagerImpl, QueryImpl.withTraceAppend_apply, traceFragment,
                observedResult, OnlineState.observeAll, OnlineState.observe,
                Except.map, Except.bind]
              symm
              apply OracleComp.ProgramLogic.Relational.spmf_map_const_of_no_failure
              exact probFailure_of_liftM_PMF uniformHashOutput
          | succ remaining =>
              cases encoding with
              | none =>
                  rw [onlineImpl_encodingQuery_succ_none_run]
                  simp [
                    eagerTraceImpl, eagerImpl,
                    QueryImpl.withTraceAppend_apply, traceFragment,
                    observedResult, OnlineState.observeAll,
                    OnlineState.observe, Except.map, Except.bind]
              | some encoding =>
                  rw [onlineImpl_encodingQuery_succ_some_run]
                  simp [eagerTraceImpl, eagerImpl,
                    QueryImpl.withTraceAppend_apply, traceFragment,
                    observedResult, OnlineState.observeAll,
                    OnlineState.observe, Except.map, Except.bind]
                  apply congrArg (fun observe => observe <$>
                    (liftM uniformHashOutput : SPMF HashOutput))
                  funext output
                  cases happly : CappedEncodingMonitor.State.applyObserved
                      encoding (.query epoch output) with
                  | none => rfl
                  | some result =>
                      rcases result with ⟨next, hit⟩
                      cases hit <;> rfl
  | encodingSignAttempt epoch =>
      cases state with
      | mk encoding chain fuel =>
          cases encoding with
          | none =>
              rw [onlineImpl_encodingSignAttempt_none_run]
              simp [
                eagerTraceImpl, eagerImpl,
                QueryImpl.withTraceAppend_apply, traceFragment,
                observedResult, OnlineState.observeAll, OnlineState.observe,
                Except.map, Except.bind]
          | some encoding =>
              rw [onlineImpl_encodingSignAttempt_some_run]
              simp [eagerTraceImpl, eagerImpl,
                QueryImpl.withTraceAppend_apply, traceFragment,
                observedResult, OnlineState.observeAll, OnlineState.observe,
                Except.map, Except.bind]
              apply congrArg (fun observe => observe <$>
                (liftM uniformHashOutput : SPMF HashOutput))
              funext output
              cases happly : CappedEncodingMonitor.State.applyObserved
                  encoding (.sign epoch output) with
              | none => rfl
              | some result =>
                  rcases result with ⟨next, hit⟩
                  cases hit <;> rfl
  | probe index target =>
      cases state with
      | mk encoding chain fuel =>
          cases fuel with
          | zero =>
              rw [onlineImpl_probe_zero_run]
              simp [eagerTraceImpl, eagerImpl,
                QueryImpl.withTraceAppend_apply, traceFragment,
                observedResult, OnlineState.observeAll, OnlineState.observe,
                Except.map, Except.bind]
          | succ remaining =>
              rw [onlineImpl_probe_succ_run]
              simp [eagerTraceImpl, eagerImpl,
                QueryImpl.withTraceAppend_apply, traceFragment,
                observedResult, OnlineState.observeAll, OnlineState.observe,
                Except.map, Except.bind]
              cases hrevealed : chain.revealed index <;>
                simp
  | reveal index =>
      cases state with
      | mk encoding chain fuel =>
          cases hrevealed : chain.revealed index with
          | none =>
              rw [onlineImpl_reveal_run]
              simp [eagerTraceImpl, eagerImpl,
                QueryImpl.withTraceAppend_apply, traceFragment,
                observedResult, OnlineState.observeAll, OnlineState.observe,
                Except.map, Except.bind, hrevealed]
              by_cases hhit : table index ∈ chain.pending index <;>
                simp [hhit]
          | some value =>
              have hvalue := hagrees index value hrevealed
              rw [onlineImpl_reveal_run]
              simp [eagerTraceImpl, eagerImpl,
                QueryImpl.withTraceAppend_apply, traceFragment,
                observedResult, OnlineState.observeAll, OnlineState.observe,
                Except.map, Except.bind, hrevealed, hvalue]

theorem onlineResultHit_observedResult_eq_runObserved_of_hazardCount_le
    (table : Index → Digest)
    (encoding : Option EncodingMonitor.State)
    (chain : AdaptiveRevealMonitor.State Index)
    (fuel : Nat) (value : α) (trace : ActionTrace Index)
    (hcount : hazardCount trace ≤ fuel) :
    onlineResultHit table
        (observedResult table ⟨encoding, chain, fuel⟩ (value, trace)) =
      runObserved table encoding chain trace := by
  induction trace generalizing encoding chain fuel with
  | nil =>
      simp [observedResult, OnlineState.observeAll, onlineResultHit,
        runObserved, Except.map]
  | cons action trace ih =>
      cases action with
      | encoding action =>
          cases action with
          | query epoch output =>
              cases fuel with
              | zero => simp [hazardCount] at hcount
              | succ remaining =>
                  simp only [hazardCount, Nat.succ_le_succ_iff] at hcount
                  cases encoding with
                  | none =>
                      simpa [observedResult, OnlineState.observeAll,
                        OnlineState.observe, runObserved, Except.bind] using
                          ih none chain remaining hcount
                  | some encoding =>
                      cases happly : CappedEncodingMonitor.State.applyObserved
                          encoding (.query epoch output) with
                      | none =>
                          simpa [observedResult, OnlineState.observeAll,
                            OnlineState.observe, runObserved, happly,
                            Except.bind] using
                              ih none chain remaining hcount
                      | some result =>
                          rcases result with ⟨next, hit⟩
                          cases hit with
                          | false =>
                              simpa [observedResult, OnlineState.observeAll,
                                OnlineState.observe, runObserved, happly,
                                Except.bind] using
                                  ih (some next) chain remaining hcount
                          | true =>
                              simp [observedResult, OnlineState.observeAll,
                                OnlineState.observe, runObserved, happly,
                                onlineResultHit, Except.bind, Except.map]
          | sign epoch output =>
              simp only [hazardCount] at hcount
              cases encoding with
              | none =>
                  simpa [observedResult, OnlineState.observeAll,
                    OnlineState.observe, runObserved, Except.bind] using
                      ih none chain fuel hcount
              | some encoding =>
                  cases happly : CappedEncodingMonitor.State.applyObserved
                      encoding (.sign epoch output) with
                  | none =>
                      simpa [observedResult, OnlineState.observeAll,
                        OnlineState.observe, runObserved, happly,
                        Except.bind] using
                          ih none chain fuel hcount
                  | some result =>
                      rcases result with ⟨next, hit⟩
                      cases hit with
                      | false =>
                          simpa [observedResult, OnlineState.observeAll,
                            OnlineState.observe, runObserved, happly,
                            Except.bind] using
                              ih (some next) chain fuel hcount
                      | true =>
                          simp [observedResult, OnlineState.observeAll,
                            OnlineState.observe, runObserved, happly,
                            onlineResultHit, Except.bind, Except.map]
      | chain action =>
          cases action with
          | probe index target =>
              cases fuel with
              | zero => simp [hazardCount] at hcount
              | succ remaining =>
                  simp only [hazardCount, Nat.succ_le_succ_iff] at hcount
                  cases hrevealed : chain.revealed index with
                  | none =>
                      simpa [observedResult, OnlineState.observeAll,
                        OnlineState.observe, runObserved, hrevealed,
                        Except.bind] using
                          ih encoding (chain.addPending index target)
                            remaining hcount
                  | some revealed =>
                      simpa [observedResult, OnlineState.observeAll,
                        OnlineState.observe, runObserved, hrevealed,
                        Except.bind] using
                          ih encoding chain remaining hcount
          | reveal index output =>
              simp only [hazardCount] at hcount
              cases hrevealed : chain.revealed index with
              | some revealed =>
                  simpa [observedResult, OnlineState.observeAll,
                    OnlineState.observe, runObserved, hrevealed,
                    Except.bind] using
                      ih encoding chain fuel hcount
              | none =>
                  by_cases hhit : table index ∈ chain.pending index
                  · simp [observedResult, OnlineState.observeAll,
                      OnlineState.observe, runObserved, hrevealed, hhit,
                      onlineResultHit, Except.bind, Except.map]
                  · simpa [observedResult, OnlineState.observeAll,
                      OnlineState.observe, runObserved, hrevealed, hhit,
                      Except.bind] using
                        ih encoding (chain.install index (table index)) fuel
                          hcount

theorem relTriple_eagerTrace_onlineImpl
    (table : Index → Digest) (state : OnlineState Index)
    (computation : OracleComp (World Index) α)
    (hagrees : RevealProbeOracleSimulation.StateAgrees table state.chain) :
    RelTriple
      ((simulateQ (eagerTraceImpl table) computation).run)
      ((simulateQ (onlineImpl table) computation).run state).run
      (fun eager online => online = observedResult table state eager) := by
  classical
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      exact relTriple_pure_pure (by
        rfl)
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, WriterT.run_bind', StateT.run_bind,
        ExceptT.run_bind, OracleQuery.input_query]
      have hhead : RelTriple
          ((eagerTraceImpl table input).run)
          ((onlineImpl table input).run state).run
          (fun eager online => online = observedResult table state eager) := by
        apply relTriple_post_mono
          (relTriple_of_evalDist_map_eq_general _ _
            (observedResult table state) id
            (by simpa using
              (onlineImpl_query_run_eq_observedResult table input state
                hagrees).symm))
        intro eager online heq
        simpa using heq.symm
      apply relTriple_bind hhead
      intro eagerHead onlineHead hheadResult
      cases hobserved : state.observeAll table eagerHead.2 with
      | error error =>
          have honline : onlineHead = .error error := by
            simpa [observedResult, hobserved, Except.map] using hheadResult
          subst onlineHead
          rw [honline]
          change RelTriple
            ((Prod.map id (fun trace => eagerHead.2 ++ trace)) <$>
              (simulateQ (eagerTraceImpl table) (next eagerHead.1)).run)
            (pure (.error error) : ProbComp _)
            (fun eager online =>
              online = observedResult table state eager)
          apply relTriple_post_mono
            (relTriple_of_evalDist_map_eq_general _ _
              (observedResult table state) id (by
                calc
                  𝒟[observedResult table state <$>
                      (Prod.map id (fun trace => eagerHead.2 ++ trace) <$>
                        (simulateQ (eagerTraceImpl table)
                          (next eagerHead.1)).run)] =
                      𝒟[(fun _ => Except.error error) <$>
                        (simulateQ (eagerTraceImpl table)
                          (next eagerHead.1)).run] := by
                        apply congrArg evalDist
                        rw [Functor.map_map]
                        apply congrArg (fun observe => observe <$>
                          (simulateQ (eagerTraceImpl table)
                            (next eagerHead.1)).run)
                        funext eagerTail
                        exact observedResult_append_error table state
                          eagerHead.2 eagerTail.2 eagerTail.1 error hobserved
                  _ = evalDist (pure (Except.error error) :
                      ProbComp (Except Bool (α × OnlineState Index))) :=
                    evalDist_map_const_probComp _ (Except.error error)
                  _ = evalDist (id <$> (pure (Except.error error) :
                      ProbComp (Except Bool (α × OnlineState Index)))) := by
                    rw [id_map]))
          intro eagerTail onlineTail heq
          simpa using heq.symm
      | ok nextState =>
          have honline : onlineHead = .ok (eagerHead.1, nextState) := by
            simpa [observedResult, hobserved, Except.map] using hheadResult
          subst onlineHead
          rw [honline]
          have hnextAgrees := state.observeAll_preserves_stateAgrees table
            nextState eagerHead.2 hagrees hobserved
          change RelTriple
            ((Prod.map id (fun trace => eagerHead.2 ++ trace)) <$>
              (simulateQ (eagerTraceImpl table) (next eagerHead.1)).run)
            ((simulateQ (onlineImpl table) (next eagerHead.1)).run
              nextState).run
            (fun eager online =>
              online = observedResult table state eager)
          simpa only [id_map] using
            (relTriple_map (f :=
                Prod.map id (fun trace => eagerHead.2 ++ trace)) (g := id)
              (relTriple_post_mono
                (ih eagerHead.1 nextState hnextAgrees)
                (by
                  intro eagerTail onlineTail htail
                  change onlineTail = observedResult table state
                    (eagerTail.1, eagerHead.2 ++ eagerTail.2)
                  rw [observedResult_append_ok table state nextState
                    eagerHead.2 eagerTail.2 eagerTail.1 hobserved]
                  exact htail)))

theorem evalDist_onlineImpl_eq_observedResult_eagerTrace
    (table : Index → Digest) (state : OnlineState Index)
    (computation : OracleComp (World Index) α)
    (hagrees : RevealProbeOracleSimulation.StateAgrees table state.chain) :
    evalDist ((simulateQ (onlineImpl table) computation).run state).run =
      evalDist (observedResult table state <$>
        (simulateQ (eagerTraceImpl table) computation).run) := by
  have hcoupling := relTriple_eagerTrace_onlineImpl table state computation
    hagrees
  have hmapped := evalDist_map_eq_of_relTriple
    (relTriple_post_mono hcoupling (by
      intro eager online hrelation
      exact hrelation.symm))
  simpa using hmapped.symm

theorem runObserved_probability_eq_onlineResultHit_of_hazardBound
    (table : Index → Digest) (fuel : Nat)
    (computation : OracleComp (World Index) α)
    (hbound : computation.IsQueryBoundP IsHazardQuery fuel) :
    Pr[(fun result => runObserved table
          (some EncodingMonitor.State.empty)
          AdaptiveRevealMonitor.State.empty result.2 = true) |
        (simulateQ (eagerTraceImpl table) computation).run] =
      Pr[(fun result => onlineResultHit table result = true) |
        ((simulateQ (onlineImpl table) computation).run
          (OnlineState.empty fuel)).run] := by
  let initial := OnlineState.empty (Index := Index) fuel
  have hcoupling := relTriple_with_support
    (relTriple_eagerTrace_onlineImpl table initial computation
      (RevealProbeOracleSimulation.stateAgrees_empty table))
  apply le_antisymm
  · apply probEvent_le_of_relTriple hcoupling
    intro eager online hrelation heager
    have hcount := simulate_eagerTrace_support_hazardCount_le table computation
      fuel hbound eager hrelation.2.1
    have hhit := onlineResultHit_observedResult_eq_runObserved_of_hazardCount_le
      table (some EncodingMonitor.State.empty)
        AdaptiveRevealMonitor.State.empty fuel eager.1 eager.2 hcount
    change onlineResultHit table (observedResult table initial eager) =
      runObserved table (some EncodingMonitor.State.empty)
        AdaptiveRevealMonitor.State.empty eager.2 at hhit
    rw [hrelation.1, hhit]
    exact heager
  · apply probEvent_le_of_relTriple (relTriple_symm hcoupling)
    intro online eager hrelation honline
    have hcount := simulate_eagerTrace_support_hazardCount_le table computation
      fuel hbound eager hrelation.2.1
    have hhit := onlineResultHit_observedResult_eq_runObserved_of_hazardCount_le
      table (some EncodingMonitor.State.empty)
        AdaptiveRevealMonitor.State.empty fuel eager.1 eager.2 hcount
    change onlineResultHit table (observedResult table initial eager) =
      runObserved table (some EncodingMonitor.State.empty)
        AdaptiveRevealMonitor.State.empty eager.2 at hhit
    rw [hrelation.1, hhit] at honline
    exact honline

theorem enforced_combinedHit_probability_eq_onlineExperiment_direct
    (fuel : Nat) (computation : OracleComp (World Index) α) :
    Pr[fun result : (Index → Digest) × (α × ActionTrace Index) =>
        CombinedHit result.1 (enforceHazardTrace fuel result.2.2) |
      eagerExperiment computation] =
    Pr[(fun hit : Bool => hit = true) |
      onlineExperiment fuel (enforceHazardBound fuel computation)] := by
  calc
    _ = Pr[ExperimentHit |
        enforceEagerResult fuel <$> eagerExperiment computation] := by
      rw [probEvent_map]
      rfl
    _ = Pr[ExperimentHit |
        eagerExperiment (enforceHazardBound fuel computation)] := by
      rw [eagerExperiment_enforceHazardBound_eq_map]
    _ = _ := by
      unfold eagerExperiment onlineExperiment ExperimentHit
      rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
      apply tsum_congr
      intro table
      congr 1
      rw [show (do
          let result ← (simulateQ (eagerTraceImpl table)
            (enforceHazardBound fuel computation)).run
          pure (table, result)) =
        Prod.mk table <$> (simulateQ (eagerTraceImpl table)
          (enforceHazardBound fuel computation)).run by rfl]
      rw [probEvent_map, probEvent_map]
      change Pr[(fun result => CombinedHit table result.2) |
          (simulateQ (eagerTraceImpl table)
            (enforceHazardBound fuel computation)).run] =
        Pr[(fun result => onlineResultHit table result = true) |
          ((simulateQ (onlineImpl table)
            (enforceHazardBound fuel computation)).run
              (OnlineState.empty fuel)).run]
      simpa [runObserved_empty_eq_combinedHit] using
        runObserved_probability_eq_onlineResultHit_of_hazardBound table fuel
          (enforceHazardBound fuel computation)
          (enforceHazardBound_isHazardQueryBoundP fuel computation)

end XmssSecurity.FirstLaneOracleSimulation
