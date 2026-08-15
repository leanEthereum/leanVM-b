import XmssSecurity.CausalHighTableSimulator
import XmssSecurity.CausalRevealTraceReplay
import XmssSecurity.CausalUntilHit
import XmssSecurity.CausalDirectLazySigning

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity
namespace RevealProbeOracleSimulation

variable {Index : Type} [Fintype Index] [DecidableEq Index]

omit [Fintype Index] [DecidableEq Index] in
theorem simulate_eagerTrace_support_traceAgrees
    (table : Index → Digest) (computation : OracleComp (World Index) α)
    (result : α × ActionTrace Index)
    (hresult : result ∈ support
      ((simulateQ (eagerTraceImpl table) computation).run)) :
    TraceAgrees table result.2 := by
  induction computation using OracleComp.inductionOn generalizing result with
  | pure value =>
      simp only [simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      trivial
  | query_bind input next ih =>
      rw [simulateQ_query_bind, WriterT.run_bind',
        mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      cases input with
      | uniform n =>
          simp [eagerTraceImpl, eagerImpl, traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hhead
          obtain ⟨output, rfl⟩ := hhead
          rw [support_map] at htail
          obtain ⟨tail, htail, rfl⟩ := htail
          exact ih output tail htail
      | probe index target =>
          simp [eagerTraceImpl, eagerImpl, traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hhead
          subst head
          rw [support_map] at htail
          obtain ⟨tail, htail, rfl⟩ := htail
          simp only [List.cons_append]
          exact ih () tail htail
      | reveal index =>
          simp [eagerTraceImpl, eagerImpl, traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hhead
          subst head
          rw [support_map] at htail
          obtain ⟨tail, htail, rfl⟩ := htail
          simp only [List.cons_append]
          exact ⟨rfl, ih (table index) tail htail⟩

def advanceObserved
    (table : Index → Digest) :
    AdaptiveRevealMonitor.State Index → ActionTrace Index →
      Option (AdaptiveRevealMonitor.State Index)
  | state, [] =>
      if tableHits state table then none else some state
  | state, .probe index target :: rest =>
      match state.revealed index with
      | some _ => advanceObserved table state rest
      | none => advanceObserved table (state.addPending index target) rest
  | state, .reveal index _ :: rest =>
      match state.revealed index with
      | some _ => advanceObserved table state rest
      | none =>
          if table index ∈ state.pending index then none
          else advanceObserved table (state.install index (table index)) rest

theorem advanceObserved_eq_none_iff_runObserved_eq_true
    (table : Index → Digest) (state : AdaptiveRevealMonitor.State Index)
    (trace : ActionTrace Index) :
    advanceObserved table state trace = none ↔
      runObserved table state trace = true := by
  induction trace generalizing state with
  | nil =>
      by_cases hhit : tableHits state table <;>
        simp [advanceObserved, runObserved, hhit]
  | cons action rest ih =>
      cases action with
      | probe index target =>
          simp only [advanceObserved, runObserved]
          cases hrevealed : state.revealed index <;> simp [ih]
      | reveal index value =>
          simp only [advanceObserved, runObserved]
          cases hrevealed : state.revealed index with
          | some previous => simp [ih]
          | none =>
              by_cases hhit : table index ∈ state.pending index
              · simp [hhit]
              · simp [hhit, ih]

theorem advanceObserved_eq_some_implies_runObserved_eq_false
    (table : Index → Digest) (state final : AdaptiveRevealMonitor.State Index)
    (trace : ActionTrace Index)
    (hadvance : advanceObserved table state trace = some final) :
    runObserved table state trace = false := by
  cases hrun : runObserved table state trace
  · rfl
  · have := (advanceObserved_eq_none_iff_runObserved_eq_true
      table state trace).2 hrun
    rw [hadvance] at this
    cases this

theorem advanceObserved_eq_none_append
    (table : Index → Digest) (state : AdaptiveRevealMonitor.State Index)
    (left right : ActionTrace Index)
    (hleft : advanceObserved table state left = none) :
    advanceObserved table state (left ++ right) = none := by
  apply (advanceObserved_eq_none_iff_runObserved_eq_true
    table state (left ++ right)).2
  apply runObserved_append_eq_true table state left right
  exact (advanceObserved_eq_none_iff_runObserved_eq_true
    table state left).1 hleft

theorem advanceObserved_append_of_some
    (table : Index → Digest) (state final : AdaptiveRevealMonitor.State Index)
    (left right : ActionTrace Index)
    (hleft : advanceObserved table state left = some final) :
    advanceObserved table state (left ++ right) =
      advanceObserved table final right := by
  induction left generalizing state final with
  | nil =>
      by_cases hhit : tableHits state table
      · simp [advanceObserved, hhit] at hleft
      · simp [advanceObserved, hhit] at hleft
        subst final
        rfl
  | cons action left ih =>
      cases action with
      | probe index target =>
          simp only [List.cons_append, advanceObserved] at hleft ⊢
          cases hrevealed : state.revealed index with
          | none =>
              rw [hrevealed] at hleft
              simp only at hleft ⊢
              exact ih (state.addPending index target) final hleft
          | some value =>
              rw [hrevealed] at hleft
              simp only at hleft ⊢
              exact ih state final hleft
      | reveal index value =>
          simp only [List.cons_append, advanceObserved] at hleft ⊢
          cases hrevealed : state.revealed index with
          | some previous =>
              rw [hrevealed] at hleft
              simp only at hleft ⊢
              exact ih state final hleft
          | none =>
              rw [hrevealed] at hleft
              simp only at hleft ⊢
              by_cases hhit : table index ∈ state.pending index
              · simp [hhit] at hleft ⊢
              · rw [if_neg hhit] at hleft ⊢
                exact ih (state.install index (table index)) final hleft

theorem advanceObserved_append
    (table : Index → Digest) (state : AdaptiveRevealMonitor.State Index)
    (left right : ActionTrace Index) :
    advanceObserved table state (left ++ right) =
      (advanceObserved table state left).bind fun middle =>
        advanceObserved table middle right := by
  cases hleft : advanceObserved table state left with
  | none =>
      rw [advanceObserved_eq_none_append table state left right hleft]
      simp
  | some final =>
      rw [advanceObserved_append_of_some table state final left right hleft]
      simp

theorem advanceObserved_preserves_stateAgrees
    (table : Index → Digest)
    (monitor finalMonitor : AdaptiveRevealMonitor.State Index)
    (trace : ActionTrace Index)
    (hadvance : advanceObserved table monitor trace = some finalMonitor)
    (hagrees : StateAgrees table monitor) :
    StateAgrees table finalMonitor := by
  induction trace generalizing monitor finalMonitor with
  | nil =>
      simp only [advanceObserved] at hadvance
      split at hadvance
      · contradiction
      · exact Option.some.inj hadvance ▸ hagrees
  | cons action rest ih =>
      cases action with
      | probe index target =>
          simp only [advanceObserved] at hadvance
          cases hrevealed : monitor.revealed index with
          | some value =>
              rw [hrevealed] at hadvance
              exact ih monitor finalMonitor hadvance hagrees
          | none =>
              rw [hrevealed] at hadvance
              exact ih (monitor.addPending index target) finalMonitor hadvance
                (hagrees.addPending index target)
      | reveal index value =>
          simp only [advanceObserved] at hadvance
          cases hrevealed : monitor.revealed index with
          | some previous =>
              rw [hrevealed] at hadvance
              exact ih monitor finalMonitor hadvance hagrees
          | none =>
              rw [hrevealed] at hadvance
              by_cases hhit : table index ∈ monitor.pending index
              · simp [hhit] at hadvance
              · apply ih (monitor.install index (table index)) finalMonitor
                  (by simpa [hhit] using hadvance)
                  (hagrees.install index)

theorem advanceObserved_preserves_replayed_reveals
    (table : Index → Digest)
    (monitor finalMonitor : AdaptiveRevealMonitor.State Index)
    (before after : Index → Option Digest) (trace : ActionTrace Index)
    (hadvance : advanceObserved table monitor trace = some finalMonitor)
    (hmonitor : StateAgrees table monitor)
    (hinitial : monitor.revealed = before)
    (hagrees : TraceAgrees table trace)
    (hreplay : ReplaysCausalReveals before trace after) :
    finalMonitor.revealed = after := by
  induction hreplay generalizing monitor finalMonitor with
  | nil revealed =>
      simp only [advanceObserved] at hadvance
      split at hadvance
      · contradiction
      · exact Option.some.inj hadvance |>.symm ▸ hinitial
  | probe initial final index target trace hrest ih =>
      simp only [advanceObserved] at hadvance
      simp only [TraceAgrees] at hagrees
      cases hrevealed : monitor.revealed index with
      | some value =>
          rw [hrevealed] at hadvance
          exact ih monitor finalMonitor hadvance hmonitor hinitial hagrees
      | none =>
          rw [hrevealed] at hadvance
          apply ih (monitor.addPending index target) finalMonitor hadvance
            (hmonitor.addPending index target)
          · simpa [AdaptiveRevealMonitor.State.addPending] using hinitial
          · exact hagrees
  | reveal initial final index value trace changed hchange hrest ih =>
      simp only [advanceObserved] at hadvance
      simp only [TraceAgrees] at hagrees
      cases hrevealed : monitor.revealed index with
      | some previous =>
          rw [hrevealed] at hadvance
          apply ih monitor finalMonitor hadvance hmonitor
          · funext candidate
            by_cases heq : candidate = index
            · subst candidate
              have hprevious := hmonitor index previous hrevealed
              rw [hagrees.1] at hprevious
              rw [hchange.1]
              exact hrevealed.trans (congrArg some hprevious.symm)
            · rw [hchange.2 candidate heq, ← hinitial]
          · exact hagrees.2
      | none =>
          rw [hrevealed] at hadvance
          by_cases hhit : table index ∈ monitor.pending index
          · simp [hhit] at hadvance
          · apply ih (monitor.install index (table index)) finalMonitor
              (by simpa [hrevealed, hhit] using hadvance)
              (hmonitor.install index)
            · funext candidate
              by_cases heq : candidate = index
              · subst candidate
                rw [hchange.1]
                simp [AdaptiveRevealMonitor.State.install, hagrees.1]
              · rw [hchange.2 candidate heq, ← hinitial]
                simp [AdaptiveRevealMonitor.State.install,
                  Function.update_of_ne heq]
            · exact hagrees.2

end RevealProbeOracleSimulation

theorem simulate_eagerTrace_filteredCausalAttackerHashQueryFromHigh_support_replays
    (table high : ChainValueIndex → Digest) (secretKey : SecretKey)
    (selected : ChainIndex) (input : HashInput) (state : CausalHashState)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((filteredCausalAttackerHashQueryFromHigh high secretKey selected input).run
          state)).run)) :
    ReplaysCausalReveals state.revealed result.2 result.1.2.revealed := by
  generalize hplan :
    filteredCausalAttackerHashPlan secretKey selected input state = plan
  cases plan with
  | cached output =>
      rw [filteredCausalAttackerHashQueryFromHigh_run, hplan] at hresult
      simp only [simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      change ReplaysCausalReveals state.revealed []
        (causalRecordedState secretKey selected input state).revealed
      simpa only [causalRecordedState_revealed] using
        ReplaysCausalReveals.nil state.revealed
  | reveal index =>
      rw [filteredCausalAttackerHashQueryFromHigh_run, hplan,
        simulate_eagerTrace_causalRevealHashQueryFromHigh] at hresult
      simp only [support_pure, Set.mem_singleton_iff] at hresult
      subst result
      apply ReplaysCausalReveals.reveal state.revealed _ index (table index) []
        (causalRevealResultState secretKey selected input state index
          (table index) (Rom.hashOutputEquivDigestPair.symm
            (high index, table index))).revealed
      · exact causalRevealResultState_transition secretKey selected input state
          index (table index) _
      · exact ReplaysCausalReveals.nil _
  | conditioned digest =>
      rw [filteredCausalAttackerHashQueryFromHigh_run, hplan,
        simulateQ_bind, WriterT.run_bind',
        RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp,
        mem_support_bind_iff] at hresult
      obtain ⟨sample, hsample, hpure⟩ := hresult
      rw [support_map] at hsample
      obtain ⟨output, _houtput, rfl⟩ := hsample
      simp only [List.nil_append] at hpure
      subst result
      change ReplaysCausalReveals state.revealed []
        ({ (causalRecordedState secretKey selected input state) with
          cache := (causalRecordedState secretKey selected input state).cache.cacheQuery
            input output }).revealed
      simpa only [causalRecordedState_revealed] using
        ReplaysCausalReveals.nil state.revealed
  | fresh =>
      rw [filteredCausalAttackerHashQueryFromHigh_run, hplan,
        simulate_eagerTrace_causalHashQuery] at hresult
      rw [support_map] at hresult
      obtain ⟨sample, _hsample, rfl⟩ := hresult
      change ReplaysCausalReveals state.revealed []
        ({ (causalRecordedState secretKey selected input state) with
          cache := sample.2 }).revealed
      simpa only [causalRecordedState_revealed] using
        ReplaysCausalReveals.nil state.revealed

theorem simulate_eagerTrace_filteredProbingAttackerHashQueryAtFromHigh_support_replays
    (table high : ChainValueIndex → Digest) (secretKey : SecretKey)
    (selected : ChainIndex) (input : HashInput) (state : CausalHashState)
    (probe : Option (ChainValueIndex × Digest))
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredProbingAttackerHashQueryAtFromHigh high secretKey selected input
          state probe)).run)) :
    ReplaysCausalReveals state.revealed result.2 result.1.2.revealed := by
  cases probe with
  | none =>
      exact
        simulate_eagerTrace_filteredCausalAttackerHashQueryFromHigh_support_replays
          table high secretKey selected input state result hresult
  | some probe =>
      cases hrevealed : state.revealed probe.1 with
      | some value =>
          rw [filteredProbingAttackerHashQueryAtFromHigh, hrevealed] at hresult
          exact
            simulate_eagerTrace_filteredCausalAttackerHashQueryFromHigh_support_replays
              table high secretKey selected input state result hresult
      | none =>
          rw [simulate_eagerTrace_filteredProbingAttackerHashQueryAtFromHigh_hidden_eq_map
            table high secretKey selected input state probe.1 probe.2 hrevealed,
              support_map] at hresult
          obtain ⟨tail, htail, rfl⟩ := hresult
          exact ReplaysCausalReveals.probe state.revealed tail.1.2.revealed
            probe.1 probe.2 tail.2
              (simulate_eagerTrace_filteredCausalAttackerHashQueryFromHigh_support_replays
                table high secretKey selected input state tail htail)

theorem CausalHashState.recordReveal_transition
    (state : CausalHashState) (index : ChainValueIndex) (value : Digest) :
    CausalRevealTransition state.revealed index value
      (state.recordReveal index value).revealed := by
  constructor
  · simp [CausalHashState.recordReveal]
  · intro candidate hne
    simp [CausalHashState.recordReveal, Function.update_of_ne hne]

theorem simulate_eagerTrace_filteredCausalSigningQuery_support_replays
    (table : ChainValueIndex → Digest)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (state : CausalHashState)
    (result : (Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredCausalSigningQuery keyView selected request state)).run)) :
    ReplaysCausalReveals state.revealed result.2 result.1.2.revealed := by
  rw [simulate_eagerTrace_filteredCausalSigningQuery] at hresult
  unfold filteredEagerSigningQuery at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨randomness, _hrandomness, hresult⟩ := hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨encoded, _hencoded, hresult⟩ := hresult
  cases hdecode : TargetSum.decodeDigest encoded.1 with
  | none =>
      simp [filteredEagerSigningReveal, hdecode] at hresult
      subst result
      exact ReplaysCausalReveals.nil state.revealed
  | some encoding =>
      simp [filteredEagerSigningReveal, hdecode] at hresult
      subst result
      let index := (request.epoch, encoding selected)
      apply ReplaysCausalReveals.reveal state.revealed _ index (table index) []
        (({ state with cache := encoded.2 }).recordReveal
          index (table index)).revealed
      · exact CausalHashState.recordReveal_transition
          { state with cache := encoded.2 } index (table index)
      · exact ReplaysCausalReveals.nil _
structure MonitoredCausalState where
  causal : CausalHashState
  monitor : Option (AdaptiveRevealMonitor.State ChainValueIndex)
  trace : RevealProbeOracleSimulation.ActionTrace ChainValueIndex

def MonitoredCausalState.bad (state : MonitoredCausalState) : Prop :=
  state.monitor = none

def MonitoredCausalState.TraceConsistent
    (table : ChainValueIndex → Digest) (state : MonitoredCausalState) : Prop :=
  state.monitor = RevealProbeOracleSimulation.advanceObserved table
    AdaptiveRevealMonitor.State.empty state.trace

def monitoredCausalResult
    (table : ChainValueIndex → Digest) (initial : MonitoredCausalState)
    (result : (α × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :
    α × MonitoredCausalState :=
  (result.1.1, {
    causal := result.1.2
    monitor := initial.monitor.bind fun monitor =>
      RevealProbeOracleSimulation.advanceObserved table monitor result.2
    trace := initial.trace ++ result.2 })

theorem monitoredCausalResult_traceConsistent
    (table : ChainValueIndex → Digest) (initial : MonitoredCausalState)
    (result : (α × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hinitial : initial.TraceConsistent table) :
    (monitoredCausalResult table initial result).2.TraceConsistent table := by
  unfold MonitoredCausalState.TraceConsistent at hinitial ⊢
  change (initial.monitor.bind fun monitor =>
      RevealProbeOracleSimulation.advanceObserved table monitor result.2) =
    RevealProbeOracleSimulation.advanceObserved table
      AdaptiveRevealMonitor.State.empty (initial.trace ++ result.2)
  rw [hinitial, RevealProbeOracleSimulation.advanceObserved_append]

theorem monitoredCausalState_initial_traceConsistent
    (table : ChainValueIndex → Digest) (causal : CausalHashState) :
    MonitoredCausalState.TraceConsistent table
      ⟨causal, some AdaptiveRevealMonitor.State.empty, []⟩ := by
  simp [MonitoredCausalState.TraceConsistent,
    RevealProbeOracleSimulation.advanceObserved,
    RevealProbeOracleSimulation.tableHits,
    AdaptiveRevealMonitor.State.empty]

theorem MonitoredCausalState.bad_implies_runObserved
    (table : ChainValueIndex → Digest) (state : MonitoredCausalState)
    (hconsistent : state.TraceConsistent table) (hbad : state.bad) :
    RevealProbeOracleSimulation.runObserved table
      AdaptiveRevealMonitor.State.empty state.trace = true := by
  apply (RevealProbeOracleSimulation.advanceObserved_eq_none_iff_runObserved_eq_true
    table AdaptiveRevealMonitor.State.empty state.trace).1
  rw [← hconsistent]
  exact hbad

noncomputable def monitorCausalTrace
    (table : ChainValueIndex → Digest)
    (computation : CausalHashState → ProbComp
      ((α × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) :
    StateT MonitoredCausalState ProbComp α := fun state =>
  monitoredCausalResult table state <$> computation state.causal

theorem monitorCausalTrace_run
    (table : ChainValueIndex → Digest)
    (computation : CausalHashState → ProbComp
      ((α × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (state : MonitoredCausalState) :
    (monitorCausalTrace table computation).run state =
      monitoredCausalResult table state <$> computation state.causal := rfl

theorem map_monitorCausalTrace_projection
    (table : ChainValueIndex → Digest)
    (computation : CausalHashState → ProbComp
      ((α × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (state : MonitoredCausalState) :
    (fun result : α × MonitoredCausalState =>
      ((result.1, result.2.causal), result.2.trace)) <$>
        (monitorCausalTrace table computation).run state =
      (fun result : (α × CausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace ChainValueIndex =>
        (result.1, state.trace ++ result.2)) <$>
          computation state.causal := by
  rw [monitorCausalTrace_run, Functor.map_map]
  apply map_congr
  intro result
  simp [monitoredCausalResult]

noncomputable def monitoredEagerStateImpl
    {ι : Type} {spec : OracleSpec ι}
    (table : ChainValueIndex → Digest)
    (impl : QueryImpl spec
      (StateT CausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World ChainValueIndex)))) :
    QueryImpl spec (StateT MonitoredCausalState ProbComp) :=
  fun input => monitorCausalTrace table fun causalState =>
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((impl input).run causalState)).run

@[simp]
theorem monitoredEagerStateImpl_apply
    {ι : Type} {spec : OracleSpec ι}
    (table : ChainValueIndex → Digest)
    (impl : QueryImpl spec
      (StateT CausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World ChainValueIndex))))
    (input : spec.Domain) :
    monitoredEagerStateImpl table impl input =
      monitorCausalTrace table (fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((impl input).run causalState)).run) := rfl

set_option maxRecDepth 1000000 in
theorem map_simulate_monitoredEagerStateImpl_projection
    {ι : Type} {spec : OracleSpec ι}
    (table : ChainValueIndex → Digest)
    (impl : QueryImpl spec
      (StateT CausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World ChainValueIndex))))
    (computation : OracleComp spec α) (state : MonitoredCausalState) :
    (fun result : α × MonitoredCausalState =>
      ((result.1, result.2.causal), result.2.trace)) <$>
        (simulateQ (monitoredEagerStateImpl table impl) computation).run state =
      (fun result : ((α × CausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((simulateQ impl computation).run state.causal)).run := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, StateT.run_bind, WriterT.run_bind', map_bind,
        simulateQ_spec_query]
      unfold monitoredEagerStateImpl
      rw [monitorCausalTrace_run]
      simp only [bind_map_left]
      apply bind_congr
      intro head
      change (fun result : α × MonitoredCausalState =>
          ((result.1, result.2.causal), result.2.trace)) <$>
            (simulateQ (monitoredEagerStateImpl table impl)
              (next head.1.1)).run (monitoredCausalResult table state head).2 = _
      rw [ih head.1.1 (monitoredCausalResult table state head).2]
      simp [monitoredCausalResult, List.append_assoc]

noncomputable def causalStateImplOfRun
    {ι : Type} {spec : OracleSpec ι}
    (runStep : (input : spec.Domain) → CausalHashState →
      OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)
        (spec.Range input × CausalHashState)) :
    QueryImpl spec
      (StateT CausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World ChainValueIndex))) :=
  fun input => StateT.mk (runStep input)

noncomputable def monitoredEagerRunImpl
    {ι : Type} {spec : OracleSpec ι}
    (table : ChainValueIndex → Digest)
    (runStep : (input : spec.Domain) → CausalHashState →
      OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)
        (spec.Range input × CausalHashState)) :
    QueryImpl spec (StateT MonitoredCausalState ProbComp) :=
  fun input => monitorCausalTrace table fun causalState =>
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (runStep input causalState)).run

theorem map_simulate_monitoredEagerRunImpl_projection
    {ι : Type} {spec : OracleSpec ι}
    (table : ChainValueIndex → Digest)
    (runStep : (input : spec.Domain) → CausalHashState →
      OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)
        (spec.Range input × CausalHashState))
    (computation : OracleComp spec α) (state : MonitoredCausalState) :
    (fun result : α × MonitoredCausalState =>
      ((result.1, result.2.causal), result.2.trace)) <$>
        (simulateQ (monitoredEagerRunImpl table runStep) computation).run state =
      (fun result : ((α × CausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((simulateQ (causalStateImplOfRun runStep) computation).run
            state.causal)).run := by
  exact map_simulate_monitoredEagerStateImpl_projection table
    (causalStateImplOfRun runStep) computation state

theorem monitorCausalTrace_preserves_bad
    (table : ChainValueIndex → Digest)
    (computation : CausalHashState → ProbComp
      ((α × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (state : MonitoredCausalState) (hbad : state.bad)
    (result : α × MonitoredCausalState)
    (hresult : result ∈ support ((monitorCausalTrace table computation).run state)) :
    result.2.bad := by
  rw [monitorCausalTrace_run] at hresult
  rw [support_map] at hresult
  obtain ⟨raw, _hraw, rfl⟩ := hresult
  change (monitoredCausalResult table state raw).2.monitor = none
  simp only [monitoredCausalResult]
  change state.monitor = none at hbad
  rw [hbad]
  rfl

theorem monitorCausalTrace_preserves_traceConsistent
    (table : ChainValueIndex → Digest)
    (computation : CausalHashState → ProbComp
      ((α × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (state : MonitoredCausalState) (hconsistent : state.TraceConsistent table)
    (result : α × MonitoredCausalState)
    (hresult : result ∈ support ((monitorCausalTrace table computation).run state)) :
    result.2.TraceConsistent table := by
  rw [monitorCausalTrace_run, support_map] at hresult
  obtain ⟨raw, _hraw, rfl⟩ := hresult
  exact monitoredCausalResult_traceConsistent table state raw hconsistent

def MonitoredFilteredStateRelation
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftBase rightBase : QueryCache HashSpec)
    (table : ChainValueIndex → Digest)
    (leftCache : QueryCache HashSpec) (right : MonitoredCausalState) : Prop :=
  ∃ monitor,
    right.monitor = some monitor ∧
      RevealProbeOracleSimulation.StateAgrees table monitor ∧
      monitor.revealed = right.causal.revealed ∧
      FilteredCausalStateRelation parameter selected leftBase rightBase table
        leftCache right.causal

theorem monitoredFilteredStateRelation_initial
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftBase rightBase : QueryCache HashSpec)
    (table : ChainValueIndex → Digest)
    (leftCache : QueryCache HashSpec) (rightState : CausalHashState)
    (hstate : FilteredCausalStateRelation parameter selected leftBase rightBase
      table leftCache rightState)
    (hhidden : ∀ index, rightState.revealed index = none) :
    MonitoredFilteredStateRelation parameter selected leftBase rightBase table
      leftCache
      ⟨rightState, some AdaptiveRevealMonitor.State.empty, []⟩ := by
  refine ⟨AdaptiveRevealMonitor.State.empty, rfl,
    RevealProbeOracleSimulation.stateAgrees_empty table, ?_, hstate⟩
  funext index
  simp [AdaptiveRevealMonitor.State.empty, hhidden index]

theorem relTriple_monitorCausalTrace_of_filtered_until_hit
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftBase rightBase : QueryCache HashSpec)
    (table : ChainValueIndex → Digest)
    (leftComputation : ProbComp (α × QueryCache HashSpec))
    (rightComputation : CausalHashState → ProbComp
      ((α × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (rightState : MonitoredCausalState)
    (monitor : AdaptiveRevealMonitor.State ChainValueIndex)
    (hmonitor : rightState.monitor = some monitor)
    (hmonitorAgrees : RevealProbeOracleSimulation.StateAgrees table monitor)
    (hrevealed : monitor.revealed = rightState.causal.revealed)
    (hcouple : RelTriple leftComputation
      (rightComputation rightState.causal)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1.1 ∧
          FilteredCausalStateRelation parameter selected leftBase rightBase table
            leftResult.2 rightResult.1.2) ∨
          RevealProbeOracleSimulation.runObserved table monitor rightResult.2 =
            true))
    (htrace : ∀ result ∈ support (rightComputation rightState.causal),
      RevealProbeOracleSimulation.TraceAgrees table result.2 ∧
        ReplaysCausalReveals rightState.causal.revealed result.2
          result.1.2.revealed) :
    RelTriple leftComputation
      ((monitorCausalTrace table rightComputation).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredFilteredStateRelation parameter selected leftBase rightBase
            table leftResult.2 rightResult.2) ∨
          rightResult.2.bad) := by
  rw [monitorCausalTrace_run]
  have hmapped : RelTriple (id <$> leftComputation)
      (monitoredCausalResult table rightState <$>
        rightComputation rightState.causal)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredFilteredStateRelation parameter selected leftBase rightBase
            table leftResult.2 rightResult.2) ∨
          rightResult.2.bad) :=
    relTriple_map (f := id)
      (g := monitoredCausalResult table rightState)
      (relTriple_post_mono (relTriple_with_support hcouple)
      (fun leftResult rightResult hresult => by
        have htraceResult := htrace rightResult hresult.2.2
        rcases hresult.1 with hexact | hhit
        · cases hadvance : RevealProbeOracleSimulation.advanceObserved table
              monitor rightResult.2 with
          | none =>
              right
              change (rightState.monitor.bind fun current =>
                RevealProbeOracleSimulation.advanceObserved table current
                  rightResult.2) = none
              rw [hmonitor]
              exact hadvance
          | some finalMonitor =>
              left
              refine ⟨hexact.1, finalMonitor, ?_, ?_, ?_, hexact.2⟩
              · change (rightState.monitor.bind fun current =>
                    RevealProbeOracleSimulation.advanceObserved table current
                      rightResult.2) = some finalMonitor
                rw [hmonitor]
                exact hadvance
              · exact RevealProbeOracleSimulation.advanceObserved_preserves_stateAgrees
                  table monitor finalMonitor rightResult.2 hadvance
                    hmonitorAgrees
              · exact RevealProbeOracleSimulation.advanceObserved_preserves_replayed_reveals
                  table monitor finalMonitor rightState.causal.revealed
                    rightResult.1.2.revealed rightResult.2 hadvance
                      hmonitorAgrees hrevealed htraceResult.1 htraceResult.2
        · right
          change (rightState.monitor.bind fun current =>
            RevealProbeOracleSimulation.advanceObserved table current
              rightResult.2) = none
          rw [hmonitor]
          exact (RevealProbeOracleSimulation.advanceObserved_eq_none_iff_runObserved_eq_true
            table monitor rightResult.2).2 hhit))
  simpa only [id_map] using hmapped

set_option maxRecDepth 100000 in
theorem relTriple_programmed_monitoredHashQueryFromHigh_until_hit
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenCacheRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1 ∈ support (actualFixedChainKeygen selected))
    (leftCache : QueryCache HashSpec) (rightState : MonitoredCausalState)
    (hstate : MonitoredFilteredStateRelation left.secretKey.parameter selected
      left.cache right.1.cache right.2 leftCache rightState)
    (input : HashInput) (index : ChainValueIndex) (target : Digest)
    (hprobe : chainInputProbe? left.secretKey.parameter selected input =
      some (index, target)) :
    RelTriple
      (((randomOracle input).run leftCache) :
        ProbComp (HashOutput × QueryCache HashSpec))
      ((monitorCausalTrace right.2 (fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.2)
          (filteredProbingAttackerHashQueryAtFromHigh
            (chainValueHighTableOfEdges
              (chainEdgeHighTableOfCache left.cache
                left.secretKey.parameter selected left.table))
            right.1.secretKey selected input causalState
              (some (index, target)))).run)).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredFilteredStateRelation left.secretKey.parameter selected
            left.cache right.1.cache right.2 leftResult.2 rightResult.2) ∨
          rightResult.2.bad) := by
  obtain ⟨monitor, hmonitor, hmonitorAgrees, hrevealed, hcausal⟩ := hstate
  apply relTriple_monitorCausalTrace_of_filtered_until_hit (α := HashOutput)
    left.secretKey.parameter selected left.cache right.1.cache right.2
      ((randomOracle input).run leftCache) _ rightState monitor hmonitor
        hmonitorAgrees hrevealed
  · have hcouple :=
      relTriple_programmed_filteredProbingAttackerHashQueryAtFromHigh_until_hit
        selected left right hrel hleftSupport hrightSupport leftCache
          rightState.causal hcausal monitor input index target hprobe hrevealed
    change RelTriple
      (((randomOracle input).run leftCache) :
        ProbComp (HashOutput × QueryCache HashSpec))
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.2)
        (filteredProbingAttackerHashQueryAtFromHigh
          (chainValueHighTableOfEdges
            (chainEdgeHighTableOfCache left.cache left.secretKey.parameter
              selected left.table))
          right.1.secretKey selected input rightState.causal
            (some (index, target)))).run)
      (FilteredHashUntilHitRelation left.secretKey.parameter selected
        left.cache right.1.cache right.2 monitor) at hcouple
    change RelTriple
      (((randomOracle input).run leftCache) :
        ProbComp (HashOutput × QueryCache HashSpec))
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.2)
        (filteredProbingAttackerHashQueryAtFromHigh
          (chainValueHighTableOfEdges
            (chainEdgeHighTableOfCache left.cache left.secretKey.parameter
              selected left.table))
          right.1.secretKey selected input rightState.causal
            (some (index, target)))).run)
      (FilteredHashUntilHitRelation left.secretKey.parameter selected
        left.cache right.1.cache right.2 monitor)
    exact hcouple
  · intro result hresult
    exact ⟨RevealProbeOracleSimulation.simulate_eagerTrace_support_traceAgrees
        right.2 _ result hresult,
      simulate_eagerTrace_filteredProbingAttackerHashQueryAtFromHigh_support_replays
        right.2
          (chainValueHighTableOfEdges
            (chainEdgeHighTableOfCache left.cache left.secretKey.parameter
              selected left.table))
          right.1.secretKey selected input rightState.causal
            (some (index, target)) result hresult⟩

theorem relTriple_programmed_monitoredUniformQuery
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftBase rightBase : QueryCache HashSpec)
    (table : ChainValueIndex → Digest)
    (leftCache : QueryCache HashSpec) (rightState : MonitoredCausalState)
    (hstate : MonitoredFilteredStateRelation parameter selected leftBase
      rightBase table leftCache rightState)
    (n : Nat) :
    RelTriple
      ((fun output : Fin (n + 1) => (output, leftCache)) <$>
        (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
      ((monitorCausalTrace table (fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((causalUniformImpl n).run causalState)).run)).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredFilteredStateRelation parameter selected leftBase rightBase
            table leftResult.2 rightResult.2) ∨
          rightResult.2.bad) := by
  obtain ⟨monitor, hmonitor, hmonitorAgrees, hrevealed, hcausal⟩ := hstate
  apply relTriple_monitorCausalTrace_of_filtered_until_hit
    parameter selected leftBase rightBase table _ _ rightState monitor hmonitor
      hmonitorAgrees hrevealed
  · rw [simulate_eagerTrace_causalUniformImpl]
    have hmapped : RelTriple
        ((fun output : Fin (n + 1) => (output, leftCache)) <$>
          (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
        ((fun output : Fin (n + 1) =>
          ((output, rightState.causal),
            ([] : RevealProbeOracleSimulation.ActionTrace ChainValueIndex))) <$>
          (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
        (fun leftResult rightResult =>
          leftResult.1 = rightResult.1.1 ∧
            FilteredCausalStateRelation parameter selected leftBase rightBase
              table leftResult.2 rightResult.1.2) := by
      apply relTriple_map
      apply relTriple_post_mono
        (relTriple_refl
          (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
      intro leftOutput rightOutput houtput
      subst rightOutput
      exact ⟨rfl, hcausal⟩
    apply relTriple_post_mono hmapped
    intro leftResult rightResult hresult
    exact Or.inl hresult
  · intro result hresult
    rw [simulate_eagerTrace_causalUniformImpl, support_map] at hresult
    obtain ⟨output, _houtput, rfl⟩ := hresult
    exact ⟨by trivial, ReplaysCausalReveals.nil rightState.causal.revealed⟩

set_option maxRecDepth 100000 in
theorem relTriple_programmed_monitoredSigningQuery
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenStableRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1 ∈ support (actualFixedChainKeygen selected))
    (leftCache : QueryCache HashSpec) (rightState : MonitoredCausalState)
    (hstate : MonitoredFilteredStateRelation left.secretKey.parameter selected
      left.cache right.1.cache right.2 leftCache rightState)
    (request : SignRequest) :
    RelTriple
      ((simulateQ xmssRomImpl
        (Concrete.scheme.sign left.publicKey left.secretKey
          request.epoch request.message)).run leftCache)
      ((monitorCausalTrace right.2 (fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.2)
          (filteredCausalSigningQuery right.1 selected request
            causalState)).run)).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredFilteredStateRelation left.secretKey.parameter selected
            left.cache right.1.cache right.2 leftResult.2 rightResult.2) ∨
          rightResult.2.bad) := by
  obtain ⟨monitor, hmonitor, hmonitorAgrees, hrevealed, hcausal⟩ := hstate
  apply relTriple_monitorCausalTrace_of_filtered_until_hit
    (α := Option Signature) left.secretKey.parameter selected left.cache
      right.1.cache right.2 _ _ rightState monitor hmonitor hmonitorAgrees
        hrevealed
  · apply relTriple_post_mono
      (relTriple_programmed_filteredCausalSigningQuery selected left right hrel
        hleftSupport hrightSupport leftCache rightState.causal hcausal request)
    intro leftResult rightResult hresult
    exact Or.inl hresult
  · intro result hresult
    exact ⟨RevealProbeOracleSimulation.simulate_eagerTrace_support_traceAgrees
        right.2 _ result hresult,
      simulate_eagerTrace_filteredCausalSigningQuery_support_replays right.2
        right.1 selected request rightState.causal result hresult⟩

end XmssSecurity
