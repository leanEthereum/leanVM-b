import SphincsSecurity.Proof.FewTimeOriginInvariant
import SphincsSecurity.Proof.FewTimeTargetSigner

/-!
# Monitoring one adaptive target candidate

This proof-only wrapper follows an origin monitor while retaining the view at one fixed ordinal in
the stream of fresh direct answers and fresh signer selections. Its signer uses
`signWithTargetView`, whose projection is the ordinary viewed signer.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

namespace Concrete

structure OriginTargetMonitorState {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) where
  origin : OriginMonitorState configuration
  candidateOrdinal : Nat
  targetView : Option FewTimeView
  valid : Bool

noncomputable def OriginTargetMonitorState.initial
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources)
    (cache : QueryCache HashSpec) : OriginTargetMonitorState configuration :=
  ⟨OriginMonitorState.initial configuration cache, 0, none, true⟩

def OriginTargetMonitorState.recordCandidate
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (allowed : Bool) (view : FewTimeView) : OriginTargetMonitorState configuration :=
  { state with
    candidateOrdinal := state.candidateOrdinal + 1
    targetView := if state.candidateOrdinal = targetOrdinal then some view else state.targetView
    valid := if state.candidateOrdinal = targetOrdinal then state.valid && allowed else state.valid }

def OriginTargetMonitorState.advanceOrigin
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginTargetMonitorState configuration)
    (origin : OriginMonitorState configuration) : OriginTargetMonitorState configuration :=
  { state with origin := origin }

noncomputable def originTargetMonitoredAdversaryImpl
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (OriginTargetMonitorState configuration) ProbComp) := by
  intro input
  cases input with
  | inl worldInput =>
      exact fun state => do
        let (output, origin) ←
          ((originMonitoredAdversaryImpl configuration secretKey (.inl worldInput)).run
            state.origin)
        let advanced := state.advanceOrigin origin
        match worldInput with
        | .inl _ => pure (output, advanced)
        | .inr hashInput =>
            if state.origin.viewed.cache hashInput = none then
              pure (output, advanced.recordCandidate targetOrdinal
                (decide (configuration.sourceAt? state.origin.directOrdinal = none))
                (hashOutputFewTimeView output))
            else
              pure (output, advanced)
  | inr request =>
      exact fun state => do
        let (targetResult, finalCache) ←
          (simulateQ romImpl (signWithTargetView secretKey request)).run
            state.origin.viewed.cache
        let result := targetSignerResultView targetResult
        let trace := fullAdversaryTraceUpdate (.inr request) state.origin.viewed.cache result.1
          finalCache state.origin.viewed.trace
        let monitored := monitorSigner secretKey request state.origin (result, finalCache)
        let origin : OriginMonitorState configuration :=
          ⟨⟨finalCache, trace, state.origin.viewed.views ++ [result.2],
            state.origin.viewed.targetView⟩, monitored.1, state.origin.directOrdinal,
            state.origin.signerOrdinal + 1, monitored.2⟩
        let advanced := state.advanceOrigin origin
        match targetResult.2 with
        | none => pure (result.1, advanced)
        | some (input, view) =>
            if state.origin.viewed.cache input = none then
              pure (result.1, advanced.recordCandidate targetOrdinal
                (decide (pattern.selectedAt? state.origin.signerOrdinal = none)) view)
            else
              pure (result.1, advanced)

theorem originTargetMonitoredAdversaryImpl_query_projection
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginTargetMonitorState configuration) :
    (fun result => (result.1, result.2.origin)) <$>
        ((originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
          state) =
      (originMonitoredAdversaryImpl configuration secretKey input).run state.origin := by
  classical
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput =>
          rw [originTargetMonitoredAdversaryImpl]
          simp only [StateT.run, map_eq_bind_pure_comp, bind_assoc]
          apply bind_congr
          intro result
          rfl
      | inr hashInput =>
          rw [originTargetMonitoredAdversaryImpl]
          simp only [StateT.run, map_eq_bind_pure_comp, bind_assoc]
          by_cases hfresh : state.origin.viewed.cache hashInput = none
          · simp [OriginTargetMonitorState.advanceOrigin,
              OriginTargetMonitorState.recordCandidate, hfresh, Function.comp_def]
          · simp [OriginTargetMonitorState.advanceOrigin,
              hfresh, Function.comp_def]
  | inr request =>
      let updateOrigin := fun
          run : (Option Signature × Option FewTimeView) × QueryCache HashSpec =>
        let trace := fullAdversaryTraceUpdate (.inr request) state.origin.viewed.cache
          run.1.1 run.2 state.origin.viewed.trace
        let monitored := monitorSigner secretKey request state.origin run
        (⟨⟨run.2, trace, state.origin.viewed.views ++ [run.1.2],
            state.origin.viewed.targetView⟩, monitored.1, state.origin.directOrdinal,
            state.origin.signerOrdinal + 1, monitored.2⟩ : OriginMonitorState configuration)
      calc
        _ = (fun run => (run.1.1, updateOrigin run)) <$>
            ((fun run => (targetSignerResultView run.1, run.2)) <$>
              (simulateQ romImpl (signWithTargetView secretKey request)).run
                state.origin.viewed.cache) := by
          rw [originTargetMonitoredAdversaryImpl]
          simp only [StateT.run, map_eq_bind_pure_comp, bind_assoc]
          apply bind_congr
          intro targetRun
          cases hselection : targetRun.1.2 with
          | none =>
              simp only [pure_bind]
              rfl
          | some selection =>
              rcases selection with ⟨input, view⟩
              by_cases hfresh : state.origin.viewed.cache input = none
              · simp only [hfresh, if_pos, pure_bind]
                rfl
              · simp only [hfresh]
                rfl
        _ = (fun run => (run.1.1, updateOrigin run)) <$>
            (simulateQ romImpl (signWithView secretKey request)).run
              state.origin.viewed.cache := by
          rw [simulateQ_signWithTargetView_projection_run]
        _ = _ := by
          rw [originMonitoredAdversaryImpl]
          simp only [StateT.run, map_eq_bind_pure_comp]
          rfl

theorem originTargetMonitoredAdversaryImpl_projection
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration) :
    Prod.map id OriginTargetMonitorState.origin <$>
        (simulateQ (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
          computation).run initialState =
      (simulateQ (originMonitoredAdversaryImpl configuration secretKey)
        computation).run initialState.origin := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
    (originMonitoredAdversaryImpl configuration secretKey)
    OriginTargetMonitorState.origin
  intro input state
  exact originTargetMonitoredAdversaryImpl_query_projection configuration secretKey
    targetOrdinal input state

theorem probEvent_originTargetMonitoredAdversaryImpl_projection
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration)
    (event : α × OriginMonitorState configuration → Prop) :
    Pr[event |
      (simulateQ (originMonitoredAdversaryImpl configuration secretKey)
        computation).run initialState.origin] =
      Pr[fun result : α × OriginTargetMonitorState configuration =>
          event (result.1, result.2.origin) |
        (simulateQ
          (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
          computation).run initialState] := by
  rw [← originTargetMonitoredAdversaryImpl_projection configuration secretKey
    targetOrdinal computation initialState, probEvent_map]
  rfl

theorem probEvent_originMonitored_le_originTargetMonitored
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration)
    (originEvent : α × OriginMonitorState configuration → Prop)
    (targetEvent : α × OriginTargetMonitorState configuration → Prop)
    (himp : ∀ result ∈ support
      ((simulateQ
        (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run initialState),
      originEvent (result.1, result.2.origin) → targetEvent result) :
    Pr[originEvent |
      (simulateQ (originMonitoredAdversaryImpl configuration secretKey)
        computation).run initialState.origin] ≤
      Pr[targetEvent |
        (simulateQ
          (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
          computation).run initialState] := by
  classical
  rw [probEvent_originTargetMonitoredAdversaryImpl_projection configuration secretKey
    targetOrdinal computation initialState originEvent]
  exact probEvent_mono himp

end Concrete

end SphincsSecurity
