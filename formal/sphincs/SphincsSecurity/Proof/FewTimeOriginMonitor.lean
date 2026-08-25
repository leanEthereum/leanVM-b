import SphincsSecurity.Proof.FewTimeOriginSchedule

/-!
# Monitoring one padded origin configuration

This proof-only state follows the viewed traced adversary execution. It records the input and view
at configured direct sources, records fresh selected signer views, and checks fixed-input reuse at
configured prehit signer positions. Forgetting the monitor fields leaves the viewed trace unchanged.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

namespace Concrete

structure OriginMonitorState {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) where
  viewed : ViewedFullTraceState
  observation : OriginObservation configuration
  directOrdinal : Nat
  signerOrdinal : Nat
  valid : Bool

noncomputable def OriginMonitorState.initial {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources)
    (cache : QueryCache HashSpec) : OriginMonitorState configuration :=
  ⟨⟨cache, ⟨[], [], []⟩, [], none⟩, OriginObservation.empty configuration, 0, 0, true⟩

noncomputable def monitorDirectSource {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (input : HashInput) (output : HashOutput) :
    OriginObservation configuration × Bool := by
  classical
  match configuration.sourceAt? state.directOrdinal with
  | none => exact (state.observation, state.valid)
  | some selected =>
      if state.viewed.cache input = none ∧ signAttemptResultOfOutput output ≠ none then
        exact (state.observation.recordSource selected input (hashOutputFewTimeView output),
          state.valid)
      else
        exact (state.observation, false)

noncomputable def monitorSigner {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (secretKey : SecretKey) (request : SignRequest)
    (state : OriginMonitorState configuration)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec) :
    OriginObservation configuration × Bool := by
  classical
  match pattern.selectedAt? state.signerOrdinal with
  | none => exact (state.observation, state.valid)
  | some selected =>
      if hprehit : selected ∈ configuration.prehit then
        let prehit : ↑configuration.prehit := ⟨selected, hprehit⟩
        if prehit ∈ state.observation.seenSources ∧
            PrehitSuccessfulSignerView
              (onlyInputCache state.viewed.cache (state.observation.sourceInputs prehit))
              secretKey request (fun view => view = state.observation.views selected) result then
          exact (state.observation, state.valid)
        else
          exact (state.observation, false)
      else
        match freshSuccessfulView? state.viewed.cache secretKey request result with
        | none => exact (state.observation, false)
        | some view => exact (state.observation.recordFresh selected view, state.valid)

noncomputable def originMonitoredAdversaryImpl {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec) (StateT (OriginMonitorState configuration) ProbComp) := by
  intro input
  cases input with
  | inl worldInput =>
      exact fun state => do
        let (output, finalCache) ← (romImpl worldInput).run state.viewed.cache
        let trace := fullAdversaryTraceUpdate (.inl worldInput) state.viewed.cache output
          finalCache state.viewed.trace
        match worldInput with
        | .inl _ =>
            pure (output, ⟨⟨finalCache, trace, state.viewed.views, state.viewed.targetView⟩,
              state.observation, state.directOrdinal, state.signerOrdinal, state.valid⟩)
        | .inr hashInput =>
            let monitored := monitorDirectSource state hashInput output
            pure (output, ⟨⟨finalCache, trace, state.viewed.views, state.viewed.targetView⟩,
              monitored.1, state.directOrdinal + 1, state.signerOrdinal, monitored.2⟩)
  | inr request =>
      exact fun state => do
        let (result, finalCache) ←
          (simulateQ romImpl (signWithView secretKey request)).run state.viewed.cache
        let trace := fullAdversaryTraceUpdate (.inr request) state.viewed.cache result.1
          finalCache state.viewed.trace
        let monitored := monitorSigner secretKey request state (result, finalCache)
        pure (result.1, ⟨⟨finalCache, trace, state.viewed.views ++ [result.2],
          state.viewed.targetView⟩, monitored.1, state.directOrdinal,
          state.signerOrdinal + 1, monitored.2⟩)

theorem originMonitoredAdversaryImpl_query_projection {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginMonitorState configuration) :
    (fun result => (result.1, result.2.viewed)) <$>
        ((originMonitoredAdversaryImpl configuration secretKey input).run state) =
      (viewedFullTracedMappedAdversaryImpl secretKey input).run state.viewed := by
  classical
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput =>
          simp only [originMonitoredAdversaryImpl, viewedFullTracedMappedAdversaryImpl,
            StateT.run, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
      | inr hashInput =>
          simp only [originMonitoredAdversaryImpl, viewedFullTracedMappedAdversaryImpl,
            StateT.run, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  | inr request =>
      simp only [originMonitoredAdversaryImpl, viewedFullTracedMappedAdversaryImpl,
        StateT.run, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]

theorem originMonitoredAdversaryImpl_projection {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginMonitorState configuration) :
    Prod.map id OriginMonitorState.viewed <$>
        (simulateQ (originMonitoredAdversaryImpl configuration secretKey)
          computation).run initialState =
      (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run initialState.viewed := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (originMonitoredAdversaryImpl configuration secretKey)
    (viewedFullTracedMappedAdversaryImpl secretKey)
    OriginMonitorState.viewed
  intro input state
  exact originMonitoredAdversaryImpl_query_projection configuration secretKey input state

end Concrete

end SphincsSecurity
