import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeHistoryLiveRisk
import SphincsSecurity.Proof.OtsProbePrivateValueAdaptiveSampling
import SphincsSecurity.Proof.OtsProbePrivateValueReplacement

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def liveValueObserve
    (table : OtsSecretIndex → HashOutput) (observe : Nat → α → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (value : α) : ProbComp Bool :=
  if DeferredCompletable table context then observe fuel value else pure true

instance liveValueObserve_dooms
    (table : OtsSecretIndex → HashOutput) (observe : Nat → α → ProbComp Bool) :
    ObserverDooms table (liveValueObserve table observe) where
  eq_true _ _ _ _ _ hdoomed := by simp [liveValueObserve, hdoomed]

instance liveValueObserve_synchronized
    (table : OtsSecretIndex → HashOutput) (observe : Nat → α → ProbComp Bool) :
    ObserverSynchronized table (liveValueObserve table observe) where
  eq_of_synchronized left right fuel value hcontext _ _ := by
    have hleft := hcontext.2.2.2
    have hright : DeferredCompletable table right := by
      obtain ⟨completion, hcompletion⟩ := hleft
      exact ⟨completion, (hcontext.1.deferredCompletion_iff completion).mp hcompletion⟩
    simp [liveValueObserve, hleft, hright]

noncomputable def runResolvedLiveValue
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) : ProbComp (Option (Nat × α)) := do
  let result ← runResolvedFromTable context fuel table computation
  match result with
  | none => pure none
  | some result =>
      if DeferredCompletable table result.context then pure (some (result.remaining, result.value)) else pure none

theorem runResolvedLiveValue_observe_eq
    (table : OtsSecretIndex → HashOutput) (test : Option (Nat × α) → Bool) (htest : test none = true)
    (context : DeferredContext) (fuel : Nat) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    runResolvedObserve (liveValueObserve table (fun remaining value => pure (test (some (remaining, value)))))
        context fuel table computation = test <$> runResolvedLiveValue table context fuel computation := by
  unfold runResolvedObserve runResolvedLiveValue
  rw [map_bind]
  apply bind_congr
  intro result
  cases result with
  | none => simp [finishObserve, htest]
  | some result =>
      by_cases hcomplete : DeferredCompletable table result.context <;> simp [finishObserve, liveValueObserve, hcomplete, htest]

theorem evalDist_runResolvedLiveValue_of_finalizationSynchronized
    (table : OtsSecretIndex → HashOutput) (left right : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hvalues : left.state.values = right.state.values) (hrevealed : left.state.revealed = right.state.revealed) :
    evalDist (runResolvedLiveValue table left fuel computation) = evalDist (runResolvedLiveValue table right fuel computation) := by
  apply evalDist_eq_of_bool_tests_none
  intro test htest
  rw [← runResolvedLiveValue_observe_eq table test htest, ← runResolvedLiveValue_observe_eq table test htest]
  exact evalDist_runResolvedObserve_eq_of_finalizationSynchronized computation left right fuel table hcontext hvalues hrevealed

theorem finalizationViewEq_clearPending_known
    (target : Position) (output : HashOutput) (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hknown : context.positionValue target = some output) :
    FinalizationViewEq table context { context with state := context.state.clearPending (.position target) } := by
  have hstarts := startTableAgrees_of_deferredCompletable hcomplete
  obtain ⟨completion, hcompletion⟩ := hcomplete
  have hclean := clean_of_deferredCompletion hcompletion
  refine ⟨hvalid.valuesConsistent, (hvalid.clearPending (.position target)).valuesConsistent,
    hstarts, hstarts, rfl, hclean, ?_, ?_⟩
  · intro coordinate value hvalue
    by_cases heq : coordinate = .position target
    · subst coordinate
      exact not_hitAt_clearPending_self context.state (.position target) value
    · exact (hitAt_clearPending_of_ne context.state (.position target) coordinate value heq).not.mpr
        (hclean coordinate value hvalue)
  · intro coordinate hvalue
    have hne : coordinate ≠ .position target := by
      intro heq
      subst coordinate
      change context.positionValue target = none at hvalue
      rw [hknown] at hvalue
      contradiction
    exact (pendingAt_clearPending_of_ne context.state (.position target) coordinate hne).symm

theorem evalDist_runResolvedLiveValue_clearPending_known
    (target : Position) (output : HashOutput) (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (fuel : Nat) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hknown : context.positionValue target = some output) :
    evalDist (runResolvedLiveValue table context fuel computation) =
      evalDist (runResolvedLiveValue table { context with state := context.state.clearPending (.position target) } fuel computation) := by
  apply evalDist_runResolvedLiveValue_of_finalizationSynchronized
  · exact ⟨finalizationViewEq_clearPending_known target output table context hvalid hcomplete hknown,
      hvalid, hvalid.clearPending (.position target), hcomplete⟩
  · rfl
  · rfl

theorem DeferredContext.Valid.replacePrivatePosition
    {context : DeferredContext} (hvalid : context.Valid) (target : Position) (output : HashOutput)
    (hstate : context.state.values (.position target) = none) :
    (replacePrivatePosition target output context).Valid := by
  refine ⟨?_, hvalid.2⟩
  intro position value hvalue
  change context.state.values (.position position) = some value at hvalue
  by_cases heq : position = target
  · subst position
    simp [hstate] at hvalue
  · change Function.update context.values target (some output) position = some value
    rw [Function.update_of_ne heq]
    exact hvalid.1 position value hvalue

theorem evalDist_runResolvedLiveValue_eq_retained_value
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    evalDist (runResolvedLiveValue table context fuel computation) =
      evalDist ((fun result => (retainCompletableResult result).map (fun result => (result.remaining, result.value))) <$>
        runResolvedFromTable context fuel table computation) := by
  unfold runResolvedLiveValue
  rw [map_eq_bind_pure_comp]
  apply evalDist_bind_congr
  intro result hresult
  cases result with
  | none => rfl
  | some result =>
      have hcore := resolvedCore_of_mem_runResolvedFromTable computation context fuel table result hconsistent hstarts hresult
      by_cases hcomplete : DeferredCompletable table result.context <;> simp [retainCompletableResult, hcore.1, hcomplete]

end SphincsSecurity.Concrete.OtsProbeSimulation
