import SphincsSecurity.Proof.OtsProbePrivateValueFirstAccessCharge
import SphincsSecurity.Proof.OtsProbeResolvedPrivateObserver

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def privateResolutionObserve
    (target : Position) (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (value : α) : ProbComp Bool := do
  let resolved ← resolveDeferredPositionValue target context
  match resolved with
  | none => pure true
  | some resolved =>
      if DeferredCompletable table resolved.toDeferredContext then observe resolved.toDeferredContext fuel value
      else pure true

instance privateResolutionObserve_dooms
    (target : Position) (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → ProbComp Bool) :
    ObserverDooms table (privateResolutionObserve target table observe) where
  eq_true context fuel value hconsistent _hstarts hdoomed := by
    unfold privateResolutionObserve
    calc
      _ = evalDist (resolveDeferredPositionValue target context >>= fun _ => pure true) := by
        apply evalDist_bind_congr
        intro result hresult
        cases result with
        | none => rfl
        | some result =>
            have hstillDoomed : ¬DeferredCompletable table result.toDeferredContext := by
              rintro ⟨completion, hcompletion⟩
              have hback := (deferredCompletion_resolveDeferredPositionValue_iff target result
                hconsistent hresult completion).mp hcompletion
              exact hdoomed ⟨completion, hback.1⟩
            simp [hstillDoomed]
      _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        (resolveDeferredPositionValue target context) (by simp [resolveDeferredPositionValue, LazyRevealProbe.sampleHashOutput])
        (pure true)

theorem privateResolutionObserve_neutral
    (target : Position) (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → ProbComp Bool) :
    ObserverPositionNeutralAt table target (privateResolutionObserve target table observe) := by
  intro context fuel value _hvalid _hcomplete _hensured
  unfold privateResolutionObserve
  apply evalDist_bind_congr
  intro result hresult
  cases result with
  | none => rfl
  | some result =>
      dsimp only
      rw [resolveDeferredPositionValue_of_resolved target context result hresult]
      simp

theorem evalDist_resolvePrivate_then_run_privateResolutionObserve
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : .position target ∈ context.state.ensured) :
    evalDist (do
      let resolved ← resolveDeferredPositionValue target context
      match resolved with
      | none => pure true
      | some resolved =>
          runResolvedObserve (privateResolutionObserve target table observe) resolved.toDeferredContext fuel table computation) =
      evalDist (runResolvedObserve (privateResolutionObserve target table observe) context fuel table computation) := by
  exact evalDist_resolveDeferredPositionValue_then_runResolvedObserve_auto_at target computation context fuel table
    hvalid hcomplete hensured (privateResolutionObserve_neutral target table observe)

noncomputable def privateResolutionResult
    (target : Position) (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (fuel : Nat) (value : α) : ProbComp (Option (DeferredContext × Nat × α)) := do
  let resolved ← resolveDeferredPositionValue target context
  match resolved with
  | none => pure none
  | some resolved =>
      if DeferredCompletable table resolved.toDeferredContext then pure (some (resolved.toDeferredContext, fuel, value))
      else pure none

noncomputable def runPrivateResolvedView
    (target : Position) (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (fuel : Nat) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    ProbComp (Option (DeferredContext × Nat × α)) := do
  let result ← runResolvedFromTable context fuel table computation
  match result with
  | none => pure none
  | some result => privateResolutionResult target table result.context result.remaining result.value

theorem privateResolutionObserve_eq_map
    (target : Position) (table : OtsSecretIndex → HashOutput)
    (test : Option (DeferredContext × Nat × α) → Bool) (htest : test none = true)
    (context : DeferredContext) (fuel : Nat) (value : α) :
    privateResolutionObserve target table (fun context fuel value => pure (test (some (context, fuel, value))))
        context fuel value = test <$> privateResolutionResult target table context fuel value := by
  unfold privateResolutionObserve privateResolutionResult
  rw [map_bind]
  apply bind_congr
  intro result
  cases result with
  | none => simp [htest]
  | some result =>
      by_cases hcomplete : DeferredCompletable table result.toDeferredContext <;> simp [hcomplete, htest]

theorem runPrivateResolvedView_observe_eq
    (target : Position) (table : OtsSecretIndex → HashOutput)
    (test : Option (DeferredContext × Nat × α) → Bool) (htest : test none = true)
    (context : DeferredContext) (fuel : Nat) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    runResolvedObserve
        (privateResolutionObserve target table (fun context fuel value => pure (test (some (context, fuel, value)))))
        context fuel table computation = test <$> runPrivateResolvedView target table context fuel computation := by
  unfold runResolvedObserve runPrivateResolvedView
  rw [map_bind]
  apply bind_congr
  intro result
  cases result with
  | none => simp [finishObserve, htest]
  | some result => exact privateResolutionObserve_eq_map target table test htest result.context result.remaining result.value

theorem evalDist_eq_of_bool_tests_none (left right : ProbComp (Option α))
    (htests : ∀ test : Option α → Bool, test none = true → evalDist (test <$> left) = evalDist (test <$> right)) :
    evalDist left = evalDist right := by
  apply evalDist_ext
  intro result
  cases result with
  | none =>
      have hp : Pr[fun output => output = true | Option.isNone <$> left] =
          Pr[fun output => output = true | Option.isNone <$> right] :=
        probEvent_congr' (fun _ _ => Iff.rfl) (htests Option.isNone rfl)
      rw [probEvent_map, probEvent_map] at hp
      simpa only [Function.comp_def, Option.isNone_iff_eq_none, probEvent_eq_eq_probOutput] using hp
  | some value =>
      let test := fun result : Option α => decide (result ≠ some value)
      have hp : Pr[fun output => output = false | test <$> left] =
          Pr[fun output => output = false | test <$> right] :=
        probEvent_congr' (fun _ _ => Iff.rfl) (htests test (by simp [test]))
      rw [probEvent_map, probEvent_map] at hp
      simpa only [Function.comp_def, test, decide_eq_false_iff_not, not_not, probEvent_eq_eq_probOutput] using hp

theorem evalDist_resolvePrivate_then_runPrivateResolvedView
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : .position target ∈ context.state.ensured) :
    evalDist (do
      let resolved ← resolveDeferredPositionValue target context
      match resolved with
      | none => pure none
      | some resolved => runPrivateResolvedView target table resolved.toDeferredContext fuel computation) =
      evalDist (runPrivateResolvedView target table context fuel computation) := by
  apply evalDist_eq_of_bool_tests_none
  intro test htest
  have hdist := evalDist_resolvePrivate_then_run_privateResolutionObserve target computation
    (fun context fuel value => pure (test (some (context, fuel, value)))) context fuel table hvalid hcomplete hensured
  rw [runPrivateResolvedView_observe_eq target table test htest] at hdist
  rw [map_bind]
  apply Eq.trans _ hdist
  apply evalDist_bind_congr
  intro result _
  cases result with
  | none => simp [htest]
  | some result =>
      exact congrArg evalDist (runPrivateResolvedView_observe_eq target table test htest result.toDeferredContext fuel computation).symm

theorem evalDist_runPrivateResolvedView_eq_uniform
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : .position target ∈ context.state.ensured)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = none) :
    evalDist (runPrivateResolvedView target table context fuel computation) =
      evalDist (do
        let output ← LazyRevealProbe.sampleHashOutput
        if context.state.hitAt (.position target) output then pure none
        else runPrivateResolvedView target table (completePrivatePosition target context output).toDeferredContext fuel computation) := by
  rw [← evalDist_resolvePrivate_then_runPrivateResolvedView target computation context fuel table hvalid hcomplete hensured]
  unfold resolveDeferredPositionValue
  simp only [hstate, hvalue, bind_assoc]
  apply evalDist_bind_congr
  intro output _
  by_cases hhit : context.state.hitAt (.position target) output <;> simp [hhit, completePrivatePosition]

end SphincsSecurity.Concrete.OtsProbeSimulation
