import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbePrivateValueRawProbeRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem evalDist_privateResolutionResult_eq_none_of_not_completable
    (target : Position) (table : OtsSecretIndex → HashOutput) (context : DeferredContext) (fuel : Nat) (value : α)
    (hconsistent : context.ValuesConsistent) (hdoomed : ¬DeferredCompletable table context) :
    evalDist (privateResolutionResult target table context fuel value) =
      evalDist (pure none : ProbComp (Option (DeferredContext × Nat × α))) := by
  unfold privateResolutionResult
  calc
    _ = evalDist (resolveDeferredPositionValue target context >>= fun _ => pure none) := by
      apply evalDist_bind_congr
      intro result hresult
      cases result with
      | none => rfl
      | some result =>
          have hstillDoomed : ¬DeferredCompletable table result.toDeferredContext := by
            rintro ⟨completion, hcompletion⟩
            have hback := (deferredCompletion_resolveDeferredPositionValue_iff target result hconsistent hresult completion).mp hcompletion
            exact hdoomed ⟨completion, hback.1⟩
          simp [hstillDoomed]
    _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails
      (resolveDeferredPositionValue target context) (by simp [resolveDeferredPositionValue, LazyRevealProbe.sampleHashOutput]) (pure none)

noncomputable def LivePrivateProbeCutReached
    (target : Position) (result : Option (ResolvedRunResult (PrivateValueCut α))) : Prop :=
  PrivateProbeCutReached target (retainCompletableResult result)

theorem probEvent_privateResolvedRawCandidate_occurrence_le_live_cut
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    Pr[fun pair => pair ≠ none | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
      runPrivateResolvedView target table context fuel (privatePositionProbeCutAt target computation ordinal)] ≤
      Pr[LivePrivateProbeCutReached target | runResolvedFromTable context fuel table (privatePositionProbeCutAt target computation ordinal)] := by
  unfold runPrivateResolvedView
  rw [map_bind]
  apply probEvent_bind_le_probEvent
  intro result hresult hmiss
  cases result with
  | none => simp [privateResolvedSelectedCandidate]
  | some result =>
      have hcore := resolvedCore_of_mem_runResolvedFromTable (privatePositionProbeCutAt target computation ordinal)
        context fuel table result hconsistent hstarts hresult
      dsimp only
      by_cases hcomplete : DeferredCompletable table result.context
      · have hnone : privateRawCutCandidate target result.remaining result.value = none := by
          simpa only [LivePrivateProbeCutReached, retainCompletableResult, hcore.1, if_pos hcomplete,
            PrivateProbeCutReached, Option.map_some, privateRawCutCandidate, not_not] using hmiss
        unfold privateResolutionResult
        rw [map_bind, probEvent_bind_eq_tsum]
        apply ENNReal.tsum_eq_zero.mpr
        intro resolved
        cases resolved with
        | none => simp [privateResolvedSelectedCandidate]
        | some resolved =>
            by_cases hresolved : DeferredCompletable table resolved.toDeferredContext
            · simp only [if_pos hresolved, map_pure, privateResolvedSelectedCandidate, hnone]
              cases resolved.toDeferredContext.positionValue target <;> simp
            · simp [hresolved, privateResolvedSelectedCandidate]
      · have hdist := evalDist_privateResolutionResult_eq_none_of_not_completable target table result.context
          result.remaining result.value hcore.2.1 hcomplete
        have hmapped := evalDist_map_eq_of_evalDist_eq hdist (privateResolvedSelectedCandidate target (privateRawCutCandidate target))
        rw [probEvent_congr' (fun _ _ => Iff.rfl) hmapped]
        simp [privateResolvedSelectedCandidate]

theorem sampledPrivateProbeCharge_le_live_cut
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : .position target ∈ context.state.ensured)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = none)
    (hhidden : .position target ∉ context.state.revealed) :
    sampledPrivateProbeCharge target computation context fuel table ordinal ≤
      Pr[LivePrivateProbeCutReached target | runResolvedFromTable context fuel table (privatePositionProbeCutAt target computation ordinal)] :=
  (sampledPrivateProbeCharge_le_raw_occurrence target computation context fuel table ordinal
    hvalid hcomplete hensured hstate hvalue hhidden).trans
      (probEvent_privateResolvedRawCandidate_occurrence_le_live_cut target computation context fuel table ordinal
        hvalid.valuesConsistent (startTableAgrees_of_deferredCompletable hcomplete))

theorem probEvent_privateResolvedRawCandidate_hit_le_live_cut
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : .position target ∈ context.state.ensured)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = none)
    (hhidden : .position target ∉ context.state.revealed)
    (hcard : (context.state.pendingAt (.position target)).card + ordinal ≤ 2 ^ 126) :
    Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
      runPrivateResolvedView target table context fuel (privatePositionProbeCutAt target computation ordinal)] ≤
      Pr[LivePrivateProbeCutReached target | runResolvedFromTable context fuel table (privatePositionProbeCutAt target computation ordinal)] *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  apply (probEvent_privateResolvedRawCandidate_hit_le_charge target computation context fuel table ordinal
    hvalid hcomplete hensured hstate hvalue hhidden hcard).trans
  exact mul_le_mul' (sampledPrivateProbeCharge_le_live_cut target computation context fuel table ordinal
    hvalid hcomplete hensured hstate hvalue hhidden) le_rfl

theorem probEvent_livePrivateProbeCutReached_eq_zero_of_not_completable
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hdoomed : ¬DeferredCompletable table context) :
    Pr[LivePrivateProbeCutReached target | runResolvedFromTable context fuel table (privatePositionProbeCutAt target computation ordinal)] = 0 := by
  rw [probEvent_eq_zero_iff]
  intro result hresult
  cases result with
  | none => simp [LivePrivateProbeCutReached, retainCompletableResult, PrivateProbeCutReached, privatePositionAccessCandidate]
  | some result =>
      have hcore := resolvedCore_of_mem_runResolvedFromTable (privatePositionProbeCutAt target computation ordinal) context fuel table result
        hconsistent hstarts hresult
      have hstillDoomed := not_deferredCompletable_of_mem_runResolvedFromTable (privatePositionProbeCutAt target computation ordinal)
        context fuel table result hconsistent hstarts hresult hdoomed
      simp [LivePrivateProbeCutReached, retainCompletableResult, hcore.1, hstillDoomed, PrivateProbeCutReached, privatePositionAccessCandidate]

end SphincsSecurity.Concrete.OtsProbeSimulation
