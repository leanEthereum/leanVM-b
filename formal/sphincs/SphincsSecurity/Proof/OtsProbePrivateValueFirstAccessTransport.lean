import SphincsSecurity.Proof.OtsProbePrivateValuePendingCleanup

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem clearPending_eq_self_of_pendingAt_empty
    (state : LazyRevealProbe.State Coordinate) (coordinate : Coordinate) (hempty : state.pendingAt coordinate = ∅) :
    state.clearPending coordinate = state := by
  have hpending : state.pendingAway coordinate = state.pending := by
    apply Finset.filter_eq_self.mpr
    intro pair hpair heq
    have hmem : pair.2 ∈ state.pendingAt coordinate := by
      rw [LazyRevealProbe.State.mem_pendingAt_iff]
      simpa only [← heq, Prod.mk.eta] using hpair
    simp [hempty] at hmem
  cases state
  simp_all [LazyRevealProbe.State.clearPending]

theorem PrivateTargetState.resolve_of_no_pending
    {target : Position} {output : HashOutput} {context : DeferredContext}
    (h : PrivateTargetState target output ∅ context) :
    resolveDeferredPositionValue target context = pure (some (DeferredResolution.mk context output)) := by
  have hclear := clearPending_eq_self_of_pendingAt_empty context.state (.position target) h.2.2.2
  simp [resolveDeferredPositionValue, h.1, h.2.1, LazyRevealProbe.State.hitAt, h.2.2.2, hclear]

def privateResolvedCandidate (target : Position) (pending : Finset Digest) :
    Option (DeferredContext × Nat × PrivateValueCut α) → Option (HashOutput × Digest)
  | none => none
  | some (context, remaining, cut) => do
      let output ← context.positionValue target
      let candidate ← privateLiveCandidateProjection target pending (some (remaining, cut))
      pure (output, candidate)

theorem evalDist_privateResolvedCandidate_of_preloaded_cut
    (target : Position) (output : HashOutput) (pending : Finset Digest)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (h : PrivateTargetState target output ∅ context) :
    evalDist (privateResolvedCandidate target pending <$>
      runPrivateResolvedView target table context fuel (privatePositionAccessCut target computation)) =
      evalDist ((fun candidate => candidate.map (fun digest => (output, digest))) <$>
        (privateLiveCandidateProjection target pending <$>
          runResolvedLiveValue table context fuel (privatePositionAccessCut target computation))) := by
  unfold runPrivateResolvedView runResolvedLiveValue
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply evalDist_bind_congr
  intro result hresult
  cases result with
  | none => rfl
  | some result =>
      have hfinal := PrivateTargetState.of_mem_runResolved_no_access (privatePositionAccessCut target computation)
        context fuel table result h (privatePositionAccessCut_no_access target computation) hresult
      have hknown : result.context.positionValue target = some output := by
        simp [DeferredContext.positionValue, hfinal.1, hfinal.2.1]
      dsimp only
      unfold privateResolutionResult
      rw [hfinal.resolve_of_no_pending]
      simp only [pure_bind]
      by_cases hcomplete : DeferredCompletable table result.context
      · simp only [if_pos hcomplete, pure_bind, Function.comp_apply, privateResolvedCandidate, hknown]
        cases privateLiveCandidateProjection target pending (some (result.remaining, result.value)) <;> rfl
      · simp [hcomplete, privateResolvedCandidate, privateLiveCandidateProjection, privatePositionAccessCandidate]

theorem evalDist_privateResolvedCandidate_completePrivatePosition
    (target : Position) (output : HashOutput) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hstate : context.state.values (.position target) = none) (hhidden : .position target ∉ context.state.revealed)
    (hclean : ¬context.state.hitAt (.position target) output) :
    evalDist (privateResolvedCandidate target (context.state.pendingAt (.position target)) <$>
      runPrivateResolvedView target table (completePrivatePosition target context output).toDeferredContext fuel
        (privatePositionAccessCut target computation)) =
      evalDist ((fun candidate => candidate.map (fun digest => (output, digest))) <$>
        privatePositionFirstLiveCandidate target computation context fuel table output) := by
  have hinitial : PrivateTargetState target output ∅ (completePrivatePosition target context output).toDeferredContext := by
    refine ⟨hstate, ?_, hhidden, ?_⟩
    · simp [completePrivatePosition, DeferredStructuralValues.install]
    · ext digest
      simp [completePrivatePosition, LazyRevealProbe.State.pendingAt, LazyRevealProbe.State.clearPending,
        LazyRevealProbe.State.pendingAway]
  rw [evalDist_privateResolvedCandidate_of_preloaded_cut target output _ computation _ fuel table hinitial]
  exact evalDist_map_eq_of_evalDist_eq
    (evalDist_privatePositionFirstLiveCandidate_clearPending target computation context fuel table output hvalid hcomplete hstate hclean).symm _

def privateSampledCandidatePair (pair : HashOutput × Option Digest) : Option (HashOutput × Digest) :=
  pair.2.map (fun digest => (pair.1, digest))

theorem evalDist_privateResolvedCandidate_eq_sampled_first
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : .position target ∈ context.state.ensured)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = none)
    (hhidden : .position target ∉ context.state.revealed) :
    evalDist (privateResolvedCandidate target (context.state.pendingAt (.position target)) <$>
      runPrivateResolvedView target table context fuel (privatePositionAccessCut target computation)) =
      evalDist (privateSampledCandidatePair <$> sampledPrivatePositionFirstLiveCandidate target computation context fuel table) := by
  have hdist := evalDist_runPrivateResolvedView_eq_uniform target (privatePositionAccessCut target computation)
    context fuel table hvalid hcomplete hensured hstate hvalue
  calc
    _ = evalDist (privateResolvedCandidate target (context.state.pendingAt (.position target)) <$> (do
      let output ← LazyRevealProbe.sampleHashOutput
      if context.state.hitAt (.position target) output then pure none
      else
        runPrivateResolvedView target table (completePrivatePosition target context output).toDeferredContext fuel
          (privatePositionAccessCut target computation))) := by
      rw [evalDist_map, evalDist_map, hdist]
    _ = _ := by
      unfold sampledPrivatePositionFirstLiveCandidate filteredPrivateGuess
      simp only [map_eq_bind_pure_comp, bind_assoc]
      apply evalDist_bind_congr
      intro output _
      by_cases hhit : context.state.hitAt (.position target) output
      · simp [hhit, privateResolvedCandidate, privateSampledCandidatePair]
      · simp only [if_neg hhit, if_pos hhit]
        have htransport := evalDist_privateResolvedCandidate_completePrivatePosition target output computation
          context fuel table hvalid hcomplete hstate hhidden hhit
        simpa only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind, privateSampledCandidatePair] using htransport

def PrivateCandidatePairHit : Option (HashOutput × Digest) → Prop
  | none => False
  | some (output, candidate) => candidate = truncateHash output

theorem probEvent_privateResolvedCandidate_hit_le_charge
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : .position target ∈ context.state.ensured)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = none)
    (hhidden : .position target ∉ context.state.revealed) (hcard : context.state.pending.card ≤ 2 ^ 126) :
    Pr[PrivateCandidatePairHit | privateResolvedCandidate target (context.state.pendingAt (.position target)) <$>
      runPrivateResolvedView target table context fuel (privatePositionAccessCut target computation)] ≤
      sampledPrivatePositionFirstLiveCharge target computation context fuel table *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  have hdist := evalDist_privateResolvedCandidate_eq_sampled_first target computation context fuel table
    hvalid hcomplete hensured hstate hvalue hhidden
  rw [probEvent_congr' (fun _ _ => Iff.rfl) hdist, probEvent_map]
  have hevent (pair : HashOutput × Option Digest) : PrivateCandidatePairHit (privateSampledCandidatePair pair) ↔
      pair.2 = some (truncateHash pair.1) := by
    rcases pair with ⟨output, candidate⟩
    cases candidate <;> simp [privateSampledCandidatePair, PrivateCandidatePairHit]
  have hprob := probEvent_congr' (fun pair _ => hevent pair)
    (rfl : evalDist (sampledPrivatePositionFirstLiveCandidate target computation context fuel table) = _)
  simp only [Function.comp_def]
  rw [hprob]
  exact probEvent_sampledPrivatePositionFirstLiveCandidate_hit_le_charge target computation context fuel table hstate hhidden hcard

theorem probEvent_privateResolvedCandidate_exists_eq_charge
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : .position target ∈ context.state.ensured)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = none)
    (hhidden : .position target ∉ context.state.revealed) :
    Pr[fun pair => pair ≠ none | privateResolvedCandidate target (context.state.pendingAt (.position target)) <$>
      runPrivateResolvedView target table context fuel (privatePositionAccessCut target computation)] =
      sampledPrivatePositionFirstLiveCharge target computation context fuel table := by
  have hdist := evalDist_privateResolvedCandidate_eq_sampled_first target computation context fuel table
    hvalid hcomplete hensured hstate hvalue hhidden
  rw [probEvent_congr' (fun _ _ => Iff.rfl) hdist, probEvent_map]
  have hevent (pair : HashOutput × Option Digest) : privateSampledCandidatePair pair ≠ none ↔ pair.2 ≠ none := by
    rcases pair with ⟨output, candidate⟩
    cases candidate <;> simp [privateSampledCandidatePair]
  have hprob := probEvent_congr' (fun pair _ => hevent pair)
    (rfl : evalDist (sampledPrivatePositionFirstLiveCandidate target computation context fuel table) = _)
  simp only [Function.comp_def]
  rw [hprob]
  exact probEvent_sampledPrivatePositionFirstLiveCandidate_eq_charge target computation context fuel table hstate hhidden

theorem probEvent_privateResolvedCandidate_hit_le_occurrence
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : .position target ∈ context.state.ensured)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = none)
    (hhidden : .position target ∉ context.state.revealed) (hcard : context.state.pending.card ≤ 2 ^ 126) :
    Pr[PrivateCandidatePairHit | privateResolvedCandidate target (context.state.pendingAt (.position target)) <$>
      runPrivateResolvedView target table context fuel (privatePositionAccessCut target computation)] ≤
      Pr[fun pair => pair ≠ none | privateResolvedCandidate target (context.state.pendingAt (.position target)) <$>
        runPrivateResolvedView target table context fuel (privatePositionAccessCut target computation)] *
          ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  rw [probEvent_privateResolvedCandidate_exists_eq_charge target computation context fuel table
    hvalid hcomplete hensured hstate hvalue hhidden]
  exact probEvent_privateResolvedCandidate_hit_le_charge target computation context fuel table
    hvalid hcomplete hensured hstate hvalue hhidden hcard

end SphincsSecurity.Concrete.OtsProbeSimulation
