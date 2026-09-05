import SphincsSecurity.Proof.OtsProbePrivateValueAdaptiveSampling
import SphincsSecurity.Proof.OtsProbePrivateValueCompletion

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem retainCompletableResult_replacePrivateRunResult
    (target : Position) (before after : HashOutput) (result : ResolvedRunResult α)
    (hreplaceable : PrivatePositionReplaceable target before after result.context) :
    retainCompletableResult (some (replacePrivateRunResult target after result)) =
      (retainCompletableResult (some result)).map (replacePrivateRunResult target after) := by
  have hcomplete := deferredCompletable_replacePrivatePosition_iff target before after result.context result.table hreplaceable
  simp only [retainCompletableResult, replacePrivateRunResult]
  rw [hcomplete]
  split_ifs <;> rfl

noncomputable def privatePositionFirstLiveCandidate
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (output : HashOutput) : ProbComp (Option Digest) :=
  (fun result => (privatePositionAccessCandidate target ((retainCompletableResult result).map ResolvedRunResult.value)).filter
      (fun digest => digest ∉ context.state.pendingAt (.position target))) <$>
    runResolvedFromTable (replacePrivatePosition target output context) fuel table (privatePositionAccessCut target computation)

theorem evalDist_privatePositionFirstLiveCandidate_eq
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (before after : HashOutput)
    (hstate : context.state.values (.position target) = none) (hhidden : .position target ∉ context.state.revealed)
    (hbefore : ¬context.state.hitAt (.position target) before) (hafter : ¬context.state.hitAt (.position target) after) :
    evalDist (privatePositionFirstLiveCandidate target computation context fuel table before) =
      evalDist (privatePositionFirstLiveCandidate target computation context fuel table after) := by
  have hreplaceable : PrivatePositionReplaceable target before after (replacePrivatePosition target before context) :=
    ⟨hstate, by simp [replacePrivatePosition, DeferredStructuralValues.install], hbefore, hafter⟩
  have hreplace := evalDist_runResolved_replacePrivatePosition target before after
    (privatePositionAccessCut target computation) (replacePrivatePosition target before context) fuel table hreplaceable
    (privatePositionAccessCut_no_exposure target before after computation)
  have hdist : evalDist (runResolvedFromTable (replacePrivatePosition target after context) fuel table
      (privatePositionAccessCut target computation)) =
      evalDist (Option.map (replacePrivateRunResult target after) <$>
        runResolvedFromTable (replacePrivatePosition target before context) fuel table
          (privatePositionAccessCut target computation)) := by
    simpa [replacePrivatePosition, DeferredStructuralValues.install] using hreplace
  unfold privatePositionFirstLiveCandidate
  symm
  calc
    _ = evalDist ((fun result => (privatePositionAccessCandidate target
        ((retainCompletableResult result).map ResolvedRunResult.value)).filter
          (fun digest => digest ∉ context.state.pendingAt (.position target))) <$>
        (Option.map (replacePrivateRunResult target after) <$>
          runResolvedFromTable (replacePrivatePosition target before context) fuel table
            (privatePositionAccessCut target computation))) := by
      rw [evalDist_map, evalDist_map, hdist]
    _ = _ := by
      simp only [map_eq_bind_pure_comp, bind_assoc]
      apply evalDist_bind_congr
      intro result hresult
      cases result with
      | none => rfl
      | some result =>
          have hinitial : PrivateTargetState target before (context.state.pendingAt (.position target))
              (replacePrivatePosition target before context) :=
            ⟨hstate, by simp [replacePrivatePosition, DeferredStructuralValues.install], hhidden, rfl⟩
          have hfinal := PrivateTargetState.of_mem_runResolved_no_access (privatePositionAccessCut target computation)
            (replacePrivatePosition target before context) fuel table result hinitial
            (privatePositionAccessCut_no_access target computation) hresult
          have hbefore' : ¬result.context.state.hitAt (.position target) before := by
            simpa only [LazyRevealProbe.State.hitAt, hfinal.2.2.2] using hbefore
          have hafter' : ¬result.context.state.hitAt (.position target) after := by
            simpa only [LazyRevealProbe.State.hitAt, hfinal.2.2.2] using hafter
          have hretain := retainCompletableResult_replacePrivateRunResult target before after result
            ⟨hfinal.1, hfinal.2.1, hbefore', hafter'⟩
          simp only [pure_bind, Function.comp_apply, Option.map_some, hretain, Option.map_map]
          rfl

noncomputable def privatePositionFirstLiveCharge
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (output : HashOutput) : ENNReal :=
  ∑' result, Pr[= result | runResolvedFromTable (replacePrivatePosition target output context) fuel table
    (privatePositionAccessCut target computation)] * privatePositionCutCharge target (retainCompletableResult result)

theorem probEvent_privatePositionFirstLiveCandidate_eq_charge
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (output : HashOutput)
    (hstate : context.state.values (.position target) = none) (hhidden : .position target ∉ context.state.revealed) :
    Pr[fun candidate => candidate ≠ none | privatePositionFirstLiveCandidate target computation context fuel table output] =
      privatePositionFirstLiveCharge target computation context fuel table output := by
  unfold privatePositionFirstLiveCandidate privatePositionFirstLiveCharge
  rw [probEvent_map, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro result
  by_cases hresult : result ∈ support (runResolvedFromTable (replacePrivatePosition target output context) fuel table
      (privatePositionAccessCut target computation))
  · cases result with
    | none => simp [retainCompletableResult, privatePositionAccessCandidate, privatePositionCutCharge]
    | some result =>
        by_cases hcomplete : DeferredCompletable result.table result.context
        · simp only [retainCompletableResult, if_pos hcomplete]
          rw [privatePositionCutCharge_eq_indicator target computation context fuel table output hstate hhidden (some result) hresult]
          split_ifs <;> simp_all
        · simp [retainCompletableResult, hcomplete, privatePositionAccessCandidate, privatePositionCutCharge]
  · simp [probOutput_eq_zero_of_not_mem_support hresult]

noncomputable def sampledPrivatePositionFirstLiveCandidate
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) : ProbComp (HashOutput × Option Digest) :=
  filteredPrivateGuess (fun output => ¬context.state.hitAt (.position target) output)
    (privatePositionFirstLiveCandidate target computation context fuel table)

noncomputable def sampledPrivatePositionFirstLiveCharge
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) : ENNReal :=
  ∑' output, Pr[= output | LazyRevealProbe.sampleHashOutput] *
    if ¬context.state.hitAt (.position target) output then privatePositionFirstLiveCharge target computation context fuel table output else 0

theorem probEvent_sampledPrivatePositionFirstLiveCandidate_eq_charge
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hstate : context.state.values (.position target) = none) (hhidden : .position target ∉ context.state.revealed) :
    Pr[fun pair => pair.2 ≠ none | sampledPrivatePositionFirstLiveCandidate target computation context fuel table] =
      sampledPrivatePositionFirstLiveCharge target computation context fuel table := by
  unfold sampledPrivatePositionFirstLiveCandidate filteredPrivateGuess sampledPrivatePositionFirstLiveCharge
  rw [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro output
  by_cases hclean : ¬context.state.hitAt (.position target) output
  · rw [if_pos hclean, if_pos hclean]
    have hmap : Pr[fun pair : HashOutput × Option Digest => pair.2 ≠ none |
        privatePositionFirstLiveCandidate target computation context fuel table output >>= fun candidate => pure (output, candidate)] =
        Pr[fun candidate => candidate ≠ none | privatePositionFirstLiveCandidate target computation context fuel table output] :=
      probEvent_bind_pure_comp (privatePositionFirstLiveCandidate target computation context fuel table output)
        (fun candidate => (output, candidate)) (fun pair => pair.2 ≠ none)
    rw [hmap, probEvent_privatePositionFirstLiveCandidate_eq_charge target computation context fuel table output hstate hhidden]
  · simp [hclean]

theorem probEvent_sampledPrivatePositionFirstLiveCandidate_hit_le_charge
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hstate : context.state.values (.position target) = none) (hhidden : .position target ∉ context.state.revealed)
    (hcard : context.state.pending.card ≤ 2 ^ 126) :
    Pr[fun pair => pair.2 = some (truncateHash pair.1) |
      sampledPrivatePositionFirstLiveCandidate target computation context fuel table] ≤
      sampledPrivatePositionFirstLiveCharge target computation context fuel table *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  have hsmall : context.state.pending.card < Fintype.card Digest := hcard.trans_lt (by norm_num [digestBits])
  obtain ⟨digest, hmiss⟩ := exists_digest_not_mem_pendingAt context.state (.position target) hsmall
  let reference := hashOutputOfDigest digest
  have hclean : ¬context.state.hitAt (.position target) reference := by
    simpa only [LazyRevealProbe.State.hitAt, reference, truncateHash_hashOutputOfDigest] using hmiss
  rw [← probEvent_sampledPrivatePositionFirstLiveCandidate_eq_charge target computation context fuel table hstate hhidden]
  simpa only [sampledPrivatePositionFirstLiveCandidate, show Fintype.card Digest = 2 ^ digestBits by simp] using
    probEvent_filteredPrivateGuess_hit_le_four_thirds
      (fun output => ¬context.state.hitAt (.position target) output)
      (privatePositionFirstLiveCandidate target computation context fuel table)
      (privatePositionFirstLiveCandidate target computation context fuel table reference)
      (fun output houtput => evalDist_privatePositionFirstLiveCandidate_eq target computation context fuel table
        output reference hstate hhidden houtput hclean)
      (probEvent_no_private_pendingHit_ge_three_quarters context target hcard)

end SphincsSecurity.Concrete.OtsProbeSimulation
