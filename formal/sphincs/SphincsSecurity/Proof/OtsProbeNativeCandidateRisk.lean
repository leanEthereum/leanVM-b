import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbePrivateValueLiveProbeCut

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem probEvent_privateResolutionResult_candidate_eq_resolver
    (target : Position) (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (remaining : Nat) (value : α) (candidate : Digest)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context) :
    Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (fun _ _ => some candidate) <$>
      privateResolutionResult target table context remaining value] =
    Pr[PrivateCandidatePairHit | (fun option => option.map (fun result => (result.output, candidate))) <$>
      resolveDeferredPositionValue target context] := by
  rw [probEvent_map, privateResolutionResult, probEvent_bind_eq_tsum, probEvent_map, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro option
  by_cases hoption : option ∈ support (resolveDeferredPositionValue target context)
  · cases option with
    | none => simp [privateResolvedSelectedCandidate, PrivateCandidatePairHit]
    | some result =>
        have hnext := hcomplete.of_resolveDeferredPositionValue hvalid target result hoption
        have hvalue := resolveDeferredPositionValue_resolves target context result hoption
        simp [hnext, privateResolvedSelectedCandidate, hvalue, PrivateCandidatePairHit]
  · simp [probOutput_eq_zero_of_not_mem_support hoption]

theorem candidateFailureAllowance_position_eq_resolutionHit
    (target : Position) (table : OtsSecretIndex → HashOutput) (context : DeferredContext) (candidate : Digest)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hhidden : .position target ∉ context.state.revealed) :
    candidateFailureAllowance table context (some ⟨.position target, candidate⟩) =
      Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (fun _ (_ : Unit) => some candidate) <$>
        privateResolutionResult target table context 0 ()] := by
  rw [probEvent_privateResolutionResult_candidate_eq_resolver target table context 0 () candidate hvalid hcomplete,
    resolveDeferredPositionValue_eq_bind_output, probEvent_map, probEvent_bind_eq_tsum]
  have hterm (output : HashOutput) :
      Pr[fun option => PrivateCandidatePairHit (option.map (fun result => (result.output, candidate))) |
        resolvePrivatePositionWithOutput target context output] =
      if candidate = truncateHash output ∧ (.position target, candidate) ∉ context.state.pending then 1 else 0 := by
    by_cases hhit : context.state.hitAt (.position target) output
    · by_cases heq : candidate = truncateHash output
      · have hpending : (.position target, candidate) ∈ context.state.pending := by
          rw [heq, ← LazyRevealProbe.State.mem_pendingAt_iff]
          exact hhit
        simp [resolvePrivatePositionWithOutput, hhit, PrivateCandidatePairHit, hpending]
      · simp [resolvePrivatePositionWithOutput, hhit, PrivateCandidatePairHit, heq]
    · by_cases heq : candidate = truncateHash output
      · have hpending : (.position target, candidate) ∉ context.state.pending := by
          rw [heq, ← LazyRevealProbe.State.mem_pendingAt_iff]
          exact hhit
        have hpending' : (.position target, truncateHash output) ∉ context.state.pending := by simpa only [heq] using hpending
        simp [resolvePrivatePositionWithOutput, hhit, completePrivatePosition, PrivateCandidatePairHit, heq, hpending']
      · simp [resolvePrivatePositionWithOutput, hhit, completePrivatePosition, PrivateCandidatePairHit, heq]
  simp_rw [Function.comp_def, hterm]
  by_cases hduplicate : (.position target, candidate) ∈ context.state.pending
  · simp [candidateFailureAllowance, hduplicate]
  · simp only [candidateFailureAllowance, hhidden, hduplicate, or_self, ↓reduceIte, not_false_eq_true, and_true]
    simp only [mul_ite, mul_one, mul_zero]
    rw [← probEvent_eq_tsum_ite]
    cases hvalue : context.positionValue target with
    | none =>
        simp only [resolvedCompletionValue, hvalue, deferredPositionOutput]
        simpa only [show Fintype.card Digest = 2 ^ digestBits by simp, LazyRevealProbe.sampleHashOutput, eq_comm] using
          (SphincsSecurity.probEvent_uniform_truncateHash_eq candidate).symm
    | some output =>
        simp [resolvedCompletionValue, hvalue, deferredPositionOutput, eq_comm]

theorem privateResolutionResult_selected_eq_constant
    (target : Position) (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (remaining : Nat) (value : α) (select : Nat → α → Option Digest) :
    privateResolvedSelectedCandidate target select <$> privateResolutionResult target table context remaining value =
      privateResolvedSelectedCandidate target (fun _ _ => select remaining value) <$>
        privateResolutionResult target table context remaining value := by
  unfold privateResolutionResult
  simp only [map_bind]
  congr 1
  funext option
  cases option with
  | none => rfl
  | some result =>
      dsimp only
      split_ifs <;> simp [privateResolvedSelectedCandidate]

theorem probEvent_privateResolutionResult_selected_eq_allowance
    (target : Position) (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (remaining : Nat) (value : α) (select : Nat → α → Option Digest)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hhidden : select remaining value ≠ none → .position target ∉ context.state.revealed) :
    Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target select <$>
      privateResolutionResult target table context remaining value] =
      candidateFailureAllowance table context ((select remaining value).map (fun digest => ⟨.position target, digest⟩)) := by
  rw [privateResolutionResult_selected_eq_constant]
  cases hselect : select remaining value with
  | none =>
      have hnone : privateResolvedSelectedCandidate target (fun (_ : Nat) (_ : α) => none) = fun _ => none := by
        funext option
        cases option with
        | none => rfl
        | some pair =>
            rcases pair with ⟨final, rest, value⟩
            cases hv : final.positionValue target <;> simp [privateResolvedSelectedCandidate, hv]
      rw [hnone, probEvent_map]
      simp [PrivateCandidatePairHit, candidateFailureAllowance]
  | some candidate =>
      rw [probEvent_privateResolutionResult_candidate_eq_resolver target table context remaining value candidate hvalid hcomplete]
      simp only [Option.map_some]
      rw [candidateFailureAllowance_position_eq_resolutionHit target table context candidate hvalid hcomplete (hhidden (by simp [hselect]))]
      exact (probEvent_privateResolutionResult_candidate_eq_resolver target table context 0 () candidate hvalid hcomplete).symm

theorem probEvent_privateResolvedView_selected_eq_expectedAllowance
    (target : Position) (table : OtsSecretIndex → HashOutput) (context : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (select : Nat → α → Option Digest)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hhidden : ∀ result, some result ∈ support (runResolvedFromTable context fuel table computation) →
      select result.remaining result.value ≠ none → .position target ∉ result.context.state.revealed) :
    Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target select <$>
      runPrivateResolvedView target table context fuel computation] =
    ∑' option, Pr[= option | runResolvedFromTable context fuel table computation] *
      match option with
      | none => 0
      | some result => if DeferredCompletable table result.context then
          candidateFailureAllowance table result.context
            ((select result.remaining result.value).map (fun digest => ⟨.position target, digest⟩)) else 0 := by
  unfold runPrivateResolvedView
  rw [map_bind, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro option
  by_cases hoption : option ∈ support (runResolvedFromTable context fuel table computation)
  · cases option with
    | none => simp [privateResolvedSelectedCandidate, PrivateCandidatePairHit]
    | some result =>
        dsimp only
        have hcore := resolvedCore_of_mem_runResolvedFromTable computation context fuel table result hconsistent hstarts hoption
        by_cases hcomplete : DeferredCompletable table result.context
        · rw [if_pos hcomplete, probEvent_privateResolutionResult_selected_eq_allowance target table result.context result.remaining result.value select
            (valid_of_resolvedCore_completable table result.context hcore.2.1 hcore.2.2 hcomplete) hcomplete (hhidden result hoption)]
        · have heq := evalDist_map_eq_of_evalDist_eq
            (evalDist_privateResolutionResult_eq_none_of_not_completable target table result.context result.remaining result.value hcore.2.1 hcomplete)
            (privateResolvedSelectedCandidate target select)
          have hprob := probEvent_congr' (fun _ _ => Iff.rfl) heq (p := PrivateCandidatePairHit)
          rw [hprob]
          simp [hcomplete, privateResolvedSelectedCandidate, PrivateCandidatePairHit]
  · simp [probOutput_eq_zero_of_not_mem_support hoption]

end SphincsSecurity.Concrete.OtsProbeSimulation
