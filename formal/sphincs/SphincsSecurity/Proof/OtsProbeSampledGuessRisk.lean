import SphincsSecurity.Proof.OtsProbeRetainedGuessCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

noncomputable def structuralCandidateFailureAllowance (context : DeferredContext) : Option Probe → ℝ≥0∞
  | none => 0
  | some candidate =>
      if candidate.coordinate ∈ context.state.revealed ∨
          (candidate.coordinate, candidate.candidate) ∈ context.state.pending then 0
      else match candidate.coordinate with
        | .chainStart _ _ _ _ => 0
        | .position position => match context.positionValue position with
          | none => 0
          | some output => if truncateHash output = candidate.candidate then 1 else 0

theorem expected_candidateFailureAllowance_chainStart_of_missing
    (context : DeferredContext) (index : OtsSecretIndex) (digest : Digest)
    (hmissing : context.state.values index.coordinate = none) :
    (∑' base, Pr[= base | sampleOtsHashTable] *
      candidateFailureAllowance (completedStartTable context.state base) context (some ⟨index.coordinate, digest⟩)) ≤
      (unmaterializedCandidateCharge (materializedDeferredState context) (some ⟨index.coordinate, digest⟩) : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
  dsimp only [OtsSecretIndex.coordinate] at hmissing ⊢
  by_cases hrevealed : Coordinate.chainStart lay tree leafIdx chainIdx ∈ context.state.revealed
  · simp [candidateFailureAllowance, unmaterializedCandidateCharge, materializedDeferredState, hrevealed]
  · by_cases hduplicate : (Coordinate.chainStart lay tree leafIdx chainIdx, digest) ∈ context.state.pending
    · simp [candidateFailureAllowance, unmaterializedCandidateCharge, materializedDeferredState,
        LazyRevealProbe.pendingProbeCharge, hrevealed, hduplicate, hmissing]
    · simp only [candidateFailureAllowance, hrevealed, hduplicate, or_self, ↓reduceIte,
        resolvedCompletionValue, completedStartTable, OtsSecretIndex.coordinate, hmissing, Option.getD_none,
        unmaterializedCandidateCharge, materializedDeferredState, LazyRevealProbe.pendingProbeCharge,
        ne_eq, not_true_eq_false, Nat.cast_one, one_mul]
      simpa only [probEvent_eq_tsum_ite, mul_ite, mul_one, mul_zero] using
        probEvent_sampleOtsHashTable_cell_truncate_eq ⟨lay, tree, leafIdx, chainIdx⟩ digest

theorem candidateFailureAllowance_position_eq
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext) (position : Position) (digest : Digest) :
    candidateFailureAllowance table context (some ⟨.position position, digest⟩) =
      (unmaterializedCandidateCharge (materializedDeferredState context) (some ⟨.position position, digest⟩) : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
      structuralCandidateFailureAllowance context (some ⟨.position position, digest⟩) := by
  classical
  by_cases hrevealed : Coordinate.position position ∈ context.state.revealed
  · simp [candidateFailureAllowance, unmaterializedCandidateCharge, materializedDeferredState,
      structuralCandidateFailureAllowance, hrevealed]
  · by_cases hduplicate : (Coordinate.position position, digest) ∈ context.state.pending
    · simp [candidateFailureAllowance, unmaterializedCandidateCharge, materializedDeferredState,
        structuralCandidateFailureAllowance, LazyRevealProbe.pendingProbeCharge, hrevealed, hduplicate]
    · cases hvalue : context.positionValue position <;>
        simp [candidateFailureAllowance, resolvedCompletionValue, unmaterializedCandidateCharge,
          materializedDeferredState, structuralCandidateFailureAllowance, LazyRevealProbe.pendingProbeCharge,
          hrevealed, hduplicate, hvalue]

theorem expected_candidateFailureAllowance_le_ordinary_add_structural
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext) (candidate : Option Probe)
    (hcanonical : CanonicalMaterializedValues table context) :
    (∑' base, Pr[= base | sampleOtsHashTable] *
      candidateFailureAllowance (completedStartTable context.state base) context candidate) ≤
      (unmaterializedCandidateCharge (materializedDeferredState context) candidate : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ + structuralCandidateFailureAllowance context candidate := by
  classical
  cases candidate with
  | none => simp [candidateFailureAllowance, unmaterializedCandidateCharge, structuralCandidateFailureAllowance]
  | some candidate =>
      rcases candidate with ⟨coordinate, digest⟩
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          by_cases hrevealed : Coordinate.chainStart lay tree leafIdx chainIdx ∈ context.state.revealed
          · simp [candidateFailureAllowance, unmaterializedCandidateCharge, materializedDeferredState,
              structuralCandidateFailureAllowance, hrevealed]
          · have hmissing : context.state.values (.chainStart lay tree leafIdx chainIdx) = none := by
              rw [hcanonical]
              simp [publicMaterializedValues, hrevealed]
            simpa [structuralCandidateFailureAllowance, OtsSecretIndex.coordinate] using
              expected_candidateFailureAllowance_chainStart_of_missing context ⟨lay, tree, leafIdx, chainIdx⟩ digest hmissing
      | position position =>
          simp_rw [candidateFailureAllowance_position_eq]
          rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]

theorem executeCandidate_ordinaryCharge_eq_of_positive_fuel
    (candidate : Option Probe) (cache : SplitHashCache) (context : DeferredContext) (fuel : Nat) :
    ordinaryContinuationCharge (fun _ _ _ => 0) ((executeCandidate? candidate).run cache) context (fuel + 1) =
      (unmaterializedCandidateCharge context.state candidate : ℝ≥0∞) := by
  cases candidate with
  | none => simp [executeCandidate?, ordinaryContinuationCharge, unmaterializedCandidateCharge]
  | some candidate =>
      change ordinaryContinuationCharge (fun _ _ _ => 0)
        (LazyRevealProbe.probeQuery candidate.coordinate candidate.candidate >>= fun _ => pure ((), cache))
        context (fuel + 1) = _
      rw [LazyRevealProbe.probeQuery, ordinaryContinuationCharge_query_bind, ordinaryChargeStep.eq_def]
      by_cases hrevealed : candidate.coordinate ∈ context.state.revealed <;>
        simp [hrevealed, ordinaryContinuationCharge, unmaterializedCandidateCharge]

theorem expected_canonicalHashQuery_finished_le_ordinary_add_structural
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (input : HashInput)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hcanonical : CanonicalMaterializedValues table context)
    (hcard : context.state.pending.card + 1 < Fintype.card Digest) :
    (∑' base, Pr[= base | sampleOtsHashTable] * Pr[fun verdict => verdict = true |
      canonicalChronologicalAdversaryImpl parameter root (completedStartTable context.state base) ftsSecret
        (.inl (.inr input)) context (fuel + 1) (completedStartTable context.state base) cache >>=
          finishResolvedRunIsNone]) ≤
      (∑' base, Pr[= base | sampleOtsHashTable] *
        resolvedContextFailureRisk (completedStartTable context.state base) context) +
      ordinaryContinuationCharge (fun _ _ _ => 0)
        ((probingHashQueryAfterPublicPlan parameter input context.state
          (purePlanProbingHashQuery parameter input context.state)).run cache)
        (materializedDeferredContext context) (fuel + 1) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
      structuralCandidateFailureAllowance context (purePlanProbingHashQuery parameter input context.state).candidate? := by
  rw [probingHashQueryAfterPublicPlan_ordinaryCharge_eq_executeCandidate,
    executeCandidate_ordinaryCharge_eq_of_positive_fuel]
  calc
    _ ≤ ∑' base, Pr[= base | sampleOtsHashTable] *
        (resolvedContextFailureRisk (completedStartTable context.state base) context +
          candidateFailureAllowance (completedStartTable context.state base) context
            (purePlanProbingHashQuery parameter input context.state).candidate?) := by
      apply ENNReal.tsum_le_tsum
      intro base
      exact mul_le_mul_right (probEvent_canonicalHashQuery_finished_le_initial_add_allowance
        parameter root (completedStartTable context.state base) ftsSecret input context fuel cache hconsistent
        (startTableAgrees_completedStartTable context.state base) hcard) _
    _ = _ + ∑' base, Pr[= base | sampleOtsHashTable] *
        candidateFailureAllowance (completedStartTable context.state base) context
          (purePlanProbingHashQuery parameter input context.state).candidate? := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add]
    _ ≤ _ := by
      rw [add_assoc]
      exact add_le_add le_rfl
        (expected_candidateFailureAllowance_le_ordinary_add_structural table context _ hcanonical)

end SphincsSecurity.Concrete.OtsProbeSimulation
