import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeFreshGuessRisk
import SphincsSecurity.Proof.OtsProbePlannedCharge
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelectionMaterialize

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

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

end SphincsSecurity.Concrete.OtsProbeSimulation
