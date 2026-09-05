import SphincsSecurity.Proof.OtsProbeWeightedReserve

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem candidateFailureAllowance_eq_components
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext) (candidate : Option Probe)
    (hpublic : MaterializedStartsPublished context) :
    candidateFailureAllowance table context candidate =
      unresolvedStartCandidateAllowance table context candidate +
        unresolvedPositionCandidateCharge context candidate * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
        structuralCandidateFailureAllowance context candidate := by
  cases candidate with
  | none => simp [candidateFailureAllowance, unresolvedStartCandidateAllowance,
      unresolvedPositionCandidateCharge, structuralCandidateFailureAllowance]
  | some candidate =>
      rcases candidate with ⟨coordinate, digest⟩
      cases coordinate with
      | position position =>
          simpa only [unresolvedStartCandidateAllowance, unresolvedPositionCandidateCharge, zero_add] using
            candidateFailureAllowance_position_eq table context position digest
      | chainStart lay tree leafIdx chainIdx =>
          by_cases hmissing : context.state.values (.chainStart lay tree leafIdx chainIdx) = none
          · simp [unresolvedStartCandidateAllowance, unresolvedPositionCandidateCharge,
              structuralCandidateFailureAllowance, hmissing]
          · have hrevealed := hpublic ⟨lay, tree, leafIdx, chainIdx⟩ hmissing
            simp only [OtsSecretIndex.coordinate] at hrevealed
            simp [candidateFailureAllowance, unresolvedStartCandidateAllowance, unresolvedPositionCandidateCharge,
              structuralCandidateFailureAllowance, hrevealed, hmissing]

def KnownStructuralCandidateHit (context : DeferredContext) : Option Probe → Prop
  | some ⟨.position position, digest⟩ =>
      .position position ∉ context.state.revealed ∧ (.position position, digest) ∉ context.state.pending ∧
        ∃ output, context.positionValue position = some output ∧ truncateHash output = digest
  | _ => False

theorem structuralCandidateFailureAllowance_eq_indicator (context : DeferredContext) (candidate : Option Probe) :
    structuralCandidateFailureAllowance context candidate = if KnownStructuralCandidateHit context candidate then 1 else 0 := by
  cases candidate with
  | none => simp [structuralCandidateFailureAllowance, KnownStructuralCandidateHit]
  | some candidate =>
      rcases candidate with ⟨coordinate, digest⟩
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx => simp [structuralCandidateFailureAllowance, KnownStructuralCandidateHit]
      | position position =>
          by_cases hrevealed : Coordinate.position position ∈ context.state.revealed
          · simp [structuralCandidateFailureAllowance, KnownStructuralCandidateHit, hrevealed]
          · by_cases hpending : (Coordinate.position position, digest) ∈ context.state.pending
            · simp [structuralCandidateFailureAllowance, KnownStructuralCandidateHit, hpending]
            · cases hvalue : context.positionValue position <;>
                simp [structuralCandidateFailureAllowance, KnownStructuralCandidateHit, hrevealed, hpending, hvalue]

end SphincsSecurity.Concrete.OtsProbeSimulation
