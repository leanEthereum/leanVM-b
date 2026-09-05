import SphincsSecurity.Proof.OtsProbeNativeStartCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def materializedCandidateAllowance (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) : Option Probe → ENNReal
  | none => 0
  | some candidate => if context.state.values candidate.coordinate = none then 0
      else candidateFailureAllowance table context (some candidate)

theorem candidateFailureAllowance_eq_native_components
    (targets : Finset Position) (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (candidate : Option Probe)
    (hcoverage : ∀ target digest, candidate = some ⟨.position target, digest⟩ → target ∈ targets) :
    candidateFailureAllowance table context candidate =
      unresolvedStartCandidateAllowance table context candidate +
        (∑ target ∈ targets, privateMissingCandidateAllowance target table context candidate) +
        materializedCandidateAllowance table context candidate := by
  cases candidate with
  | none => simp [candidateFailureAllowance, unresolvedStartCandidateAllowance,
      privateMissingCandidateAllowance, materializedCandidateAllowance]
  | some candidate =>
      rcases candidate with ⟨coordinate, digest⟩
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          by_cases hmissing : context.state.values (.chainStart lay tree leafIdx chainIdx) = none <;>
            simp [unresolvedStartCandidateAllowance, privateMissingCandidateAllowance,
              privateMissingProbeInputAllowance, privateProbeInputAllowance, materializedCandidateAllowance, hmissing]
      | position position =>
          have hposition := hcoverage position digest rfl
          have hsum : (∑ target ∈ targets, privateMissingCandidateAllowance target table context
              (some ⟨.position position, digest⟩)) =
              if context.state.values (.position position) = none then
                candidateFailureAllowance table context (some ⟨.position position, digest⟩) else 0 := by
            rw [Finset.sum_eq_single position]
            · simp [privateMissingCandidateAllowance, privateMissingProbeInputAllowance, privateProbeInputAllowance]
            · intro target _ hne
              simp [privateMissingCandidateAllowance, privateMissingProbeInputAllowance, privateProbeInputAllowance, Ne.symm hne]
            · simp [hposition]
          rw [hsum]
          by_cases hmissing : context.state.values (.position position) = none <;>
            simp [unresolvedStartCandidateAllowance, materializedCandidateAllowance, hmissing]

theorem candidateFailureAllowance_le_one
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext) (candidate : Option Probe) :
    candidateFailureAllowance table context candidate ≤ 1 := by
  cases candidate with
  | none => simp [candidateFailureAllowance]
  | some candidate =>
      simp only [candidateFailureAllowance]
      split_ifs
      · exact bot_le
      · split
        · norm_num [digestBits]
        · split_ifs <;> simp

theorem materializedCandidateAllowance_le_one
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext) (candidate : Option Probe) :
    materializedCandidateAllowance table context candidate ≤ 1 := by
  cases candidate with
  | none => simp [materializedCandidateAllowance]
  | some candidate =>
      simp only [materializedCandidateAllowance]
      split_ifs
      · exact bot_le
      · exact candidateFailureAllowance_le_one table context _

theorem materializedCandidateAllowance_plan_eq_zero_of_chainsPublished
    (parameter : PublicParameter) (input : HashInput) (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (hpublic : MaterializedChainsPublished context) :
    materializedCandidateAllowance table context
      (purePlanProbingHashQuery parameter input context.state).candidate? = 0 := by
  cases hplan : (purePlanProbingHashQuery parameter input context.state).candidate? with
  | none => rfl
  | some candidate =>
      simp only [materializedCandidateAllowance]
      split_ifs with hmissing
      · rfl
      · exact hpublic.candidate_allowance_eq_zero_of_known parameter input candidate table hplan hmissing

end SphincsSecurity.Concrete.OtsProbeSimulation
