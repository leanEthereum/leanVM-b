import SphincsSecurity.Proof.OtsProbePrivateAllowanceReserve
import SphincsSecurity.Proof.OtsProbeSigningStartValues

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem purePlan_candidate_missing_or_chain
    (parameter : PublicParameter) (input : HashInput) (state : LazyRevealProbe.State Coordinate)
    (candidate : Probe)
    (hplan : (purePlanProbingHashQuery parameter input state).candidate? = some candidate) :
    state.values candidate.coordinate = none ∨ IsChainCoordinate candidate.coordinate := by
  have hchain : ∀ decoded, decodeProbe? parameter input = some decoded → IsChainCoordinate decoded.coordinate := by
    intro decoded hdecode
    exact Probe.isChainCoordinate_of_matchesInput ((decodeProbe?_eq_some_iff parameter input decoded).mp hdecode)
  unfold purePlanProbingHashQuery at hplan
  generalize decodeProbe? parameter input = decoded at hchain hplan
  generalize decodePosition? parameter input = position at hplan
  cases decoded with
  | some decoded =>
      have hdecoded := hchain decoded rfl
      cases position with
      | none => exact Or.inr ((Option.some.inj hplan) ▸ hdecoded)
      | some position =>
          cases position
          case leaf lay tree leafIdx =>
            exact Or.inl (leafInputProbePlan_some_value_none state input decoded candidate lay tree leafIdx hplan)
          all_goals exact Or.inr ((Option.some.inj hplan) ▸ hdecoded)
  | none =>
      cases position with
      | none => simp at hplan
      | some position =>
          cases position
          case node lay tree level nodeIdx =>
            exact Or.inl (firstMissingInputCoordinatePlan_some_value_none state input 0 _ candidate hplan)
          all_goals simp at hplan

theorem purePlan_materialized_candidate_is_chain
    (parameter : PublicParameter) (input : HashInput) (state : LazyRevealProbe.State Coordinate)
    (candidate : Probe)
    (hplan : (purePlanProbingHashQuery parameter input state).candidate? = some candidate)
    (hknown : state.values candidate.coordinate ≠ none) : IsChainCoordinate candidate.coordinate :=
  (purePlan_candidate_missing_or_chain parameter input state candidate hplan).resolve_left hknown

def MaterializedChainsPublished (context : DeferredContext) : Prop :=
  ∀ coordinate, IsChainCoordinate coordinate → context.state.values coordinate ≠ none → coordinate ∈ context.state.revealed

theorem MaterializedChainsPublished.starts
    {context : DeferredContext} (hpublic : MaterializedChainsPublished context) : MaterializedStartsPublished context := by
  intro start hknown
  exact hpublic start.coordinate (by cases start; trivial) hknown

theorem MaterializedChainsPublished.candidate_missing_of_hidden
    {context : DeferredContext} (hpublic : MaterializedChainsPublished context)
    (parameter : PublicParameter) (input : HashInput) (candidate : Probe)
    (hplan : (purePlanProbingHashQuery parameter input context.state).candidate? = some candidate)
    (hhidden : candidate.coordinate ∉ context.state.revealed) : context.state.values candidate.coordinate = none := by
  by_contra hknown
  exact hhidden (hpublic candidate.coordinate
    (purePlan_materialized_candidate_is_chain parameter input context.state candidate hplan hknown) hknown)

theorem MaterializedChainsPublished.candidate_allowance_eq_zero_of_known
    {context : DeferredContext} (hpublic : MaterializedChainsPublished context)
    (parameter : PublicParameter) (input : HashInput) (candidate : Probe) (table : OtsSecretIndex → HashOutput)
    (hplan : (purePlanProbingHashQuery parameter input context.state).candidate? = some candidate)
    (hknown : context.state.values candidate.coordinate ≠ none) :
    candidateFailureAllowance table context (some candidate) = 0 := by
  have hrevealed := hpublic candidate.coordinate
    (purePlan_materialized_candidate_is_chain parameter input context.state candidate hplan hknown) hknown
  simp [candidateFailureAllowance, hrevealed]

end SphincsSecurity.Concrete.OtsProbeSimulation
