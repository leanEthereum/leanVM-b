import SphincsSecurity.Proof.OtsProbeEncodingDomain

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem resolvedCachePotentialBound_peekTableInput
    (potential : SplitHashCache → ENNReal) (parameter : PublicParameter) (coordinate : Coordinate) :
    ResolvedCachePotentialBound potential (peekTableInput parameter coordinate) := by
  intro context fuel table cache
  rw [runResolvedFromTable_peekTableInput_eq_pure]
  simp [resolvedCachePotential]

theorem resolvedCachePotentialBound_revealCoordinateOutput_encoding
    (inputs : Finset HashInput) (coordinate : Coordinate) :
    ResolvedCachePotentialBound (encodingCachePotential inputs) (revealCoordinateOutput coordinate) := by
  unfold revealCoordinateOutput
  apply (resolvedCachePotentialBound_lift _ _).bind
  intro output
  exact (resolvedCachePotentialBound_modify _ _
    (fun cache => (encodingCachePotential_update_hidden inputs cache coordinate output).le)).bind
    fun _ => ResolvedCachePotentialBound.pure _ _

theorem resolvedCachePotentialBound_resolveKnownInput_encoding
    (encodingParameter parameter : PublicParameter) (encodingPosition : EncodingPosition) (message : Digest)
    (coordinate : Coordinate) (input : HashInput) :
    ResolvedCachePotentialBound (encodingCachePotential (encodingRetryInputs encodingParameter encodingPosition message))
      (resolveKnownInput parameter coordinate input) := by
  by_cases hinput : input ∈ encodingRetryInputs encodingParameter encodingPosition message
  · intro context fuel table cache
    rw [runResolvedFromTable_resolveKnownInput_of_miss parameter coordinate input context fuel table cache
      (purePeekTableInput_ne_of_mem_encodingRetryInputs encodingParameter parameter encodingPosition message context.state coordinate input hinput)]
    exact resolvedCachePotentialBound_splitHashQuery_encoding _ (.ordinary input) context fuel table cache
  · unfold resolveKnownInput
    apply (resolvedCachePotentialBound_peekTableInput _ parameter coordinate).bind
    intro known
    cases known with
    | none => exact resolvedCachePotentialBound_splitHashQuery_encoding _ _
    | some known =>
        dsimp only
        split_ifs
        · apply (resolvedCachePotentialBound_revealCoordinateOutput_encoding _ coordinate).bind
          intro output
          apply (resolvedCachePotentialBound_lift _ (LazyRevealProbe.publishQuery coordinate)).bind
          intro _
          exact (resolvedCachePotentialBound_modify _ _
            (fun cache => (encodingCachePotential_update_ordinary _ cache input output hinput).le)).bind
            fun _ => ResolvedCachePotentialBound.pure _ _
        · exact resolvedCachePotentialBound_splitHashQuery_encoding _ _

theorem resolvedCachePotentialBound_executeCandidate
    (potential : SplitHashCache → ENNReal) (candidate : Option Probe) :
    ResolvedCachePotentialBound potential (executeCandidate? candidate) := by
  cases candidate with
  | none => exact ResolvedCachePotentialBound.pure _ _
  | some candidate => exact resolvedCachePotentialBound_lift _ _

theorem resolvedCachePotentialBound_afterPlan_encoding
    (encodingParameter parameter : PublicParameter) (encodingPosition : EncodingPosition) (message : Digest)
    (input : HashInput) (plan : PlannedHashQuery) :
    ResolvedCachePotentialBound (encodingCachePotential (encodingRetryInputs encodingParameter encodingPosition message))
      (probingHashQueryAfterPlan parameter input plan) := by
  unfold probingHashQueryAfterPlan executePlannedHashQuery
  apply (resolvedCachePotentialBound_executeCandidate _ plan.candidate?).bind
  intro _
  cases plan.action with
  | ordinary => exact resolvedCachePotentialBound_splitHashQuery_encoding _ _
  | resolve coordinate =>
      exact resolvedCachePotentialBound_resolveKnownInput_encoding
        encodingParameter parameter encodingPosition message coordinate input

theorem resolvedCachePotentialBound_probingHashQuery_encoding
    (encodingParameter parameter : PublicParameter) (encodingPosition : EncodingPosition) (message : Digest) (input : HashInput) :
    ResolvedCachePotentialBound (encodingCachePotential (encodingRetryInputs encodingParameter encodingPosition message))
      (probingHashQuery parameter input) := by
  intro context fuel table cache
  rw [runResolved_probingHashQuery_eq_afterPlan]
  exact resolvedCachePotentialBound_afterPlan_encoding encodingParameter parameter encodingPosition message input
    (purePlanProbingHashQuery parameter input context.state) context fuel table cache

end SphincsSecurity.Concrete.OtsProbeSimulation
