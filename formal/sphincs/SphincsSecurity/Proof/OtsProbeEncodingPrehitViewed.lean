import SphincsSecurity.Proof.OtsProbeEncodingPrehit
import SphincsSecurity.Proof.EncodingPrehitViewedProjection

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

set_option maxRecDepth 100000 in
theorem EncodingLayerRootCandidateAt.ne_honestValue_of_prehitFree_viewed_continuation
    {accountingKey : SecretKey} (secretKey : SecretKey)
    {initialState finalState : ViewedFullTraceState}
    {previous : HashInput} {candidate : Probe} {target : Position}
    (hcandidate : EncodingLayerRootCandidateAt accountingKey.parameter previous candidate)
    (hposition : candidate.coordinate = .position target)
    (hcached : initialState.cache previous ≠ none)
    (hbefore : ¬ Settled accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret initialState.cache target)
    (hafter : Settled accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret finalState.cache target)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (value : α)
    (hrun : (value, (finalState, false)) ∈ support
      ((simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey) computation).run (initialState, false))) :
    candidate.candidate ≠ honestValue (fromCache finalState.cache)
      accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret target := by
  obtain ⟨log, hmonitor, _⟩ := encodingPrehitViewedAdversaryImpl_support_monitor accountingKey secretKey
    computation (initialState, false) (value, (finalState, false)) hrun
  exact hcandidate.ne_honestValue_of_prehitFree_continuation hposition hcached hbefore hafter
    ((simulateQ (forwardOracles + signingOracle scheme secretKey) computation).run) (value, log) hmonitor

set_option maxRecDepth 100000 in
theorem EncodingLayerRootCandidateAt.refinedReserve_of_prehitFree_viewed_matching_query
    {accountingKey : SecretKey} (secretKey : SecretKey)
    {initialState finalState : ViewedFullTraceState}
    {input : HashInput} {candidate : Probe} {target : Position}
    (hcandidate : EncodingLayerRootCandidateAt accountingKey.parameter input candidate)
    (hposition : candidate.coordinate = .position target)
    (hafter : Settled accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret finalState.cache target)
    (hmatch : candidate.candidate = honestValue (fromCache finalState.cache)
      accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret target)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α) (value : α)
    (hrun : (value, (finalState, false)) ∈ support
      ((simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey)
        ((OracleWorld + SigningSpec).query (.inl (.inr input)) >>= next)).run (initialState, false))) :
    (4 / 3 : ℝ≥0∞) ≤ otsOpeningRefinedQueryReserve accountingKey initialState.cache input := by
  obtain ⟨log, hmonitor, _⟩ := encodingPrehitViewedAdversaryImpl_support_monitor accountingKey secretKey
    ((OracleWorld + SigningSpec).query (.inl (.inr input)) >>= next) (initialState, false) (value, (finalState, false)) hrun
  have hcomputation :
      ((simulateQ (forwardOracles + signingOracle scheme secretKey)
        ((OracleWorld + SigningSpec).query (.inl (.inr input)) >>= next)).run) =
      ((liftM (OracleWorld.query (.inr input)) : OracleComp OracleWorld HashOutput) >>= fun answer =>
        (simulateQ (forwardOracles + signingOracle scheme secretKey) (next answer)).run) := by
    have hquery : (((forwardOracles + signingOracle scheme secretKey) (.inl (.inr input))).run) =
        (fun output => (output, ([] : QueryLog SigningSpec))) <$>
          (liftM (OracleWorld.query (.inr input)) : OracleComp OracleWorld HashOutput) := rfl
    rw [simulateQ_bind, WriterT.run_bind', simulateQ_spec_query, hquery]
    erw [bind_map_left]
    apply bind_congr
    intro answer
    change (fun result : α × QueryLog SigningSpec => (result.1, [] ++ result.2)) <$>
      (simulateQ (forwardOracles + signingOracle scheme secretKey) (next answer)).run = _
    simp
  rw [hcomputation] at hmonitor
  exact hcandidate.refinedReserve_of_prehitFree_matching_query hposition hafter hmatch
    (fun answer => (simulateQ (forwardOracles + signingOracle scheme secretKey) (next answer)).run) (value, log) hmonitor

end SphincsSecurity.Concrete.OtsProbeSimulation
