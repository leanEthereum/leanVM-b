import SphincsSecurity.Proof.EncodingPrehitContinuation
import SphincsSecurity.Proof.OtsOpeningRefinedReserve

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

set_option maxRecDepth 100000 in
theorem EncodingLayerRootCandidateAt.prehit_of_newly_settled
    {secretKey : SecretKey} {cache : QueryCache HashSpec}
    {previous input : HashInput} {answer : HashOutput} {candidate : Probe} {target : Position}
    (hcandidate : EncodingLayerRootCandidateAt secretKey.parameter previous candidate)
    (hposition : candidate.coordinate = .position target)
    (hcached : cache previous ≠ none)
    (hbefore : ¬ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache target)
    (hafter : Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
      (cache.cacheQuery input answer) target)
    (hmatch : candidate.candidate = honestValue (fromCache (cache.cacheQuery input answer))
      secretKey.parameter secretKey.otsSecret secretKey.ftsSecret target) :
    EncodingMessagePrehit cache secretKey input answer := by
  obtain ⟨position, index, hat, htree, hleaf, _hnotBottom, rfl⟩ := hcandidate
  have heq : layerMessagePosition index position.lay = target := Coordinate.position.inj hposition
  subst target
  exact ⟨position, index, previous, htree, hleaf, hbefore, hafter, hat, hcached, hmatch⟩

set_option maxRecDepth 100000 in
theorem EncodingLayerRootCandidateAt.ne_honestValue_of_prehitFree_settlement
    {secretKey : SecretKey} {cache : QueryCache HashSpec}
    {previous input : HashInput} {answer : HashOutput} {candidate : Probe} {target : Position}
    (hcandidate : EncodingLayerRootCandidateAt secretKey.parameter previous candidate)
    (hposition : candidate.coordinate = .position target)
    (hcached : cache previous ≠ none) (hfresh : cache input = none)
    (hbefore : ¬ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache target)
    (hafter : Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
      (cache.cacheQuery input answer) target)
    (hstep : ((answer, cache.cacheQuery input answer), false) ∈ support
      (TightEncoding.runEncodingPrehitMonitor secretKey (OracleWorld.query (.inr input)) cache false)) :
    candidate.candidate ≠ honestValue (fromCache (cache.cacheQuery input answer))
      secretKey.parameter secretKey.otsSecret secretKey.ftsSecret target := by
  intro hmatch
  exact TightEncoding.not_encodingMessagePrehit_of_mem_support_query_false secretKey input answer
    cache (cache.cacheQuery input answer) false hfresh hstep
      (hcandidate.prehit_of_newly_settled hposition hcached hbefore hafter hmatch)

set_option maxRecDepth 100000 in
theorem EncodingLayerRootCandidateAt.ne_honestValue_of_prehitFree_continuation
    {secretKey : SecretKey} {initialCache finalCache : QueryCache HashSpec}
    {previous : HashInput} {candidate : Probe} {target : Position}
    (hcandidate : EncodingLayerRootCandidateAt secretKey.parameter previous candidate)
    (hposition : candidate.coordinate = .position target)
    (hcached : initialCache previous ≠ none)
    (hbefore : ¬ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret initialCache target)
    (hafter : Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret finalCache target)
    (computation : OracleComp OracleWorld α) (value : α)
    (hrun : ((value, finalCache), false) ∈ support
      (TightEncoding.runEncodingPrehitMonitor secretKey computation initialCache false)) :
    candidate.candidate ≠ honestValue (fromCache finalCache)
      secretKey.parameter secretKey.otsSecret secretKey.ftsSecret target := by
  obtain ⟨position, index, hat, htree, hleaf, _hnotBottom, rfl⟩ := hcandidate
  have heq : layerMessagePosition index position.lay = target := Coordinate.position.inj hposition
  subst target
  exact TightEncoding.encodingMessage_ne_honestValue_of_prehitFree_continuation
    secretKey position index previous htree hleaf hat computation initialCache value finalCache hcached hbefore hafter hrun

set_option maxRecDepth 100000 in
theorem EncodingLayerRootCandidateAt.refinedReserve_of_prehitFree_matching_query
    {secretKey : SecretKey} {initialCache finalCache : QueryCache HashSpec}
    {input : HashInput} {candidate : Probe} {target : Position}
    (hcandidate : EncodingLayerRootCandidateAt secretKey.parameter input candidate)
    (hposition : candidate.coordinate = .position target)
    (hafter : Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret finalCache target)
    (hmatch : candidate.candidate = honestValue (fromCache finalCache)
      secretKey.parameter secretKey.otsSecret secretKey.ftsSecret target)
    (next : HashOutput → OracleComp OracleWorld α) (value : α)
    (hrun : ((value, finalCache), false) ∈ support
      (TightEncoding.runEncodingPrehitMonitor secretKey (OracleWorld.query (.inr input) >>= next) initialCache false)) :
    (4 / 3 : ℝ≥0∞) ≤ otsOpeningRefinedQueryReserve secretKey initialCache input := by
  obtain ⟨position, index, hat, htree, hleaf, _hnotBottom, rfl⟩ := hcandidate
  have heq : layerMessagePosition index position.lay = target := Coordinate.position.inj hposition
  subst target
  exact otsOpeningRefinedQueryReserve_ge_four_thirds_of_encodingMessageSettled secretKey initialCache input position hat
    (TightEncoding.encodingMessageSettledAt_of_prehitFree_matching_query secretKey position index input
      htree hleaf hat next initialCache value finalCache hafter hmatch hrun)

end SphincsSecurity.Concrete.OtsProbeSimulation
