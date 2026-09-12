import SphincsSecurity.Proof.Forced.FtsGuessCachedMessage
import SphincsSecurity.Proof.Residual.RetainedResidualCoverageStep
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec CanonicalProbeRouting ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs publicDigestLoop signDigestLoop

theorem publicSigningWork_complete_digest (key : SecretKey) (known : Labels) (words : OtsReferenceWords)
    (selections : ReferenceFamily) (actual : Labels) (message : Message) (cache : QueryCache HashSpec) :
    (fun result => ((completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf)) result.1.1).1, result.2)) <$>
      𝒟[(simulateQ romImpl (ResidualByteFrontend.publicSigningWork key.parameter key.root known words selections message)).run cache] =
        RetainedResidual.digestCompletionValue known words selections actual <$>
          𝒟[(simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache] := by
  rw [RetainedResidual.publicSigningWork_eq_digestWork, simulateQ_map, StateT.run_map, evalDist_map,
    Functor.map_map, publicDigestLoop_eq, simulateQ_boundaryComputation]
  rw [← boundaryRun_forget key.parameter (signDigestLoop digestAttemptLimit key message) cache,
    evalDist_map, Functor.map_map]
  change (fun result => ((completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf))
    (RetainedResidual.digestWork known words selections result.1).1).1, result.2)) <$>
      𝒟[boundaryRun key.parameter (signDigestLoop digestAttemptLimit key message) cache] = _
  congr 1
  funext result
  rcases result with ⟨⟨selected, trace⟩, after⟩
  cases selected <;> rfl

end SphincsSecurity.Concrete.FtsGuessHash
