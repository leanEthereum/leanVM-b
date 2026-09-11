import SphincsSecurity.Proof.FtsGuessCachedMessage
import SphincsSecurity.Proof.RetainedResidualCoverageStep

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

theorem cached_reference_signing_digest (key : SecretKey)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (dummy : OtsReferenceWords) (actual : Labels)
    (message : Message) (cache : QueryCache HashSpec)
    (hinputs : hashInputs (publicDigestLoop key.parameter key.root message digestAttemptLimit) ⊆ inputs) :
    (fun result => ((completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf)) result.1).1, result.2)) <$>
      cachedSeedRun inputs (simulateQ (seedLift inputs)
        (referenceProgram key.parameter key.root otsSecret labels inputs hencoding selections rows dummy (.inr message))) cache =
        RetainedResidual.digestCompletionValue (known otsSecret labels) (referenceFamilyWords selections dummy) selections actual <$>
          𝒟[(simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache] := by
  rw [cached_reference_signing_record key.parameter key.root otsSecret labels inputs hencoding selections rows dummy message cache hinputs,
    simulateQ_map, StateT.run_map, evalDist_map, Functor.map_map]
  exact publicSigningWork_complete_digest key (known otsSecret labels) (referenceFamilyWords selections dummy) selections actual message cache

theorem expected_cached_reference_signing_bank_le (key : SecretKey)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (dummy : OtsReferenceWords) (actual : Labels)
    (message : Message) (reuse : ENNReal) (budget signatures : Nat) (required : Finset FtsTree)
    (cover : CoverLogState) (bank : HashInput → Bool)
    (hinputs : hashInputs (publicDigestLoop key.parameter key.root message digestAttemptLimit) ⊆ inputs)
    (hsigned : SigningDigestsCached key.parameter cover.1 key.root cover.2)
    (hreuse : exactDigestReuseWeight key message cover.1 ≤ reuse) :
    (∑' result, Pr[= result | cachedSeedRun inputs (simulateQ (seedLift inputs)
        (referenceProgram key.parameter key.root otsSecret labels inputs hencoding selections rows dummy (.inr message))) cover.1] *
      RetainedResidual.completedSigningBankValue key reuse budget signatures required cover.2 bank message
        ((completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf)) result.1).1, result.2)) ≤
      bankedTargetEnvelope key reuse budget (signatures + 1) required cover bank false +
        targetCreationMultiplier key cover.1 (.inr message) *
          targetCreationPrice key reuse budget (signatures + 1) required cover := by
  have h := congrArg (fun law => ∑' result, Pr[= result | law] *
    RetainedResidual.completedSigningBankValue key reuse budget signatures required cover.2 bank message result)
    (cached_reference_signing_digest key otsSecret labels inputs hencoding selections rows dummy actual message cover.1 hinputs)
  rw [tsum_probOutput_map_mul] at h
  rw [h]
  have hb := RetainedResidual.expected_digestCompletionValue_bank_le key reuse budget signatures required cover bank message
    (known otsSecret labels) (referenceFamilyWords selections dummy) selections actual hsigned hreuse
  simpa only [evalDist_map, probOutput_def, SPMF.evalDist_def] using hb

end SphincsSecurity.Concrete.FtsGuessHash
