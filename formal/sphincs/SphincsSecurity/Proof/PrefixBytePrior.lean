import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.PrefixByteRun
import SphincsSecurity.Proof.ResidualBytePrior

namespace SphincsSecurity.Concrete.ResidualByteFrontend

open _root_.OracleComp OracleSpec CanonicalProbeRouting HiddenLabelObservation UniformTableCompletion ResidualTableCompletion
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs
set_option backward.isDefEq.respectTransparency false

theorem initialPrefixByteRun_erasure {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (exposedValues : InitialPublicLabels words) (high : CanonicalGraphHighHalves) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (computation : OracleComp OracleWorld Result) (hinputs : hashInputs computation ⊆ inputs) :
    let known := initialKnown words exposedValues
    let publicReplies := coordinateGraphLabels known high
    (complete (initialAllowed words exposedValues) >>= fun labels => completeRows (fun _ : inputs => none) >>= fun seed =>
      let graph := coordinateGraphLabels labels high
      let oracle := programmedHash parameter (coordinateOtsSecrets labels) (coordinateFtsSecrets labels) graph
        (finiteHashAnswer ∅ inputs (canonicalPrefixResidual parameter inputs hencoding graph selections rows seed))
      externalRun (fun input memory => pure (checkedResult (PublicEncodingMatch.Match parameter (canonicalGraphMessage graph) words selections) input
          (fixedStep parameter words (fun _ _ _ => False) known labels oracle input memory)))
        computation emptyMemory) =
      forget <$> AdaptiveResidualLabels.lazyRun
        (prefixEnvironment parameter inputs hencoding words (fun _ _ _ => False) known publicReplies selections rows)
        (simulateQ (checkedTranslate inputs
          (PublicEncodingMatch.Match parameter (knownEncodingMessage known) words selections)) computation) (initialByteState inputs words exposedValues) := by
  dsimp only
  calc
    _ = (complete (initialAllowed words exposedValues) >>= fun labels => completeRows (fun _ : inputs => none) >>= fun seed =>
      forget <$> prefixByteRun parameter inputs hencoding words (fun _ _ _ => False) (initialKnown words exposedValues)
        (coordinateGraphLabels (initialKnown words exposedValues) high) selections rows labels seed computation
        (initialByteState inputs words exposedValues)) := by
      apply RetainedObservation.bind_congr
      intro labels hlabels
      apply congrArg (completeRows (fun _ : inputs => none) >>= ·)
      funext seed
      have hagrees := initialKnown_agrees words exposedValues labels hlabels
      have hreplies := initialKnown_graphReplies words exposedValues labels hlabels high
      have h := prefixByteRun_eq_original parameter inputs hencoding words (fun _ _ _ => False)
        (initialKnown words exposedValues) (coordinateGraphLabels (initialKnown words exposedValues) high) selections rows
        (coordinateOtsSecrets labels) (coordinateFtsSecrets labels) (coordinateGraphLabels labels high)
        (by simpa only [coordinateGraphLabels_value] using hagrees) hreplies seed computation hinputs
        (initialByteState inputs words exposedValues)
        (rowsCovered_empty inputs emptyMemory (initialAllowed words exposedValues))
        (cacheMatches_empty _) (cacheClean_empty parameter words (fun _ _ _ => False) _)
      simpa only [coordinateGraphLabels_value, initialByteState] using h.symm
    _ = _ := by
      simp only [← map_bind, prefixByteRun, checkedByteRun]
      exact congrArg (forget <$> ·)
        (referenceJointPrior_erasure inputs
          (prefixEnvironment parameter inputs hencoding words (fun _ _ _ => False) (initialKnown words exposedValues)
            (coordinateGraphLabels (initialKnown words exposedValues) high) selections rows)
          words exposedValues emptyMemory (simulateQ (checkedTranslate inputs
          (PublicEncodingMatch.Match parameter (knownEncodingMessage (initialKnown words exposedValues)) words selections)) computation))

theorem initialPrefixByteRun_hashCalls_le {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (exposedValues : InitialPublicLabels words) (high : CanonicalGraphHighHalves) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (computation : OracleComp OracleWorld Result) (hinputs : hashInputs computation ⊆ inputs)
    (budget : Nat) (hbound : computation.IsQueryBoundP IsHashQuery budget)
    (result : Option Result × ExternalMemory)
    (hresult : (forget <$> AdaptiveResidualLabels.lazyRun
      (prefixEnvironment parameter inputs hencoding words (fun _ _ _ => False) (initialKnown words exposedValues)
        (coordinateGraphLabels (initialKnown words exposedValues) high) selections rows)
      (simulateQ (checkedTranslate inputs
          (PublicEncodingMatch.Match parameter (knownEncodingMessage (initialKnown words exposedValues)) words selections)) computation) (initialByteState inputs words exposedValues)) result ≠ 0) :
    result.2.hashCalls ≤ budget := by
  rw [← initialPrefixByteRun_erasure parameter inputs hencoding words exposedValues high selections rows computation hinputs] at hresult
  obtain ⟨labels, _, hresult⟩ := (RetainedObservation.bind_nonzero _ _ _).mp hresult
  obtain ⟨seed, _, hresult⟩ := (RetainedObservation.bind_nonzero _ _ _).mp hresult
  have h := checkedExternalRun_hashCalls_le parameter words (fun _ _ _ => False) (initialKnown words exposedValues)
    labels _ _ computation emptyMemory budget hbound result hresult
  simpa only [emptyMemory, Nat.zero_add] using h

theorem initialPrefixByteRun_posterior {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (exposedValues : InitialPublicLabels words) (high : CanonicalGraphHighHalves) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (computation : OracleComp OracleWorld Result) (hinputs : hashInputs computation ⊆ inputs) :
    let known := initialKnown words exposedValues
    let publicReplies := coordinateGraphLabels known high
    (complete (initialAllowed words exposedValues) >>= fun labels => completeRows (fun _ : inputs => none) >>= fun seed =>
      let graph := coordinateGraphLabels labels high
      let oracle := programmedHash parameter (coordinateOtsSecrets labels) (coordinateFtsSecrets labels) graph
        (finiteHashAnswer ∅ inputs (canonicalPrefixResidual parameter inputs hencoding graph selections rows seed))
      retainTables labels seed <$> externalRun
        (fun input memory => pure (checkedResult (PublicEncodingMatch.Match parameter (canonicalGraphMessage graph) words selections) input
          (fixedStep parameter words (fun _ _ _ => False) known labels oracle input memory)))
        computation emptyMemory) =
      forget <$> (AdaptiveResidualLabels.lazyRun
        (prefixEnvironment parameter inputs hencoding words (fun _ _ _ => False) known publicReplies selections rows)
        (simulateQ (checkedTranslate inputs
          (PublicEncodingMatch.Match parameter (knownEncodingMessage known) words selections)) computation) (initialByteState inputs words exposedValues) >>= AdaptiveResidualLabels.finish) := by
  dsimp only
  calc
    _ = (complete (initialAllowed words exposedValues) >>= fun labels => completeRows (fun _ : inputs => none) >>= fun seed =>
      forget <$> (AdaptiveResidualLabels.retain labels seed <$>
        prefixByteRun parameter inputs hencoding words (fun _ _ _ => False) (initialKnown words exposedValues)
          (coordinateGraphLabels (initialKnown words exposedValues) high) selections rows labels seed computation
          (initialByteState inputs words exposedValues))) := by
      apply RetainedObservation.bind_congr
      intro labels hlabels
      apply congrArg (completeRows (fun _ : inputs => none) >>= ·)
      funext seed
      have hagrees := initialKnown_agrees words exposedValues labels hlabels
      have hreplies := initialKnown_graphReplies words exposedValues labels hlabels high
      have h := prefixByteRun_eq_original parameter inputs hencoding words (fun _ _ _ => False)
        (initialKnown words exposedValues) (coordinateGraphLabels (initialKnown words exposedValues) high) selections rows
        (coordinateOtsSecrets labels) (coordinateFtsSecrets labels) (coordinateGraphLabels labels high)
        (by simpa only [coordinateGraphLabels_value] using hagrees) hreplies seed computation hinputs
        (initialByteState inputs words exposedValues)
        (rowsCovered_empty inputs emptyMemory (initialAllowed words exposedValues))
        (cacheMatches_empty _) (cacheClean_empty parameter words (fun _ _ _ => False) _)
      simp only [coordinateGraphLabels_value, initialByteState] at h
      rw [← h]
      simp only [Functor.map_map, forget, retainTables, AdaptiveResidualLabels.retain, initialByteState]
    _ = _ := by
      simp only [← map_bind, prefixByteRun, checkedByteRun]
      exact congrArg (forget <$> ·)
        (referenceJointPrior_posterior inputs
          (prefixEnvironment parameter inputs hencoding words (fun _ _ _ => False) (initialKnown words exposedValues)
            (coordinateGraphLabels (initialKnown words exposedValues) high) selections rows)
          words exposedValues emptyMemory (simulateQ (checkedTranslate inputs
          (PublicEncodingMatch.Match parameter (knownEncodingMessage (initialKnown words exposedValues)) words selections)) computation))

end SphincsSecurity.Concrete.ResidualByteFrontend
