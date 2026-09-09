import SphincsSecurity.Proof.ResidualByteRun
import SphincsSecurity.Proof.ReferenceJointPrior

namespace SphincsSecurity.Concrete.ResidualByteFrontend

open _root_.OracleComp OracleSpec CanonicalProbeRouting HiddenLabelObservation UniformTableCompletion ResidualTableCompletion
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs
set_option backward.isDefEq.respectTransparency false

def emptyMemory : ExternalMemory := ⟨fun _ => none, 0, 0⟩

noncomputable def initialByteState (inputs : Finset HashInput) (words : OtsReferenceWords)
    (exposedValues : InitialPublicLabels words) : State inputs :=
  ⟨initialAllowed words exposedValues, fun _ => none, emptyMemory⟩

theorem initialByteRun_erasure {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (exposedValues : InitialPublicLabels words) (high : CanonicalGraphHighHalves) (rows : CanonicalEncodingRows)
    (computation : OracleComp OracleWorld Result) (hinputs : hashInputs computation ⊆ inputs) :
    let known := initialKnown words exposedValues
    let publicReplies := coordinateGraphLabels known high
    (complete (initialAllowed words exposedValues) >>= fun labels => completeRows (fun _ : inputs => none) >>= fun seed =>
      let graph := coordinateGraphLabels labels high
      let oracle := programmedHash parameter (coordinateOtsSecrets labels) (coordinateFtsSecrets labels) graph
        (finiteHashAnswer ∅ inputs (canonicalReferenceResidual parameter inputs hencoding graph rows seed))
      externalRun (fun input memory => pure (fixedStep parameter words (fun _ _ _ => False) known labels oracle input memory))
        computation emptyMemory) =
      forget <$> AdaptiveResidualLabels.lazyRun
        (environment parameter inputs hencoding words (fun _ _ _ => False) known publicReplies rows)
        (simulateQ (translate inputs) computation) (initialByteState inputs words exposedValues) := by
  dsimp only
  calc
    _ = (complete (initialAllowed words exposedValues) >>= fun labels => completeRows (fun _ : inputs => none) >>= fun seed =>
      forget <$> byteRun parameter inputs hencoding words (fun _ _ _ => False) (initialKnown words exposedValues)
        (coordinateGraphLabels (initialKnown words exposedValues) high) rows labels seed computation
        (initialByteState inputs words exposedValues)) := by
      apply RetainedObservation.bind_congr
      intro labels hlabels
      apply congrArg (completeRows (fun _ : inputs => none) >>= ·)
      funext seed
      have hagrees := initialKnown_agrees words exposedValues labels hlabels
      have hreplies := initialKnown_graphReplies words exposedValues labels hlabels high
      have h := byteRun_eq_original parameter inputs hencoding words (fun _ _ _ => False)
        (initialKnown words exposedValues) (coordinateGraphLabels (initialKnown words exposedValues) high) rows
        (coordinateOtsSecrets labels) (coordinateFtsSecrets labels) (coordinateGraphLabels labels high)
        (by simpa only [coordinateGraphLabels_value] using hagrees) hreplies seed computation hinputs
        (initialByteState inputs words exposedValues)
        (rowsCovered_empty inputs emptyMemory (initialAllowed words exposedValues))
        (cacheMatches_empty _) (cacheClean_empty parameter words (fun _ _ _ => False) _)
      simpa only [coordinateGraphLabels_value, initialByteState] using h.symm
    _ = _ := by
      simp only [← map_bind, byteRun]
      exact congrArg (forget <$> ·)
        (referenceJointPrior_erasure inputs
          (environment parameter inputs hencoding words (fun _ _ _ => False) (initialKnown words exposedValues)
            (coordinateGraphLabels (initialKnown words exposedValues) high) rows)
          words exposedValues emptyMemory (simulateQ (translate inputs) computation))

theorem initialByteRun_hashCalls_le {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (exposedValues : InitialPublicLabels words) (high : CanonicalGraphHighHalves) (rows : CanonicalEncodingRows)
    (computation : OracleComp OracleWorld Result) (hinputs : hashInputs computation ⊆ inputs)
    (budget : Nat) (hbound : computation.IsQueryBoundP IsHashQuery budget)
    (result : Option Result × ExternalMemory)
    (hresult : (forget <$> AdaptiveResidualLabels.lazyRun
      (environment parameter inputs hencoding words (fun _ _ _ => False) (initialKnown words exposedValues)
        (coordinateGraphLabels (initialKnown words exposedValues) high) rows)
      (simulateQ (translate inputs) computation) (initialByteState inputs words exposedValues)) result ≠ 0) :
    result.2.hashCalls ≤ budget := by
  rw [← initialByteRun_erasure parameter inputs hencoding words exposedValues high rows computation hinputs] at hresult
  obtain ⟨labels, _, hresult⟩ := (RetainedObservation.bind_nonzero _ _ _).mp hresult
  obtain ⟨seed, _, hresult⟩ := (RetainedObservation.bind_nonzero _ _ _).mp hresult
  have h := fixedExternalRun_hashCalls_le parameter words (fun _ _ _ => False) (initialKnown words exposedValues)
    labels _ computation emptyMemory budget hbound result hresult
  simpa only [emptyMemory, Nat.zero_add] using h

def retainTables {Result : Type} {inputs : Finset HashInput} (labels : Labels) (seed : inputs → HashOutput)
    (result : Option Result × ExternalMemory) : Option (Labels × (inputs → HashOutput) × Result) × ExternalMemory :=
  (result.1.map (fun value => (labels, seed, value)), result.2)

theorem initialByteRun_posterior {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (exposedValues : InitialPublicLabels words) (high : CanonicalGraphHighHalves) (rows : CanonicalEncodingRows)
    (computation : OracleComp OracleWorld Result) (hinputs : hashInputs computation ⊆ inputs) :
    let known := initialKnown words exposedValues
    let publicReplies := coordinateGraphLabels known high
    (complete (initialAllowed words exposedValues) >>= fun labels => completeRows (fun _ : inputs => none) >>= fun seed =>
      let graph := coordinateGraphLabels labels high
      let oracle := programmedHash parameter (coordinateOtsSecrets labels) (coordinateFtsSecrets labels) graph
        (finiteHashAnswer ∅ inputs (canonicalReferenceResidual parameter inputs hencoding graph rows seed))
      retainTables labels seed <$> externalRun
        (fun input memory => pure (fixedStep parameter words (fun _ _ _ => False) known labels oracle input memory))
        computation emptyMemory) =
      forget <$> (AdaptiveResidualLabels.lazyRun
        (environment parameter inputs hencoding words (fun _ _ _ => False) known publicReplies rows)
        (simulateQ (translate inputs) computation) (initialByteState inputs words exposedValues) >>= AdaptiveResidualLabels.finish) := by
  dsimp only
  calc
    _ = (complete (initialAllowed words exposedValues) >>= fun labels => completeRows (fun _ : inputs => none) >>= fun seed =>
      forget <$> (AdaptiveResidualLabels.retain labels seed <$>
        byteRun parameter inputs hencoding words (fun _ _ _ => False) (initialKnown words exposedValues)
          (coordinateGraphLabels (initialKnown words exposedValues) high) rows labels seed computation
          (initialByteState inputs words exposedValues))) := by
      apply RetainedObservation.bind_congr
      intro labels hlabels
      apply congrArg (completeRows (fun _ : inputs => none) >>= ·)
      funext seed
      have hagrees := initialKnown_agrees words exposedValues labels hlabels
      have hreplies := initialKnown_graphReplies words exposedValues labels hlabels high
      have h := byteRun_eq_original parameter inputs hencoding words (fun _ _ _ => False)
        (initialKnown words exposedValues) (coordinateGraphLabels (initialKnown words exposedValues) high) rows
        (coordinateOtsSecrets labels) (coordinateFtsSecrets labels) (coordinateGraphLabels labels high)
        (by simpa only [coordinateGraphLabels_value] using hagrees) hreplies seed computation hinputs
        (initialByteState inputs words exposedValues)
        (rowsCovered_empty inputs emptyMemory (initialAllowed words exposedValues))
        (cacheMatches_empty _) (cacheClean_empty parameter words (fun _ _ _ => False) _)
      simp only [coordinateGraphLabels_value, initialByteState] at h
      rw [← h]
      simp only [Functor.map_map, forget, retainTables, AdaptiveResidualLabels.retain, initialByteState]
    _ = _ := by
      simp only [← map_bind, byteRun]
      exact congrArg (forget <$> ·)
        (referenceJointPrior_posterior inputs
          (environment parameter inputs hencoding words (fun _ _ _ => False) (initialKnown words exposedValues)
            (coordinateGraphLabels (initialKnown words exposedValues) high) rows)
          words exposedValues emptyMemory (simulateQ (translate inputs) computation))

end SphincsSecurity.Concrete.ResidualByteFrontend
