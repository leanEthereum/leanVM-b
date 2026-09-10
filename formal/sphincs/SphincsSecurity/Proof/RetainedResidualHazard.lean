import SphincsSecurity.Proof.ResidualByteCheckedHazard
import SphincsSecurity.Proof.RetainedResidualCandidateHistory
import SphincsSecurity.Proof.RetainedResidualOriginalBudget

namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing)
open ResidualByteFrontend (HiddenCandidateBound probeHazard)
open FtsProbeSimulation (unloggedRetainedRestComputation)
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem prob_hashQuery_primitiveStop_le (routing : Routing) (input : inputs) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hbound : HiddenCandidateBound words routing.disclosed (project state)) :
    Pr[fun result => result.1 = none |
      lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
        (simulateQ (embed inputs routing) (ResidualByteFrontend.hashQuery input)) state] ≤
      probeHazard state.memory.external.probes := by
  have h := ResidualByteFrontend.prob_prefixHashQuery_stop_le parameter inputs words routing.disclosed routing.known hencoding
    publicReplies selections rows input (project state) ha hcovered hbound
  rw [← lazyRun_embed_project parameter inputs hencoding words publicReplies selections rows routing _ state ha] at h
  simpa only [probEvent_map, Function.comp_def, projectResult, project] using h

theorem prob_checkedHashQuery_stop_le (routing : Routing) (input : inputs) (state : State inputs)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput (fun counter => rows (position, counter)) = selections position)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hbound : HiddenCandidateBound words routing.disclosed (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) state.memory.external.cache) :
    Pr[fun result => result.1 = none |
      lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
        (simulateQ (embed inputs routing)
          (ResidualByteFrontend.checkedHashQuery (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) input)) state] ≤
      probeHazard state.memory.external.probes := by
  have h := ResidualByteFrontend.prob_checkedPrefixHashQuery_stop_le parameter inputs words routing.disclosed routing.known hencoding
    publicReplies selections rows hselect input (project state) ha hcovered hbound hclean
  rw [← lazyRun_embed_project parameter inputs hencoding words publicReplies selections rows routing _ state ha] at h
  simpa only [probEvent_map, Function.comp_def, projectResult, project] using h

variable (key : SecretKey) (adversary : Adversary) (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
  (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
  (q : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule) (stopped : Bool)

omit parameter inputs hencoding words publicReplies selections rows in
theorem initialMonitoredSource_hiddenCandidateBound
    (result : Option (Forgery × Bool) × MonitoredState (gameInputs adversary))
    (hresult : initialMonitoredSource key adversary encoding dummy exposed high q required stopAfter stopped result ≠ 0) :
    MonitoredValid (gameInputs adversary) result.2 ∧
      HiddenCandidateBound (referenceFamilyWords encoding.selections dummy) result.2.1.memory.routing.disclosed (project result.2.1) := by
  unfold initialMonitoredSource at hresult
  have hnative := map_nonzero _ (fun result => (result.1, result.2.1)) result hresult
  rw [monitoredRun_erasure] at hnative
  have ha := initialAllowed_nonempty (referenceFamilyWords encoding.selections dummy) exposed
  have hc := initialState_rowsCovered (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact lazyRun_nonempty _ _ (initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed)
      ha (result.1, result.2.1) hnative
  · exact lazyRun_rowsCovered key.parameter (gameInputs adversary) _ (referenceFamilyWords encoding.selections dummy)
      (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high) encoding.selections encoding.rows
      _ _ ha hc (result.1, result.2.1) hnative
  · exact lazyInitialSource_hiddenCandidateBound key (gameInputs adversary) _ (referenceFamilyWords encoding.selections dummy)
      (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high) encoding.selections encoding.rows
      exposed (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩)
      (sourceInputs_unlogged_subset_gameInputs adversary key) (result.1, result.2.1) hnative

omit parameter inputs hencoding words publicReplies selections rows in
theorem prob_next_primitiveStop_after_initialMonitoredSource_le
    (result : Option (Forgery × Bool) × MonitoredState (gameInputs adversary))
    (hresult : initialMonitoredSource key adversary encoding dummy exposed high q required stopAfter stopped result ≠ 0)
    (input : gameInputs adversary) :
    Pr[fun next => next.1 = none |
      lazyRun
        (environment key.parameter (gameInputs adversary) (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
          (referenceFamilyWords encoding.selections dummy)
          (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
          encoding.selections encoding.rows)
        (simulateQ (embed (gameInputs adversary) result.2.1.memory.routing) (ResidualByteFrontend.hashQuery input)) result.2.1] ≤
      probeHazard result.2.1.memory.external.probes := by
  have h := initialMonitoredSource_hiddenCandidateBound key adversary encoding dummy exposed high q required stopAfter stopped result hresult
  exact prob_hashQuery_primitiveStop_le key.parameter (gameInputs adversary) _ (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high) encoding.selections encoding.rows
    result.2.1.memory.routing input result.2.1 h.1.1 h.1.2 h.2

end SphincsSecurity.Concrete.RetainedResidual
