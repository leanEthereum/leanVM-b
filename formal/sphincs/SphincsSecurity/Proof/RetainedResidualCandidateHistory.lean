import SphincsSecurity.Proof.RetainedResidualSigningCandidates

namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open ResidualByteFrontend (HiddenCandidateBound)
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

variable (key : SecretKey) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem lazyRun_request_hiddenCandidateBound (input : (OracleWorld + SigningSpec).Domain)
    (hinputs : requestInputs key input ⊆ inputs) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hbound : HiddenCandidateBound words state.memory.routing.disclosed (project state))
    (result : Option ((OracleWorld + SigningSpec).Range input) × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (adversaryImpl inputs key.parameter key.root words selections input) state result ≠ 0) :
    HiddenCandidateBound words result.2.memory.routing.disclosed (project result.2) := by
  cases input with
  | inl input =>
      change lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (externalProgram inputs key.parameter words selections (liftM (OracleWorld.query input))) state result ≠ 0 at hresult
      rw [lazyRun_externalProgram] at hresult
      have hafter := lazyByteRun_hiddenCandidateBound key.parameter inputs hencoding words publicReplies selections rows
        state.memory.routing _ hinputs state ha hbound result hresult
      have hrouting := lazyRun_embed_routing key.parameter inputs hencoding words publicReplies selections rows
        state.memory.routing _ state ha result hresult
      rw [hrouting]
      exact hafter
  | inr message =>
      exact lazyRun_signingProgram_hiddenCandidateBound inputs words publicReplies selections rows key hencoding message hinputs state
        ha hcovered hbound result hresult

theorem lazyRun_source_hiddenCandidateBound {Result : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (hinputs : sourceInputs key computation ⊆ inputs)
    (state : State inputs) (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hbound : HiddenCandidateBound words state.memory.routing.disclosed (project state))
    (result : Option Result × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (adversaryImpl inputs key.parameter key.root words selections) computation) state result ≠ 0) :
    HiddenCandidateBound words result.2.memory.routing.disclosed (project result.2) := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, lazyRun, runWith_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact hbound
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, lazyRun_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨middle, hmiddle, hresult⟩ := hresult
      have hafter := lazyRun_request_hiddenCandidateBound key inputs hencoding words publicReplies selections rows input
        ((requestInputs_subset key input next).trans hinputs) state ha hcovered hbound middle hmiddle
      have ha' := lazyRun_nonempty (environment key.parameter inputs hencoding words publicReplies selections rows) _ state ha middle hmiddle
      have hcovered' := lazyRun_rowsCovered key.parameter inputs hencoding words publicReplies selections rows _ state ha hcovered middle hmiddle
      rcases middle with ⟨answer, after⟩
      cases answer with
      | none =>
          simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact hafter
      | some answer =>
          exact ih answer ((sourceInputs_next_subset key input next answer).trans hinputs) after ha' hcovered' hafter result hresult

theorem lazyInitialSource_hiddenCandidateBound {Result : Type}
    (exposed : InitialPublicLabels words) (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (hinputs : sourceInputs key computation ⊆ inputs) (result : Option Result × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (adversaryImpl inputs key.parameter key.root words selections) computation)
      (initialState inputs words exposed) result ≠ 0) :
    HiddenCandidateBound words result.2.memory.routing.disclosed (project result.2) :=
  lazyRun_source_hiddenCandidateBound key inputs hencoding words publicReplies selections rows computation hinputs
    (initialState inputs words exposed) (initialAllowed_nonempty words exposed)
    (initialState_rowsCovered inputs words exposed) (initialState_hiddenCandidateBound inputs words exposed) result hresult

end SphincsSecurity.Concrete.RetainedResidual
