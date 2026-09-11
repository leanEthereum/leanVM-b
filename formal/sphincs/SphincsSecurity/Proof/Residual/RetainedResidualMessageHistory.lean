import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualDigestLaw
import SphincsSecurity.Proof.Residual.RetainedResidualRows

namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
set_option backward.isDefEq.respectTransparency false

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem lazyRun_rowsCovered {Result : Type} (computation : OracleComp (World inputs) Result) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) (result : Option Result × State inputs)
    (hresult : lazyRun (environment parameter inputs hencoding words publicReplies selections rows) computation state result ≠ 0) :
    ResidualByteFrontend.RowsCovered inputs (project result.2) := by
  rw [← run_erasure _ _ state ha, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨actual, _, hresult⟩ := hresult
  rw [RetainedObservation.bind_nonzero] at hresult
  obtain ⟨seed, _, hresult⟩ := hresult
  exact observedRun_rowsCovered parameter inputs hencoding words publicReplies selections rows actual seed computation state hcovered result hresult

end SphincsSecurity.Concrete.RetainedResidual
