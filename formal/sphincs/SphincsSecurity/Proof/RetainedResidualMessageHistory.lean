import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.RetainedResidualDigestLaw
import SphincsSecurity.Proof.RetainedResidualRows

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

theorem lazyByteRun_digest_after_history {History : Type}
    (history : OracleComp (World inputs) History) (initial : State inputs)
    (ha : ∀ coordinate, (initial.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project initial))
    (reached : Option History × State inputs)
    (hreached : lazyRun (environment parameter inputs hencoding words publicReplies selections rows) history initial reached ≠ 0)
    (key : SecretKey) (hparameter : key.parameter = parameter) (message : Message) (attempts : Nat)
    (hinputs : hashInputs (signDigestLoop attempts key message) ⊆ inputs) :
    cacheResult <$> lazyByteRun parameter inputs hencoding words publicReplies selections rows reached.2.memory.routing
      (boundaryComputation parameter (publicDigestLoop parameter key.root message attempts)) reached.2 =
      Prod.map some id <$> 𝒟[boundaryRun parameter (signDigestLoop attempts key message) reached.2.memory.external.cache] :=
  lazyByteRun_publicDigestBoundary_rom parameter inputs hencoding words publicReplies selections rows _ key hparameter message attempts
    hinputs reached.2 (lazyRun_rowsCovered parameter inputs hencoding words publicReplies selections rows history initial ha hcovered reached hreached)

end SphincsSecurity.Concrete.RetainedResidual
