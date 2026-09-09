import SphincsSecurity.Proof.EncodingSelectionCache

namespace SphincsSecurity.Concrete

noncomputable def canonicalEncodingInputs (parameter : PublicParameter) : Finset HashInput :=
  Finset.univ.biUnion fun position : EncodingPosition =>
    (Finset.univ : Finset (Digest × Fin encodingAttemptLimit)).image fun pair =>
      encodingRetryInput parameter position pair.1 pair.2.val

end SphincsSecurity.Concrete
