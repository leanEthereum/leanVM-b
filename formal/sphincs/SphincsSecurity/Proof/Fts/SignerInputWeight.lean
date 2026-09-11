import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FewTimeUniform

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def successfulSignerInputWeight (key : SecretKey) (message : Message)
    (weight : HashInput → FewTimeView → ENNReal)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec) : ENNReal :=
  match result.1.1, result.1.2 with
  | some signature, some view => weight
      (tweakableHashInput key.parameter .message (messageDigestPayload key.root message signature.randomness)) view
  | _, _ => 0

noncomputable def cachedSignerInputWeight (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (weight : HashInput → FewTimeView → ENNReal) (input : HashInput) : ENNReal :=
  match before input with
  | none => 0
  | some output =>
      if (∃ randomness, input = tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) ∧
          Admissible (truncateMessageDigest output) then weight input (hashOutputFewTimeView output) else 0

end SphincsSecurity.Concrete
