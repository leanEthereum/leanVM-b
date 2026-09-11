import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FewTimeUniform

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def observedSigningView? (answers : HashInput → Option HashOutput) (root : Digest) (entry : SigningEntry) : Option FewTimeView := do
  let signature ← entry.2
  let answer ← answers (messageDigestPayload root entry.1 signature.randomness)
  pure (hashOutputFewTimeView answer)

end SphincsSecurity.Concrete
