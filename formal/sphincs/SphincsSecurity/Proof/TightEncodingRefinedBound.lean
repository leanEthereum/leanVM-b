import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Statement

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

def primitiveAccountingKey (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) : SecretKey :=
  ⟨parameter, default, otsSecret, ftsSecret⟩

end SphincsSecurity.Concrete
