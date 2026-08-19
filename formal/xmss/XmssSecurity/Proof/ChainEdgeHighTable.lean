import XmssSecurity.Proof.ChainEdgeHighUniformity

open OracleComp OracleSpec

namespace XmssSecurity

noncomputable def chainEdgeHighTableOfCache
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (selected : ChainIndex) (table : ChainValueIndex → Digest) :
    ChainEdgeIndex → Digest := fun edge =>
  match cache (chainTableEdgeInput parameter selected table edge) with
  | none => 0
  | some output => (Rom.hashOutputEquivDigestPair output).1

end XmssSecurity
