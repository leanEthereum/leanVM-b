import XmssSecurity.Statement.CacheReplay
import VCVio.OracleComp.QueryTracking.LoggingOracle

open OracleComp OracleSpec

namespace XmssSecurity

def extendHashCacheWithLog (initialCache : QueryCache HashSpec) :
    QueryLog HashSpec → QueryCache HashSpec
  | [] => initialCache
  | ⟨input, output⟩ :: tail =>
      extendHashCacheWithLog (initialCache.cacheQuery input output) tail

def hashCacheOfLog (log : QueryLog HashSpec) : QueryCache HashSpec :=
  extendHashCacheWithLog ∅ log

namespace Concrete

def precomputedSecretKey (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (cache : QueryCache HashSpec) :
    SecretKey where
  parameter := parameter
  chainStart := secret
  chainValue := fun epoch chain digit =>
    Wots.walk (CacheView.chainStep cache parameter epoch chain) 0 digit.val
      (secret epoch chain)
  treeValue := fun height node =>
    CacheReplay.treeNode cache parameter secret height.val node

noncomputable def precomputedKeygen :
    OracleComp OracleWorld (PublicKey × SecretKey) := do
  let parameter ← liftM samplePublicParameter
  let secret ← liftM sampleSecret
  let result ← liftM
    (treeNode parameter secret treeHeight rootNode :
      OracleComp HashSpec Digest).withQueryLog
  let cache := hashCacheOfLog result.2
  return (⟨result.1, parameter⟩, precomputedSecretKey parameter secret cache)

attribute [irreducible] precomputedKeygen

end Concrete

end XmssSecurity
