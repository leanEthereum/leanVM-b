import XmssSecurity.CacheReplay
import VCVio.OracleComp.QueryTracking.LoggingOracle

open OracleComp OracleSpec

namespace XmssSecurity

def hashCacheOfLog : QueryLog HashSpec → QueryCache HashSpec
  | [] => ∅
  | ⟨input, output⟩ :: tail =>
      (hashCacheOfLog tail).cacheQuery input output

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

def erasePrecomputation (secretKey : SecretKey) : SecretKey :=
  SecretKey.withoutPrecomputation secretKey.parameter secretKey.chainStart

def erasePrecomputedKeyResult (result : PublicKey × SecretKey) :
    PublicKey × SecretKey :=
  (result.1, erasePrecomputation result.2)

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

theorem erasePrecomputedKeygen_eq_keygen :
    erasePrecomputedKeyResult <$> precomputedKeygen = keygen := by
  unfold precomputedKeygen keygen
  simp only [erasePrecomputedKeyResult, erasePrecomputation,
    precomputedSecretKey, map_bind, map_pure]
  apply bind_congr
  intro parameter
  apply bind_congr
  intro secret
  rw [bind_pure_comp, bind_pure_comp]
  rw [← liftM_map, ← liftM_map]
  apply congrArg (fun computation : OracleComp HashSpec (PublicKey × SecretKey) =>
    (liftM computation : OracleComp OracleWorld (PublicKey × SecretKey)))
  calc
    (fun result : Digest × QueryLog HashSpec =>
        (PublicKey.mk result.1 parameter,
          SecretKey.withoutPrecomputation parameter secret)) <$>
        (treeNode parameter secret treeHeight rootNode :
          OracleComp HashSpec Digest).withQueryLog =
      (fun root : Digest =>
        (PublicKey.mk root parameter,
          SecretKey.withoutPrecomputation parameter secret)) <$>
        (Prod.fst <$> (treeNode parameter secret treeHeight rootNode :
          OracleComp HashSpec Digest).withQueryLog) := by
            rw [Functor.map_map]
    _ = _ := congrArg
      (fun computation : OracleComp HashSpec Digest =>
        (fun root : Digest =>
          (PublicKey.mk root parameter,
            SecretKey.withoutPrecomputation parameter secret)) <$> computation)
      (loggingOracle.fst_map_run_simulateQ
        (treeNode parameter secret treeHeight rootNode :
          OracleComp HashSpec Digest))

end Concrete

end XmssSecurity
