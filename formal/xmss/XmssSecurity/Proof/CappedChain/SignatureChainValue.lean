import XmssSecurity.Proof.PrecomputedKeygenCache
import XmssSecurity.Proof.ChainOraclePresampling
import XmssSecurity.Proof.CappedChain.ChainHiddenTable

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

def replaceSignatureChainValue
    (signature : Signature) (chain : ChainIndex) (value : Digest) : Signature :=
  { signature with
    chainValue := Function.update signature.chainValue chain value }

@[simp]
theorem replaceSignatureChainValue_same
    (signature : Signature) (chain : ChainIndex) (value : Digest) :
    (replaceSignatureChainValue signature chain value).chainValue chain = value := by
  simp [replaceSignatureChainValue]

theorem replaceSignatureChainValue_other
    (signature : Signature) (chain candidate : ChainIndex) (value : Digest)
    (hne : candidate ≠ chain) :
    (replaceSignatureChainValue signature chain value).chainValue candidate =
      signature.chainValue candidate := by
  simp [replaceSignatureChainValue, Function.update_of_ne hne]

theorem Concrete.CacheReplay.signWithEncoding_chainValue_eq_keygenChainValueTable
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (epoch : Epoch) (randomness : Randomness) (encoding : Encoding)
    (chain : ChainIndex) :
    (Concrete.CacheReplay.signWithEncoding largerCache keyResult.1.2
      epoch randomness encoding).chainValue chain =
      keygenChainValueTable keyResult.2 keyResult.1.2 chain
        (epoch, encoding chain) := by
  have hwalk := Concrete.keygen_chainWalk_eq_of_cache_le keyResult hkeygen
    largerCache hle epoch chain (encoding chain).val
    (Nat.le_pred_of_lt (encoding chain).isLt)
  simp only [Concrete.CacheReplay.signWithEncoding,
    Concrete.CacheReplay.signedChainValues, keygenChainValueTable]
  exact hwalk.symm

end XmssSecurity.CappedChain
