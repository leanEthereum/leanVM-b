import SphincsSecurity.Proof.FewTime
import SphincsSecurity.Proof.Hypertree

/-!
# Correctness

`Ver` accepts a signature built from the secrets: the digest fixes an index, the few-time opening
recovers the few-time public key, the three layers chain it up to the root, and the root is the one
key generation published. Nothing here is probabilistic; it holds against every answer function, so
in particular against the random oracle on every path of its support.
-/

namespace SphincsSecurity.Concrete

open OracleComp

/-- **Correctness.** An honest signature verifies. -/
theorem eval_verify (f : QueryImpl HashSpec Id) (secretKey : SecretKey) (publicKey : PublicKey)
    (message : Message) (signature : Signature) (digest : MessageDigest)
    (codeword : Layer → Encoding)
    (hparameter : publicKey.parameter = secretKey.parameter)
    (hpkroot : publicKey.root = evalWithAnswerFn f (treeRoot secretKey.parameter topLayer rootTree
      (secretKey.otsSecret topLayer rootTree)))
    (hdigest : evalWithAnswerFn f (messageDigest publicKey.parameter publicKey.root message
      signature.randomness) = digest)
    (hadmissible : Admissible digest)
    (hftsSecret : signature.ftsSecret = fun tree =>
      secretKey.ftsSecret (digestIndex digest) tree (digestLeaves digest (ftsIndexOf tree)))
    (hftsPath : signature.ftsPath = evalWithAnswerFn f (ftsOpen secretKey.parameter
      (digestIndex digest) (digestLeaves digest) (secretKey.ftsSecret (digestIndex digest))))
    (hchain : ∀ lay : Layer, signature.chainValue lay
      = fun chainIdx => evalWithAnswerFn f (chainWalk secretKey.parameter lay
          (treeIndexAt (digestIndex digest) lay) (leafIndexAt (digestIndex digest) lay) chainIdx 0
          (codeword lay chainIdx).val (secretKey.otsSecret lay
            (treeIndexAt (digestIndex digest) lay) (leafIndexAt (digestIndex digest) lay) chainIdx)))
    (hpath : ∀ (lay : Layer) (level : Nat), level < layerHeight lay →
      signaturePath signature lay level = evalWithAnswerFn f (treeNode secretKey.parameter lay
        (treeIndexAt (digestIndex digest) lay)
        (secretKey.otsSecret lay (treeIndexAt (digestIndex digest) lay)) level
        (Nat.xor ((leafIndexAt (digestIndex digest) lay).val / 2 ^ level) 1)))
    (hencode : ∀ lay : Layer, evalWithAnswerFn f (encode secretKey.parameter lay
        (treeIndexAt (digestIndex digest) lay) (leafIndexAt (digestIndex digest) lay)
        (evalWithAnswerFn f (layerMessage secretKey (digestIndex digest) lay))
        (signature.counter lay)) = some (codeword lay)) :
    evalWithAnswerFn f (verify publicKey message signature) = true := by
  rw [verify_eq, evalWithAnswerFn_bind, hdigest, if_neg (by simpa using hadmissible),
    evalWithAnswerFn_bind, hparameter, hftsSecret, hftsPath,
    eval_ftsRecover f secretKey.parameter (digestIndex digest) (digestLeaves digest)
      (secretKey.ftsSecret (digestIndex digest)),
    evalWithAnswerFn_bind,
    eval_verifyLayers f secretKey (digestIndex digest) signature codeword hchain hpath hencode,
    evalWithAnswerFn_pure, hpkroot]
  simp

end SphincsSecurity.Concrete
