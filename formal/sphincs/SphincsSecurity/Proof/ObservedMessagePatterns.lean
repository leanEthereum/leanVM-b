import SphincsSecurity.Proof.JointProbeMessageAnswers
import SphincsSecurity.Proof.MessageCollision

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
open FtsProbeSimulation (messageAnswers)

def ObservedMessageDigest (answers : HashInput → Option HashOutput) (root : Digest)
    (message : Message) (randomness : Randomness) (digest : MessageDigest) : Prop :=
  ∃ answer, answers (messageDigestPayload root message randomness) = some answer ∧ truncateMessageDigest answer = digest

def ObservedMessageCollision (answers : HashInput → Option HashOutput) (root : Digest)
    (log : QueryLog SigningSpec) (forgery : Forgery) : Prop :=
  ∃ (entry : SigningEntry) (signature : Signature) (digest : MessageDigest),
    entry ∈ log ∧ entry.2 = some signature ∧ Admissible digest ∧
      ObservedMessageDigest answers root entry.1 signature.randomness digest ∧
      ObservedMessageDigest answers root forgery.message forgery.signature.randomness digest ∧
      messageDigestPayload root entry.1 signature.randomness ≠ messageDigestPayload root forgery.message forgery.signature.randomness

def ObservedFewTimeCover (answers : HashInput → Option HashOutput) (root : Digest)
    (log : QueryLog SigningSpec) (forgery : Forgery) : Prop :=
  ∃ digest : MessageDigest,
    ObservedMessageDigest answers root forgery.message forgery.signature.randomness digest ∧ Admissible digest ∧
      ∀ tree : FtsTree, ∃ (entry : SigningEntry) (signature : Signature) (signedDigest : MessageDigest),
        entry ∈ log ∧ entry.2 = some signature ∧ Admissible signedDigest ∧
          ObservedMessageDigest answers root entry.1 signature.randomness signedDigest ∧
          messageDigestPayload root entry.1 signature.randomness ≠ messageDigestPayload root forgery.message forgery.signature.randomness ∧
          digestIndex signedDigest = digestIndex digest ∧
          digestLeaves signedDigest (ftsIndexOf tree) = digestLeaves digest (ftsIndexOf tree)

theorem CachedRun.observedMessageDigest {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {parameter : PublicParameter} {root : Digest} {message : Message} {randomness : Randomness}
    (hf : cache.AgreesWithFn f) (hrun : CachedRun cache f (messageDigest parameter root message randomness)) :
    ObservedMessageDigest (messageAnswers parameter cache) root message randomness
      (evalWithAnswerFn f (messageDigest parameter root message randomness)) := by
  obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp (CachedRun.messageDigest_cached hrun)
  refine ⟨answer, hanswer, ?_⟩
  change truncateMessageDigest answer = truncateMessageDigest (f (tweakableHashInput parameter .message
    (messageDigestPayload root message randomness)))
  rw [hf hanswer]

theorem messageDigestCollision_observed {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {key : SecretKey} {log : QueryLog SigningSpec} {forgery : Forgery}
    (hf : cache.AgreesWithFn f) (hcollision : MessageDigestCollision f cache key log forgery) :
    ObservedMessageCollision (messageAnswers key.parameter cache) key.root log forgery := by
  obtain ⟨entry, signature, hentry, hresponse, hsigned, htarget, hne, hequal⟩ := hcollision
  obtain ⟨_, _, _, hdigest, _, _, _, _, _, _, _⟩ := hsigned.indexed
  obtain ⟨_, digest, heval, hadmissible, _, _, hcached⟩ := hdigest.extract
  refine ⟨entry, signature, digest, hentry, hresponse, hadmissible, ?_, ?_, ?_⟩
  · simpa only [heval] using CachedRun.observedMessageDigest hf hcached
  · have htargetEval := hequal.symm.trans heval
    simpa only [htargetEval] using CachedRun.observedMessageDigest hf htarget
  · exact fun h => hne (congrArg (tweakableHashInput key.parameter .message) h)

theorem properFewTimeLeak_observed {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {key : SecretKey} {log : QueryLog SigningSpec} {forgery : Forgery} {digest : MessageDigest}
    (hf : cache.AgreesWithFn f)
    (htarget : CachedRun cache f (messageDigest key.parameter key.root forgery.message forgery.signature.randomness))
    (heval : evalWithAnswerFn f (messageDigest key.parameter key.root forgery.message forgery.signature.randomness) = digest)
    (hadmissible : Admissible digest)
    (hproper : ProperFewTimeLeak f cache key log (digestIndex digest) (digestLeaves digest)) :
    ObservedFewTimeCover (messageAnswers key.parameter cache) key.root log forgery := by
  refine ⟨digest, ?_, hadmissible, ?_⟩
  · simpa only [heval] using CachedRun.observedMessageDigest hf htarget
  · intro tree
    obtain ⟨entry, signature, leaves, hentry, hresponse, hsigned, hhonest, hleaf⟩ := hproper.1 tree
    obtain ⟨_, signedDigest, hsignedEval, hsignedAdmissible, hindex, hleaves, hcached⟩ := hhonest.1.extract
    refine ⟨entry, signature, signedDigest, hentry, hresponse, hsignedAdmissible, ?_, ?_, hindex.symm, ?_⟩
    · simpa only [hsignedEval] using CachedRun.observedMessageDigest hf hcached
    · intro hpayload
      obtain ⟨hmessage, hrandomness⟩ := messageDigestPayload_injective key.root hpayload
      have heval' : evalWithAnswerFn f (messageDigest key.parameter key.root entry.1 signature.randomness) = digest := by
        simpa only [hmessage, hrandomness] using heval
      exact hproper.2 entry signature hentry hresponse hsigned (hsigned.honest_fts_at_of_digest digest heval')
    · simpa only [hleaves] using hleaf

theorem observedMessageCollision_implies_cover {answers : HashInput → Option HashOutput} {root : Digest}
    {log : QueryLog SigningSpec} {forgery : Forgery}
    (hcollision : ObservedMessageCollision answers root log forgery) : ObservedFewTimeCover answers root log forgery := by
  obtain ⟨entry, signature, digest, hentry, hresponse, hadmissible, hsigned, htarget, hne⟩ := hcollision
  exact ⟨digest, htarget, hadmissible, fun _ => ⟨entry, signature, digest, hentry, hresponse, hadmissible, hsigned, hne, rfl, rfl⟩⟩

end SphincsSecurity.Concrete
