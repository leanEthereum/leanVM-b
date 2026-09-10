import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FewTimeViewTrace
import SphincsSecurity.Proof.OneTimeEvents

/-!
# Terminal events on the observational game

The final probability bounds use the game that retains the actual forgery, signing transcript and
cache intervals. This prevents an existential terminal witness from choosing a transcript unrelated
to the supported execution.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

theorem FullAdversaryTrace.CacheChain.start_le_finish
    {secretKey : SecretKey} {start finish : QueryCache HashSpec}
    {intervals : List AdversaryCacheEntry}
    (hchain : FullAdversaryTrace.CacheChain start intervals finish)
    (hvalid : ∀ entry ∈ intervals,
      (entry.output, entry.finalCache) ∈ support
        ((unloggedMappedAdversaryImpl secretKey entry.input).run entry.initialCache)) :
    start ≤ finish := by
  induction intervals generalizing start finish with
  | nil =>
      change finish = start at hchain
      exact le_of_eq hchain.symm
  | cons head rest ih =>
      obtain ⟨hstart, hrest⟩ := hchain
      have hhead : head.initialCache ≤ head.finalCache :=
        unloggedMappedAdversaryImpl_cache_le secretKey head.input head.initialCache
          (head.output, head.finalCache) (hvalid head (by simp))
      rw [← hstart]
      exact hhead.trans (ih hrest fun entry hentry => hvalid entry (by simp [hentry]))

namespace Concrete

def ViewedTerminalWitnessFor (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (event : QueryImpl HashSpec Id → QueryCache HashSpec → SecretKey →
      QueryLog SigningSpec → Forgery → Index → (DigestTree → FtsLeaf) → Prop)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState) : Prop :=
  ∃ (f : QueryImpl HashSpec Id) (digest : MessageDigest),
    result.2.cache.AgreesWithFn f
      ∧ SigningTranscript.Valid result.2.trace.signing.toSigningLog
      ∧ ¬SigningTranscript.Contains result.2.trace.signing.toSigningLog result.1.2.1
      ∧ evalWithAnswerFn f
          (messageDigest parameter result.1.1 result.1.2.1.message
            result.1.2.1.signature.randomness) = digest
      ∧ Admissible digest
      ∧ event f result.2.cache ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
        result.2.trace.signing.toSigningLog result.1.2.1
          (digestIndex digest) (digestLeaves digest)

def ViewedWinningTerminalWitnessFor (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (event : QueryImpl HashSpec Id → QueryCache HashSpec → SecretKey →
      QueryLog SigningSpec → Forgery → Index → (DigestTree → FtsLeaf) → Prop)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState) : Prop :=
  ∃ (f : QueryImpl HashSpec Id) (digest : MessageDigest),
    result.2.cache.AgreesWithFn f
      ∧ SigningTranscript.Valid result.2.trace.signing.toSigningLog
      ∧ ¬SigningTranscript.Contains result.2.trace.signing.toSigningLog result.1.2.1
      ∧ evalWithAnswerFn f
          (messageDigest parameter result.1.1 result.1.2.1.message
            result.1.2.1.signature.randomness) = digest
      ∧ Admissible digest
      ∧ evalWithAnswerFn f
          (verify ⟨result.1.1, parameter⟩ result.1.2.1.message result.1.2.1.signature) = true
      ∧ event f result.2.cache ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
        result.2.trace.signing.toSigningLog result.1.2.1
          (digestIndex digest) (digestLeaves digest)

def ViewedWinningFreshLayerOpeningWitness (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :=
  ViewedWinningTerminalWitnessFor parameter otsSecret ftsSecret
    fun f cache secretKey signingLog forgery index leaves =>
      SettledForgedFreshLayerOpening f cache secretKey signingLog index leaves forgery.signature

def ViewedEncodingCollisionWitness (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :=
  ViewedTerminalWitnessFor parameter otsSecret ftsSecret
    fun f cache secretKey signingLog _ _ _ =>
      EncodingCollision f cache secretKey signingLog

def ViewedWinningBackwardChainOpeningWitness (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :=
  ViewedWinningTerminalWitnessFor parameter otsSecret ftsSecret
    fun f cache secretKey signingLog forgery index leaves =>
      SettledForgedBackwardChainOpening f cache secretKey signingLog index leaves
        forgery.signature

def ViewedMessageDigestCollisionWitness (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :=
  ViewedTerminalWitnessFor parameter otsSecret ftsSecret
    fun f cache secretKey signingLog forgery index leaves =>
      MessageDigestCollision f cache secretKey signingLog forgery ∧
        FewTimeLeak f cache secretKey signingLog index leaves

def ViewedUncoveredFtsSecretWitness (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :=
  ViewedTerminalWitnessFor parameter otsSecret ftsSecret
    fun f cache secretKey signingLog forgery index leaves =>
      UncoveredFtsSecret f cache secretKey signingLog index leaves forgery.signature.ftsSecret

theorem gameAfterSecretsWithViewTrace_verdictCache_projection (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    (fun result => (result.1.2.2, result.2.cache)) <$>
        gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret =
      (simulateQ romImpl (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run ∅ := by
  calc
    _ = (fun result : (Digest × Forgery × Bool) ×
          (QueryCache HashSpec × FullAdversaryTrace) => (result.1.2.2, result.2.1)) <$>
        ((fun result => (result.1, result.2.base)) <$>
          gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret) := by
      simp only [Functor.map_map, ViewedFullTraceState.base]
    _ = (fun result : (Digest × Forgery × Bool) ×
          (QueryCache HashSpec × FullAdversaryTrace) => (result.1.2.2, result.2.1)) <$>
        gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret := by
      rw [gameAfterSecretsWithViewTrace_projection]
    _ = _ := gameAfterSecretsWithFullTrace_projection adversary parameter otsSecret ftsSecret

end Concrete

end SphincsSecurity
