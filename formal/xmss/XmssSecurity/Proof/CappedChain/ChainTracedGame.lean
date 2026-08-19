import XmssSecurity.Proof.CappedChain.ChainInputTrace
import XmssSecurity.Proof.CappedChain.GameWithKeygenCache

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

def actionTraceOutcome
    (publicKey : PublicKey) (secretKey : SecretKey)
    (result : (Forgery × Bool) × AttackerActionTrace) : GameOutcome :=
  ⟨publicKey, secretKey, result.1.1, result.2.toSigningLog, result.1.2⟩

noncomputable def detailedGameAfterKeygenWithActionTrace
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    ProbComp ((GameOutcome × QueryCache HashSpec) × AttackerActionTrace) :=
  (fun result => ((actionTraceOutcome publicKey secretKey result.1, result.2), result.1.2)) <$>
    (simulateQ xmssRomImpl
      (sourceActionTracedDetailedGameAfterKeygen adversary publicKey secretKey)).run initialCache

theorem detailedGameAfterKeygenWithActionTrace_projection
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    Prod.fst <$> detailedGameAfterKeygenWithActionTrace adversary publicKey secretKey initialCache =
      (simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.scheme adversary publicKey secretKey)).run initialCache := by
  have hsource := sourceActionTracedDetailedGameAfterKeygen_log_projection adversary
    publicKey secretKey
  have hsimulated := congrArg
    (fun computation => (simulateQ xmssRomImpl computation).run initialCache) hsource
  simpa [detailedGameAfterKeygenWithActionTrace, actionTraceOutcome,
    simulateQ_map, StateT.run_map, Functor.map_map, Function.comp_def] using hsimulated

noncomputable def detailedGameWithKeygenCacheAndActionTrace
    (adversary : Adversary Concrete.scheme) :
    ProbComp ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace) := do
  let keyResult ← (simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅
  let execution ← detailedGameAfterKeygenWithActionTrace adversary keyResult.1.1
    keyResult.1.2 keyResult.2
  pure ((keyResult, execution.1), execution.2)

theorem detailedGameWithKeygenCacheAndActionTrace_projection
    (adversary : Adversary Concrete.scheme) :
    Prod.fst <$> detailedGameWithKeygenCacheAndActionTrace adversary =
      detailedGameWithKeygenCache adversary := by
  unfold detailedGameWithKeygenCacheAndActionTrace detailedGameWithKeygenCache
  simp only [map_bind]
  apply bind_congr
  intro keyResult
  rw [← detailedGameAfterKeygenWithActionTrace_projection adversary keyResult.1.1
    keyResult.1.2 keyResult.2]
  simp [Functor.map_map]

noncomputable def actionTracedForgeryEncoding
    (result : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace)) : Encoding :=
  (TargetSum.decodeDigest
    (Concrete.CacheView.encodingHash result.1.2.2 result.1.1.1.2.parameter
      result.1.2.1.forgery.epoch
      (result.1.2.1.forgery.message,
        result.1.2.1.forgery.signature.randomness))).getD
          (fun _ => ⟨0, by simp [chainLength]⟩)

end XmssSecurity.CappedChain
