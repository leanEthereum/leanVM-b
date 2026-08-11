import XmssSecurity.SignCacheHitProbability
import XmssSecurity.SigningLogReplay

open OracleComp OracleSpec

namespace XmssSecurity

structure SigningCacheEntry where
  request : SignRequest
  signature : Option Signature
  initialCache : QueryCache HashSpec
  finalCache : QueryCache HashSpec

abbrev SigningCacheTrace := List SigningCacheEntry

def SigningCacheTrace.toSigningLog (trace : SigningCacheTrace) : QueryLog SigningSpec :=
  trace.map fun entry => ⟨entry.request, entry.signature⟩

noncomputable def unloggedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec) ProbComp) := by
  classical
  intro input
  cases input with
  | inl worldInput =>
      exact xmssRomImpl worldInput
  | inr request =>
      exact simulateQ xmssRomImpl
        (Concrete.scheme.sign publicKey secretKey request.epoch request.message)

theorem unloggedMappedAdversaryImpl_apply_inl
    (publicKey : PublicKey) (secretKey : SecretKey)
    (worldInput : OracleWorld.Domain) :
    unloggedMappedAdversaryImpl publicKey secretKey (.inl worldInput) =
      xmssRomImpl worldInput := by
  rfl

theorem unloggedMappedAdversaryImpl_apply_inr
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) :
    unloggedMappedAdversaryImpl publicKey secretKey (.inr request) =
      (simulateQ xmssRomImpl
        (Concrete.scheme.sign publicKey secretKey request.epoch request.message) :
          StateT (QueryCache HashSpec) ProbComp (Option Signature)) := by
  rfl

def signingCacheTraceUpdate
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalCache : QueryCache HashSpec)
    (trace : SigningCacheTrace) : SigningCacheTrace :=
  match input with
  | .inl _ => trace
  | .inr request =>
      trace ++ [SigningCacheEntry.mk request output initialCache finalCache]

noncomputable def cacheTracedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec × SigningCacheTrace) ProbComp) :=
  QueryImpl.extendState (unloggedMappedAdversaryImpl publicKey secretKey)
    signingCacheTraceUpdate

theorem cacheTracedMappedAdversaryImpl_cache_projection
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace) :
    Prod.map id Prod.fst <$>
        (simulateQ (cacheTracedMappedAdversaryImpl publicKey secretKey)
          computation).run (initialCache, initialTrace) =
      (simulateQ (unloggedMappedAdversaryImpl publicKey secretKey)
        computation).run initialCache := by
  exact OracleComp.extendState_run_proj_eq
    (unloggedMappedAdversaryImpl publicKey secretKey) signingCacheTraceUpdate
    computation initialCache initialTrace

theorem signingCacheTrace_unchanged_map_eq
    (computation : ProbComp (α × QueryCache HashSpec))
    (trace : SigningCacheTrace) :
    (fun result => ((result.1, result.2.2.toSigningLog), result.2.1)) <$>
        ((fun result => (result.1, (result.2, trace))) <$> computation) =
      (fun result =>
        ((result.1.1, trace.toSigningLog ++ result.1.2), result.2)) <$>
        ((fun result => ((result.1, ([] : QueryLog SigningSpec)), result.2)) <$>
          computation) := by
  simp only [Functor.map_map]
  apply congrArg (fun transform => transform <$> computation)
  funext result
  simp

theorem signingCacheTrace_append_map_eq
    (computation : ProbComp (Option Signature × QueryCache HashSpec))
    (trace : SigningCacheTrace) (request : SignRequest)
    (initialCache : QueryCache HashSpec) :
    (fun result => ((result.1, result.2.2.toSigningLog), result.2.1)) <$>
        ((fun result =>
          (result.1, (result.2,
            trace ++ [SigningCacheEntry.mk request result.1 initialCache result.2]))) <$>
          computation) =
      (fun result =>
        ((result.1.1, trace.toSigningLog ++ result.1.2), result.2)) <$>
        ((fun result =>
          ((result.1, [⟨request, result.1⟩]), result.2)) <$> computation) := by
  simp only [Functor.map_map]
  apply congrArg (fun transform => transform <$> computation)
  funext result
  simp [SigningCacheTrace.toSigningLog]

end XmssSecurity
