import XmssSecurity.CappedGlobalChainHighPublicProgram
import XmssSecurity.FirstLaneOracleSimulation

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

abbrev GlobalFirstLaneWorld :=
  FirstLaneOracleSimulation.World GlobalChainValueIndex

def globalFirstLaneRevealProbeImpl :
    QueryImpl (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (OracleComp GlobalFirstLaneWorld) := fun input =>
  match input with
  | .uniform n => FirstLaneOracleSimulation.uniformQuery n
  | .probe index target => FirstLaneOracleSimulation.probeQuery index target
  | .reveal index => FirstLaneOracleSimulation.revealQuery index

def globalFirstLaneLiftRevealProbe
    (computation : OracleComp
      (RevealProbeOracleSimulation.World GlobalChainValueIndex) α) :
    OracleComp GlobalFirstLaneWorld α :=
  simulateQ globalFirstLaneRevealProbeImpl computation

noncomputable def globalFirstLaneFreshEncodingQuery
    (kind : EncodingSampleKind) (epoch : Epoch) (input : HashInput)
    (state : GlobalCausalHashState) :
    OracleComp GlobalFirstLaneWorld (HashOutput × GlobalCausalHashState) := do
  let output ← match kind with
    | .query => FirstLaneOracleSimulation.encodingQuery epoch
    | .sign => FirstLaneOracleSimulation.encodingSignAttemptQuery epoch
    | .side => FirstLaneOracleSimulation.liftProbComp uniformHashOutput
  pure (output, state.setCache (state.cache.cacheQuery input output))

noncomputable def globalFirstLaneAttackerHashQueryFromHighRun
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput) :
    GlobalCausalHashState →
      OracleComp GlobalFirstLaneWorld (HashOutput × GlobalCausalHashState) :=
  fun state =>
  match encodingInputEpoch? secretKey.parameter input with
  | some epoch =>
      let recorded := globalCausalRecordedState secretKey input state
      match state.cache input with
      | some output => pure (output, recorded)
      | none => globalFirstLaneFreshEncodingQuery .query epoch input recorded
  | none =>
      globalFirstLaneLiftRevealProbe
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run state)

noncomputable def globalFirstLaneAttackerHashQueryFromHigh
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput) :
    StateT GlobalCausalHashState (OracleComp GlobalFirstLaneWorld)
      HashOutput :=
  globalFirstLaneAttackerHashQueryFromHighRun high secretKey input

noncomputable def globalFirstLaneEncodingHashQuery
    (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (randomness : Randomness) (state : GlobalCausalHashState) :
    OracleComp GlobalFirstLaneWorld (HashOutput × GlobalCausalHashState) :=
  let input := Concrete.CacheView.encodingInput secretKey.parameter epoch
    (message, randomness)
  match state.cache input with
  | some output => pure (output, state)
  | none => globalFirstLaneFreshEncodingQuery .sign epoch input state

noncomputable def globalFirstLaneSigningAttempt
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    OracleComp GlobalFirstLaneWorld
      (Option Signature × GlobalCausalHashState) := do
  let randomness ← FirstLaneOracleSimulation.liftProbComp
    Concrete.signingRandomness
  let encoded ← globalFirstLaneEncodingHashQuery keyView.secretKey
    request.epoch request.message randomness state
  match TargetSum.decodeDigest (truncateHash encoded.1) with
  | none => pure (none, encoded.2)
  | some encoding => do
      let result ← globalFirstLaneLiftRevealProbe
        ((revealGlobalSignatureChains request encoding allChains
          (Concrete.CacheReplay.signWithEncoding keyView.cache keyView.secretKey
            request.epoch randomness encoding)).run encoded.2)
      pure (some result.1, result.2)

noncomputable def globalFirstLaneSignBoundedAttempts : Nat →
    ProgrammedGlobalChainKeygenView → SignRequest → GlobalCausalHashState →
    OracleComp GlobalFirstLaneWorld
      (Option Signature × GlobalCausalHashState)
  | 0, _keyView, _request, state => pure (none, state)
  | attempts + 1, keyView, request, state => do
      let result ← globalFirstLaneSigningAttempt keyView request state
      match result.1 with
      | some signature => pure (some signature, result.2)
      | none =>
          globalFirstLaneSignBoundedAttempts attempts keyView request result.2

noncomputable def globalFirstLaneSigningQuery
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    OracleComp GlobalFirstLaneWorld
      (Option Signature × GlobalCausalHashState) :=
  globalFirstLaneSignBoundedAttempts signingAttemptLimit keyView request state

def globalFirstLaneUniformImpl :
    QueryImpl unifSpec
      (StateT GlobalCausalHashState
        (OracleComp GlobalFirstLaneWorld)) := fun n state => do
  let output ← FirstLaneOracleSimulation.uniformQuery n
  pure (output, state)

noncomputable def globalFirstLaneHashImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl HashSpec
      (StateT GlobalCausalHashState
        (OracleComp GlobalFirstLaneWorld)) :=
  globalFirstLaneAttackerHashQueryFromHigh
    (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey

noncomputable def globalFirstLaneOracleImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl OracleWorld
      (StateT GlobalCausalHashState
        (OracleComp GlobalFirstLaneWorld)) :=
  globalFirstLaneUniformImpl + globalFirstLaneHashImpl keyView edgeHigh

noncomputable def globalFirstLaneSigningImpl
    (keyView : ProgrammedGlobalChainKeygenView) :
    QueryImpl SigningSpec
      (StateT GlobalCausalHashState
        (OracleComp GlobalFirstLaneWorld)) :=
  globalFirstLaneSigningQuery keyView

noncomputable def globalFirstLaneBaseMappedAdversaryImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalCausalHashState
        (OracleComp GlobalFirstLaneWorld)) :=
  globalFirstLaneOracleImpl keyView edgeHigh +
    globalFirstLaneSigningImpl keyView

noncomputable def globalFirstLaneVerifierImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl OracleWorld
      (StateT GlobalCausalHashState
        (OracleComp GlobalFirstLaneWorld)) :=
  globalFirstLaneOracleImpl keyView edgeHigh

noncomputable def globalFirstLaneDetailedExecution
    (adversary : Adversary Concrete.scheme)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    StateT GlobalCausalHashState (OracleComp GlobalFirstLaneWorld)
      (Forgery × Bool) := do
  let handled ← simulateQ
    (globalFirstLaneBaseMappedAdversaryImpl keyView edgeHigh)
      (adversary.main keyView.publicKey)
  let verified ← simulateQ (globalFirstLaneVerifierImpl keyView edgeHigh)
    (Concrete.scheme.verify keyView.publicKey handled.epoch
      handled.message handled.signature)
  pure (handled, verified)

abbrev GlobalFirstLaneResult :=
  GlobalHighDirectKeyResult × ((Forgery × Bool) × GlobalCausalHashState)

noncomputable def globalFirstLaneProgram
    (adversary : Adversary Concrete.scheme) :
    OracleComp GlobalFirstLaneWorld GlobalFirstLaneResult := do
  let keyResult ← FirstLaneOracleSimulation.liftProbComp
    globalHighDirectKeygen
  let execution ← (globalFirstLaneDetailedExecution adversary keyResult.1
    keyResult.2).run (globalFilteredCausalKeygenState keyResult.1)
  pure (keyResult, execution)

noncomputable def globalFirstLanePublicProgram
    (adversary : Adversary Concrete.scheme) :
    OracleComp GlobalFirstLaneWorld Unit := do
  let result ← globalFirstLaneProgram adversary
  globalFirstLaneLiftRevealProbe
    (RevealProbeOracleSimulation.emitObservedTrace
      (globalHighDirectForgeryPrimaryProbeTrace result))

end XmssSecurity.CappedChain
