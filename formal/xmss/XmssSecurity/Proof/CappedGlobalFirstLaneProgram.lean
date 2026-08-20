import XmssSecurity.Proof.CappedGlobalChainHighPublicProgram
import XmssSecurity.Proof.FirstLaneOracleSimulation

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

@[irreducible]
noncomputable def globalFirstLaneAttackerHashQueryAtEpoch
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (epoch : Epoch) :
    OracleComp GlobalFirstLaneWorld (HashOutput × GlobalCausalHashState) :=
  let recorded := globalCausalRecordedState secretKey input state
  match state.cache input with
  | some output => pure (output, recorded)
  | none => globalFirstLaneFreshEncodingQuery .query epoch input recorded

@[irreducible]
noncomputable def globalFirstLaneAttackerHashQueryByEpoch
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) : Option Epoch →
      OracleComp GlobalFirstLaneWorld (HashOutput × GlobalCausalHashState)
  | some epoch => globalFirstLaneAttackerHashQueryAtEpoch secretKey input state epoch
  | none =>
      globalFirstLaneLiftRevealProbe
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run state)

@[irreducible]
noncomputable def globalFirstLaneAttackerHashQueryFromHighRun
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput) :
    GlobalCausalHashState →
      OracleComp GlobalFirstLaneWorld (HashOutput × GlobalCausalHashState) :=
  fun state => globalFirstLaneAttackerHashQueryByEpoch high secretKey input state
    (encodingInputEpoch? secretKey.parameter input)

theorem globalFirstLaneAttackerHashQueryFromHighRun_eq_some
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (epoch : Epoch)
    (hepoch : encodingInputEpoch? secretKey.parameter input = some epoch) :
    globalFirstLaneAttackerHashQueryFromHighRun high secretKey input state =
      globalFirstLaneAttackerHashQueryAtEpoch secretKey input state epoch := by
  unfold globalFirstLaneAttackerHashQueryFromHighRun
  rw [hepoch]
  unfold globalFirstLaneAttackerHashQueryByEpoch
  rfl

theorem globalFirstLaneAttackerHashQueryFromHighRun_eq_none
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (hepoch : encodingInputEpoch? secretKey.parameter input = none) :
    globalFirstLaneAttackerHashQueryFromHighRun high secretKey input state =
      globalFirstLaneLiftRevealProbe
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run state) := by
  unfold globalFirstLaneAttackerHashQueryFromHighRun
  rw [hepoch]
  unfold globalFirstLaneAttackerHashQueryByEpoch
  rfl

theorem globalFirstLaneAttackerHashQueryAtEpoch_eq_cached
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (epoch : Epoch) (output : HashOutput)
    (hcache : state.cache input = some output) :
    globalFirstLaneAttackerHashQueryAtEpoch secretKey input state epoch =
      pure (output, globalCausalRecordedState secretKey input state) := by
  unfold globalFirstLaneAttackerHashQueryAtEpoch
  rw [hcache]

theorem globalFirstLaneAttackerHashQueryAtEpoch_eq_fresh
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (epoch : Epoch)
    (hcache : state.cache input = none) :
    globalFirstLaneAttackerHashQueryAtEpoch secretKey input state epoch =
      globalFirstLaneFreshEncodingQuery .query epoch input
        (globalCausalRecordedState secretKey input state) := by
  unfold globalFirstLaneAttackerHashQueryAtEpoch
  rw [hcache]

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

noncomputable abbrev globalFirstLaneHashFromHighImpl
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) :
    QueryImpl HashSpec
      (StateT GlobalCausalHashState
        (OracleComp GlobalFirstLaneWorld)) :=
  fun input state =>
    globalFirstLaneAttackerHashQueryFromHighRun high secretKey input state

noncomputable abbrev globalFirstLaneHashImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl HashSpec
      (StateT GlobalCausalHashState
        (OracleComp GlobalFirstLaneWorld)) :=
  globalFirstLaneHashFromHighImpl
    (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey

noncomputable def globalFirstLaneOracleExecution
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : OracleWorld.Domain) (state : GlobalCausalHashState) :
    OracleComp GlobalFirstLaneWorld
      (OracleWorld.Range input × GlobalCausalHashState) :=
  match input with
  | .inl n => (globalFirstLaneUniformImpl n).run state
  | .inr hashInput =>
      globalFirstLaneAttackerHashQueryFromHighRun
        (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey hashInput
          state

noncomputable def globalFirstLaneOracleImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl OracleWorld
      (StateT GlobalCausalHashState
        (OracleComp GlobalFirstLaneWorld)) :=
  fun input state => globalFirstLaneOracleExecution keyView edgeHigh input state

noncomputable def globalFirstLaneSigningImpl
    (keyView : ProgrammedGlobalChainKeygenView) :
    QueryImpl SigningSpec
      (StateT GlobalCausalHashState
        (OracleComp GlobalFirstLaneWorld)) :=
  globalFirstLaneSigningQuery keyView

noncomputable def globalFirstLaneVerifierImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl OracleWorld
      (StateT GlobalCausalHashState
        (OracleComp GlobalFirstLaneWorld)) :=
  globalFirstLaneOracleImpl keyView edgeHigh

end XmssSecurity.CappedChain
