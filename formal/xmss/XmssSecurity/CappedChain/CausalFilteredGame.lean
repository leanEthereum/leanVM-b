import XmssSecurity.CausalFilteredSuffix
import XmssSecurity.CappedChain.CausalFilteredSimulator

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

def IsDirectHashAction :
    (OracleWorld + SigningSpec).Domain → Prop
  | .inl (.inr _) => True
  | _ => False

instance : DecidablePred IsDirectHashAction := fun input => by
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl _ => exact isFalse (by simp [IsDirectHashAction])
      | inr _ => exact isTrue trivial
  | inr _ => exact isFalse (by simp [IsDirectHashAction])

theorem filteredCausalSigningAttempt_isProbeQueryBoundP
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (state : CausalHashState) :
    (filteredCausalSigningAttempt keyView selected request state)
      |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  unfold filteredCausalSigningAttempt
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (RevealProbeOracleSimulation.liftProbComp_isProbeQueryBoundP
      Concrete.signingRandomness 0)
  intro randomness _hrandomness
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (RevealProbeOracleSimulation.liftProbComp_isProbeQueryBoundP
      ((simulateQ randomOracle
        (Concrete.encodingHash keyView.secretKey.parameter request.epoch
          request.message randomness)).run state.cache) 0)
  intro encoded _hencoded
  cases hdecode : TargetSum.decodeDigest encoded.1 with
  | none =>
      exact OracleComp.isQueryBoundP_pure
        (p := RevealProbeOracleSimulation.IsProbeQuery)
          (none, { state with cache := encoded.2 }) 0
  | some encoding =>
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (RevealProbeOracleSimulation.revealQuery_isProbeQueryBoundP
          (request.epoch, encoding selected) 0)
      intro value _hvalue
      exact OracleComp.isQueryBoundP_pure
        (p := RevealProbeOracleSimulation.IsProbeQuery)
        (some (replaceSignatureChainValue
          (Concrete.CacheReplay.signWithEncoding keyView.cache
            keyView.secretKey request.epoch randomness encoding)
          selected value),
        { { state with cache := encoded.2 } with
          revealed := Function.update state.revealed
            (request.epoch, encoding selected) (some value) }) 0

theorem filteredCausalSignBoundedAttempts_isProbeQueryBoundP
    (attempts : Nat)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (state : CausalHashState) :
    (filteredCausalSignBoundedAttempts attempts keyView selected request state)
      |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  induction attempts generalizing state with
  | zero =>
      exact OracleComp.isQueryBoundP_pure
        (p := RevealProbeOracleSimulation.IsProbeQuery) (none, state) 0
  | succ attempts ih =>
      rw [filteredCausalSignBoundedAttempts]
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (filteredCausalSigningAttempt_isProbeQueryBoundP keyView selected
          request state)
      intro result _hresult
      cases result.1 with
      | none => exact ih result.2
      | some signature =>
          exact OracleComp.isQueryBoundP_pure
            (p := RevealProbeOracleSimulation.IsProbeQuery)
              (some signature, result.2) 0

theorem filteredCausalSigningQuery_isProbeQueryBoundP
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (state : CausalHashState) :
    (filteredCausalSigningQuery keyView selected request state)
      |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  unfold filteredCausalSigningQuery
  exact filteredCausalSignBoundedAttempts_isProbeQueryBoundP signingAttemptLimit
    keyView selected request state

noncomputable def filteredDirectMappedAdversaryImpl
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT CausalHashState
        (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))) :=
  fun input =>
    match input with
    | .inl (.inl n) => causalUniformImpl n
    | .inl (.inr hashInput) => StateT.mk (fun state =>
        filteredProbingAttackerHashQueryAt keyView.secretKey selected hashInput
          state (chainInputProbe? keyView.secretKey.parameter selected hashInput))
    | .inr request => StateT.mk (fun state =>
        filteredCausalSigningQuery keyView selected request state)

noncomputable def filteredDirectVerifierImpl
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex) :
    QueryImpl OracleWorld
      (StateT CausalHashState
        (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))) :=
  fun input =>
    match input with
    | .inl n => causalUniformImpl n
    | .inr hashInput => StateT.mk (fun state =>
        filteredProbingAttackerHashQueryAt keyView.secretKey selected hashInput
          state (chainInputProbe? keyView.secretKey.parameter selected hashInput))

noncomputable def filteredDirectActionTracedMappedAdversaryImpl
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex) :
    QueryImpl (OracleWorld + SigningSpec)
      (WriterT AttackerActionTrace
        (StateT CausalHashState
          (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)))) :=
  (filteredDirectMappedAdversaryImpl keyView selected).withTraceAppend
    attackerActionFragment

noncomputable def filteredDirectDetailedGameAfterKeygen
    (adversary : Adversary Concrete.scheme)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex) :
    StateT CausalHashState
      (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))
      ((Forgery × Bool) × AttackerActionTrace) := do
  let handled ← (simulateQ
    (filteredDirectActionTracedMappedAdversaryImpl keyView selected)
      (adversary.main keyView.publicKey)).run
  let verified ← simulateQ (filteredDirectVerifierImpl keyView selected)
    (Concrete.scheme.verify keyView.publicKey handled.1.epoch
      handled.1.message handled.1.signature)
  pure ((handled.1, verified), handled.2)

end XmssSecurity.CappedChain
