import XmssSecurity.Proof.CappedGlobalFirstLaneBounds
import XmssSecurity.Proof.CappedGlobalChainHighActionTrace
import XmssSecurity.Proof.FirstLaneOnlineMonitor
import XmssSecurity.Proof.FirstLaneHazardEnforcement

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

noncomputable def onlineFirstLaneLift
    (input : (OracleWorld + SigningSpec).Domain)
    (base : StateT GlobalCausalHashState (OracleComp GlobalFirstLaneWorld)
      ((OracleWorld + SigningSpec).Range input)) :
    StateT GlobalHighDirectTracedState (OracleComp GlobalFirstLaneWorld)
      ((OracleWorld + SigningSpec).Range input) :=
  StateT.mk fun state => do
    let result ← base.run state.1
    pure (result.1,
      (result.2, state.2 ++ attackerActionFragment input result.1))

noncomputable def onlineFirstLaneMappedAdversaryImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalHighDirectTracedState
        (OracleComp GlobalFirstLaneWorld)) := fun input =>
  match input with
  | .inl worldInput => onlineFirstLaneLift (.inl worldInput)
      (globalFirstLaneOracleImpl keyView edgeHigh worldInput)
  | .inr request => onlineFirstLaneLift (.inr request)
      (globalFirstLaneSigningImpl keyView request)

noncomputable def onlineFirstLaneVerifierImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl OracleWorld
      (StateT GlobalHighDirectTracedState
        (OracleComp GlobalFirstLaneWorld)) := fun input =>
  StateT.mk fun state =>
    (fun result => (result.1, (result.2, state.2))) <$>
      (globalFirstLaneVerifierImpl keyView edgeHigh input).run state.1

noncomputable def onlineFirstLaneDetailedExecution
    (adversary : Adversary)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    StateT GlobalHighDirectTracedState (OracleComp GlobalFirstLaneWorld)
      (Forgery × Bool) := StateT.mk fun initial => do
  let handled ← (simulateQ
    (onlineFirstLaneMappedAdversaryImpl keyView edgeHigh)
      (adversary.main keyView.publicKey)).run initial
  let verified ← (simulateQ
    (onlineFirstLaneVerifierImpl keyView edgeHigh)
      (Concrete.scheme.verify keyView.publicKey handled.1.epoch
        handled.1.message handled.1.signature)).run handled.2
  pure ((handled.1, verified.1), verified.2)

abbrev OnlineFirstLaneResult :=
  GlobalHighDirectKeyResult ×
    ((Forgery × Bool) × GlobalHighDirectTracedState)

def onlineFirstLaneDirectResult
    (result : OnlineFirstLaneResult) : GlobalHighDirectResult :=
  (result.1, (result.2.1, result.2.2.1))

noncomputable def onlineFirstLaneForgeryProbes
    (result : OnlineFirstLaneResult) :
    RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex :=
  globalHighDirectForgeryPrimaryProbeTrace
    (onlineFirstLaneDirectResult result)

noncomputable def onlineFirstLaneCoreProgram
    (adversary : Adversary) :
    OracleComp GlobalFirstLaneWorld OnlineFirstLaneResult := do
  let keyResult ← FirstLaneOracleSimulation.liftProbComp globalHighDirectKeygen
  let execution ← (onlineFirstLaneDetailedExecution adversary keyResult.1
    keyResult.2).run
      (globalFilteredCausalKeygenState keyResult.1, [])
  pure (keyResult, execution)

noncomputable def onlineFirstLaneProgram
    (adversary : Adversary) :
    OracleComp GlobalFirstLaneWorld OnlineFirstLaneResult := do
  let result ← onlineFirstLaneCoreProgram adversary
  let _ ← globalFirstLaneLiftRevealProbe
    (RevealProbeOracleSimulation.emitObservedTrace
      (onlineFirstLaneForgeryProbes result))
  pure result

noncomputable def onlineFirstLaneExperiment
    (fuel : Nat) (adversary : Adversary) : ProbComp Bool :=
  FirstLaneOracleSimulation.onlineExperiment fuel
    (onlineFirstLaneProgram adversary)

noncomputable def enforcedOnlineFirstLaneExperiment
    (fuel : Nat) (adversary : Adversary) : ProbComp Bool :=
  FirstLaneOracleSimulation.onlineExperiment fuel
    (FirstLaneOracleSimulation.enforceHazardBound fuel
      (onlineFirstLaneProgram adversary))

theorem onlineFirstLaneExperiment_true_probability_le
    (fuel : Nat) (adversary : Adversary) :
    Pr[(fun hit : Bool => hit = true) |
        onlineFirstLaneExperiment fuel adversary] ≤
      (fuel : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) :=
  FirstLaneOracleSimulation.onlineExperiment_true_probability_le fuel
    (onlineFirstLaneProgram adversary)

theorem enforcedOnlineFirstLaneExperiment_true_probability_le
    (fuel : Nat) (adversary : Adversary) :
    Pr[(fun hit : Bool => hit = true) |
        enforcedOnlineFirstLaneExperiment fuel adversary] ≤
      (fuel : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) :=
  FirstLaneOracleSimulation.onlineExperiment_true_probability_le fuel
    (FirstLaneOracleSimulation.enforceHazardBound fuel
      (onlineFirstLaneProgram adversary))

end XmssSecurity.CappedChain
