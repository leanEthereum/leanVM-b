import XmssSecurity.EncodingActionTrace
import VCVio.OracleComp.Constructions.SampleableType

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

set_option maxRecDepth 100000

inductive EncodingSampleKind where
  | side
  | query
  | sign
deriving DecidableEq

structure EncodingSampleAddress where
  kind : EncodingSampleKind
  epoch : Option Epoch
deriving DecidableEq

abbrev EncodingSampleSpec : OracleSpec EncodingSampleAddress :=
  EncodingSampleAddress →ₒ HashOutput
abbrev EncodingSamplingWorld := unifSpec + EncodingSampleSpec

noncomputable def uniformHashOutput : ProbComp HashOutput :=
  $ᵗ HashOutput

noncomputable def uniformWorldImpl : QueryImpl unifSpec ProbComp :=
  HasQuery.toQueryImpl

noncomputable def encodingOutputImpl : QueryImpl EncodingSampleSpec ProbComp :=
  fun _address => uniformHashOutput

noncomputable def encodingSamplingWorldImpl :
    QueryImpl EncodingSamplingWorld ProbComp :=
  uniformWorldImpl + encodingOutputImpl

def encodingSampleQuery (address : EncodingSampleAddress) :
    OracleComp EncodingSamplingWorld HashOutput :=
  OracleComp.liftComp
    (liftM (EncodingSampleSpec.query address) :
      OracleComp EncodingSampleSpec HashOutput)
    EncodingSamplingWorld

def encodingUniformQuery (index : unifSpec.Domain) :
    OracleComp EncodingSamplingWorld (unifSpec.Range index) :=
  OracleComp.liftComp
    (liftM (unifSpec.query index) : ProbComp (unifSpec.Range index))
    EncodingSamplingWorld

noncomputable def encodingSampleAddress
    (parameter : PublicParameter) (kind : EncodingSampleKind)
    (input : HashInput) : EncodingSampleAddress :=
  match encodingInputEpoch? parameter input with
  | none => ⟨.side, none⟩
  | some epoch => ⟨kind, some epoch⟩

noncomputable def freshEncodingSampleImpl
    (parameter : PublicParameter) (kind : EncodingSampleKind) :
    QueryImpl HashSpec (OracleComp EncodingSamplingWorld) :=
  fun input => encodingSampleQuery (encodingSampleAddress parameter kind input)

noncomputable def splitRandomOracle
    (parameter : PublicParameter) (kind : EncodingSampleKind) :
    QueryImpl HashSpec
      (StateT (QueryCache HashSpec) (OracleComp EncodingSamplingWorld)) :=
  (freshEncodingSampleImpl parameter kind).withCaching

noncomputable def splitUniformOracle :
    QueryImpl unifSpec
      (StateT (QueryCache HashSpec) (OracleComp EncodingSamplingWorld)) :=
  QueryImpl.liftTarget
    (StateT (QueryCache HashSpec) (OracleComp EncodingSamplingWorld))
    ((fun index => encodingUniformQuery index) :
      QueryImpl unifSpec (OracleComp EncodingSamplingWorld))

noncomputable def splitXmssRomImpl
    (parameter : PublicParameter) (kind : EncodingSampleKind) :
    QueryImpl OracleWorld
      (StateT (QueryCache HashSpec) (OracleComp EncodingSamplingWorld)) :=
  splitUniformOracle + splitRandomOracle parameter kind

theorem simulateQ_encodingUniformQuery (index : unifSpec.Domain) :
    simulateQ encodingSamplingWorldImpl (encodingUniformQuery index) =
      (liftM (unifSpec.query index) : ProbComp (unifSpec.Range index)) := by
  rw [encodingUniformQuery, encodingSamplingWorldImpl,
    QueryImpl.simulateQ_add_liftComp_left]
  exact QueryImpl.simulateQ_toQueryImpl _

theorem splitUniformOracle_bridge
    (index : unifSpec.Domain) (cache : QueryCache HashSpec) :
    simulateQ encodingSamplingWorldImpl
        ((splitUniformOracle index).run cache) =
      (unifFwdImpl HashSpec index).run cache := by
  rw [splitUniformOracle, QueryImpl.liftTarget_apply, StateT.run_monadLift,
    simulateQ_bind, monadLift_eq_self, simulateQ_encodingUniformQuery]
  simp only [simulateQ_pure]
  simp [unifFwdImpl, QueryImpl.liftTarget_apply, StateT.run_monadLift]

theorem simulateQ_encodingSamplingWorld_query
    (address : EncodingSampleAddress) :
    simulateQ encodingSamplingWorldImpl
      (encodingSampleQuery address) = uniformHashOutput := by
  rw [encodingSampleQuery, encodingSamplingWorldImpl,
    QueryImpl.simulateQ_add_liftComp_right, simulateQ_spec_query]
  rfl

theorem simulateQ_freshEncodingSampleImpl
    (parameter : PublicParameter) (kind : EncodingSampleKind)
    (input : HashInput) :
    simulateQ encodingSamplingWorldImpl
      (freshEncodingSampleImpl parameter kind input) = uniformHashOutput := by
  unfold freshEncodingSampleImpl
  exact simulateQ_encodingSamplingWorld_query
    (encodingSampleAddress parameter kind input)

theorem uniformSampleImpl_hash_eq (input : HashInput) :
    (uniformSampleImpl (spec := HashSpec)) input = uniformHashOutput := by
  rfl

noncomputable def runSplitRandomOracle
    (parameter : PublicParameter) (kind : EncodingSampleKind)
    (input : HashInput) (cache : QueryCache HashSpec) :
    ProbComp (HashOutput × QueryCache HashSpec) :=
  simulateQ encodingSamplingWorldImpl
    ((splitRandomOracle parameter kind input).run cache)

noncomputable def runRandomOracle
    (input : HashInput) (cache : QueryCache HashSpec) :
    ProbComp (HashOutput × QueryCache HashSpec) :=
  (randomOracle input).run cache

theorem randomOracle_run_none_eq_uniformHashOutput
    (input : HashInput) (cache : QueryCache HashSpec)
    (hcache : cache input = none) :
    (randomOracle input).run cache =
      (fun output => (output, cache.cacheQuery input output)) <$>
        uniformHashOutput := by
  rw [randomOracle, QueryImpl.withCaching_run_none _ hcache]
  rw [uniformSampleImpl_hash_eq]

theorem splitRandomOracle_bridge
    (parameter : PublicParameter) (kind : EncodingSampleKind)
    (input : HashInput) (cache : QueryCache HashSpec) :
    runSplitRandomOracle parameter kind input cache =
      runRandomOracle input cache := by
  unfold runSplitRandomOracle runRandomOracle
  cases hcache : cache input with
  | some output =>
      simp [splitRandomOracle, hcache]
  | none =>
      rw [splitRandomOracle, QueryImpl.withCaching_run_none _ hcache,
        simulateQ_map]
      exact (congrArg
        (fun computation : ProbComp HashOutput =>
          (fun output => (output, cache.cacheQuery input output)) <$> computation)
        (simulateQ_freshEncodingSampleImpl parameter kind input)).trans
        (randomOracle_run_none_eq_uniformHashOutput input cache hcache).symm

theorem splitRandomOracle_evalDist_simulation
    (parameter : PublicParameter) (kind : EncodingSampleKind)
    (computation : OracleComp HashSpec α) (cache : QueryCache HashSpec) :
    𝒟[simulateQ encodingSamplingWorldImpl
        ((simulateQ (splitRandomOracle parameter kind) computation).run cache)] =
      𝒟[(simulateQ randomOracle computation).run cache] := by
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  apply OracleComp.evalDist_simulateQ_run_congr
  intro input state
  exact congrArg evalDist
    (splitRandomOracle_bridge parameter kind input state)

theorem splitXmssRom_evalDist_simulation
    (parameter : PublicParameter) (kind : EncodingSampleKind)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    𝒟[simulateQ encodingSamplingWorldImpl
        ((simulateQ (splitXmssRomImpl parameter kind) computation).run cache)] =
      𝒟[(simulateQ xmssRomImpl computation).run cache] := by
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  apply OracleComp.evalDist_simulateQ_run_congr
  intro input state
  cases input with
  | inl index =>
      simp only [splitXmssRomImpl, xmssRomImpl, QueryImpl.add_apply_inl]
      exact congrArg evalDist (splitUniformOracle_bridge index state)
  | inr hashInput =>
      simp only [splitXmssRomImpl, xmssRomImpl, QueryImpl.add_apply_inr]
      exact congrArg evalDist
        (splitRandomOracle_bridge parameter kind hashInput state)

noncomputable def splitUnloggedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec) (OracleComp EncodingSamplingWorld)) := by
  intro input
  cases input with
  | inl worldInput =>
      exact splitXmssRomImpl secretKey.parameter .query worldInput
  | inr request =>
      exact simulateQ (splitXmssRomImpl secretKey.parameter .sign)
        (Concrete.scheme.sign publicKey secretKey request.epoch request.message)

theorem splitUnloggedMappedAdversaryImpl_query_bridge
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (cache : QueryCache HashSpec) :
    𝒟[simulateQ encodingSamplingWorldImpl
        ((splitUnloggedMappedAdversaryImpl publicKey secretKey input).run cache)] =
      𝒟[(unloggedMappedAdversaryImpl publicKey secretKey input).run cache] := by
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl index =>
          simp only [splitUnloggedMappedAdversaryImpl,
            unloggedMappedAdversaryImpl_apply_inl, splitXmssRomImpl,
            xmssRomImpl, QueryImpl.add_apply_inl]
          exact congrArg evalDist (splitUniformOracle_bridge index cache)
      | inr hashInput =>
          simp only [splitUnloggedMappedAdversaryImpl,
            unloggedMappedAdversaryImpl_apply_inl, splitXmssRomImpl,
            xmssRomImpl, QueryImpl.add_apply_inr]
          exact congrArg evalDist
            (splitRandomOracle_bridge secretKey.parameter .query hashInput cache)
  | inr request =>
      simp only [splitUnloggedMappedAdversaryImpl,
        unloggedMappedAdversaryImpl_apply_inr]
      exact splitXmssRom_evalDist_simulation secretKey.parameter .sign
        (Concrete.scheme.sign publicKey secretKey request.epoch request.message) cache

theorem splitUnloggedMappedAdversary_evalDist_simulation
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) :
    𝒟[simulateQ encodingSamplingWorldImpl
        ((simulateQ (splitUnloggedMappedAdversaryImpl publicKey secretKey)
          computation).run cache)] =
      𝒟[(simulateQ (unloggedMappedAdversaryImpl publicKey secretKey)
        computation).run cache] := by
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  apply OracleComp.evalDist_simulateQ_run_congr
  intro input state
  exact splitUnloggedMappedAdversaryImpl_query_bridge
    publicKey secretKey input state

noncomputable def encodingSamplingController
    (computation : OracleComp EncodingSamplingWorld α) :
    ProbComp
      (EncodingMonitor.ControllerAction
        (OracleComp EncodingSamplingWorld α)) :=
  OracleComp.construct
    (C := fun _ => ProbComp
      (EncodingMonitor.ControllerAction
        (OracleComp EncodingSamplingWorld α)))
    (fun _result => pure .stop)
    (fun input next recursivelyContinue =>
      match input with
      | .inl index => do
          let output ← (liftM (unifSpec.query index) :
            ProbComp (unifSpec.Range index))
          recursivelyContinue output
      | .inr address =>
          match address.kind, address.epoch with
          | .query, some epoch => pure (.query epoch next)
          | .sign, some epoch => pure (.sign epoch next)
          | _, _ => do
              let output ← uniformHashOutput
              pure (.skip (next output)))
    computation

noncomputable def runEncodingSamplingMonitor
    (fuel : Nat) (computation : OracleComp EncodingSamplingWorld α) :
    ProbComp Bool :=
  EncodingMonitor.runProbabilistic encodingSamplingController
    EncodingMonitor.State.empty fuel computation

theorem runEncodingSamplingMonitor_true_probability_le
    (fuel : Nat) (computation : OracleComp EncodingSamplingWorld α) :
    Pr[(fun hit : Bool => hit = true) |
      runEncodingSamplingMonitor fuel computation] ≤
      (fuel : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  exact EncodingMonitor.runProbabilistic_empty_true_probability_le
    encodingSamplingController fuel computation

end XmssSecurity
