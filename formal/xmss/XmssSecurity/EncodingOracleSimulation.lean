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
  input : HashInput
deriving DecidableEq

abbrev EncodingSampleSpec : OracleSpec EncodingSampleAddress :=
  EncodingSampleAddress →ₒ HashOutput
abbrev EncodingSamplingWorld := unifSpec + EncodingSampleSpec

@[simp]
def IsEncodingSampleAt (kind : EncodingSampleKind) (epoch : Epoch) :
    EncodingSamplingWorld.Domain → Prop
  | .inr address => address.kind = kind ∧ address.epoch = some epoch
  | _ => False

noncomputable instance (kind : EncodingSampleKind) (epoch : Epoch) :
    DecidablePred (IsEncodingSampleAt kind epoch) :=
  Classical.decPred _

noncomputable instance : IsUniformSpec EncodingSampleSpec :=
  IsUniformSpec.ofFintypeInhabited _

noncomputable def uniformHashOutput : ProbComp HashOutput :=
  $ᵗ HashOutput

theorem uniformHashOutput_if_truncate_eq_probability_le
    (target : Digest) (resume : HashOutput → ProbComp Bool) (ε : ℝ≥0∞)
    (hresume : ∀ output, truncateHash output ≠ target →
      Pr[(fun hit : Bool => hit = true) | resume output] ≤ ε) :
    Pr[(fun hit : Bool => hit = true) |
      uniformHashOutput >>= fun output =>
        if truncateHash output = target then pure true
        else resume output] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ + ε := by
  unfold uniformHashOutput
  refine (probEvent_bind_le_probEvent_add
    (mx := ($ᵗ HashOutput))
    (my := fun output =>
      if truncateHash output = target then pure true else resume output)
    (q := fun hit : Bool => hit = true)
    (p := fun output : HashOutput => truncateHash output = target)
    (ε := ε) ?_).trans_eq ?_
  · intro output _ hmiss
    simp only [hmiss, ↓reduceIte]
    exact hresume output hmiss
  · rw [Rom.uniform_truncate_probability]

theorem uniformHashOutput_if_truncate_mem_probability_le
    (targets : Finset Digest) (resume : HashOutput → ProbComp Bool) (ε : ℝ≥0∞)
    (hresume : ∀ output, truncateHash output ∉ targets →
      Pr[(fun hit : Bool => hit = true) | resume output] ≤ ε) :
    Pr[(fun hit : Bool => hit = true) |
      uniformHashOutput >>= fun output =>
        if truncateHash output ∈ targets then pure true
        else resume output] ≤
      (targets.card : ℝ≥0∞) *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ + ε := by
  unfold uniformHashOutput
  refine (probEvent_bind_le_probEvent_add
    (mx := ($ᵗ HashOutput))
    (my := fun output =>
      if truncateHash output ∈ targets then pure true else resume output)
    (q := fun hit : Bool => hit = true)
    (p := fun output : HashOutput => truncateHash output ∈ targets)
    (ε := ε) ?_).trans ?_
  · intro output _ hmiss
    simp only [hmiss, ↓reduceIte]
    exact hresume output hmiss
  · exact add_le_add
      (EncodingMonitor.uniform_truncate_mem_finset_le targets) le_rfl

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

def encodingSampleAddressFromEpoch
    (kind : EncodingSampleKind) (input : HashInput) :
    Option Epoch → EncodingSampleAddress
  | none => ⟨.side, none, input⟩
  | some epoch => ⟨kind, some epoch, input⟩

noncomputable def encodingSampleAddress
    (parameter : PublicParameter) (kind : EncodingSampleKind)
    (input : HashInput) : EncodingSampleAddress :=
  encodingSampleAddressFromEpoch kind input
    (encodingInputEpoch? parameter input)

theorem encodingSampleAddress_eq_of_epoch
    (parameter : PublicParameter) (kind : EncodingSampleKind)
    (input : HashInput) (epoch : Epoch)
    (hepoch : encodingInputEpoch? parameter input = some epoch) :
    encodingSampleAddress parameter kind input = ⟨kind, some epoch, input⟩ := by
  rw [encodingSampleAddress, hepoch]
  rfl

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

theorem encodingUniformQuery_encodingSample_bound
    (index : unifSpec.Domain) :
    (encodingUniformQuery index).IsQueryBoundP (· matches .inr _) 0 := by
  unfold encodingUniformQuery
  rw [OracleComp.liftComp_query]
  change (liftM (EncodingSamplingWorld.query (Sum.inl index)) :
    OracleComp EncodingSamplingWorld _) |>.IsQueryBoundP (· matches .inr _) 0
  rw [OracleComp.isQueryBoundP_query_iff]
  simp

theorem encodingSampleQuery_encodingSample_bound
    (address : EncodingSampleAddress) :
    (encodingSampleQuery address).IsQueryBoundP (· matches .inr _) 1 := by
  unfold encodingSampleQuery
  rw [OracleComp.liftComp_query]
  change (liftM (EncodingSamplingWorld.query (Sum.inr address)) :
    OracleComp EncodingSamplingWorld _) |>.IsQueryBoundP (· matches .inr _) 1
  rw [OracleComp.isQueryBoundP_query_iff]
  simp

theorem splitUniformOracle_bridge
    (index : unifSpec.Domain) (cache : QueryCache HashSpec) :
    simulateQ encodingSamplingWorldImpl
        ((splitUniformOracle index).run cache) =
      (unifFwdImpl HashSpec index).run cache := by
  rw [splitUniformOracle, QueryImpl.liftTarget_apply, StateT.run_monadLift,
    simulateQ_bind, monadLift_eq_self, simulateQ_encodingUniformQuery]
  simp only [simulateQ_pure]
  simp [unifFwdImpl, QueryImpl.liftTarget_apply, StateT.run_monadLift]

theorem splitUniformOracle_encodingSample_bound
    (index : unifSpec.Domain) (cache : QueryCache HashSpec) :
    ((splitUniformOracle index).run cache).IsQueryBoundP
      (· matches .inr _) 0 := by
  rw [splitUniformOracle, QueryImpl.liftTarget_apply, StateT.run_monadLift]
  exact encodingUniformQuery_encodingSample_bound index

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

theorem splitRandomOracle_encodingSample_bound
    (parameter : PublicParameter) (kind : EncodingSampleKind)
    (input : HashInput) (cache : QueryCache HashSpec) :
    ((splitRandomOracle parameter kind input).run cache).IsQueryBoundP
      (· matches .inr _) 1 := by
  apply QueryImpl.isQueryBoundP_run_withCaching
    (freshEncodingSampleImpl parameter kind) input
  exact encodingSampleQuery_encodingSample_bound
    (encodingSampleAddress parameter kind input)

theorem splitXmssRom_encodingSample_bound
    (parameter : PublicParameter) (kind : EncodingSampleKind)
    (computation : OracleComp OracleWorld α) (fuel : Nat)
    (hbound : computation.IsQueryBoundP (· matches .inr _) fuel)
    (cache : QueryCache HashSpec) :
    ((simulateQ (splitXmssRomImpl parameter kind) computation).run cache)
      |>.IsQueryBoundP (· matches .inr _) fuel := by
  apply OracleComp.IsQueryBoundP.simulateQ_run_add_inr_of_step
    (p := fun input : OracleWorld.Domain => input matches .inr _)
    (q := fun input : EncodingSamplingWorld.Domain => input matches .inr _)
    (fun input => by simp) hbound
  · exact splitUniformOracle_encodingSample_bound
  · intro input _ cache
    exact splitRandomOracle_encodingSample_bound parameter kind input cache
  · intro input hfalse
    simp at hfalse

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

noncomputable def splitCacheTracedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec × SigningCacheTrace)
        (OracleComp EncodingSamplingWorld)) :=
  QueryImpl.extendState
    (splitUnloggedMappedAdversaryImpl publicKey secretKey)
    signingCacheTraceUpdate

noncomputable def splitEncodingTracedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)
        (OracleComp EncodingSamplingWorld)) :=
  QueryImpl.extendState
    (splitCacheTracedMappedAdversaryImpl publicKey secretKey)
    (encodingActionTraceUpdate secretKey)

theorem splitCacheTracedMappedAdversaryImpl_query_bridge
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : QueryCache HashSpec × SigningCacheTrace) :
    𝒟[simulateQ encodingSamplingWorldImpl
        ((splitCacheTracedMappedAdversaryImpl publicKey secretKey input).run state)] =
      𝒟[(cacheTracedMappedAdversaryImpl publicKey secretKey input).run state] := by
  unfold splitCacheTracedMappedAdversaryImpl cacheTracedMappedAdversaryImpl
  rw [QueryImpl.extendState_apply, QueryImpl.extendState_apply]
  simp only [simulateQ_bind, simulateQ_pure, evalDist_bind]
  rw [splitUnloggedMappedAdversaryImpl_query_bridge]

theorem splitCacheTracedMappedAdversary_evalDist_simulation
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : QueryCache HashSpec × SigningCacheTrace) :
    𝒟[simulateQ encodingSamplingWorldImpl
        ((simulateQ (splitCacheTracedMappedAdversaryImpl publicKey secretKey)
          computation).run state)] =
      𝒟[(simulateQ (cacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run state] := by
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  apply OracleComp.evalDist_simulateQ_run_congr
  intro input currentState
  exact splitCacheTracedMappedAdversaryImpl_query_bridge
    publicKey secretKey input currentState

theorem splitEncodingTracedMappedAdversaryImpl_query_bridge
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : (QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) :
    𝒟[simulateQ encodingSamplingWorldImpl
        ((splitEncodingTracedMappedAdversaryImpl publicKey secretKey input).run state)] =
      𝒟[(encodingTracedMappedAdversaryImpl publicKey secretKey input).run state] := by
  unfold splitEncodingTracedMappedAdversaryImpl
    encodingTracedMappedAdversaryImpl
  rw [QueryImpl.extendState_apply, QueryImpl.extendState_apply]
  simp only [simulateQ_bind, simulateQ_pure, evalDist_bind]
  rw [splitCacheTracedMappedAdversaryImpl_query_bridge]

theorem splitEncodingTracedMappedAdversary_evalDist_simulation
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : (QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) :
    𝒟[simulateQ encodingSamplingWorldImpl
        ((simulateQ (splitEncodingTracedMappedAdversaryImpl publicKey secretKey)
          computation).run state)] =
      𝒟[(simulateQ (encodingTracedMappedAdversaryImpl publicKey secretKey)
        computation).run state] := by
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  apply OracleComp.evalDist_simulateQ_run_congr
  intro input currentState
  exact splitEncodingTracedMappedAdversaryImpl_query_bridge
    publicKey secretKey input currentState

noncomputable def splitDetailedGameAfterKeygenWithEncodingTrace
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    OracleComp EncodingSamplingWorld (GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) := do
  let (forgery, adversaryState) ←
    (simulateQ (splitEncodingTracedMappedAdversaryImpl publicKey secretKey)
      (adversary.main publicKey)).run ((initialCache, []), [])
  let (verified, finalCache) ←
    (simulateQ (splitXmssRomImpl secretKey.parameter .query)
      (Concrete.scheme.verify publicKey forgery.epoch forgery.message
        forgery.signature)).run adversaryState.1.1
  let finalEncodingTrace := appendVerificationEncodingObservation secretKey forgery
    adversaryState.1.1 finalCache adversaryState.2
  pure (⟨publicKey, secretKey, forgery, adversaryState.1.2.toSigningLog, verified⟩,
    ((finalCache, adversaryState.1.2), finalEncodingTrace))

theorem splitDetailedGameAfterKeygenWithEncodingTrace_evalDist_simulation
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    𝒟[simulateQ encodingSamplingWorldImpl
        (splitDetailedGameAfterKeygenWithEncodingTrace adversary publicKey secretKey
          initialCache)] =
      𝒟[detailedGameAfterKeygenWithEncodingTrace adversary publicKey secretKey
        initialCache] := by
  unfold splitDetailedGameAfterKeygenWithEncodingTrace
    detailedGameAfterKeygenWithEncodingTrace
  simp only [simulateQ_bind, simulateQ_pure, evalDist_bind]
  rw [splitEncodingTracedMappedAdversary_evalDist_simulation]
  simp_rw [splitXmssRom_evalDist_simulation]

noncomputable def splitDetailedGameWithEncodingTrace
    (adversary : Adversary Concrete.scheme) :
    ProbComp (GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) := do
  let keyResult ← (simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅
  simulateQ encodingSamplingWorldImpl
    (splitDetailedGameAfterKeygenWithEncodingTrace adversary keyResult.1.1
      keyResult.1.2 keyResult.2)

theorem splitDetailedGameWithEncodingTrace_evalDist_simulation
    (adversary : Adversary Concrete.scheme) :
    𝒟[splitDetailedGameWithEncodingTrace adversary] =
      𝒟[detailedGameWithEncodingTrace adversary] := by
  unfold splitDetailedGameWithEncodingTrace detailedGameWithEncodingTrace
  simp only [evalDist_bind]
  simp_rw [splitDetailedGameAfterKeygenWithEncodingTrace_evalDist_simulation]

noncomputable def encodingSampleControllerStep
    (address : EncodingSampleAddress)
    (next : HashOutput → OracleComp EncodingSamplingWorld α) :
    ProbComp
      (EncodingMonitor.ControllerAction
        (OracleComp EncodingSamplingWorld α)) :=
  match address.kind, address.epoch with
  | .query, some epoch => pure (.query epoch next)
  | .sign, some epoch => pure (.sign epoch next)
  | _, _ => do
      let output ← uniformHashOutput
      pure (.skip (next output))

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
      | .inr address => encodingSampleControllerStep address next)
    computation

noncomputable def runEncodingSamplingMonitor
    (fuel : Nat) (computation : OracleComp EncodingSamplingWorld α) :
    ProbComp Bool :=
  EncodingMonitor.runProbabilistic encodingSamplingController
    EncodingMonitor.State.empty fuel computation

def EncodingSamplingContinuationBound (fuel : Nat) :
    EncodingMonitor.ControllerAction
      (OracleComp EncodingSamplingWorld α) → Prop
  | .stop => True
  | .skip next => next.IsQueryBoundP (· matches .inr _) fuel
  | .query _ next => ∀ output, (next output).IsQueryBoundP (· matches .inr _) fuel
  | .sign _ next => ∀ output, (next output).IsQueryBoundP (· matches .inr _) fuel

theorem encodingSamplingController_continuationBound
    (computation : OracleComp EncodingSamplingWorld α) (fuel : Nat)
    (hbound : computation.IsQueryBoundP (· matches .inr _) fuel.succ)
    (action : EncodingMonitor.ControllerAction
      (OracleComp EncodingSamplingWorld α))
    (hmem : action ∈ support (encodingSamplingController computation)) :
    EncodingSamplingContinuationBound fuel action := by
  induction computation using OracleComp.inductionOn with
  | pure result =>
      simp [encodingSamplingController] at hmem
      subst action
      trivial
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      simp only [encodingSamplingController,
        OracleComp.construct_query_bind] at hmem
      cases input with
      | inl index =>
          rw [mem_support_bind_iff] at hmem
          obtain ⟨output, _houtput, hcontinue⟩ := hmem
          exact ih output (by simpa using hbound.2 output) hcontinue
      | inr address =>
          cases address with
          | mk kind epoch =>
              cases epoch with
              | none =>
                  simp only [encodingSampleControllerStep] at hmem
                  change action ∈ support (uniformHashOutput >>= fun output =>
                    pure (.skip (next output))) at hmem
                  rw [mem_support_bind_iff] at hmem
                  obtain ⟨output, _houtput, haction⟩ := hmem
                  simp only [support_pure, Set.mem_singleton_iff] at haction
                  subst action
                  simpa [EncodingSamplingContinuationBound] using hbound.2 output
              | some epoch =>
                  cases kind with
                  | side =>
                      simp only [encodingSampleControllerStep] at hmem
                      change action ∈ support (uniformHashOutput >>= fun output =>
                        pure (.skip (next output))) at hmem
                      rw [mem_support_bind_iff] at hmem
                      obtain ⟨output, _houtput, haction⟩ := hmem
                      simp only [support_pure, Set.mem_singleton_iff] at haction
                      subst action
                      simpa [EncodingSamplingContinuationBound] using hbound.2 output
                  | query =>
                      simp only [encodingSampleControllerStep] at hmem
                      change action ∈ support (pure (.query epoch next)) at hmem
                      simp only [support_pure, Set.mem_singleton_iff] at hmem
                      subst action
                      intro output
                      simpa using hbound.2 output
                  | sign =>
                      simp only [encodingSampleControllerStep] at hmem
                      change action ∈ support (pure (.sign epoch next)) at hmem
                      simp only [support_pure, Set.mem_singleton_iff] at hmem
                      subst action
                      intro output
                      simpa using hbound.2 output

theorem encodingSamplingController_eq_stop_of_zero_bound
    (computation : OracleComp EncodingSamplingWorld α)
    (hbound : computation.IsQueryBoundP (· matches .inr _) 0)
    (action : EncodingMonitor.ControllerAction
      (OracleComp EncodingSamplingWorld α))
    (hmem : action ∈ support (encodingSamplingController computation)) :
    action = .stop := by
  induction computation using OracleComp.inductionOn with
  | pure result =>
      simpa [encodingSamplingController] using hmem
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      simp only [encodingSamplingController,
        OracleComp.construct_query_bind] at hmem
      cases input with
      | inl index =>
          rw [mem_support_bind_iff] at hmem
          obtain ⟨output, _houtput, hcontinue⟩ := hmem
          exact ih output (by simpa using hbound.2 output) hcontinue
      | inr address =>
          exfalso
          simpa using hbound.1

def encodingSamplingTraceFragment
    (input : EncodingSamplingWorld.Domain)
    (output : EncodingSamplingWorld.Range input) : EncodingActionTrace :=
  match input with
  | .inl _ => []
  | .inr address =>
      match address.kind, address.epoch with
      | .query, some epoch => [.query epoch output]
      | .sign, some epoch => [.sign epoch output]
      | _, _ => []

noncomputable def encodingSamplingTraceImpl :
    QueryImpl EncodingSamplingWorld
      (WriterT EncodingActionTrace ProbComp) :=
  QueryImpl.withTraceAppend encodingSamplingWorldImpl
    encodingSamplingTraceFragment

theorem encodingSamplingTraceImpl_query_run
    (address : EncodingSampleAddress) :
    (encodingSamplingTraceImpl (.inr address)).run =
      (fun output =>
        (output, encodingSamplingTraceFragment (.inr address) output)) <$>
          encodingSamplingWorldImpl (.inr address) := by
  unfold encodingSamplingTraceImpl
  rw [QueryImpl.withTraceAppend_apply, WriterT.run_bind']
  rw [WriterT.run_monadLift']
  simp [WriterT.run_tell]

theorem encodingSamplingTraceImpl_support_trace
    (address : EncodingSampleAddress)
    (result : EncodingSamplingWorld.Range (.inr address) × EncodingActionTrace)
    (hmem : result ∈ support (encodingSamplingTraceImpl (.inr address)).run) :
    result.2 = encodingSamplingTraceFragment (.inr address) result.1 := by
  rw [encodingSamplingTraceImpl_query_run, support_map] at hmem
  obtain ⟨output, _houtput, heq⟩ := hmem
  subst result
  rfl

theorem encodingSampleQuery_tagged_support_trace
    (kind : EncodingSampleKind) (epoch : Epoch) (input : HashInput)
    (result : HashOutput × EncodingActionTrace)
    (hmem : result ∈ support
      (simulateQ encodingSamplingTraceImpl
        (encodingSampleQuery ⟨kind, some epoch, input⟩)).run) :
    result.2 = match kind with
      | .query => [.query epoch result.1]
      | .sign => [.sign epoch result.1]
      | .side => [] := by
  let address := EncodingSampleAddress.mk kind (some epoch) input
  change result ∈ support
    (simulateQ encodingSamplingTraceImpl (encodingSampleQuery address)).run at hmem
  unfold encodingSampleQuery at hmem
  rw [OracleComp.liftComp_query, simulateQ_map, WriterT.run_map', support_map]
    at hmem
  obtain ⟨outerResult, houter, hresultEq⟩ := hmem
  simp only [OracleQuery.input_query] at houter
  rw [simulateQ_liftM_query encodingSamplingTraceImpl
    (EncodingSampleSpec.query address)] at houter
  simp only [QueryImpl.mapQuery, WriterT.run_map', support_map] at houter
  obtain ⟨handledResult, hhandled, houterEq⟩ := houter
  change handledResult ∈
    support (encodingSamplingTraceImpl (.inr address)).run at hhandled
  have htrace :=
    encodingSamplingTraceImpl_support_trace address handledResult hhandled
  have hresultTrace : result.2 = handledResult.2 := by
    calc
      result.2 = outerResult.2 := by
        simpa using (congrArg Prod.snd hresultEq).symm
      _ = handledResult.2 := by
        simpa using (congrArg Prod.snd houterEq).symm
  have hresultOutput : result.1 = handledResult.1 := by
    calc
      result.1 = outerResult.1 := by
        simpa using (congrArg Prod.fst hresultEq).symm
      _ = handledResult.1 := by
        simpa using (congrArg Prod.fst houterEq).symm
  rw [hresultTrace, hresultOutput]
  cases kind <;> simpa [address, encodingSamplingTraceFragment] using htrace

theorem encodingSampleQuery_query_support_trace
    (epoch : Epoch) (input : HashInput)
    (result : HashOutput × EncodingActionTrace)
    (hmem : result ∈ support
      (simulateQ encodingSamplingTraceImpl
        (encodingSampleQuery ⟨.query, some epoch, input⟩)).run) :
    result.2 = [.query epoch result.1] := by
  simpa using
    encodingSampleQuery_tagged_support_trace .query epoch input result hmem

theorem encodingSampleQuery_sign_support_trace
    (epoch : Epoch) (input : HashInput)
    (result : HashOutput × EncodingActionTrace)
    (hmem : result ∈ support
      (simulateQ encodingSamplingTraceImpl
        (encodingSampleQuery ⟨.sign, some epoch, input⟩)).run) :
    result.2 = [.sign epoch result.1] := by
  simpa using
    encodingSampleQuery_tagged_support_trace .sign epoch input result hmem

theorem encodingSamplingTrace_projection
    (computation : OracleComp EncodingSamplingWorld α) :
    Prod.fst <$>
        (simulateQ encodingSamplingTraceImpl computation).run =
      simulateQ encodingSamplingWorldImpl computation := by
  exact QueryImpl.fst_map_run_withTraceAppend
    encodingSamplingWorldImpl encodingSamplingTraceFragment computation

noncomputable def sampledDetailedGameWithEncodingTrace
    (adversary : Adversary Concrete.scheme) :
    ProbComp ((GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
        EncodingActionTrace) := do
  let keyResult ← (simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅
  (simulateQ encodingSamplingTraceImpl
    (splitDetailedGameAfterKeygenWithEncodingTrace adversary keyResult.1.1
      keyResult.1.2 keyResult.2)).run

theorem sampledDetailedGameWithEncodingTrace_projection
    (adversary : Adversary Concrete.scheme) :
    Prod.fst <$> sampledDetailedGameWithEncodingTrace adversary =
      splitDetailedGameWithEncodingTrace adversary := by
  unfold sampledDetailedGameWithEncodingTrace splitDetailedGameWithEncodingTrace
  rw [map_bind]
  apply bind_congr
  intro keyResult
  exact encodingSamplingTrace_projection
    (splitDetailedGameAfterKeygenWithEncodingTrace adversary keyResult.1.1
      keyResult.1.2 keyResult.2)

theorem detailedGameWithEncodingTrace_monitorHit_probability_eq_sampled
    (adversary : Adversary Concrete.scheme) :
    Pr[(fun execution : GameOutcome ×
        ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
      EncodingMonitor.runObserved EncodingMonitor.State.empty execution.2.2 = true) |
      detailedGameWithEncodingTrace adversary] =
    Pr[(fun execution : (GameOutcome ×
        ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
          EncodingActionTrace =>
      EncodingMonitor.runObserved EncodingMonitor.State.empty
        execution.1.2.2 = true) |
      sampledDetailedGameWithEncodingTrace adversary] := by
  calc
    _ = Pr[(fun execution : GameOutcome ×
          ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
        EncodingMonitor.runObserved EncodingMonitor.State.empty
          execution.2.2 = true) |
        splitDetailedGameWithEncodingTrace adversary] := by
      rw [probEvent_def, probEvent_def,
        splitDetailedGameWithEncodingTrace_evalDist_simulation]
    _ = _ := by
      rw [← sampledDetailedGameWithEncodingTrace_projection, probEvent_map]
      rfl

noncomputable def applyEncodingQueryMonitor
    (epoch : Epoch)
    (resume : HashOutput → EncodingMonitor.State → ProbComp Bool)
    (state : EncodingMonitor.State) : ProbComp Bool := do
  let output ← uniformHashOutput
  match state.applyObserved (.query epoch output) with
  | none => pure false
  | some (nextState, hit) =>
      if hit then pure true else resume output nextState

noncomputable def applyEncodingSignMonitor
    (epoch : Epoch)
    (resume : HashOutput → EncodingMonitor.State → ProbComp Bool)
    (state : EncodingMonitor.State) : ProbComp Bool := do
  let output ← uniformHashOutput
  match state.applyObserved (.sign epoch output) with
  | none => pure false
  | some (nextState, hit) =>
      if hit then pure true else resume output nextState

noncomputable def applyEncodingSampleMonitor
    (address : EncodingSampleAddress)
    (resume : HashOutput → EncodingMonitor.State → ProbComp Bool)
    (state : EncodingMonitor.State) : ProbComp Bool :=
  match address.kind, address.epoch with
  | .query, some epoch => applyEncodingQueryMonitor epoch resume state
  | .sign, some epoch => applyEncodingSignMonitor epoch resume state
  | _, _ => uniformHashOutput >>= fun output => resume output state

noncomputable def runStructuralEncodingMonitor
    (state : EncodingMonitor.State)
    (computation : OracleComp EncodingSamplingWorld α) : ProbComp Bool :=
  OracleComp.construct
    (C := fun _ => EncodingMonitor.State → ProbComp Bool)
    (fun _result _state => pure false)
    (fun input _next recursivelyMonitor state =>
      match input with
      | .inl index => do
          let output ← (liftM (unifSpec.query index) :
            ProbComp (unifSpec.Range index))
          recursivelyMonitor output state
      | .inr address =>
          applyEncodingSampleMonitor address recursivelyMonitor state)
    computation state

theorem applyEncodingQueryMonitor_true_probability_le
    (epoch : Epoch)
    (resume : HashOutput → EncodingMonitor.State → ProbComp Bool)
    (state : EncodingMonitor.State) (fuel : Nat)
    (hresume : ∀ output nextState,
      Pr[(fun hit : Bool => hit = true) | resume output nextState] ≤
        ((fuel + nextState.pendingCount : Nat) : ℝ≥0∞) *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) :
    Pr[(fun hit : Bool => hit = true) |
      applyEncodingQueryMonitor epoch resume state] ≤
      ((fuel.succ + state.pendingCount : Nat) : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  cases hsigned : state.signed epoch with
  | none =>
      unfold applyEncodingQueryMonitor
      simp only [EncodingMonitor.State.applyObserved, hsigned]
      refine probEvent_bind_le_of_forall_le fun output _ => ?_
      refine (hresume output
        (state.addPending epoch (truncateHash output))).trans ?_
      have hcount := state.pendingCount_addPending_le epoch
        (truncateHash output)
      have hnat : fuel + (state.addPending epoch
            (truncateHash output)).pendingCount ≤
          fuel.succ + state.pendingCount := by omega
      exact mul_le_mul' (Nat.cast_le.mpr hnat) le_rfl
  | some target =>
      have hcollision := uniformHashOutput_if_truncate_eq_probability_le target
        (fun output => resume output state)
        (((fuel + state.pendingCount : Nat) : ℝ≥0∞) *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) (by
        intro output _hmiss
        exact hresume output state
      )
      have hrewrite :
          applyEncodingQueryMonitor epoch resume state =
            uniformHashOutput >>= fun output =>
              if truncateHash output = target then pure true
              else resume output state := by
        unfold applyEncodingQueryMonitor
        simp only [EncodingMonitor.State.applyObserved, hsigned,
          decide_eq_true_eq]
      rw [hrewrite]
      refine hcollision.trans ?_
      push_cast
      ring_nf
      exact le_rfl

theorem applyEncodingSignMonitor_true_probability_le
    (epoch : Epoch)
    (resume : HashOutput → EncodingMonitor.State → ProbComp Bool)
    (state : EncodingMonitor.State) (fuel : Nat)
    (hresume : ∀ output nextState,
      Pr[(fun hit : Bool => hit = true) | resume output nextState] ≤
        ((fuel + nextState.pendingCount : Nat) : ℝ≥0∞) *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) :
    Pr[(fun hit : Bool => hit = true) |
      applyEncodingSignMonitor epoch resume state] ≤
      ((fuel.succ + state.pendingCount : Nat) : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  cases hsigned : state.signed epoch with
  | some target =>
      simp [applyEncodingSignMonitor,
        EncodingMonitor.State.applyObserved, hsigned]
  | none =>
      have hcollision := uniformHashOutput_if_truncate_mem_probability_le
        (state.pending epoch)
        (fun output => resume output
          (state.install epoch (truncateHash output)))
        (((fuel + (state.install epoch 0).pendingCount : Nat) : ℝ≥0∞) *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) (by
        intro output _hmiss
        have hcount :
            (state.install epoch (truncateHash output)).pendingCount =
              (state.install epoch 0).pendingCount :=
          state.pendingCount_install_eq epoch _ _
        simpa [hcount] using hresume output
          (state.install epoch (truncateHash output))
      )
      have hrewrite :
          applyEncodingSignMonitor epoch resume state =
            uniformHashOutput >>= fun output =>
              if truncateHash output ∈ state.pending epoch then pure true
              else resume output
                (state.install epoch (truncateHash output)) := by
        unfold applyEncodingSignMonitor
        simp only [EncodingMonitor.State.applyObserved, hsigned,
          decide_eq_true_eq]
      rw [hrewrite]
      refine hcollision.trans ?_
      have hconserve := state.pendingCount_install_add epoch 0
      have hnat :
          (state.pending epoch).card +
              (fuel + (state.install epoch 0).pendingCount) ≤
            fuel.succ + state.pendingCount := by omega
      rw [← add_mul]
      gcongr
      rw [← Nat.cast_add]
      exact Nat.cast_le.mpr hnat

theorem applyEncodingSampleMonitor_true_probability_le
    (address : EncodingSampleAddress)
    (resume : HashOutput → EncodingMonitor.State → ProbComp Bool)
    (state : EncodingMonitor.State) (fuel : Nat)
    (hresume : ∀ output nextState,
      Pr[(fun hit : Bool => hit = true) | resume output nextState] ≤
        ((fuel + nextState.pendingCount : Nat) : ℝ≥0∞) *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) :
    Pr[(fun hit : Bool => hit = true) |
      applyEncodingSampleMonitor address resume state] ≤
      ((fuel.succ + state.pendingCount : Nat) : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rcases address with ⟨kind, epoch, input⟩
  cases epoch with
  | none =>
      cases kind <;> unfold applyEncodingSampleMonitor
      all_goals
        refine probEvent_bind_le_of_forall_le fun output _ => ?_
        refine (hresume output state).trans ?_
        gcongr
        omega
  | some epoch =>
      cases kind with
      | side =>
          unfold applyEncodingSampleMonitor
          refine probEvent_bind_le_of_forall_le fun output _ => ?_
          refine (hresume output state).trans ?_
          gcongr
          omega
      | query =>
          unfold applyEncodingSampleMonitor
          exact applyEncodingQueryMonitor_true_probability_le
            epoch resume state fuel hresume
      | sign =>
          unfold applyEncodingSampleMonitor
          exact applyEncodingSignMonitor_true_probability_le
            epoch resume state fuel hresume

theorem runStructuralEncodingMonitor_true_probability_le
    (state : EncodingMonitor.State)
    (computation : OracleComp EncodingSamplingWorld α) (fuel : Nat)
    (hbound : computation.IsQueryBoundP (· matches .inr _) fuel) :
    Pr[(fun hit : Bool => hit = true) |
      runStructuralEncodingMonitor state computation] ≤
      ((fuel + state.pendingCount : Nat) : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure result =>
      rw [runStructuralEncodingMonitor, OracleComp.construct_pure, probEvent_pure]
      simp
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      cases input with
      | inl index =>
          rw [runStructuralEncodingMonitor, OracleComp.construct_query_bind]
          change Pr[(fun hit : Bool => hit = true) |
            (liftM (unifSpec.query index) : ProbComp _) >>= fun output =>
              runStructuralEncodingMonitor state (next output)] ≤ _
          refine probEvent_bind_le_of_forall_le fun output _ => ?_
          exact ih output state fuel (by simpa using hbound.2 output)
      | inr address =>
          cases fuel with
          | zero =>
              simp at hbound
          | succ fuel =>
              rw [runStructuralEncodingMonitor,
                OracleComp.construct_query_bind]
              exact applyEncodingSampleMonitor_true_probability_le address
                (fun output nextState =>
                  runStructuralEncodingMonitor nextState (next output)) state fuel
                (fun output nextState => ih output nextState fuel
                  (by simpa using hbound.2 output))

noncomputable def runTracedEncodingMonitor
    (state : EncodingMonitor.State)
    (computation : OracleComp EncodingSamplingWorld α) : ProbComp Bool :=
  (fun result => EncodingMonitor.runObserved state result.2) <$>
    (simulateQ encodingSamplingTraceImpl computation).run

theorem runTracedEncodingMonitor_cons_probability_le
    (state : EncodingMonitor.State) (action : EncodingMonitor.ObservedAction)
    (computation : OracleComp EncodingSamplingWorld α)
    (resume : EncodingMonitor.State → ProbComp Bool)
    (hresume : ∀ nextState,
      Pr[(fun hit : Bool => hit = true) |
        runTracedEncodingMonitor nextState computation] ≤
      Pr[(fun hit : Bool => hit = true) | resume nextState]) :
    Pr[(fun hit : Bool => hit = true) |
      (fun result =>
        EncodingMonitor.runObserved state (action :: result.2)) <$>
          (simulateQ encodingSamplingTraceImpl computation).run] ≤
    Pr[(fun hit : Bool => hit = true) |
      match state.applyObserved action with
      | none => pure false
      | some (nextState, hit) =>
          if hit then pure true else resume nextState] := by
  cases happly : state.applyObserved action with
  | none =>
      simp [EncodingMonitor.runObserved_cons, happly]
  | some result =>
      rcases result with ⟨nextState, hit⟩
      cases hit with
      | false =>
          simpa only [runTracedEncodingMonitor,
            EncodingMonitor.runObserved_cons, happly, Bool.false_or,
            Bool.false_eq_true, ↓reduceIte] using hresume nextState
      | true =>
          simp [EncodingMonitor.runObserved_cons, happly]

theorem runTracedEncodingMonitor_probability_le_structural
    (state : EncodingMonitor.State)
    (computation : OracleComp EncodingSamplingWorld α) :
    Pr[(fun hit : Bool => hit = true) |
      runTracedEncodingMonitor state computation] ≤
    Pr[(fun hit : Bool => hit = true) |
      runStructuralEncodingMonitor state computation] := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure result =>
      simp [runTracedEncodingMonitor, runStructuralEncodingMonitor,
        encodingSamplingTraceImpl]
  | query_bind input next ih =>
      simp only [runTracedEncodingMonitor, simulateQ_query_bind,
        WriterT.run_bind', runStructuralEncodingMonitor,
        OracleComp.construct_query_bind]
      cases input with
      | inl index =>
          simp only [OracleQuery.input_query,
            monadLift_self, encodingSamplingTraceImpl,
            QueryImpl.withTraceAppend_apply, encodingSamplingWorldImpl,
            QueryImpl.add_apply_inl, uniformWorldImpl,
            encodingSamplingTraceFragment, WriterT.run_bind',
            WriterT.run_monadLift', WriterT.run_tell, WriterT.run_pure',
            map_eq_bind_pure_comp, bind_assoc, pure_bind,
            List.nil_append, Prod.map_apply, id_eq,
            Function.comp_apply]
          apply probEvent_bind_mono
          intro output _houtput
          change Pr[(fun hit : Bool => hit = true) |
              runTracedEncodingMonitor state (next output)] ≤
            Pr[(fun hit : Bool => hit = true) |
              runStructuralEncodingMonitor state (next output)]
          exact ih output state
      | inr address =>
          simp only [OracleQuery.input_query,
            monadLift_self, encodingSamplingTraceImpl,
            QueryImpl.withTraceAppend_apply, encodingSamplingWorldImpl,
            QueryImpl.add_apply_inr, encodingOutputImpl,
            encodingSamplingTraceFragment, WriterT.run_bind',
            WriterT.run_monadLift', WriterT.run_tell, WriterT.run_pure',
            map_eq_bind_pure_comp, bind_assoc, pure_bind,
            Prod.map_apply, id_eq,
            Function.comp_apply]
          rcases address with ⟨kind, epoch, input⟩
          cases epoch with
          | none =>
              cases kind <;> unfold applyEncodingSampleMonitor
              all_goals
                apply probEvent_bind_mono
                intro output _houtput
                change Pr[(fun hit : Bool => hit = true) |
                    runTracedEncodingMonitor state (next output)] ≤
                  Pr[(fun hit : Bool => hit = true) |
                    runStructuralEncodingMonitor state (next output)]
                exact ih output state
          | some epoch =>
              cases kind with
              | side =>
                  unfold applyEncodingSampleMonitor
                  apply probEvent_bind_mono
                  intro output _houtput
                  change Pr[(fun hit : Bool => hit = true) |
                      runTracedEncodingMonitor state (next output)] ≤
                    Pr[(fun hit : Bool => hit = true) |
                      runStructuralEncodingMonitor state (next output)]
                  exact ih output state
              | query =>
                  unfold applyEncodingSampleMonitor applyEncodingQueryMonitor
                  apply probEvent_bind_mono
                  intro output _houtput
                  exact runTracedEncodingMonitor_cons_probability_le state
                    (.query epoch output) (next output)
                    (fun nextState =>
                      runStructuralEncodingMonitor nextState (next output))
                    (fun nextState => ih output nextState)
              | sign =>
                  unfold applyEncodingSampleMonitor applyEncodingSignMonitor
                  apply probEvent_bind_mono
                  intro output _houtput
                  exact runTracedEncodingMonitor_cons_probability_le state
                    (.sign epoch output) (next output)
                    (fun nextState =>
                      runStructuralEncodingMonitor nextState (next output))
                    (fun nextState => ih output nextState)

theorem runTracedEncodingMonitor_empty_true_probability_le
    (computation : OracleComp EncodingSamplingWorld α) (fuel : Nat)
    (hbound : computation.IsQueryBoundP (· matches .inr _) fuel) :
    Pr[(fun hit : Bool => hit = true) |
      runTracedEncodingMonitor EncodingMonitor.State.empty computation] ≤
      (fuel : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  refine (runTracedEncodingMonitor_probability_le_structural
    EncodingMonitor.State.empty computation).trans ?_
  simpa [div_eq_mul_inv] using
    runStructuralEncodingMonitor_true_probability_le
      EncodingMonitor.State.empty computation fuel hbound

theorem encodingSamplingTrace_collision_probability_le
    (computation : OracleComp EncodingSamplingWorld α) (fuel : Nat)
    (hbound : computation.IsQueryBoundP (· matches .inr _) fuel) :
    Pr[(fun result : α × EncodingActionTrace =>
        EncodingMonitor.runObserved EncodingMonitor.State.empty result.2 = true) |
      (simulateQ encodingSamplingTraceImpl computation).run] ≤
      (fuel : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  change Pr[((fun hit : Bool => hit = true) ∘ fun result =>
      EncodingMonitor.runObserved EncodingMonitor.State.empty result.2) |
    (simulateQ encodingSamplingTraceImpl computation).run] ≤ _
  rw [← probEvent_map]
  exact runTracedEncodingMonitor_empty_true_probability_le computation fuel hbound

theorem runEncodingSamplingMonitor_true_probability_le
    (fuel : Nat) (computation : OracleComp EncodingSamplingWorld α) :
    Pr[(fun hit : Bool => hit = true) |
      runEncodingSamplingMonitor fuel computation] ≤
      (fuel : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  exact EncodingMonitor.runProbabilistic_empty_true_probability_le
    encodingSamplingController fuel computation

end XmssSecurity
