import XmssSecurity.Proof.CappedGlobalKeygen
import XmssSecurity.Proof.CappedGlobalTreeCacheCorrespondence
import XmssSecurity.Proof.CappedChain.ChainTracedGame
import XmssSecurity.Proof.PrecomputedKeygenCache
import XmssSecurity.Proof.CappedGlobalChainOrigin
import XmssSecurity.Proof.CappedChain.ChainRevealFiltering
import XmssSecurity.Proof.CappedChain.SignatureChainValue
import XmssSecurity.Proof.RevealProbeOracleSimulation
import XmssSecurity.Proof.CappedChain.CausalSigningKeygenCoupling
import XmssSecurity.Proof.StatementLemmas

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

noncomputable def trajectoryProgrammedGlobalChainKeygen :
    ProbComp ProgrammedGlobalChainKeygenView :=
  eraseAllChainTrajectories <$> programmedAllChainTrajectoryKeygen

theorem evalDist_coupledGlobalChainKeygen_eq_trajectoryProgrammed :
    evalDist coupledGlobalChainKeygen =
      evalDist trajectoryProgrammedGlobalChainKeygen :=
  evalDist_coupledGlobalChainKeygen_eq_programmedTrajectories

theorem evalDist_actualGlobalChainKeygen_eq_trajectoryProgrammed :
    evalDist actualGlobalChainKeygen =
      evalDist trajectoryProgrammedGlobalChainKeygen :=
  evalDist_actualGlobalChainKeygen_eq_programmedAllChainTrajectories

theorem trajectoryProgrammedGlobalChainKeygen_support_table
    (result : ProgrammedGlobalChainKeygenView)
    (hresult : result ∈ support trajectoryProgrammedGlobalChainKeygen) :
    globalKeygenChainValueTable result.cache result.secretKey = result.table := by
  apply actualGlobalChainKeygen_support_table result
  exact (mem_support_iff_of_evalDist_eq
    evalDist_actualGlobalChainKeygen_eq_trajectoryProgrammed result).mpr hresult

abbrev GlobalChainActionTracedResult :=
  ((ProgrammedGlobalChainKeygenView × (GameOutcome × QueryCache HashSpec)) ×
    AttackerActionTrace)

def eraseGlobalChainKeygenView
    (result : GlobalChainActionTracedResult) :
    ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace) :=
  ((((result.1.1.publicKey, Concrete.materializePrecomputation
      result.1.1.cache result.1.1.secretKey), result.1.1.cache),
    result.1.2), result.2)


structure GlobalCausalHashState where
  cache : QueryCache HashSpec
  keygenCache : QueryCache HashSpec
  revealed : GlobalChainValueIndex → Option Digest
  probes : List (GlobalChainValueIndex × Digest)

def GlobalCausalHashState.recordProbe
    (state : GlobalCausalHashState)
    (probe : Option (GlobalChainValueIndex × Digest)) :
    GlobalCausalHashState :=
  { state with probes :=
      match probe with
      | none => state.probes
      | some value => state.probes ++ [value] }

@[simp]
theorem GlobalCausalHashState.recordProbe_cache
    (state : GlobalCausalHashState)
    (probe : Option (GlobalChainValueIndex × Digest)) :
    (state.recordProbe probe).cache = state.cache := rfl

@[simp]
theorem GlobalCausalHashState.recordProbe_keygenCache
    (state : GlobalCausalHashState)
    (probe : Option (GlobalChainValueIndex × Digest)) :
    (state.recordProbe probe).keygenCache = state.keygenCache := rfl

@[simp]
theorem GlobalCausalHashState.recordProbe_revealed
    (state : GlobalCausalHashState)
    (probe : Option (GlobalChainValueIndex × Digest)) :
    (state.recordProbe probe).revealed = state.revealed := rfl

def GlobalCausalHashState.recordReveal
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (value : Digest) : GlobalCausalHashState :=
  { state with revealed := Function.update state.revealed index (some value) }

def GlobalCausalHashState.setCache
    (state : GlobalCausalHashState) (cache : QueryCache HashSpec) :
    GlobalCausalHashState :=
  { state with cache := cache }

@[simp]
theorem GlobalCausalHashState.setCache_revealed
    (state : GlobalCausalHashState) (cache : QueryCache HashSpec) :
    (state.setCache cache).revealed = state.revealed := rfl

noncomputable def globalCausalHashQuery
    (input : HashInput) :
    StateT GlobalCausalHashState
      (OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex))
      HashOutput := fun state =>
  (fun result : HashOutput × QueryCache HashSpec =>
    (result.1, state.setCache result.2)) <$>
      RevealProbeOracleSimulation.liftProbComp
        ((randomOracle input).run state.cache)

theorem globalCausalHashQuery_run
    (input : HashInput) (state : GlobalCausalHashState) :
    (globalCausalHashQuery input).run state =
      (fun result : HashOutput × QueryCache HashSpec =>
        (result.1, state.setCache result.2)) <$>
          RevealProbeOracleSimulation.liftProbComp
            ((randomOracle input).run state.cache) := rfl

noncomputable def globalCausalRecordedState
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) : GlobalCausalHashState :=
  state.recordProbe (globalChainInputProbe? secretKey.parameter input)

@[simp]
theorem globalCausalRecordedState_cache
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    (globalCausalRecordedState secretKey input state).cache = state.cache := by
  rw [globalCausalRecordedState]
  exact GlobalCausalHashState.recordProbe_cache state _

@[simp]
theorem globalCausalRecordedState_keygenCache
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    (globalCausalRecordedState secretKey input state).keygenCache =
      state.keygenCache := by
  rw [globalCausalRecordedState]
  exact GlobalCausalHashState.recordProbe_keygenCache state _

@[simp]
theorem globalCausalRecordedState_revealed
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    (globalCausalRecordedState secretKey input state).revealed =
      state.revealed := by
  rw [globalCausalRecordedState]
  exact GlobalCausalHashState.recordProbe_revealed state _

def globalCausalUniformImpl :
    QueryImpl unifSpec
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  fun n => liftM (RevealProbeOracleSimulation.uniformQuery
    (Index := GlobalChainValueIndex) n)

noncomputable def revealGlobalSignatureChains
    (request : SignRequest) (encoding : ChainIndex → Digit) :
    List ChainIndex → Signature →
      StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex)) Signature
  | [], signature => pure signature
  | chain :: chains, signature => fun state => do
      let index : GlobalChainValueIndex :=
        (chain, request.epoch, encoding chain)
      let value ← RevealProbeOracleSimulation.revealQuery index
      (revealGlobalSignatureChains request encoding chains
        (replaceSignatureChainValue signature chain value)).run
          (state.recordReveal index value)

def globalSignatureRevealResult
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : ChainIndex → Digit) :
    List ChainIndex → Signature → GlobalCausalHashState →
      Signature × GlobalCausalHashState
  | [], signature, state => (signature, state)
  | chain :: chains, signature, state =>
      let index : GlobalChainValueIndex :=
        (chain, request.epoch, encoding chain)
      globalSignatureRevealResult table request encoding chains
        (replaceSignatureChainValue signature chain (table index))
        (state.recordReveal index (table index))

def globalSignatureRevealTrace
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : ChainIndex → Digit) :
    List ChainIndex →
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex
  | [] => []
  | chain :: chains =>
      let index : GlobalChainValueIndex :=
        (chain, request.epoch, encoding chain)
      .reveal index (table index) ::
        globalSignatureRevealTrace table request encoding chains

theorem simulate_eagerTrace_revealGlobalSignatureChains
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (chains : List ChainIndex) (signature : Signature)
    (state : GlobalCausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((revealGlobalSignatureChains request encoding chains signature).run
          state)).run =
      pure (globalSignatureRevealResult table request encoding chains
          signature state,
        globalSignatureRevealTrace table request encoding chains) := by
  induction chains generalizing signature state with
  | nil =>
      simp [revealGlobalSignatureChains, globalSignatureRevealResult,
        globalSignatureRevealTrace]
  | cons chain chains ih =>
      rw [revealGlobalSignatureChains]
      change (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table) (do
          let value ← RevealProbeOracleSimulation.revealQuery
            (chain, request.epoch, encoding chain)
          (revealGlobalSignatureChains request encoding chains
            (replaceSignatureChainValue signature chain value)).run
              (state.recordReveal
                (chain, request.epoch, encoding chain) value))).run = _
      rw [simulateQ_bind, WriterT.run_bind',
        RevealProbeOracleSimulation.simulate_eagerTrace_revealQuery]
      simp only [pure_bind]
      rw [ih]
      simp [globalSignatureRevealResult, globalSignatureRevealTrace]

theorem globalSignatureRevealResult_chainValue_of_not_mem
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (chains : List ChainIndex) (signature : Signature)
    (state : GlobalCausalHashState) (candidate : ChainIndex)
    (hnotmem : candidate ∉ chains) :
    (globalSignatureRevealResult table request encoding chains signature
      state).1.chainValue candidate = signature.chainValue candidate := by
  induction chains generalizing signature state with
  | nil => rfl
  | cons chain chains ih =>
      simp only [List.mem_cons, not_or] at hnotmem
      rw [globalSignatureRevealResult]
      rw [ih _ _ hnotmem.2]
      exact replaceSignatureChainValue_other signature chain candidate
        (table (chain, request.epoch, encoding chain))
        hnotmem.1

theorem globalSignatureRevealResult_chainValue_of_mem
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (chains : List ChainIndex) (signature : Signature)
    (state : GlobalCausalHashState) (candidate : ChainIndex)
    (hnodup : chains.Nodup) (hmem : candidate ∈ chains) :
    (globalSignatureRevealResult table request encoding chains signature
      state).1.chainValue candidate =
        table (candidate, request.epoch, encoding candidate) := by
  induction chains generalizing signature state with
  | nil => simp at hmem
  | cons chain chains ih =>
      rw [List.nodup_cons] at hnodup
      rw [List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · subst candidate
        rw [globalSignatureRevealResult,
          globalSignatureRevealResult_chainValue_of_not_mem]
        · exact replaceSignatureChainValue_same signature chain _
        · exact hnodup.1
      · rw [globalSignatureRevealResult]
        exact ih _ _ hnodup.2 hmem

theorem globalSignatureRevealResult_allChains_chainValue
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (signature : Signature) (state : GlobalCausalHashState)
    (chain : ChainIndex) :
    (globalSignatureRevealResult table request encoding allChains signature
      state).1.chainValue chain =
        table (chain, request.epoch, encoding chain) := by
  apply globalSignatureRevealResult_chainValue_of_mem
  · exact allChains_nodup
  · simp [allChains]

theorem globalCausalHashQuery_run_isProbeQueryBoundP
    (input : HashInput) (state : GlobalCausalHashState) :
    (globalCausalHashQuery input).run state |>.IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery 0 := by
  unfold globalCausalHashQuery
  apply (OracleComp.isQueryBoundP_map_iff _ _ 0).2
  exact RevealProbeOracleSimulation.liftProbComp_isProbeQueryBoundP
    ((randomOracle input).run state.cache) 0

theorem revealGlobalSignatureChains_run_isProbeQueryBoundP
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (chains : List ChainIndex) (signature : Signature)
    (state : GlobalCausalHashState) :
    (revealGlobalSignatureChains request encoding chains signature).run state
        |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  induction chains generalizing signature state with
  | nil => simp [revealGlobalSignatureChains]
  | cons chain chains ih =>
      rw [revealGlobalSignatureChains]
      let index : GlobalChainValueIndex :=
        (chain, request.epoch, encoding chain)
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (RevealProbeOracleSimulation.revealQuery_isProbeQueryBoundP index 0)
      intro value _hvalue
      exact ih (replaceSignatureChainValue signature chain value)
        (state.recordReveal index value)


theorem Signature.eq_of_fields
    (left right : Signature)
    (hrandomness : left.randomness = right.randomness)
    (hchainValue : left.chainValue = right.chainValue)
    (hauthPath : left.authPath = right.authPath) :
    left = right := by
  cases left
  cases right
  simp_all

theorem globalSignatureRevealResult_randomness
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (chains : List ChainIndex) (signature : Signature)
    (state : GlobalCausalHashState) :
    (globalSignatureRevealResult table request encoding chains signature
      state).1.randomness = signature.randomness := by
  induction chains generalizing signature state with
  | nil => rfl
  | cons chain chains ih =>
      rw [globalSignatureRevealResult]
      exact ih _ _

theorem globalSignatureRevealResult_authPath
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (chains : List ChainIndex) (signature : Signature)
    (state : GlobalCausalHashState) :
    (globalSignatureRevealResult table request encoding chains signature
      state).1.authPath = signature.authPath := by
  induction chains generalizing signature state with
  | nil => rfl
  | cons chain chains ih =>
      rw [globalSignatureRevealResult]
      exact ih _ _

theorem globalSignatureRevealResult_cache
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (chains : List ChainIndex) (signature : Signature)
    (state : GlobalCausalHashState) :
    (globalSignatureRevealResult table request encoding chains signature
      state).2.cache = state.cache := by
  induction chains generalizing signature state with
  | nil => rfl
  | cons chain chains ih =>
      rw [globalSignatureRevealResult, ih]
      rfl

theorem globalSignatureRevealResult_keygenCache
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (chains : List ChainIndex) (signature : Signature)
    (state : GlobalCausalHashState) :
    (globalSignatureRevealResult table request encoding chains signature
      state).2.keygenCache = state.keygenCache := by
  induction chains generalizing signature state with
  | nil => rfl
  | cons chain chains ih =>
      rw [globalSignatureRevealResult, ih]
      rfl

def ProgrammedGlobalChainKeygenView.keyResult
    (view : ProgrammedGlobalChainKeygenView) :
    (PublicKey × SecretKey) × QueryCache HashSpec :=
  ((view.publicKey, view.secretKey), view.cache)

theorem actualGlobalChainKeygen_support_keyResult
    (view : ProgrammedGlobalChainKeygenView)
    (hview : view ∈ support actualGlobalChainKeygen) :
    view.keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅) := by
  unfold actualGlobalChainKeygen at hview
  rw [mem_support_bind_iff] at hview
  obtain ⟨keyResult, hkeyResult, hpure⟩ := hview
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst view
  exact hkeyResult

theorem trajectoryProgrammedGlobalChainKeygen_support_keyResult
    (view : ProgrammedGlobalChainKeygenView)
    (hview : view ∈ support trajectoryProgrammedGlobalChainKeygen) :
    view.keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅) := by
  apply actualGlobalChainKeygen_support_keyResult view
  exact (mem_support_iff_of_evalDist_eq
    evalDist_actualGlobalChainKeygen_eq_trajectoryProgrammed view).mpr hview

theorem keygen_support_treeCacheStable
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅)) :
    TreeCacheStable keyResult.1.2.parameter keyResult.1.2.chainStart
      keyResult.2 := by
  let chain : ChainIndex := ⟨0, by norm_num [numChains]⟩
  let view : ProgrammedFixedChainKeygenView := {
    publicKey := keyResult.1.1
    secretKey := keyResult.1.2
    cache := keyResult.2
    table := XmssSecurity.keygenChainValueTable keyResult.2 keyResult.1.2 chain
  }
  apply actualFixedChainKeygen_support_treeCacheStable chain view
  unfold actualFixedChainKeygen
  rw [mem_support_bind_iff]
  exact ⟨keyResult, hkeyResult, by simp [view]⟩

theorem trajectoryProgrammedGlobalChainKeygen_support_treeCacheStable
    (view : ProgrammedGlobalChainKeygenView)
    (hview : view ∈ support trajectoryProgrammedGlobalChainKeygen) :
    TreeCacheStable view.secretKey.parameter view.secretKey.chainStart
      view.cache := by
  exact keygen_support_treeCacheStable view.keyResult
    (trajectoryProgrammedGlobalChainKeygen_support_keyResult view hview)

def ProgrammedGlobalChainKeygenStableRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) : Prop :=
  ProgrammedGlobalChainKeygenRelation left right ∧
    TreeCacheStable left.secretKey.parameter left.secretKey.chainStart
      left.cache ∧
    TreeCacheStable right.1.secretKey.parameter right.1.secretKey.chainStart
      right.1.cache

theorem keygen_parameter_eq
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅)) :
    keyResult.1.1.parameter = keyResult.1.2.parameter := by
  obtain ⟨parameter, secret, root, hkey, _hroot⟩ :=
    Concrete.keygen_support_rootTree keyResult hkeyResult
  exact congrArg (fun result => result.1.parameter = result.2.parameter) hkey ▸ rfl

theorem keygenViews_signWithEncoding_eq_globalReveal
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1 ∈ support trajectoryProgrammedGlobalChainKeygen)
    (leftCache rightCache : QueryCache HashSpec)
    (hleftLe : left.cache ≤ leftCache)
    (hrightLe : right.1.cache ≤ rightCache)
    (request : SignRequest) (randomness : Randomness) (encoding : Encoding)
    (rightState : GlobalCausalHashState) :
    Concrete.CacheReplay.signWithEncoding leftCache left.secretKey
        request.epoch randomness encoding =
      (globalSignatureRevealResult right.2 request encoding allChains
        (Concrete.CacheReplay.signWithEncoding rightCache right.1.secretKey
          request.epoch randomness encoding) rightState).1 := by
  have hleftKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    left hleftSupport
  have hrightKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    right.1 hrightSupport
  have hparameter : left.secretKey.parameter =
      right.1.secretKey.parameter := by
    calc
      left.secretKey.parameter = left.publicKey.parameter :=
        (keygen_parameter_eq left.keyResult hleftKey).symm
      _ = right.1.publicKey.parameter :=
        congrArg PublicKey.parameter hrel.1.2.1
      _ = right.1.secretKey.parameter :=
        keygen_parameter_eq right.1.keyResult hrightKey
  apply Signature.eq_of_fields
  · rw [globalSignatureRevealResult_randomness]
    rfl
  · funext chain
    rw [globalSignatureRevealResult_allChains_chainValue]
    have hchain :=
      Concrete.CacheReplay.signWithEncoding_chainValue_eq_keygenChainValueTable
        left.keyResult hleftKey leftCache hleftLe request.epoch randomness
          encoding chain
    rw [show (Concrete.CacheReplay.signWithEncoding leftCache left.secretKey
        request.epoch randomness encoding).chainValue chain =
      keygenChainValueTable left.cache left.secretKey chain
        (request.epoch, encoding chain) by
          simpa [ProgrammedGlobalChainKeygenView.keyResult] using hchain]
    change globalKeygenChainValueTable left.cache left.secretKey
      (chain, request.epoch, encoding chain) = _
    rw [trajectoryProgrammedGlobalChainKeygen_support_table left hleftSupport,
      hrel.1.1]
  · funext level
    calc
      (Concrete.CacheReplay.signWithEncoding leftCache left.secretKey
          request.epoch randomness encoding).authPath level =
        Concrete.CacheReplay.authenticationPath left.cache left.secretKey
          request.epoch level := by
            rw [Concrete.CacheReplay.signWithEncoding]
            exact congrFun (hrel.2.1.authenticationPath_eq left.secretKey
              left.cache leftCache hleftLe request.epoch).symm level
      _ = Concrete.CacheReplay.authenticationPath right.1.cache
          right.1.secretKey request.epoch level :=
            congrFun (hrel.1.2.2 request.epoch) level
      _ = (globalSignatureRevealResult right.2 request encoding allChains
          (Concrete.CacheReplay.signWithEncoding rightCache right.1.secretKey
            request.epoch randomness encoding) rightState).1.authPath level := by
        rw [globalSignatureRevealResult_authPath]
        change Concrete.CacheReplay.authenticationPath right.1.cache
            right.1.secretKey request.epoch level =
          Concrete.CacheReplay.authenticationPath rightCache
            right.1.secretKey request.epoch level
        exact congrFun (hrel.2.2.authenticationPath_eq right.1.secretKey
          right.1.cache rightCache hrightLe request.epoch) level

def GlobalSigningComparableHashInput
    (parameter : PublicParameter) (input : HashInput) : Prop :=
  ∃ epoch message randomness,
    input = Concrete.CacheView.encodingInput parameter epoch
      (message, randomness)

def GlobalSigningRevealsAgree
    (table : GlobalChainValueIndex → Digest)
    (state : GlobalCausalHashState) : Prop :=
  ∀ index value, state.revealed index = some value → table index = value

theorem GlobalSigningRevealsAgree.setCache
    {table : GlobalChainValueIndex → Digest}
    {state : GlobalCausalHashState}
    (hagrees : GlobalSigningRevealsAgree table state)
    (cache : QueryCache HashSpec) :
    GlobalSigningRevealsAgree table { state with cache := cache } :=
  hagrees

theorem GlobalSigningRevealsAgree.recordReveal
    {table : GlobalChainValueIndex → Digest}
    {state : GlobalCausalHashState}
    (hagrees : GlobalSigningRevealsAgree table state)
    (index : GlobalChainValueIndex) :
    GlobalSigningRevealsAgree table
      (state.recordReveal index (table index)) := by
  intro candidate value hvalue
  by_cases heq : candidate = index
  · subst candidate
    simp [GlobalCausalHashState.recordReveal] at hvalue
    exact hvalue
  · simp [GlobalCausalHashState.recordReveal,
      Function.update_of_ne heq] at hvalue
    exact hagrees candidate value hvalue

theorem GlobalSigningRevealsAgree.globalSignatureRevealResult
    {table : GlobalChainValueIndex → Digest}
    {state : GlobalCausalHashState}
    (hagrees : GlobalSigningRevealsAgree table state)
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (chains : List ChainIndex) (signature : Signature) :
    GlobalSigningRevealsAgree table
      (globalSignatureRevealResult table request encoding chains signature
        state).2 := by
  induction chains generalizing signature state with
  | nil =>
      change GlobalSigningRevealsAgree table state
      exact hagrees
  | cons chain chains ih =>
      change GlobalSigningRevealsAgree table
        (XmssSecurity.CappedChain.globalSignatureRevealResult table request
          encoding chains
          (replaceSignatureChainValue signature chain
            (table (chain, request.epoch, encoding chain)))
          (state.recordReveal (chain, request.epoch, encoding chain)
            (table (chain, request.epoch, encoding chain)))).2
      apply ih
      exact hagrees.recordReveal (chain, request.epoch, encoding chain)



def CoupledGlobalChainKeygenFullCacheRelation
    (parameter : PublicParameter)
    (left : CoupledGlobalChainKeygenView)
    (right : CoupledGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) : Prop :=
  CoupledGlobalChainKeygenRelation parameter left right ∧
    ∃ leftEndpoints rightEndpoints,
      GlobalTreeCacheCorrespondence parameter leftEndpoints rightEndpoints
        left.cache right.1.cache ∧
      ReplayEndpointsMatch parameter left.secret leftEndpoints left.cache ∧
      ReplayEndpointsMatch parameter right.1.secret rightEndpoints
        right.1.cache

def ProgrammedGlobalChainKeygenFullCacheRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) : Prop :=
  ProgrammedGlobalChainKeygenFullRelation left right ∧
    ∃ leftEndpoints rightEndpoints,
      GlobalTreeCacheCorrespondence left.secretKey.parameter leftEndpoints
        rightEndpoints left.cache right.1.cache ∧
      ReplayEndpointsMatch left.secretKey.parameter left.secretKey.chainStart
        leftEndpoints left.cache ∧
      ReplayEndpointsMatch right.1.secretKey.parameter
        right.1.secretKey.chainStart rightEndpoints right.1.cache


theorem Concrete.CacheView.encodingInput_ne_leafInput
    (parameter : PublicParameter) (encodingEpoch epoch : Epoch)
    (message : Message) (randomness : Randomness)
    (endpoints : ChainIndex → Digest) :
    Concrete.CacheView.encodingInput parameter encodingEpoch
        (message, randomness) ≠
      Concrete.CacheView.leafInput parameter epoch endpoints := by
  intro heq
  have hdomain := domain_eq_of_tweakableHashInput_eq parameter heq
  simp at hdomain

def GlobalTreeSigningCacheRelation
    (parameter : PublicParameter)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec) : Prop :=
  ∃ leftEndpoints rightEndpoints,
    GlobalTreeCacheCorrespondence parameter leftEndpoints rightEndpoints
      leftCache rightCache ∧
    ReplayEndpointsMatch parameter leftSecret leftEndpoints leftCache ∧
    ReplayEndpointsMatch parameter rightSecret rightEndpoints rightCache

def ProgrammedGlobalChainKeygenFullCacheStableRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) : Prop :=
  ProgrammedGlobalChainKeygenFullCacheRelation left right ∧
    TreeCacheStable left.secretKey.parameter left.secretKey.chainStart
      left.cache ∧
    TreeCacheStable right.1.secretKey.parameter right.1.secretKey.chainStart
      right.1.cache ∧
    GlobalTreeSigningCacheRelation left.secretKey.parameter
      left.secretKey.chainStart right.1.secretKey.chainStart left.cache
        right.1.cache

theorem ProgrammedGlobalChainKeygenFullCacheStableRelation.toStable
    {left : ProgrammedGlobalChainKeygenView}
    {right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)}
    (hrel : ProgrammedGlobalChainKeygenFullCacheStableRelation left right) :
    ProgrammedGlobalChainKeygenStableRelation left right :=
  ⟨hrel.1.1.1, hrel.2.1, hrel.2.2.1⟩

end XmssSecurity.CappedChain
