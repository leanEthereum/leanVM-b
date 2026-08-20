import XmssSecurity.Proof.CappedGlobalCausalStrategyProgram
import XmssSecurity.Proof.CappedChain.CausalSigningKeygenCoupling
import XmssSecurity.Proof.StatementLemmas

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

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


end XmssSecurity.CappedChain
