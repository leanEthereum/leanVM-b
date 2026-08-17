import XmssSecurity.CappedGlobalCausalSigningProjection
import XmssSecurity.CappedChain.CausalSigningKeygenCoupling

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

def ProgrammedGlobalChainKeygenView.keyResult
    (view : ProgrammedGlobalChainKeygenView) :
    (PublicKey × SecretKey) × QueryCache HashSpec :=
  ((view.publicKey, view.secretKey), view.cache)

theorem actualGlobalChainKeygen_support_keyResult
    (view : ProgrammedGlobalChainKeygenView)
    (hview : view ∈ support actualGlobalChainKeygen) :
    view.keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅) := by
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
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅) := by
  apply actualGlobalChainKeygen_support_keyResult view
  exact (mem_support_iff_of_evalDist_eq
    evalDist_actualGlobalChainKeygen_eq_trajectoryProgrammed view).mpr hview

theorem keygen_support_treeCacheStable
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅)) :
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

set_option maxRecDepth 1000000 in
set_option linter.constructorNameAsVariable false in
theorem trajectoryProgrammedWithBase_support_keyViews
    (result : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (hresult : result ∈ support
      (trajectoryProgrammedGlobalChainKeygen >>= fun keyView =>
        ($ᵗ (GlobalChainValueIndex → Digest)) >>= fun base =>
        pure (keyView, base))) :
    result.1 ∈ support trajectoryProgrammedGlobalChainKeygen := by
  rw [mem_support_bind_iff] at hresult
  obtain ⟨keyView, hkeyView, hbaseBind⟩ := hresult
  rw [mem_support_bind_iff] at hbaseBind
  obtain ⟨base, _hbase, hpure⟩ := hbaseBind
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  have hfirst : result.1 = keyView := congrArg Prod.fst hpure
  rw [hfirst]
  exact hkeyView

theorem relTriple_trajectoryProgrammedGlobalChainKeygen_withBase_stable :
    RelTriple trajectoryProgrammedGlobalChainKeygen
      (trajectoryProgrammedGlobalChainKeygen >>= fun keyView =>
        ($ᵗ (GlobalChainValueIndex → Digest)) >>= fun base =>
        pure (keyView, base))
      ProgrammedGlobalChainKeygenStableRelation := by
  apply relTriple_post_mono
    (relTriple_with_support
      relTriple_trajectoryProgrammedGlobalChainKeygen_withBase)
  intro left right hrel
  refine ⟨hrel.1, ?_, ?_⟩
  · exact trajectoryProgrammedGlobalChainKeygen_support_treeCacheStable
      left hrel.2.1
  · exact trajectoryProgrammedGlobalChainKeygen_support_treeCacheStable
      right.1 (trajectoryProgrammedWithBase_support_keyViews right hrel.2.2)

theorem keygen_parameter_eq
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅)) :
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

theorem relTriple_globalEncodingHash_run
    (parameter : PublicParameter) (left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (GlobalSigningComparableHashInput parameter) left right)
    (epoch : Epoch) (message : Message) (randomness : Randomness) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.encodingHash parameter epoch message randomness)).run left)
      ((simulateQ randomOracle
        (Concrete.encodingHash parameter epoch message randomness)).run right)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          HashCachesAgreeOn (GlobalSigningComparableHashInput parameter)
            leftResult.2 rightResult.2 ∧
          left ≤ leftResult.2 ∧ right ≤ rightResult.2 ∧
          Concrete.CacheView.encodingHash leftResult.2 parameter epoch
            (message, randomness) = leftResult.1 ∧
          Concrete.CacheView.encodingHash rightResult.2 parameter epoch
            (message, randomness) = rightResult.1) := by
  have hquery := relTriple_randomOracle_run_of_cachesAgreeOn
    (GlobalSigningComparableHashInput parameter) left right
    (Concrete.CacheView.encodingInput parameter epoch (message, randomness))
    ⟨epoch, message, randomness, rfl⟩ hagrees
  have hmapped : RelTriple
      ((fun result : HashOutput × QueryCache HashSpec =>
        (truncateHash result.1, result.2)) <$> (randomOracle
          (Concrete.CacheView.encodingInput parameter epoch
            (message, randomness))).run left)
      ((fun result : HashOutput × QueryCache HashSpec =>
        (truncateHash result.1, result.2)) <$> (randomOracle
          (Concrete.CacheView.encodingInput parameter epoch
            (message, randomness))).run right)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          HashCachesAgreeOn (GlobalSigningComparableHashInput parameter)
            leftResult.2 rightResult.2 ∧
          left ≤ leftResult.2 ∧ right ≤ rightResult.2) := by
    apply relTriple_map
    apply relTriple_post_mono hquery
    intro leftResult rightResult hresult
    exact ⟨congrArg truncateHash hresult.1, hresult.2⟩
  have hstrengthened := relTriple_strengthen_support hmapped
    (fun result hresult => encodingHash_run_cache_eq parameter left result.2
      epoch message randomness result.1 (by
        simpa [Concrete.encodingHash, Concrete.tweakableHash,
          Concrete.oracleHash, Concrete.CacheView.encodingInput,
          map_eq_bind_pure_comp] using hresult))
    (fun result hresult => encodingHash_run_cache_eq parameter right result.2
      epoch message randomness result.1 (by
        simpa [Concrete.encodingHash, Concrete.tweakableHash,
          Concrete.oracleHash, Concrete.CacheView.encodingInput,
          map_eq_bind_pure_comp] using hresult))
  apply relTriple_post_mono hstrengthened
  intro leftResult rightResult hresult
  exact ⟨hresult.1.1, hresult.1.2.1, hresult.1.2.2.1,
    hresult.1.2.2.2, hresult.2.1, hresult.2.2⟩

def GlobalSignAttemptResultRelation
    (table : GlobalChainValueIndex → Digest)
    (parameter : PublicParameter) (epoch : Epoch) (message : Message)
    (randomness : Randomness) (initialLeft initialRight : QueryCache HashSpec)
    (request : SignRequest)
    (leftResult rightResult : Option Signature × QueryCache HashSpec) : Prop :=
  ∃ decoded : Option Encoding,
    TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash leftResult.2 parameter epoch
        (message, randomness)) = decoded ∧
    (match decoded with
      | none => leftResult.1 = none ∧ rightResult.1 = none
      | some encoding => ∃ signature,
          signature.randomness = randomness ∧
          rightResult.1 = some signature ∧
          ∀ state : GlobalCausalHashState,
            leftResult.1 = some (globalSignatureRevealResult table request
              encoding allChains signature state).1) ∧
    HashCachesAgreeOn (GlobalSigningComparableHashInput parameter)
      leftResult.2 rightResult.2 ∧
    initialLeft ≤ leftResult.2 ∧ initialRight ≤ rightResult.2

set_option maxRecDepth 100000 in
theorem relTriple_keygenViews_globalSignAttempt_run
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1 ∈ support trajectoryProgrammedGlobalChainKeygen)
    (leftCache rightCache : QueryCache HashSpec)
    (hcacheAgreement : HashCachesAgreeOn
      (GlobalSigningComparableHashInput left.secretKey.parameter)
      leftCache rightCache)
    (hleftLe : left.cache ≤ leftCache)
    (hrightLe : right.1.cache ≤ rightCache)
    (request : SignRequest) (randomness : Randomness) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.signAttempt left.secretKey request.epoch request.message
          randomness)).run leftCache)
      ((simulateQ randomOracle
        (Concrete.signAttempt right.1.secretKey request.epoch request.message
          randomness)).run rightCache)
      (GlobalSignAttemptResultRelation right.2 left.secretKey.parameter
        request.epoch request.message randomness left.cache right.1.cache
          request) := by
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
  unfold Concrete.signAttempt
  simp only [simulateQ_bind, StateT.run_bind]
  rw [← hparameter]
  apply relTriple_bind
    (relTriple_globalEncodingHash_run left.secretKey.parameter leftCache
      rightCache hcacheAgreement request.epoch request.message randomness)
  intro leftDigestResult rightDigestResult hdigest
  have hdigestEq : leftDigestResult.1 = rightDigestResult.1 := hdigest.1
  rw [← hdigestEq]
  cases hdecode : TargetSum.decodeDigest leftDigestResult.1 with
  | none =>
      simp only [simulateQ_pure, StateT.run_pure]
      apply relTriple_pure_pure
      exact ⟨none, by simpa [hdigest.2.2.2.2.1] using hdecode,
        ⟨rfl, rfl⟩, hdigest.2.1, hleftLe.trans hdigest.2.2.1,
        hrightLe.trans hdigest.2.2.2.1⟩
  | some encoding =>
      have hleftRun := Concrete.keygen_signWithEncoding_run_eq_pure
        left.keyResult hleftKey hrel.2.1 leftDigestResult.2
        (hleftLe.trans hdigest.2.2.1) request.epoch randomness encoding
      have hrightRun := Concrete.keygen_signWithEncoding_run_eq_pure
        right.1.keyResult hrightKey hrel.2.2 rightDigestResult.2
        (hrightLe.trans hdigest.2.2.2.1) request.epoch randomness encoding
      rw [simulateQ_map, StateT.run_map, simulateQ_map, StateT.run_map]
      rw [show (simulateQ randomOracle
          (Concrete.signWithEncoding left.secretKey request.epoch randomness
            encoding)).run leftDigestResult.2 =
        pure (Concrete.CacheReplay.signWithEncoding leftDigestResult.2
          left.secretKey request.epoch randomness encoding,
            leftDigestResult.2) by
          simpa [ProgrammedGlobalChainKeygenView.keyResult] using hleftRun]
      rw [show (simulateQ randomOracle
          (Concrete.signWithEncoding right.1.secretKey request.epoch randomness
            encoding)).run rightDigestResult.2 =
        pure (Concrete.CacheReplay.signWithEncoding rightDigestResult.2
          right.1.secretKey request.epoch randomness encoding,
            rightDigestResult.2) by
          simpa [ProgrammedGlobalChainKeygenView.keyResult] using hrightRun]
      simp only [Functor.map]
      apply relTriple_pure_pure
      refine ⟨some encoding, ?_, ?_, hdigest.2.1,
        hleftLe.trans hdigest.2.2.1, hrightLe.trans hdigest.2.2.2.1⟩
      · simpa [hdigest.2.2.2.2.1] using hdecode
      · refine ⟨Concrete.CacheReplay.signWithEncoding rightDigestResult.2
          right.1.secretKey request.epoch randomness encoding, rfl, rfl, ?_⟩
        intro state
        exact congrArg some (keygenViews_signWithEncoding_eq_globalReveal
          left right hrel hleftSupport hrightSupport leftDigestResult.2
          rightDigestResult.2 (hleftLe.trans hdigest.2.2.1)
          (hrightLe.trans hdigest.2.2.2.1) request randomness encoding state)

def GlobalSignResultRelation
    (table : GlobalChainValueIndex → Digest)
    (parameter : PublicParameter) (request : SignRequest)
    (initialLeft initialRight : QueryCache HashSpec)
    (leftResult rightResult : Option Signature × QueryCache HashSpec) : Prop :=
  ∃ randomness,
    GlobalSignAttemptResultRelation table parameter request.epoch
      request.message randomness initialLeft initialRight request
        leftResult rightResult

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
theorem relTriple_keygenViews_globalSampledBoundedSignStep
    (attempts : Nat)
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1 ∈ support trajectoryProgrammedGlobalChainKeygen)
    (leftCache rightCache : QueryCache HashSpec)
    (hcacheAgreement : HashCachesAgreeOn
      (GlobalSigningComparableHashInput left.secretKey.parameter)
      leftCache rightCache)
    (hleftLe : left.cache ≤ leftCache)
    (hrightLe : right.1.cache ≤ rightCache)
    (request : SignRequest)
    (postcondition :
      (Option Signature × QueryCache HashSpec) →
      (Option Signature × QueryCache HashSpec) → Prop)
    (hcontinuation : ∀ randomness leftResult rightResult,
      GlobalSignAttemptResultRelation right.2 left.secretKey.parameter
        request.epoch request.message randomness left.cache right.1.cache
          request leftResult rightResult →
      RelTriple
        (Concrete.signBoundedAttemptsContinuation attempts left.secretKey
          request.epoch request.message leftResult)
        (Concrete.signBoundedAttemptsContinuation attempts right.1.secretKey
          request.epoch request.message rightResult)
        postcondition) :
    RelTriple
      (sampledBoundedSignStep attempts left.secretKey request leftCache)
      (sampledBoundedSignStep attempts right.1.secretKey request rightCache)
      postcondition := by
  unfold sampledBoundedSignStep
  rw [Concrete.signBoundedAttempts_run_succ_eq,
    Concrete.signBoundedAttempts_run_succ_eq]
  rw [← Concrete.signingRandomness_eq]
  refine relTriple_bind
    (R := fun leftRandomness rightRandomness : Randomness =>
      leftRandomness = rightRandomness)
    (S := postcondition)
    (fa := fun randomness =>
      (simulateQ randomOracle
        (Concrete.signAttempt left.secretKey request.epoch request.message
          randomness)).run leftCache >>=
        Concrete.signBoundedAttemptsContinuation attempts left.secretKey
          request.epoch request.message)
    (fb := fun randomness =>
      (simulateQ randomOracle
        (Concrete.signAttempt right.1.secretKey request.epoch request.message
          randomness)).run rightCache >>=
        Concrete.signBoundedAttemptsContinuation attempts right.1.secretKey
          request.epoch request.message)
    (relTriple_refl Concrete.signingRandomness) ?_
  intro leftRandomness rightRandomness heq
  subst rightRandomness
  apply relTriple_bind
    (S := postcondition)
    (fa := Concrete.signBoundedAttemptsContinuation attempts left.secretKey
      request.epoch request.message)
    (fb := Concrete.signBoundedAttemptsContinuation attempts right.1.secretKey
      request.epoch request.message)
    (relTriple_keygenViews_globalSignAttempt_run left right hrel hleftSupport
      hrightSupport leftCache rightCache hcacheAgreement hleftLe hrightLe
        request leftRandomness)
  exact hcontinuation leftRandomness

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
theorem relTriple_keygenViews_globalSignBoundedAttempts_succ_run
    (attempts : Nat)
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1 ∈ support trajectoryProgrammedGlobalChainKeygen)
    (leftCache rightCache : QueryCache HashSpec)
    (hcacheAgreement : HashCachesAgreeOn
      (GlobalSigningComparableHashInput left.secretKey.parameter)
      leftCache rightCache)
    (hleftLe : left.cache ≤ leftCache)
    (hrightLe : right.1.cache ≤ rightCache)
    (request : SignRequest) :
    RelTriple
      ((simulateQ xmssRomImpl
        (Concrete.signBoundedAttempts (attempts + 1) left.secretKey
          request.epoch request.message)).run leftCache)
      ((simulateQ xmssRomImpl
        (Concrete.signBoundedAttempts (attempts + 1) right.1.secretKey
          request.epoch request.message)).run rightCache)
      (GlobalSignResultRelation right.2 left.secretKey.parameter request
        left.cache right.1.cache) := by
  induction attempts generalizing leftCache rightCache with
  | zero =>
      rw [Concrete.signBoundedAttempts_run_succ_eq_sampledStep,
        Concrete.signBoundedAttempts_run_succ_eq_sampledStep]
      refine relTriple_keygenViews_globalSampledBoundedSignStep 0 left right
        hrel hleftSupport hrightSupport leftCache rightCache hcacheAgreement
          hleftLe hrightLe request
          (GlobalSignResultRelation right.2 left.secretKey.parameter request
            left.cache right.1.cache) ?_
      intro randomness leftResult rightResult hresult
      unfold Concrete.signBoundedAttemptsContinuation
      rcases hresult with
        ⟨decoded, hdecode, hoptions, hcaches, hleftFinal, hrightFinal⟩
      cases decoded with
      | none =>
          rcases hoptions with ⟨hleftNone, hrightNone⟩
          rw [hleftNone, hrightNone]
          simp only [Concrete.signBoundedAttempts, simulateQ_pure,
            StateT.run_pure]
          apply relTriple_pure_pure
          exact ⟨randomness, none, hdecode, ⟨rfl, rfl⟩, hcaches,
            hleftFinal, hrightFinal⟩
      | some encoding =>
          rcases hoptions with
            ⟨signature, hrandomness, hrightSome, hleftSome⟩
          rw [hrightSome]
          have hleft := hleftSome GlobalCausalHashState.empty
          rw [hleft]
          apply relTriple_pure_pure
          exact ⟨randomness, some encoding, hdecode,
            ⟨signature, hrandomness, rfl, fun state =>
              (hleftSome GlobalCausalHashState.empty).symm.trans
                (hleftSome state)⟩, hcaches,
            hleftFinal, hrightFinal⟩
  | succ attempts ih =>
      rw [Concrete.signBoundedAttempts_run_succ_eq_sampledStep,
        Concrete.signBoundedAttempts_run_succ_eq_sampledStep]
      refine relTriple_keygenViews_globalSampledBoundedSignStep (attempts + 1)
        left right hrel hleftSupport hrightSupport leftCache rightCache
          hcacheAgreement hleftLe hrightLe request
          (GlobalSignResultRelation right.2 left.secretKey.parameter request
            left.cache right.1.cache) ?_
      intro randomness leftResult rightResult hresult
      unfold Concrete.signBoundedAttemptsContinuation
      rcases hresult with
        ⟨decoded, hdecode, hoptions, hcaches, hleftFinal, hrightFinal⟩
      cases decoded with
      | none =>
          rcases hoptions with ⟨hleftNone, hrightNone⟩
          rw [hleftNone, hrightNone]
          exact ih leftResult.2 rightResult.2 hcaches hleftFinal hrightFinal
      | some encoding =>
          rcases hoptions with
            ⟨signature, hrandomness, hrightSome, hleftSome⟩
          rw [hrightSome]
          have hleft := hleftSome GlobalCausalHashState.empty
          rw [hleft]
          apply relTriple_pure_pure
          exact ⟨randomness, some encoding, hdecode,
            ⟨signature, hrandomness, rfl, fun state =>
              (hleftSome GlobalCausalHashState.empty).symm.trans
                (hleftSome state)⟩, hcaches,
            hleftFinal, hrightFinal⟩

set_option maxRecDepth 100000 in
theorem relTriple_keygenViews_globalSign_run
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1 ∈ support trajectoryProgrammedGlobalChainKeygen)
    (leftCache rightCache : QueryCache HashSpec)
    (hcacheAgreement : HashCachesAgreeOn
      (GlobalSigningComparableHashInput left.secretKey.parameter)
      leftCache rightCache)
    (hleftLe : left.cache ≤ leftCache)
    (hrightLe : right.1.cache ≤ rightCache)
    (request : SignRequest) :
    RelTriple
      ((simulateQ xmssRomImpl
        (Concrete.cappedScheme.sign left.publicKey left.secretKey
          request.epoch request.message)).run leftCache)
      ((simulateQ xmssRomImpl
        (Concrete.cappedScheme.sign right.1.publicKey right.1.secretKey
          request.epoch request.message)).run rightCache)
      (GlobalSignResultRelation right.2 left.secretKey.parameter request
        left.cache right.1.cache) := by
  simp only [Concrete.cappedScheme, Concrete.cappedSign_eq]
  have hlimit : signingAttemptLimit = (signingAttemptLimit - 1) + 1 := by
    norm_num [signingAttemptLimit]
  rw [hlimit]
  exact relTriple_keygenViews_globalSignBoundedAttempts_succ_run
    (signingAttemptLimit - 1) left right hrel hleftSupport hrightSupport
      leftCache rightCache hcacheAgreement hleftLe hrightLe request

end XmssSecurity.CappedChain
