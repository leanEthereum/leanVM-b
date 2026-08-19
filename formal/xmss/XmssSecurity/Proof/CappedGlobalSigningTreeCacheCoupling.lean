import XmssSecurity.Proof.CappedGlobalTreeKeygenCacheCoupling
import XmssSecurity.Proof.CappedGlobalSigningKeygenCoupling

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

theorem Concrete.CacheView.encodingInput_ne_chainInput
    (parameter : PublicParameter) (encodingEpoch epoch : Epoch)
    (message : Message) (randomness : Randomness) (chain : ChainIndex)
    (position : ChainStep) (value : Digest) :
    Concrete.CacheView.encodingInput parameter encodingEpoch
        (message, randomness) ≠
      Concrete.CacheView.chainInput parameter epoch chain position value := by
  intro heq
  have hdomain := domain_eq_of_tweakableHashInput_eq parameter heq
  simp at hdomain

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

theorem Concrete.CacheView.encodingInput_ne_merkleInput
    (parameter : PublicParameter) (epoch : Epoch)
    (message : Message) (randomness : Randomness) (level : MerkleLevel)
    (node : MerkleNode) (left right : Digest) :
    Concrete.CacheView.encodingInput parameter epoch (message, randomness) ≠
      Concrete.CacheView.merkleInput parameter level node left right := by
  intro heq
  have hdomain := domain_eq_of_tweakableHashInput_eq parameter heq
  simp at hdomain

theorem Concrete.CacheView.chainStep_cacheQuery_encodingInput
    (cache : QueryCache HashSpec) (output : HashOutput)
    (parameter : PublicParameter) (encodingEpoch epoch : Epoch)
    (message : Message) (randomness : Randomness) (chain : ChainIndex) :
    Concrete.CacheView.chainStep
        (cache.cacheQuery
          (Concrete.CacheView.encodingInput parameter encodingEpoch
            (message, randomness)) output)
        parameter epoch chain =
      Concrete.CacheView.chainStep cache parameter epoch chain := by
  funext position value
  unfold Concrete.CacheView.chainStep
  split
  · unfold Concrete.CacheView.digestAt
    rw [QueryCache.cacheQuery_of_ne]
    exact (Concrete.CacheView.encodingInput_ne_chainInput parameter
      encodingEpoch epoch message randomness chain _ value).symm
  · rfl

theorem Concrete.CacheReplay.oneTimePublicKey_cacheQuery_encodingInput
    (cache : QueryCache HashSpec) (output : HashOutput)
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (encodingEpoch epoch : Epoch) (message : Message)
    (randomness : Randomness) :
    Concrete.CacheReplay.oneTimePublicKey
        (cache.cacheQuery
          (Concrete.CacheView.encodingInput parameter encodingEpoch
            (message, randomness)) output)
        parameter secret epoch =
      Concrete.CacheReplay.oneTimePublicKey cache parameter secret epoch := by
  unfold Concrete.CacheReplay.oneTimePublicKey
  funext chain
  rw [Concrete.CacheView.chainStep_cacheQuery_encodingInput]

theorem ReplayEndpointsMatch.cacheQuery_encodingInput
    (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest)
    (endpoints : Epoch → ChainIndex → Digest)
    (cache : QueryCache HashSpec)
    (hrel : ReplayEndpointsMatch parameter secret endpoints cache)
    (encodingEpoch : Epoch) (message : Message) (randomness : Randomness)
    (output : HashOutput) :
    ReplayEndpointsMatch parameter secret endpoints
      (cache.cacheQuery
        (Concrete.CacheView.encodingInput parameter encodingEpoch
          (message, randomness)) output) := by
  intro epoch
  rw [Concrete.CacheReplay.oneTimePublicKey_cacheQuery_encodingInput]
  exact hrel epoch

theorem GlobalTreeCacheCorrespondence.cacheQuery_encodingInput
    (parameter : PublicParameter)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec)
    (hrel : GlobalTreeCacheCorrespondence parameter leftEndpoints
      rightEndpoints leftCache rightCache)
    (epoch : Epoch) (message : Message) (randomness : Randomness)
    (output : HashOutput) :
    GlobalTreeCacheCorrespondence parameter leftEndpoints rightEndpoints
      (leftCache.cacheQuery
        (Concrete.CacheView.encodingInput parameter epoch
          (message, randomness)) output)
      (rightCache.cacheQuery
        (Concrete.CacheView.encodingInput parameter epoch
          (message, randomness)) output) := by
  constructor
  · apply hrel.merkle.cacheQuery_distinct
    · intro input hinput
      obtain ⟨level, node, haddress⟩ := hinput
      intro heq
      have hencoding : AtHashAddress parameter (.encoding epoch) input := by
        rw [heq]
        simp [Concrete.CacheView.encodingInput]
      have hdomain := atHashAddress_unique parameter (.merkle level node)
        (.encoding epoch) input haddress hencoding
      simp at hdomain
    · intro input hinput
      obtain ⟨level, node, haddress⟩ := hinput
      intro heq
      have hencoding : AtHashAddress parameter (.encoding epoch) input := by
        rw [heq]
        simp [Concrete.CacheView.encodingInput]
      have hdomain := atHashAddress_unique parameter (.merkle level node)
        (.encoding epoch) input haddress hencoding
      simp at hdomain
  · apply hrel.leaves.cacheQuery_distinct
    · intro candidate
      exact Concrete.CacheView.encodingInput_ne_leafInput parameter epoch
        candidate message randomness (leftEndpoints candidate)
    · intro candidate
      exact Concrete.CacheView.encodingInput_ne_leafInput parameter epoch
        candidate message randomness (rightEndpoints candidate)

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

set_option maxRecDepth 1000000 in
theorem relTriple_trajectoryProgrammedGlobalChainKeygen_withBase_fullCacheStable :
    RelTriple trajectoryProgrammedGlobalChainKeygen
      (trajectoryProgrammedGlobalChainKeygen >>= fun keyView =>
        ($ᵗ (GlobalChainValueIndex → Digest)) >>= fun base =>
        pure (keyView, base))
      ProgrammedGlobalChainKeygenFullCacheStableRelation := by
  apply relTriple_post_mono
    (relTriple_with_support
      relTriple_trajectoryProgrammedGlobalChainKeygen_withBase_fullCache)
  intro left right hrel
  obtain ⟨hfull, hleftSupport, hrightSupport⟩ := hrel
  have hrightViewSupport : right.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen :=
    trajectoryProgrammedWithBase_support_keyViews right hrightSupport
  have hleftKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    left hleftSupport
  have hrightKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    right.1 hrightViewSupport
  have hparameter : left.secretKey.parameter =
      right.1.secretKey.parameter := by
    calc
      left.secretKey.parameter = left.publicKey.parameter :=
        (keygen_parameter_eq left.keyResult hleftKey).symm
      _ = right.1.publicKey.parameter :=
        congrArg PublicKey.parameter hfull.1.1.2.1
      _ = right.1.secretKey.parameter :=
        keygen_parameter_eq right.1.keyResult hrightKey
  obtain ⟨leftEndpoints, rightEndpoints, hcache, hleftReplay,
    hrightReplay⟩ := hfull.2
  refine ⟨hfull,
    trajectoryProgrammedGlobalChainKeygen_support_treeCacheStable left
      hleftSupport,
    trajectoryProgrammedGlobalChainKeygen_support_treeCacheStable right.1
      hrightViewSupport,
    leftEndpoints, rightEndpoints, hcache, hleftReplay, ?_⟩
  rw [hparameter]
  exact hrightReplay

theorem GlobalTreeSigningCacheRelation.cacheQuery_encodingInput
    (parameter : PublicParameter)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec)
    (hrel : GlobalTreeSigningCacheRelation parameter leftSecret rightSecret
      leftCache rightCache)
    (epoch : Epoch) (message : Message) (randomness : Randomness)
    (output : HashOutput) :
    GlobalTreeSigningCacheRelation parameter leftSecret rightSecret
      (leftCache.cacheQuery
        (Concrete.CacheView.encodingInput parameter epoch
          (message, randomness)) output)
      (rightCache.cacheQuery
        (Concrete.CacheView.encodingInput parameter epoch
          (message, randomness)) output) := by
  obtain ⟨leftEndpoints, rightEndpoints, hcache, hleft, hright⟩ := hrel
  exact ⟨leftEndpoints, rightEndpoints,
    hcache.cacheQuery_encodingInput parameter leftEndpoints rightEndpoints
      leftCache rightCache epoch message randomness output,
    ReplayEndpointsMatch.cacheQuery_encodingInput parameter leftSecret
      leftEndpoints leftCache hleft epoch message randomness output,
    ReplayEndpointsMatch.cacheQuery_encodingInput parameter rightSecret
      rightEndpoints rightCache hright epoch message randomness output⟩

def GlobalEncodingHashFullResultRelation
    (parameter : PublicParameter)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (initialLeft initialRight : QueryCache HashSpec)
    (epoch : Epoch) (message : Message) (randomness : Randomness)
    (leftResult rightResult : Digest × QueryCache HashSpec) : Prop :=
  leftResult.1 = rightResult.1 ∧
    HashCachesAgreeOn (GlobalSigningComparableHashInput parameter)
      leftResult.2 rightResult.2 ∧
    initialLeft ≤ leftResult.2 ∧ initialRight ≤ rightResult.2 ∧
    Concrete.CacheView.encodingHash leftResult.2 parameter epoch
      (message, randomness) = leftResult.1 ∧
    Concrete.CacheView.encodingHash rightResult.2 parameter epoch
      (message, randomness) = rightResult.1 ∧
    GlobalTreeSigningCacheRelation parameter leftSecret rightSecret
      leftResult.2 rightResult.2

set_option maxRecDepth 1000000 in
theorem relTriple_globalEncodingHash_run_full
    (parameter : PublicParameter)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (GlobalSigningComparableHashInput parameter) left right)
    (htree : GlobalTreeSigningCacheRelation parameter leftSecret rightSecret
      left right)
    (epoch : Epoch) (message : Message) (randomness : Randomness) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.encodingHash parameter epoch message randomness)).run left)
      ((simulateQ randomOracle
        (Concrete.encodingHash parameter epoch message randomness)).run right)
      (GlobalEncodingHashFullResultRelation parameter leftSecret rightSecret
        left right epoch message randomness) := by
  let input := Concrete.CacheView.encodingInput parameter epoch
    (message, randomness)
  have hinput : GlobalSigningComparableHashInput parameter input :=
    ⟨epoch, message, randomness, rfl⟩
  have hraw : RelTriple
      ((randomOracle input).run left)
      ((randomOracle input).run right)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          HashCachesAgreeOn (GlobalSigningComparableHashInput parameter)
            leftResult.2 rightResult.2 ∧
          left ≤ leftResult.2 ∧ right ≤ rightResult.2 ∧
          GlobalTreeSigningCacheRelation parameter leftSecret rightSecret
            leftResult.2 rightResult.2) := by
    cases hleft : left input with
    | none =>
        have hright : right input = none := by
          rw [← hagrees input hinput]
          exact hleft
        rw [randomOracle, QueryImpl.withCaching_run_none _ hleft,
          QueryImpl.withCaching_run_none _ hright,
          map_eq_bind_pure_comp, map_eq_bind_pure_comp]
        apply relTriple_bind (relTriple_refl ($ᵗ HashOutput))
        intro leftOutput rightOutput houtput
        subst rightOutput
        exact relTriple_pure_pure ⟨rfl,
          hagrees.cacheQuery (GlobalSigningComparableHashInput parameter)
            left right input leftOutput,
          QueryCache.le_cacheQuery left hleft,
          QueryCache.le_cacheQuery right hright,
          htree.cacheQuery_encodingInput parameter leftSecret rightSecret
            left right epoch message randomness leftOutput⟩
    | some output =>
        have hright : right input = some output := by
          rw [← hagrees input hinput]
          exact hleft
        rw [randomOracle, QueryImpl.withCaching_run_some _ hleft,
          QueryImpl.withCaching_run_some _ hright]
        exact relTriple_pure_pure ⟨rfl, hagrees, le_rfl, le_rfl, htree⟩
  have hmapped : RelTriple
      ((fun result : HashOutput × QueryCache HashSpec =>
        (truncateHash result.1, result.2)) <$> (randomOracle input).run left)
      ((fun result : HashOutput × QueryCache HashSpec =>
        (truncateHash result.1, result.2)) <$> (randomOracle input).run right)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          HashCachesAgreeOn (GlobalSigningComparableHashInput parameter)
            leftResult.2 rightResult.2 ∧
          left ≤ leftResult.2 ∧ right ≤ rightResult.2 ∧
          GlobalTreeSigningCacheRelation parameter leftSecret rightSecret
            leftResult.2 rightResult.2) := by
    apply relTriple_map
    apply relTriple_post_mono hraw
    intro leftResult rightResult hresult
    exact ⟨congrArg truncateHash hresult.1, hresult.2⟩
  have hstrengthened := relTriple_strengthen_support hmapped
    (fun result hresult => encodingHash_run_cache_eq parameter left result.2
      epoch message randomness result.1 (by
        simpa [Concrete.encodingHash, Concrete.tweakableHash,
          Concrete.oracleHash, Concrete.CacheView.encodingInput,
          map_eq_bind_pure_comp, input] using hresult))
    (fun result hresult => encodingHash_run_cache_eq parameter right result.2
      epoch message randomness result.1 (by
        simpa [Concrete.encodingHash, Concrete.tweakableHash,
          Concrete.oracleHash, Concrete.CacheView.encodingInput,
          map_eq_bind_pure_comp, input] using hresult))
  apply relTriple_post_mono hstrengthened
  intro leftResult rightResult hresult
  exact ⟨hresult.1.1, hresult.1.2.1, hresult.1.2.2.1,
    hresult.1.2.2.2.1, hresult.2.1, hresult.2.2,
    hresult.1.2.2.2.2⟩

def GlobalSignAttemptFullResultRelation
    (table : GlobalChainValueIndex → Digest)
    (parameter : PublicParameter)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (message : Message) (randomness : Randomness)
    (initialLeft initialRight : QueryCache HashSpec) (request : SignRequest)
    (leftResult rightResult : Option Signature × QueryCache HashSpec) : Prop :=
  GlobalSignAttemptResultRelation table parameter epoch message randomness
      initialLeft initialRight request leftResult rightResult ∧
    GlobalTreeSigningCacheRelation parameter leftSecret rightSecret
      leftResult.2 rightResult.2

set_option maxRecDepth 1000000 in
theorem relTriple_keygenViews_globalSignAttempt_run_full
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
    (htree : GlobalTreeSigningCacheRelation left.secretKey.parameter
      left.secretKey.chainStart right.1.secretKey.chainStart
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
      (GlobalSignAttemptFullResultRelation right.2 left.secretKey.parameter
        left.secretKey.chainStart right.1.secretKey.chainStart request.epoch
          request.message randomness left.cache right.1.cache request) := by
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
    (relTriple_globalEncodingHash_run_full left.secretKey.parameter
      left.secretKey.chainStart right.1.secretKey.chainStart leftCache
        rightCache hcacheAgreement htree request.epoch request.message
          randomness)
  intro leftDigestResult rightDigestResult hdigest
  unfold GlobalEncodingHashFullResultRelation at hdigest
  obtain ⟨hdigestEq, hcaches, hleftFinal, hrightFinal,
    hleftHash, _hrightHash, htreeFinal⟩ := hdigest
  rw [← hdigestEq]
  cases hdecode : TargetSum.decodeDigest leftDigestResult.1 with
  | none =>
      simp only [simulateQ_pure, StateT.run_pure]
      apply relTriple_pure_pure
      refine ⟨⟨none, ?_, ⟨rfl, rfl⟩, hcaches,
        hleftLe.trans hleftFinal, hrightLe.trans hrightFinal⟩, htreeFinal⟩
      simpa [hleftHash] using hdecode
  | some encoding =>
      have hleftRun := Concrete.keygen_signWithEncoding_run_eq_pure
        left.keyResult hleftKey hrel.2.1 leftDigestResult.2
        (hleftLe.trans hleftFinal) request.epoch randomness encoding
      have hrightRun := Concrete.keygen_signWithEncoding_run_eq_pure
        right.1.keyResult hrightKey hrel.2.2 rightDigestResult.2
        (hrightLe.trans hrightFinal) request.epoch randomness encoding
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
      refine ⟨⟨some encoding, ?_, ?_, hcaches,
        hleftLe.trans hleftFinal, hrightLe.trans hrightFinal⟩, htreeFinal⟩
      · simpa [hleftHash] using hdecode
      · refine ⟨Concrete.CacheReplay.signWithEncoding rightDigestResult.2
          right.1.secretKey request.epoch randomness encoding, rfl, rfl, ?_⟩
        intro state
        exact congrArg some (keygenViews_signWithEncoding_eq_globalReveal
          left right hrel hleftSupport hrightSupport leftDigestResult.2
          rightDigestResult.2 (hleftLe.trans hleftFinal)
          (hrightLe.trans hrightFinal) request randomness encoding state)

def GlobalSignFullResultRelation
    (table : GlobalChainValueIndex → Digest)
    (parameter : PublicParameter)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (request : SignRequest) (initialLeft initialRight : QueryCache HashSpec)
    (leftResult rightResult : Option Signature × QueryCache HashSpec) : Prop :=
  GlobalSignResultRelation table parameter request initialLeft initialRight
      leftResult rightResult ∧
    GlobalTreeSigningCacheRelation parameter leftSecret rightSecret
      leftResult.2 rightResult.2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
theorem relTriple_keygenViews_globalSampledBoundedSignStep_full
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
    (htree : GlobalTreeSigningCacheRelation left.secretKey.parameter
      left.secretKey.chainStart right.1.secretKey.chainStart
      leftCache rightCache)
    (hleftLe : left.cache ≤ leftCache)
    (hrightLe : right.1.cache ≤ rightCache)
    (request : SignRequest)
    (postcondition :
      (Option Signature × QueryCache HashSpec) →
      (Option Signature × QueryCache HashSpec) → Prop)
    (hcontinuation : ∀ randomness leftResult rightResult,
      GlobalSignAttemptFullResultRelation right.2 left.secretKey.parameter
        left.secretKey.chainStart right.1.secretKey.chainStart request.epoch
          request.message randomness left.cache right.1.cache request
            leftResult rightResult →
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
    (relTriple_keygenViews_globalSignAttempt_run_full left right hrel
      hleftSupport hrightSupport leftCache rightCache hcacheAgreement htree
        hleftLe hrightLe request leftRandomness)
  exact hcontinuation leftRandomness

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
theorem relTriple_keygenViews_globalSignBoundedAttempts_succ_run_full
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
    (htree : GlobalTreeSigningCacheRelation left.secretKey.parameter
      left.secretKey.chainStart right.1.secretKey.chainStart
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
      (GlobalSignFullResultRelation right.2 left.secretKey.parameter
        left.secretKey.chainStart right.1.secretKey.chainStart request
          left.cache right.1.cache) := by
  induction attempts generalizing leftCache rightCache with
  | zero =>
      rw [Concrete.signBoundedAttempts_run_succ_eq_sampledStep,
        Concrete.signBoundedAttempts_run_succ_eq_sampledStep]
      refine relTriple_keygenViews_globalSampledBoundedSignStep_full 0 left
        right hrel hleftSupport hrightSupport leftCache rightCache
          hcacheAgreement htree hleftLe hrightLe request
          (GlobalSignFullResultRelation right.2 left.secretKey.parameter
            left.secretKey.chainStart right.1.secretKey.chainStart request
              left.cache right.1.cache) ?_
      intro randomness leftResult rightResult hresult
      unfold Concrete.signBoundedAttemptsContinuation
      obtain ⟨hattempt, htreeFinal⟩ := hresult
      rcases hattempt with
        ⟨decoded, hdecode, hoptions, hcaches, hleftFinal, hrightFinal⟩
      cases decoded with
      | none =>
          rcases hoptions with ⟨hleftNone, hrightNone⟩
          rw [hleftNone, hrightNone]
          simp only [Concrete.signBoundedAttempts, simulateQ_pure,
            StateT.run_pure]
          apply relTriple_pure_pure
          exact ⟨⟨randomness, none, hdecode, ⟨rfl, rfl⟩, hcaches,
            hleftFinal, hrightFinal⟩, htreeFinal⟩
      | some encoding =>
          rcases hoptions with
            ⟨signature, hrandomness, hrightSome, hleftSome⟩
          rw [hrightSome]
          have hleft := hleftSome GlobalCausalHashState.empty
          rw [hleft]
          apply relTriple_pure_pure
          exact ⟨⟨randomness, some encoding, hdecode,
            ⟨signature, hrandomness, rfl, fun state =>
              (hleftSome GlobalCausalHashState.empty).symm.trans
                (hleftSome state)⟩, hcaches, hleftFinal, hrightFinal⟩,
            htreeFinal⟩
  | succ attempts ih =>
      rw [Concrete.signBoundedAttempts_run_succ_eq_sampledStep,
        Concrete.signBoundedAttempts_run_succ_eq_sampledStep]
      refine relTriple_keygenViews_globalSampledBoundedSignStep_full
        (attempts + 1) left right hrel hleftSupport hrightSupport leftCache
          rightCache hcacheAgreement htree hleftLe hrightLe request
          (GlobalSignFullResultRelation right.2 left.secretKey.parameter
            left.secretKey.chainStart right.1.secretKey.chainStart request
              left.cache right.1.cache) ?_
      intro randomness leftResult rightResult hresult
      unfold Concrete.signBoundedAttemptsContinuation
      obtain ⟨hattempt, htreeFinal⟩ := hresult
      rcases hattempt with
        ⟨decoded, hdecode, hoptions, hcaches, hleftFinal, hrightFinal⟩
      cases decoded with
      | none =>
          rcases hoptions with ⟨hleftNone, hrightNone⟩
          rw [hleftNone, hrightNone]
          exact ih leftResult.2 rightResult.2 hcaches htreeFinal hleftFinal
            hrightFinal
      | some encoding =>
          rcases hoptions with
            ⟨signature, hrandomness, hrightSome, hleftSome⟩
          rw [hrightSome]
          have hleft := hleftSome GlobalCausalHashState.empty
          rw [hleft]
          apply relTriple_pure_pure
          exact ⟨⟨randomness, some encoding, hdecode,
            ⟨signature, hrandomness, rfl, fun state =>
              (hleftSome GlobalCausalHashState.empty).symm.trans
                (hleftSome state)⟩, hcaches, hleftFinal, hrightFinal⟩,
            htreeFinal⟩

set_option maxRecDepth 1000000 in
theorem relTriple_keygenViews_globalSign_run_full
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
    (htree : GlobalTreeSigningCacheRelation left.secretKey.parameter
      left.secretKey.chainStart right.1.secretKey.chainStart
      leftCache rightCache)
    (hleftLe : left.cache ≤ leftCache)
    (hrightLe : right.1.cache ≤ rightCache)
    (request : SignRequest) :
    RelTriple
      ((simulateQ xmssRomImpl
        (Concrete.scheme.sign left.publicKey
          (Concrete.materializePrecomputation left.cache left.secretKey)
          request.epoch request.message)).run leftCache)
      ((simulateQ xmssRomImpl
        (Concrete.scheme.sign right.1.publicKey
          (Concrete.materializePrecomputation right.1.cache right.1.secretKey)
          request.epoch request.message)).run rightCache)
      (GlobalSignFullResultRelation right.2 left.secretKey.parameter
        left.secretKey.chainStart right.1.secretKey.chainStart request
          left.cache right.1.cache) := by
  simp only [Concrete.scheme]
  have hleftKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    left hleftSupport
  have hrightKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    right.1 hrightSupport
  apply relTriple_of_evalDist_eq_left
    (Concrete.evalDist_precomputedCappedSign_materialized_eq_cappedSign
      left.keyResult hleftKey hrel.2.1 leftCache hleftLe
        request.epoch request.message)
  apply relTriple_of_evalDist_eq_right
    (Concrete.evalDist_precomputedCappedSign_materialized_eq_cappedSign
      right.1.keyResult hrightKey hrel.2.2 rightCache hrightLe
        request.epoch request.message).symm
  rw [Concrete.cappedSign_eq, Concrete.cappedSign_eq]
  have hlimit : signingAttemptLimit = (signingAttemptLimit - 1) + 1 := by
    norm_num [signingAttemptLimit]
  rw [hlimit]
  exact relTriple_keygenViews_globalSignBoundedAttempts_succ_run_full
    (signingAttemptLimit - 1) left right hrel hleftSupport hrightSupport
      leftCache rightCache hcacheAgreement htree hleftLe hrightLe request

def GlobalSigningQueryFullResultRelation
    (parameter : PublicParameter)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftBase rightBase : QueryCache HashSpec)
    (table : GlobalChainValueIndex → Digest)
    (leftResult : Option Signature × QueryCache HashSpec)
    (rightResult : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) : Prop :=
  GlobalSigningQueryResultRelation parameter leftBase rightBase table
      leftResult rightResult ∧
    GlobalTreeSigningCacheRelation parameter leftSecret rightSecret
      leftResult.2 rightResult.1.2.cache

set_option maxRecDepth 1000000 in
theorem relTriple_keygenViews_globalCausalSigningQuery_run_full
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1 ∈ support trajectoryProgrammedGlobalChainKeygen)
    (leftCache : QueryCache HashSpec) (rightState : GlobalCausalHashState)
    (hcacheAgreement : HashCachesAgreeOn
      (GlobalSigningComparableHashInput left.secretKey.parameter)
      leftCache rightState.cache)
    (htree : GlobalTreeSigningCacheRelation left.secretKey.parameter
      left.secretKey.chainStart right.1.secretKey.chainStart
      leftCache rightState.cache)
    (hleftLe : left.cache ≤ leftCache)
    (hrightLe : right.1.cache ≤ rightState.cache)
    (hkeygenCache : rightState.keygenCache = right.1.cache)
    (hreveals : GlobalSigningRevealsAgree right.2 rightState)
    (request : SignRequest) :
    RelTriple
      ((simulateQ xmssRomImpl
        (Concrete.scheme.sign left.publicKey
          (Concrete.materializePrecomputation left.cache left.secretKey)
          request.epoch request.message)).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.2)
        (globalCausalSigningQueryAfterRealRom right.1.publicKey
          (Concrete.materializePrecomputation right.1.cache right.1.secretKey)
            request rightState)).run)
      (GlobalSigningQueryFullResultRelation left.secretKey.parameter
        left.secretKey.chainStart right.1.secretKey.chainStart left.cache
          right.1.cache right.2) := by
  have hsign := relTriple_keygenViews_globalSign_run_full left right hrel
    hleftSupport hrightSupport leftCache rightState.cache hcacheAgreement htree
      hleftLe hrightLe request
  rw [simulate_eagerTrace_globalCausalSigningQueryAfterRealRom]
  rw [show
    (simulateQ xmssRomImpl
      (Concrete.scheme.sign left.publicKey
        (Concrete.materializePrecomputation left.cache left.secretKey)
        request.epoch request.message)).run leftCache =
      ((simulateQ xmssRomImpl
        (Concrete.scheme.sign left.publicKey
          (Concrete.materializePrecomputation left.cache left.secretKey)
          request.epoch request.message)).run leftCache >>= pure) by simp]
  apply relTriple_bind hsign
  intro leftSigned rightSigned hsigned
  obtain ⟨hsigned, htreeSigned⟩ := hsigned
  rcases hsigned with ⟨randomness, decoded, hdecode, hoptions,
    hcaches, hleftFinal, hrightFinal⟩
  cases decoded with
  | none =>
      rcases hoptions with ⟨hleftNone, hrightNone⟩
      rw [hrightNone]
      simp only [revealGlobalSignatureOption_run, simulateQ_pure,
        WriterT.run_pure]
      apply relTriple_pure_pure
      exact ⟨⟨hleftNone, hcaches, hleftFinal, hrightFinal,
        hkeygenCache, hreveals.setCache rightSigned.2⟩, htreeSigned⟩
  | some encoding =>
      rcases hoptions with
        ⟨signature, hrandomness, hrightSome, hleftRevealed⟩
      rw [hrightSome]
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
      have hencodingHash :
          Concrete.CacheView.encodingHash leftSigned.2
              left.secretKey.parameter request.epoch
                (request.message, randomness) =
            Concrete.CacheView.encodingHash rightSigned.2
              right.1.secretKey.parameter request.epoch
                (request.message, randomness) := by
        rw [← hparameter]
        unfold Concrete.CacheView.encodingHash Concrete.CacheView.digestAt
        rw [hcaches _ ⟨request.epoch, request.message, randomness, rfl⟩]
      have hdecodeRight : TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash rightSigned.2
            right.1.secretKey.parameter request.epoch
              (request.message, signature.randomness)) = some encoding := by
        rw [hrandomness, ← hencodingHash]
        exact hdecode
      have hreveal :
          revealGlobalSignatureOption
              (Concrete.materializePrecomputation right.1.cache right.1.secretKey)
                request (some signature) =
            revealGlobalSignatureOption right.1.secretKey request
              (some signature) := by
        unfold revealGlobalSignatureOption
        rfl
      rw [hreveal]
      rw [simulate_eagerTrace_revealGlobalSignatureOption_some_of_decode
        right.2 right.1.secretKey request signature
          { rightState with cache := rightSigned.2 } encoding hdecodeRight]
      apply relTriple_pure_pure
      unfold GlobalSigningQueryFullResultRelation
        GlobalSigningQueryResultRelation
      simp only [globalSignatureRevealResult_cache,
        globalSignatureRevealResult_keygenCache]
      refine ⟨⟨hleftRevealed { rightState with cache := rightSigned.2 },
        hcaches, hleftFinal, hrightFinal, hkeygenCache, ?_⟩, htreeSigned⟩
      exact (hreveals.setCache rightSigned.2).globalSignatureRevealResult
        request encoding allChains signature

end XmssSecurity.CappedChain
