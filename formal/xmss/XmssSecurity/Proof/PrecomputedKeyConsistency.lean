import XmssSecurity.Proof.CappedChain.TreeCacheStability
import XmssSecurity.Proof.PrecomputedKeygenCache

open OracleComp OracleSpec

namespace XmssSecurity

def PrecomputedKeyConsistent (keygenCache : QueryCache HashSpec)
    (secretKey : SecretKey) : Prop :=
  ∀ largerCache, keygenCache ≤ largerCache →
    ∀ epoch randomness encoding,
      Concrete.precomputedSignWithEncoding secretKey epoch randomness encoding =
        Concrete.CacheReplay.signWithEncoding largerCache secretKey epoch randomness encoding

theorem keygen_support_treeCacheStable
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅)) :
    CappedChain.TreeCacheStable keyResult.1.2.parameter keyResult.1.2.chainStart
      keyResult.2 := by
  let chain : ChainIndex := ⟨0, by norm_num [numChains]⟩
  let view : ProgrammedFixedChainKeygenView := {
    publicKey := keyResult.1.1
    secretKey := keyResult.1.2
    cache := keyResult.2
    table := keygenChainValueTable keyResult.2 keyResult.1.2 chain
  }
  apply CappedChain.actualFixedChainKeygen_support_treeCacheStable chain view
  unfold actualFixedChainKeygen
  rw [mem_support_bind_iff]
  exact ⟨keyResult, hkeyResult, by simp [view]⟩

theorem Concrete.precomputedKeygen_support_oldKeygen
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅)) :
    ((keyResult.1.1, Concrete.erasePrecomputation keyResult.1.2), keyResult.2) ∈
      support ((simulateQ romImpl Concrete.keygen).run ∅) := by
  have hmapped : ((Concrete.erasePrecomputedKeyResult keyResult.1, keyResult.2)) ∈
      support ((simulateQ romImpl
        (Concrete.erasePrecomputedKeyResult <$> Concrete.precomputedKeygen)).run ∅) := by
    rw [simulateQ_map, StateT.run_map, support_map]
    exact ⟨keyResult, hmem, rfl⟩
  rw [Concrete.erasePrecomputedKeygen_eq_keygen] at hmapped
  exact hmapped

theorem Concrete.oldKeygen_support_materializedPrecomputedKeygen
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅)) :
    Concrete.materializeCachedKeyResult keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅) := by
  apply (mem_support_iff_of_evalDist_eq
    Concrete.evalDist_materialized_keygen_eq_precomputedKeygen _).mp
  rw [support_map]
  exact ⟨keyResult, hmem, rfl⟩

theorem Concrete.precomputedKeygen_support_secretKey_components
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅)) :
    ∃ parameter secret,
      keyResult.1.2 = Concrete.precomputedSecretKey parameter secret keyResult.2 := by
  unfold Concrete.precomputedKeygen at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨parameter, parameterCache⟩, hparameter, hafterParameter⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hafterParameter
  obtain ⟨⟨secret, secretCache⟩, hsecret, hafterSecret⟩ := hafterParameter
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hafterSecret
  obtain ⟨⟨treeResult, rootCache⟩, hroot, hout⟩ := hafterSecret
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hout
  subst keyResult
  have hparameterCache : parameterCache = ∅ :=
    xmssRom_lift_probComp_cache_eq Concrete.samplePublicParameter ∅
      (parameter, parameterCache) hparameter
  have hsecretCache : secretCache = ∅ := by
    calc
      secretCache = parameterCache :=
        xmssRom_lift_probComp_cache_eq Concrete.sampleSecret parameterCache
          (secret, secretCache) hsecret
      _ = ∅ := hparameterCache
  have hroute :
      simulateQ romImpl
          (liftM (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest).withQueryLog) =
        simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest).withQueryLog := by
    simp only [romImpl]
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest).withQueryLog
  rw [hroute, hsecretCache] at hroot
  have hcache := hashCacheOfLog_eq_finalCache_of_empty
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest) (treeResult, rootCache) hroot
  exact ⟨parameter, secret, by simp only; rw [hcache]⟩

theorem Concrete.precomputedKeygen_support_consistent
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅)) :
    PrecomputedKeyConsistent keyResult.2 keyResult.1.2 := by
  obtain ⟨parameter, secret, hsecretKey⟩ :=
    Concrete.precomputedKeygen_support_secretKey_components keyResult hmem
  have hold := Concrete.precomputedKeygen_support_oldKeygen keyResult hmem
  have hstable := keygen_support_treeCacheStable
    ((keyResult.1.1, Concrete.erasePrecomputation keyResult.1.2), keyResult.2) hold
  intro largerCache hle epoch randomness encoding
  rw [hsecretKey] at hold hstable ⊢
  unfold Concrete.precomputedSignWithEncoding Concrete.CacheReplay.signWithEncoding
  congr 1
  · rw [Concrete.CacheReplay.precomputedSignedChainValues_eq]
    funext chain
    exact Concrete.keygen_chainWalk_eq_of_cache_le
      ((keyResult.1.1,
        Concrete.erasePrecomputation
          (Concrete.precomputedSecretKey parameter secret keyResult.2)), keyResult.2)
      hold largerCache hle epoch chain (encoding chain).val
        (Nat.le_pred_of_lt (encoding chain).isLt)
  · rw [Concrete.CacheReplay.precomputedAuthenticationPath_eq]
    exact CappedChain.TreeCacheStable.authenticationPath_eq
      (Concrete.precomputedSecretKey parameter secret keyResult.2) keyResult.2
      hstable largerCache hle epoch

theorem Concrete.precomputedKeygen_cache_none_encodingInput
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (targetEpoch : Epoch) (targetInput : Message × Randomness) :
    keyResult.2
      (Concrete.CacheView.encodingInput keyResult.1.2.parameter targetEpoch targetInput) =
        none := by
  let oldKeyResult : (PublicKey × SecretKey) × QueryCache HashSpec :=
    ((keyResult.1.1, Concrete.erasePrecomputation keyResult.1.2), keyResult.2)
  have hold := Concrete.precomputedKeygen_support_oldKeygen keyResult hmem
  exact Concrete.keygen_cache_none_encodingInput oldKeyResult hold targetEpoch targetInput

theorem Concrete.precomputedKeygen_chainWalk_eq_of_cache_le
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (epoch : Epoch) (chain : ChainIndex) (steps : Nat)
    (hsteps : steps ≤ chainLength - 1) :
    Wots.walk
        (Concrete.CacheView.chainStep keyResult.2 keyResult.1.2.parameter epoch chain)
        0 steps (keyResult.1.2.chainStart epoch chain) =
      Wots.walk
        (Concrete.CacheView.chainStep largerCache keyResult.1.2.parameter epoch chain)
        0 steps (keyResult.1.2.chainStart epoch chain) := by
  let oldKeyResult : (PublicKey × SecretKey) × QueryCache HashSpec :=
    ((keyResult.1.1, Concrete.erasePrecomputation keyResult.1.2), keyResult.2)
  have hold := Concrete.precomputedKeygen_support_oldKeygen keyResult hmem
  exact Concrete.keygen_chainWalk_eq_of_cache_le oldKeyResult hold largerCache hle epoch
    chain steps hsteps

theorem Concrete.precomputedKeygen_cache_has_chainInput
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (epoch : Epoch) (chain : ChainIndex) (step : ChainStep) :
    ∃ output, keyResult.2
      (Concrete.CacheView.chainInput keyResult.1.2.parameter epoch chain step
        (Wots.walk
          (Concrete.CacheView.chainStep keyResult.2 keyResult.1.2.parameter epoch chain)
          0 step.val (keyResult.1.2.chainStart epoch chain))) = some output := by
  let oldKeyResult : (PublicKey × SecretKey) × QueryCache HashSpec :=
    ((keyResult.1.1, Concrete.erasePrecomputation keyResult.1.2), keyResult.2)
  have hold := Concrete.precomputedKeygen_support_oldKeygen keyResult hmem
  exact Concrete.keygen_cache_has_chainInput oldKeyResult hold epoch chain step

theorem Concrete.precomputedKeygen_cache_chainInput_eq_none_of_ne
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (epoch : Epoch) (chain : ChainIndex) (step : ChainStep) (value : Digest)
    (hne : value ≠ Wots.walk
      (Concrete.CacheView.chainStep keyResult.2 keyResult.1.2.parameter epoch chain)
      0 step.val (keyResult.1.2.chainStart epoch chain)) :
    keyResult.2
      (Concrete.CacheView.chainInput keyResult.1.2.parameter epoch chain step value) = none := by
  let oldKeyResult : (PublicKey × SecretKey) × QueryCache HashSpec :=
    ((keyResult.1.1, Concrete.erasePrecomputation keyResult.1.2), keyResult.2)
  have hold := Concrete.precomputedKeygen_support_oldKeygen keyResult hmem
  exact Concrete.keygen_cache_chainInput_eq_none_of_ne oldKeyResult hold epoch chain step
    value hne

theorem Concrete.precomputedKeygen_cache_has_chainValue_preimage
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (epoch : Epoch) (chain : ChainIndex) (digit : Digit)
    (hpositive : 0 < digit.val) :
    ∃ previous : ChainStep, ∃ output,
      previous.val + 1 = digit.val ∧
      keyResult.2
        (Concrete.CacheView.chainInput keyResult.1.2.parameter epoch chain previous
          (Wots.walk
            (Concrete.CacheView.chainStep keyResult.2 keyResult.1.2.parameter epoch chain)
            0 previous.val (keyResult.1.2.chainStart epoch chain))) = some output ∧
      truncateHash output =
        Wots.signChain
          (Concrete.CacheView.chainStep keyResult.2 keyResult.1.2.parameter epoch chain)
          digit (keyResult.1.2.chainStart epoch chain) := by
  let oldKeyResult : (PublicKey × SecretKey) × QueryCache HashSpec :=
    ((keyResult.1.1, Concrete.erasePrecomputation keyResult.1.2), keyResult.2)
  have hold := Concrete.precomputedKeygen_support_oldKeygen keyResult hmem
  exact Concrete.keygen_cache_has_chainValue_preimage oldKeyResult hold epoch chain digit
    hpositive

theorem Concrete.precomputedKeygen_cache_has_merkleInput_in_largerCache
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (level : MerkleLevel) (node : MerkleNode)
    (hnode : node.val < 2 ^ (treeHeight - (level.val + 1))) :
    ∃ output, keyResult.2
      (Concrete.CacheView.merkleInput keyResult.1.2.parameter level node
        (Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node false))
        (Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node true))) = some output := by
  let oldKeyResult : (PublicKey × SecretKey) × QueryCache HashSpec :=
    ((keyResult.1.1, Concrete.erasePrecomputation keyResult.1.2), keyResult.2)
  have hold := Concrete.precomputedKeygen_support_oldKeygen keyResult hmem
  exact Concrete.keygen_cache_has_merkleInput_in_largerCache oldKeyResult hold largerCache
    hle level node hnode

theorem Concrete.precomputedKeygen_cache_merkleInput_eq_none_of_ne_in_largerCache
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (level : MerkleLevel) (node : MerkleNode)
    (hnode : node.val < 2 ^ (treeHeight - (level.val + 1)))
    (left right : Digest)
    (hne : (left, right) ≠
      (Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node false),
        Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node true))) :
    keyResult.2
      (Concrete.CacheView.merkleInput keyResult.1.2.parameter level node left right) = none := by
  let oldKeyResult : (PublicKey × SecretKey) × QueryCache HashSpec :=
    ((keyResult.1.1, Concrete.erasePrecomputation keyResult.1.2), keyResult.2)
  have hold := Concrete.precomputedKeygen_support_oldKeygen keyResult hmem
  exact Concrete.keygen_cache_merkleInput_eq_none_of_ne_in_largerCache oldKeyResult hold
    largerCache hle level node hnode left right hne

theorem Concrete.precomputedKeygen_merkleChildren_eq_of_cache_le
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (level : MerkleLevel) (node : MerkleNode)
    (hnode : node.val < 2 ^ (treeHeight - (level.val + 1))) :
    (Concrete.CacheReplay.treeNode keyResult.2 keyResult.1.2.parameter
        keyResult.1.2.chainStart level.val (Concrete.childNode node false),
      Concrete.CacheReplay.treeNode keyResult.2 keyResult.1.2.parameter
        keyResult.1.2.chainStart level.val (Concrete.childNode node true)) =
    (Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
        keyResult.1.2.chainStart level.val (Concrete.childNode node false),
      Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
        keyResult.1.2.chainStart level.val (Concrete.childNode node true)) := by
  let oldKeyResult : (PublicKey × SecretKey) × QueryCache HashSpec :=
    ((keyResult.1.1, Concrete.erasePrecomputation keyResult.1.2), keyResult.2)
  have hold := Concrete.precomputedKeygen_support_oldKeygen keyResult hmem
  exact Concrete.keygen_merkleChildren_eq_of_cache_le oldKeyResult hold largerCache hle
    level node hnode

end XmssSecurity
