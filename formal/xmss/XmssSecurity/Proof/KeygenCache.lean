import XmssSecurity.Proof.MerkleQueryBound
import XmssSecurity.Proof.Execution
import XmssSecurity.Proof.LazyScheme

open OracleComp OracleSpec

namespace XmssSecurity

theorem Concrete.keygen_support_rootTree
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅)) :
    ∃ parameter secret root,
      keyResult.1 = (⟨root, parameter⟩,
        SecretKey.withoutPrecomputation parameter secret) ∧
      (root, keyResult.2) ∈ support
        ((simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run ∅) := by
  unfold Concrete.keygen at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨parameter, parameterCache⟩, hparameter, hafterParameter⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hafterParameter
  obtain ⟨⟨secret, secretCache⟩, hsecret, hafterSecret⟩ := hafterParameter
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hafterSecret
  obtain ⟨⟨root, rootCache⟩, hroot, hout⟩ := hafterSecret
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hout
  cases hout
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
            OracleComp HashSpec Digest)) =
        simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest) := by
    simp only [romImpl]
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)
  rw [hroute, hsecretCache] at hroot
  exact ⟨parameter, secret, root, rfl, hroot⟩

theorem Concrete.keygen_cache_unique_leafAddress
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (targetEpoch : Epoch) (left right : HashInput)
    (leftOutput rightOutput : HashOutput)
    (hleftP : AtHashAddress keyResult.1.2.parameter (.leaf targetEpoch) left)
    (hrightP : AtHashAddress keyResult.1.2.parameter (.leaf targetEpoch) right)
    (hleft : keyResult.2 left = some leftOutput)
    (hright : keyResult.2 right = some rightOutput) :
    left = right := by
  obtain ⟨parameter, secret, root, hkey, hroot⟩ :=
    Concrete.keygen_support_rootTree keyResult hmem
  rw [hkey] at hleftP hrightP
  exact Concrete.CacheReplay.rootTree_cache_unique_leafAddress parameter secret root
    keyResult.2 hroot targetEpoch left right leftOutput rightOutput
    hleftP hrightP hleft hright

theorem Concrete.keygen_cache_unique_chainAddress
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (targetEpoch : Epoch) (targetChain : ChainIndex) (targetStep : ChainStep)
    (left right : HashInput) (leftOutput rightOutput : HashOutput)
    (hleftP : AtHashAddress keyResult.1.2.parameter
      (.chain targetEpoch targetChain targetStep) left)
    (hrightP : AtHashAddress keyResult.1.2.parameter
      (.chain targetEpoch targetChain targetStep) right)
    (hleft : keyResult.2 left = some leftOutput)
    (hright : keyResult.2 right = some rightOutput) :
    left = right := by
  obtain ⟨parameter, secret, root, hkey, hroot⟩ :=
    Concrete.keygen_support_rootTree keyResult hmem
  rw [hkey] at hleftP hrightP
  exact Concrete.CacheReplay.rootTree_cache_unique_chainAddress parameter secret root
    keyResult.2 hroot targetEpoch targetChain targetStep left right leftOutput rightOutput
    hleftP hrightP hleft hright

theorem Concrete.keygen_cache_unique_merkleAddress
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (targetLevel : MerkleLevel) (targetNode : MerkleNode)
    (left right : HashInput) (leftOutput rightOutput : HashOutput)
    (hleftP : AtHashAddress keyResult.1.2.parameter
      (.merkle targetLevel targetNode) left)
    (hrightP : AtHashAddress keyResult.1.2.parameter
      (.merkle targetLevel targetNode) right)
    (hleft : keyResult.2 left = some leftOutput)
    (hright : keyResult.2 right = some rightOutput) :
    left = right := by
  obtain ⟨parameter, secret, root, hkey, hroot⟩ :=
    Concrete.keygen_support_rootTree keyResult hmem
  rw [hkey] at hleftP hrightP
  exact Concrete.CacheReplay.rootTree_cache_unique_merkleAddress parameter secret root
    keyResult.2 hroot targetLevel targetNode left right leftOutput rightOutput
    hleftP hrightP hleft hright

/-- Key generation evaluates only chain, leaf, and Merkle domains, so its cache contains no encoding input. -/
theorem Concrete.keygen_cache_none_encodingInput
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (targetEpoch : Epoch) (targetInput : Message × Randomness) :
    keyResult.2
      (Concrete.CacheView.encodingInput keyResult.1.2.parameter targetEpoch targetInput) =
        none := by
  obtain ⟨parameter, secret, root, hkey, hroot⟩ :=
    Concrete.keygen_support_rootTree keyResult hmem
  rw [hkey]
  apply Concrete.CacheReplay.cache_none_of_zero_query_bound
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest)
    (Concrete.CacheView.encodingInput parameter targetEpoch targetInput)
    ∅ keyResult.2 root
  · exact (Concrete.treeNode_queryBound_zero_encodingAddress parameter secret targetEpoch
      treeHeight Concrete.rootNode).of_imp (by
        intro input hinput
        subst input
        rw [Concrete.CacheView.encodingInput]
        exact atHashAddress_tweakableHashInput_iff parameter
          (.encoding targetEpoch) (.encoding targetEpoch) _ |>.2 rfl)
  · simp
  · exact hroot

end XmssSecurity
