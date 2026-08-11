import XmssSecurity.KeygenCache

open OracleComp OracleSpec

namespace XmssSecurity.Concrete.CacheReplay

theorem tweakableHash_query_cached
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput)
    (initialCache finalCache : QueryCache HashSpec) (digest : Digest)
    (hmem : (digest, finalCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.tweakableHash parameter domain payload :
          OracleComp HashSpec Digest)).run initialCache)) :
    ∃ output, finalCache (tweakableHashInput parameter domain payload) = some output ∧
      digest = truncateHash output := by
  unfold Concrete.tweakableHash Concrete.oracleHash at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨output, middleCache⟩, hquery, hrest⟩ := hmem
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hrest
  cases hrest
  exact ⟨output, randomOracle_query_caches _ _ _ _ (by simpa using hquery), rfl⟩

theorem leafAt_query_cached_in_largerCache
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) (epoch : Epoch)
    (initialCache resultCache largerCache : QueryCache HashSpec) (digest : Digest)
    (hmem : (digest, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.leafAt parameter secret epoch : OracleComp HashSpec Digest)).run
          initialCache))
    (hle : resultCache ≤ largerCache) :
    ∃ output,
      largerCache (Concrete.CacheView.leafInput parameter epoch
        (oneTimePublicKey largerCache parameter secret epoch)) = some output := by
  unfold Concrete.leafAt at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨endpoints, middleCache⟩, honeTime, hleaf⟩ := hmem
  obtain ⟨output, hcached, _hdigest⟩ := tweakableHash_query_cached parameter
    (.leaf epoch) (Concrete.leafPayload endpoints) middleCache resultCache digest hleaf
  have hmiddleLe : middleCache ≤ resultCache :=
    randomOracle_cache_le (Concrete.leafHash parameter epoch endpoints :
      OracleComp HashSpec Digest) middleCache (digest, resultCache) hleaf
  have hendpoints := eval_answerFn_largerCache_eq_of_mem_support
    (Concrete.oneTimePublicKey parameter secret epoch :
      OracleComp HashSpec (ChainIndex → Digest)) initialCache middleCache largerCache
      endpoints honeTime (hmiddleLe.trans hle)
  rw [eval_oneTimePublicKey] at hendpoints
  refine ⟨output, ?_⟩
  rw [hendpoints]
  exact hle hcached

theorem leafAt_query_cached
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) (epoch : Epoch)
    (initialCache finalCache : QueryCache HashSpec) (digest : Digest)
    (hmem : (digest, finalCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.leafAt parameter secret epoch : OracleComp HashSpec Digest)).run
          initialCache)) :
    ∃ output,
      finalCache (Concrete.CacheView.leafInput parameter epoch
        (oneTimePublicKey finalCache parameter secret epoch)) = some output :=
  leafAt_query_cached_in_largerCache parameter secret epoch initialCache finalCache
    finalCache digest hmem le_rfl

theorem treeNode_leaf_query_cached_in_largerCache
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) (epoch : Epoch)
    (levels : Nat) (node : MerkleNode)
    (hlevels : levels ≤ treeHeight) (hvalid : TreeSubtreeValid levels node)
    (hcover : TreeCovers levels node epoch)
    (initialCache resultCache largerCache : QueryCache HashSpec) (digest : Digest)
    (hmem : (digest, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.treeNode parameter secret levels node :
          OracleComp HashSpec Digest)).run initialCache))
    (hle : resultCache ≤ largerCache) :
    ∃ output,
      largerCache (Concrete.CacheView.leafInput parameter epoch
        (oneTimePublicKey largerCache parameter secret epoch)) = some output := by
  induction levels generalizing node initialCache resultCache digest with
  | zero =>
      have hnode : node = epoch := treeCovers_zero_iff node epoch |>.mp hcover
      subst node
      rw [Concrete.treeNode_zero_eq] at hmem
      exact leafAt_query_cached_in_largerCache parameter secret epoch initialCache
        resultCache largerCache digest hmem hle
  | succ levels ih =>
      have hlevel : levels < treeHeight := Nat.lt_of_succ_le hlevels
      have hleftValid := childNode_subtreeValid levels node false hvalid
      have hrightValid := childNode_subtreeValid levels node true hvalid
      rw [Concrete.treeNode_succ_eq, simulateQ_bind, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨left, leftCache⟩, hleft, hrest⟩ := hmem
      have hrestAll := hrest
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
      obtain ⟨⟨right, rightCache⟩, hright, hnode⟩ := hrest
      have hpartition := treeCovers_children_sum levels node epoch hvalid
      rw [if_pos hcover] at hpartition
      by_cases hleftCover : TreeCovers levels (Concrete.childNode node false) epoch
      · have hleftLe : leftCache ≤ resultCache :=
          randomOracle_cache_le
            (do
              let right ← Concrete.treeNode parameter secret levels
                (Concrete.childNode node true)
              Concrete.nodeHash parameter ⟨levels, hlevel⟩ node left right :
              OracleComp HashSpec Digest)
            leftCache (digest, resultCache) (by
              simpa only [hlevel, ↓reduceDIte] using hrestAll)
        exact ih (Concrete.childNode node false) (Nat.le_of_succ_le hlevels)
          hleftValid hleftCover initialCache leftCache left hleft (hleftLe.trans hle)
      · have hrightCover : TreeCovers levels (Concrete.childNode node true) epoch := by
          by_contra hrightCover
          simp only [hleftCover, hrightCover, if_false, zero_add] at hpartition
          omega
        have hrightLe : rightCache ≤ resultCache :=
          randomOracle_cache_le
            (Concrete.nodeHash parameter ⟨levels, hlevel⟩ node left right :
              OracleComp HashSpec Digest)
            rightCache (digest, resultCache) (by
              simpa only [hlevel, ↓reduceDIte] using hnode)
        exact ih (Concrete.childNode node true) (Nat.le_of_succ_le hlevels)
          hrightValid hrightCover leftCache rightCache right hright (hrightLe.trans hle)

theorem rootTree_leaf_query_cached
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) (epoch : Epoch)
    (root : Digest) (cache : QueryCache HashSpec)
    (hmem : (root, cache) ∈ support
      ((simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run ∅)) :
    ∃ output,
      cache (Concrete.CacheView.leafInput parameter epoch
        (oneTimePublicKey cache parameter secret epoch)) = some output := by
  apply treeNode_leaf_query_cached_in_largerCache parameter secret epoch treeHeight
    Concrete.rootNode le_rfl
  · unfold TreeSubtreeValid Concrete.rootNode lifetime
    norm_num
  · unfold TreeCovers Concrete.rootNode
    constructor
    · simp
    · simp [lifetime]
  · exact hmem
  · exact le_rfl

end XmssSecurity.Concrete.CacheReplay

namespace XmssSecurity

/-- Every supported key generation caches the honest leaf input for every epoch. -/
theorem Concrete.keygen_cache_has_leafInput
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅))
    (epoch : Epoch) :
    ∃ output,
      keyResult.2 (Concrete.CacheView.leafInput keyResult.1.2.parameter epoch
        (Concrete.CacheReplay.oneTimePublicKey keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.chainStart epoch)) = some output := by
  obtain ⟨parameter, secret, root, hkey, hroot⟩ :=
    Concrete.keygen_support_rootTree keyResult hmem
  rw [hkey]
  exact Concrete.CacheReplay.rootTree_leaf_query_cached parameter secret epoch root
    keyResult.2 hroot

/-- A distinct leaf payload at the same epoch is absent immediately after key generation. -/
theorem Concrete.keygen_cache_leafInput_eq_none_of_ne
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅))
    (epoch : Epoch) (endpoints : ChainIndex → Digest)
    (hne : endpoints ≠ Concrete.CacheReplay.oneTimePublicKey keyResult.2
      keyResult.1.2.parameter keyResult.1.2.chainStart epoch) :
    keyResult.2 (Concrete.CacheView.leafInput keyResult.1.2.parameter epoch endpoints) = none := by
  obtain ⟨honestOutput, hhonest⟩ := Concrete.keygen_cache_has_leafInput keyResult hmem epoch
  cases hforged : keyResult.2
      (Concrete.CacheView.leafInput keyResult.1.2.parameter epoch endpoints) with
  | none => rfl
  | some forgedOutput =>
      exfalso
      apply hne
      apply Concrete.CacheView.leafInput_injective keyResult.1.2.parameter epoch
      apply Concrete.keygen_cache_unique_leafAddress keyResult hmem epoch
        (Concrete.CacheView.leafInput keyResult.1.2.parameter epoch endpoints)
        (Concrete.CacheView.leafInput keyResult.1.2.parameter epoch
          (Concrete.CacheReplay.oneTimePublicKey keyResult.2 keyResult.1.2.parameter
            keyResult.1.2.chainStart epoch))
        forgedOutput honestOutput
      · simp [Concrete.CacheView.leafInput]
      · simp [Concrete.CacheView.leafInput]
      · exact hforged
      · exact hhonest

end XmssSecurity
