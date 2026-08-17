import XmssSecurity.CausalAuthenticationPathIndependence
import XmssSecurity.MerkleQueryPresence

open OracleComp OracleSpec

namespace XmssSecurity

set_option maxRecDepth 100000 in
theorem evalDist_rootTree_run_eq_sequenceFin_chainWalk_then_rootTree
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) :
    ∀ (count : Nat) (chainAt : Fin count → ChainIndex)
      (initialCache : QueryCache HashSpec),
      𝒟[(simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run initialCache] =
      𝒟[(simulateQ randomOracle
        (Concrete.sequenceFin fun index =>
          Concrete.chainWalk parameter epoch (chainAt index) 0
            (chainLength - 1) (secret epoch (chainAt index)) :
            OracleComp HashSpec (Fin count → Digest))).run initialCache >>=
          fun _warmResult =>
            (simulateQ randomOracle
              (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                OracleComp HashSpec Digest)).run _warmResult.2] := by
  intro count
  induction count with
  | zero =>
      intro chainAt initialCache
      simp [Concrete.sequenceFin]
  | succ count ih =>
      intro chainAt initialCache
      calc
        𝒟[(simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run initialCache] =
          𝒟[(simulateQ randomOracle
            (Concrete.chainWalk parameter epoch (chainAt 0) 0
              (chainLength - 1) (secret epoch (chainAt 0)) :
              OracleComp HashSpec Digest)).run initialCache >>= fun headResult =>
                (simulateQ randomOracle
                  (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                    OracleComp HashSpec Digest)).run headResult.2] :=
          evalDist_rootTree_run_eq_chainWalk_then_rootTree
            parameter secret epoch (chainAt 0) (chainLength - 1) le_rfl initialCache
        _ = 𝒟[(simulateQ randomOracle
            (Concrete.chainWalk parameter epoch (chainAt 0) 0
              (chainLength - 1) (secret epoch (chainAt 0)) :
              OracleComp HashSpec Digest)).run initialCache >>= fun headResult =>
                (simulateQ randomOracle
                  (Concrete.sequenceFin fun index : Fin count =>
                    Concrete.chainWalk parameter epoch (chainAt index.succ) 0
                      (chainLength - 1) (secret epoch (chainAt index.succ)) :
                    OracleComp HashSpec (Fin count → Digest))).run headResult.2 >>=
                  fun tailResult =>
                    (simulateQ randomOracle
                      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                        OracleComp HashSpec Digest)).run tailResult.2] := by
          apply evalDist_bind_congr
          intro headResult _hheadResult
          exact ih (fun index => chainAt index.succ) headResult.2
        _ = 𝒟[(simulateQ randomOracle
            (Concrete.sequenceFin fun index =>
              Concrete.chainWalk parameter epoch (chainAt index) 0
                (chainLength - 1) (secret epoch (chainAt index)) :
              OracleComp HashSpec (Fin (count + 1) → Digest))).run initialCache >>=
                fun warmResult =>
                  (simulateQ randomOracle
                    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                      OracleComp HashSpec Digest)).run warmResult.2] := by
          rw [Concrete.sequenceFin, simulateQ_bind, StateT.run_bind]
          simp only [bind_assoc]
          apply evalDist_bind_congr
          intro headResult _hheadResult
          rw [simulateQ_bind, StateT.run_bind]
          simp

theorem evalDist_rootTree_run_eq_oneTimePublicKey_then_rootTree
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (initialCache : QueryCache HashSpec) :
    𝒟[(simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run initialCache] =
    𝒟[(simulateQ randomOracle
      (Concrete.oneTimePublicKey parameter secret epoch :
        OracleComp HashSpec (ChainIndex → Digest))).run initialCache >>=
          fun warmResult =>
            (simulateQ randomOracle
              (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                OracleComp HashSpec Digest)).run warmResult.2] := by
  simpa [Concrete.oneTimePublicKey] using
    (evalDist_rootTree_run_eq_sequenceFin_chainWalk_then_rootTree
      parameter secret epoch numChains (fun chain => chain) initialCache)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 100000 in
theorem evalDist_rootTree_run_eq_leafAt_then_rootTree
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (initialCache : QueryCache HashSpec) :
    𝒟[(simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run initialCache] =
    𝒟[(simulateQ randomOracle
      (Concrete.leafAt parameter secret epoch : OracleComp HashSpec Digest)).run
        initialCache >>= fun warmResult =>
          (simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run warmResult.2] := by
  rw [evalDist_rootTree_run_eq_oneTimePublicKey_then_rootTree]
  unfold Concrete.leafAt
  rw [simulateQ_bind, StateT.run_bind]
  simp only [bind_assoc]
  apply evalDist_bind_congr
  intro endpointsResult hendpointsResult
  let target : HashInput := Concrete.CacheView.leafInput parameter epoch endpointsResult.1
  have hcached : ∀ rootResult ∈ support
      ((simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run endpointsResult.2),
      ∃ output, rootResult.2 target = some output := by
    intro rootResult hrootResult
    have hcacheLe : endpointsResult.2 ≤ rootResult.2 :=
      Concrete.CacheReplay.randomOracle_cache_le
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)
        endpointsResult.2 rootResult hrootResult
    have hreplay :=
      Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
        (Concrete.oneTimePublicKey parameter secret epoch :
          OracleComp HashSpec (ChainIndex → Digest))
        initialCache endpointsResult.2 rootResult.2 endpointsResult.1
          hendpointsResult hcacheLe
    rw [Concrete.CacheReplay.eval_oneTimePublicKey] at hreplay
    obtain ⟨output, houtput⟩ :=
      Concrete.CacheReplay.treeNode_leaf_query_cached_in_largerCache
        parameter secret epoch treeHeight Concrete.rootNode le_rfl
          (by
            unfold TreeSubtreeValid Concrete.rootNode lifetime
            norm_num)
          (by
            unfold TreeCovers Concrete.rootNode
            constructor
            · simp
            · simp [lifetime])
          endpointsResult.2 rootResult.2 rootResult.2 rootResult.1
            hrootResult le_rfl
    refine ⟨output, ?_⟩
    unfold target
    rw [← hreplay]
    exact houtput
  calc
    𝒟[(simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run endpointsResult.2] =
      𝒟[(randomOracle (spec := HashSpec) target).run endpointsResult.2 >>=
        fun queryResult =>
          (simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run queryResult.2] :=
        OracleComp.evalDist_randomOracle_run_eq_query_then_of_cached
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)
          endpointsResult.2 target hcached
    _ = 𝒟[(simulateQ randomOracle
        (Concrete.leafHash parameter epoch endpointsResult.1 :
          OracleComp HashSpec Digest)).run endpointsResult.2 >>= fun leafResult =>
            (simulateQ randomOracle
              (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                OracleComp HashSpec Digest)).run leafResult.2] := by
      simp [Concrete.leafHash, Concrete.tweakableHash, Concrete.oracleHash,
        Concrete.CacheView.leafInput, target]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 100000 in
theorem evalDist_rootTree_run_eq_nodeHash_then_rootTree
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (level : Nat) (node : MerkleNode) (hlevel : level < treeHeight)
    (hvalid : TreeSubtreeValid (level + 1) node)
    (initialCache : QueryCache HashSpec)
    (leftResult rightResult : Digest × QueryCache HashSpec)
    (hleft : leftResult ∈ support
      ((simulateQ randomOracle
        (Concrete.treeNode parameter secret level
          (Concrete.childNode node false) : OracleComp HashSpec Digest)).run
            initialCache))
    (hright : rightResult ∈ support
      ((simulateQ randomOracle
        (Concrete.treeNode parameter secret level
          (Concrete.childNode node true) : OracleComp HashSpec Digest)).run
            leftResult.2)) :
    𝒟[(simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run rightResult.2] =
    𝒟[(simulateQ randomOracle
      (Concrete.nodeHash parameter ⟨level, hlevel⟩ node
        leftResult.1 rightResult.1 : OracleComp HashSpec Digest)).run
          rightResult.2 >>= fun nodeResult =>
            (simulateQ randomOracle
              (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                OracleComp HashSpec Digest)).run nodeResult.2] := by
  let target : HashInput := Concrete.CacheView.merkleInput parameter
    ⟨level, hlevel⟩ node leftResult.1 rightResult.1
  have hnode : node.val < 2 ^ (treeHeight - (level + 1)) := by
    have hfactor : 2 ^ (treeHeight - (level + 1)) * 2 ^ (level + 1) =
        2 ^ treeHeight := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    unfold TreeSubtreeValid lifetime at hvalid
    have hvalid' : (node.val + 1) * 2 ^ (level + 1) ≤
        2 ^ (treeHeight - (level + 1)) * 2 ^ (level + 1) :=
      hvalid.trans_eq hfactor.symm
    have hle : node.val + 1 ≤ 2 ^ (treeHeight - (level + 1)) :=
      Nat.le_of_mul_le_mul_right hvalid' (pow_pos (by omega) (level + 1))
    omega
  have hcontains : MerkleAddressInSubtree ⟨level, hlevel⟩ node
      treeHeight Concrete.rootNode := by
    unfold MerkleAddressInSubtree TreeCovers Concrete.rootNode
    constructor
    · exact hlevel
    · constructor
      · simp
      · simpa using hnode
  have hcached : ∀ rootResult ∈ support
      ((simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run rightResult.2),
      ∃ output, rootResult.2 target = some output := by
    intro rootResult hrootResult
    have hrightLe : rightResult.2 ≤ rootResult.2 :=
      Concrete.CacheReplay.randomOracle_cache_le
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)
        rightResult.2 rootResult hrootResult
    have hleftToRight : leftResult.2 ≤ rightResult.2 :=
      Concrete.CacheReplay.randomOracle_cache_le
        (Concrete.treeNode parameter secret level
          (Concrete.childNode node true) : OracleComp HashSpec Digest)
        leftResult.2 rightResult hright
    have hleftReplay :=
      Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
        (Concrete.treeNode parameter secret level
          (Concrete.childNode node false) : OracleComp HashSpec Digest)
        initialCache leftResult.2 rootResult.2 leftResult.1 hleft
          (hleftToRight.trans hrightLe)
    have hrightReplay :=
      Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
        (Concrete.treeNode parameter secret level
          (Concrete.childNode node true) : OracleComp HashSpec Digest)
        leftResult.2 rightResult.2 rootResult.2 rightResult.1 hright hrightLe
    rw [Concrete.CacheReplay.eval_treeNode] at hleftReplay hrightReplay
    obtain ⟨output, houtput⟩ :=
      Concrete.CacheReplay.treeNode_merkle_query_cached_in_largerCache
        parameter secret ⟨level, hlevel⟩ node treeHeight Concrete.rootNode
          le_rfl
          (by
            unfold TreeSubtreeValid Concrete.rootNode lifetime
            norm_num)
          hcontains rightResult.2 rootResult.2 rootResult.2 rootResult.1
            hrootResult le_rfl
    refine ⟨output, ?_⟩
    unfold target
    rw [hleftReplay, hrightReplay] at houtput
    exact houtput
  calc
    𝒟[(simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run rightResult.2] =
      𝒟[(randomOracle (spec := HashSpec) target).run rightResult.2 >>=
        fun queryResult =>
          (simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run queryResult.2] :=
        OracleComp.evalDist_randomOracle_run_eq_query_then_of_cached
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)
          rightResult.2 target hcached
    _ = 𝒟[(simulateQ randomOracle
        (Concrete.nodeHash parameter ⟨level, hlevel⟩ node
          leftResult.1 rightResult.1 : OracleComp HashSpec Digest)).run
            rightResult.2 >>= fun nodeResult =>
              (simulateQ randomOracle
                (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                  OracleComp HashSpec Digest)).run nodeResult.2] := by
      simp [Concrete.nodeHash, Concrete.tweakableHash, Concrete.oracleHash,
        Concrete.CacheView.merkleInput, target]

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 100000 in
theorem evalDist_rootTree_run_eq_treeNode_then_rootTree
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    ∀ (levels : Nat) (node : MerkleNode), levels ≤ treeHeight →
      TreeSubtreeValid levels node →
      ∀ initialCache : QueryCache HashSpec,
      𝒟[(simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run initialCache] =
      𝒟[(simulateQ randomOracle
        (Concrete.treeNode parameter secret levels node :
          OracleComp HashSpec Digest)).run initialCache >>= fun warmResult =>
            (simulateQ randomOracle
              (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                OracleComp HashSpec Digest)).run warmResult.2] := by
  intro levels
  induction levels with
  | zero =>
      intro node _hlevels _hvalid initialCache
      simpa [Concrete.treeNode_zero_eq] using
        (evalDist_rootTree_run_eq_leafAt_then_rootTree
          parameter secret node initialCache)
  | succ levels ih =>
      intro node hlevels hvalid initialCache
      have hlevel : levels < treeHeight := Nat.lt_of_succ_le hlevels
      have hleftValid := childNode_subtreeValid levels node false hvalid
      have hrightValid := childNode_subtreeValid levels node true hvalid
      calc
        𝒟[(simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run initialCache] =
          𝒟[(simulateQ randomOracle
            (Concrete.treeNode parameter secret levels
              (Concrete.childNode node false) : OracleComp HashSpec Digest)).run
                initialCache >>= fun leftResult =>
              (simulateQ randomOracle
                (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                  OracleComp HashSpec Digest)).run leftResult.2] :=
          ih (Concrete.childNode node false) (Nat.le_of_succ_le hlevels)
            hleftValid initialCache
        _ = 𝒟[(simulateQ randomOracle
            (Concrete.treeNode parameter secret levels
              (Concrete.childNode node false) : OracleComp HashSpec Digest)).run
                initialCache >>= fun leftResult =>
              (simulateQ randomOracle
                (Concrete.treeNode parameter secret levels
                  (Concrete.childNode node true) : OracleComp HashSpec Digest)).run
                    leftResult.2 >>= fun rightResult =>
                (simulateQ randomOracle
                  (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                    OracleComp HashSpec Digest)).run rightResult.2] := by
          apply evalDist_bind_congr
          intro leftResult _hleftResult
          exact ih (Concrete.childNode node true) (Nat.le_of_succ_le hlevels)
            hrightValid leftResult.2
        _ = 𝒟[(simulateQ randomOracle
            (Concrete.treeNode parameter secret levels
              (Concrete.childNode node false) : OracleComp HashSpec Digest)).run
                initialCache >>= fun leftResult =>
              (simulateQ randomOracle
                (Concrete.treeNode parameter secret levels
                  (Concrete.childNode node true) : OracleComp HashSpec Digest)).run
                    leftResult.2 >>= fun rightResult =>
                (simulateQ randomOracle
                  (Concrete.nodeHash parameter ⟨levels, hlevel⟩ node
                    leftResult.1 rightResult.1 : OracleComp HashSpec Digest)).run
                      rightResult.2 >>= fun nodeResult =>
                  (simulateQ randomOracle
                    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                      OracleComp HashSpec Digest)).run nodeResult.2] := by
          apply evalDist_bind_congr
          intro leftResult hleftResult
          apply evalDist_bind_congr
          intro rightResult hrightResult
          exact evalDist_rootTree_run_eq_nodeHash_then_rootTree
            parameter secret levels node hlevel hvalid initialCache
              leftResult rightResult hleftResult hrightResult
        _ = 𝒟[(simulateQ randomOracle
            (Concrete.treeNode parameter secret (levels + 1) node :
              OracleComp HashSpec Digest)).run initialCache >>= fun warmResult =>
                (simulateQ randomOracle
                  (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                    OracleComp HashSpec Digest)).run warmResult.2] := by
          rw [Concrete.treeNode_succ_eq, simulateQ_bind, StateT.run_bind]
          simp only [bind_assoc]
          apply evalDist_bind_congr
          intro leftResult _hleftResult
          rw [simulateQ_bind, StateT.run_bind]
          simp only [bind_assoc]
          apply evalDist_bind_congr
          intro rightResult _hrightResult
          simp [hlevel]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 100000 in
theorem evalDist_rootTree_run_eq_authenticationPathLevels_then_rootTree
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) :
    ∀ (levels : List MerkleLevel) (initialCache : QueryCache HashSpec),
      𝒟[(simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run initialCache] =
      𝒟[authenticationPathLevels parameter secret epoch levels initialCache >>=
        fun _pathResult =>
          (simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run _pathResult.2] := by
  intro levels
  induction levels with
  | nil =>
      intro initialCache
      simp
  | cons level levels ih =>
      intro initialCache
      calc
        𝒟[(simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run initialCache] =
          𝒟[(simulateQ randomOracle
            (Concrete.treeNode parameter secret level.val
              (Concrete.authenticationPathNode epoch level) :
              OracleComp HashSpec Digest)).run initialCache >>= fun headResult =>
                (simulateQ randomOracle
                  (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                    OracleComp HashSpec Digest)).run headResult.2] :=
          evalDist_rootTree_run_eq_treeNode_then_rootTree parameter secret
            level.val (Concrete.authenticationPathNode epoch level)
              (Nat.le_of_lt level.isLt)
              (authenticationPathNode_subtreeValid epoch level) initialCache
        _ = 𝒟[(simulateQ randomOracle
            (Concrete.treeNode parameter secret level.val
              (Concrete.authenticationPathNode epoch level) :
              OracleComp HashSpec Digest)).run initialCache >>= fun headResult =>
                authenticationPathLevels parameter secret epoch levels headResult.2 >>=
                  fun _tailResult =>
                    (simulateQ randomOracle
                      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                        OracleComp HashSpec Digest)).run _tailResult.2] := by
          apply evalDist_bind_congr
          intro headResult _hheadResult
          exact ih headResult.2
        _ = 𝒟[authenticationPathLevels parameter secret epoch
              (level :: levels) initialCache >>= fun pathResult =>
                (simulateQ randomOracle
                  (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                    OracleComp HashSpec Digest)).run pathResult.2] := by
          rw [authenticationPathLevels_cons]
          simp [bind_assoc]

theorem evalDist_rootTree_run_eq_allAuthenticationPathLevels_then_rootTree
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (initialCache : QueryCache HashSpec) :
    𝒟[(simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run initialCache] =
    𝒟[authenticationPathLevels parameter secret epoch allMerkleLevels initialCache >>=
      fun pathResult =>
        (simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run pathResult.2] :=
  evalDist_rootTree_run_eq_authenticationPathLevels_then_rootTree
    parameter secret epoch allMerkleLevels initialCache

def replayAuthenticationPathLevels
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (epoch : Epoch) :
    List MerkleLevel → List Digest
  | [] => []
  | level :: levels =>
      Concrete.CacheReplay.treeNode cache parameter secret level.val
          (Concrete.authenticationPathNode epoch level) ::
        replayAuthenticationPathLevels cache parameter secret epoch levels

theorem replayAuthenticationPathLevels_eq_map
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (epoch : Epoch)
    (levels : List MerkleLevel) :
    replayAuthenticationPathLevels cache parameter secret epoch levels =
      levels.map fun level =>
        Concrete.CacheReplay.treeNode cache parameter secret level.val
          (Concrete.authenticationPathNode epoch level) := by
  induction levels with
  | nil => rfl
  | cons level levels ih =>
      simp [replayAuthenticationPathLevels, ih]

theorem replayAllAuthenticationPathLevels_eq_listOfFn
    (cache : QueryCache HashSpec) (secretKey : SecretKey) (epoch : Epoch) :
    replayAuthenticationPathLevels cache secretKey.parameter
        secretKey.chainStart epoch allMerkleLevels =
      List.ofFn (Concrete.CacheReplay.authenticationPath cache secretKey epoch) := by
  rw [replayAuthenticationPathLevels_eq_map]
  simp [allMerkleLevels]
  funext level
  rfl

theorem authenticationPathLevels_cache_le
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) :
    ∀ (levels : List MerkleLevel) (initialCache : QueryCache HashSpec)
      (pathResult : List Digest × QueryCache HashSpec),
      pathResult ∈ support
        (authenticationPathLevels parameter secret epoch levels initialCache) →
      initialCache ≤ pathResult.2 := by
  intro levels
  induction levels with
  | nil =>
      intro initialCache pathResult hpath
      simp only [authenticationPathLevels_nil, support_pure,
        Set.mem_singleton_iff] at hpath
      subst pathResult
      exact le_rfl
  | cons level levels ih =>
      intro initialCache pathResult hpath
      rw [authenticationPathLevels_cons, mem_support_bind_iff] at hpath
      obtain ⟨headResult, hhead, htailBind⟩ := hpath
      rw [mem_support_bind_iff] at htailBind
      obtain ⟨tailResult, htail, hpure⟩ := htailBind
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst pathResult
      exact (Concrete.CacheReplay.randomOracle_cache_le
        (Concrete.treeNode parameter secret level.val
          (Concrete.authenticationPathNode epoch level) :
          OracleComp HashSpec Digest)
        initialCache headResult hhead).trans
          (ih headResult.2 tailResult htail)

theorem authenticationPathLevels_eq_replay_in_largerCache
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) :
    ∀ (levels : List MerkleLevel) (initialCache : QueryCache HashSpec)
      (pathResult : List Digest × QueryCache HashSpec),
      pathResult ∈ support
        (authenticationPathLevels parameter secret epoch levels initialCache) →
      ∀ largerCache, pathResult.2 ≤ largerCache →
        pathResult.1 = replayAuthenticationPathLevels largerCache
          parameter secret epoch levels := by
  intro levels
  induction levels with
  | nil =>
      intro initialCache pathResult hpath largerCache _hle
      simp only [authenticationPathLevels_nil, support_pure,
        Set.mem_singleton_iff] at hpath
      subst pathResult
      rfl
  | cons level levels ih =>
      intro initialCache pathResult hpath largerCache hle
      rw [authenticationPathLevels_cons, mem_support_bind_iff] at hpath
      obtain ⟨headResult, hhead, htailBind⟩ := hpath
      rw [mem_support_bind_iff] at htailBind
      obtain ⟨tailResult, htail, hpure⟩ := htailBind
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst pathResult
      have htailLe : tailResult.2 ≤ largerCache := hle
      have hheadToTail : headResult.2 ≤ tailResult.2 := by
        exact authenticationPathLevels_cache_le parameter secret epoch levels
          headResult.2 tailResult htail
      have hheadReplay :=
        Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
          (Concrete.treeNode parameter secret level.val
            (Concrete.authenticationPathNode epoch level) :
            OracleComp HashSpec Digest)
          initialCache headResult.2 largerCache headResult.1 hhead
            (hheadToTail.trans htailLe)
      rw [Concrete.CacheReplay.eval_treeNode] at hheadReplay
      simp only [replayAuthenticationPathLevels, List.cons.injEq]
      exact ⟨hheadReplay.symm,
        ih headResult.2 tailResult htail largerCache htailLe⟩

noncomputable def actualAuthenticationPathRootPairFromCache
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (initialCache : QueryCache HashSpec) :
    ProbComp (List Digest × Digest) := do
  let rootResult ← (simulateQ randomOracle
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest)).run initialCache
  pure (replayAuthenticationPathLevels rootResult.2 parameter secret epoch
    allMerkleLevels, rootResult.1)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 100000 in
theorem evalDist_actualAuthenticationPathRootPairFromCache_eq_warmed
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (initialCache : QueryCache HashSpec) :
    𝒟[actualAuthenticationPathRootPairFromCache parameter secret epoch
      initialCache] =
    𝒟[do
      let pathResult ← authenticationPathLevels parameter secret epoch
        allMerkleLevels initialCache
      let rootResult ← (simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run pathResult.2
      pure (pathResult.1, rootResult.1)] := by
  unfold actualAuthenticationPathRootPairFromCache
  calc
    𝒟[(simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run initialCache >>= fun rootResult =>
        pure (replayAuthenticationPathLevels rootResult.2 parameter secret epoch
          allMerkleLevels, rootResult.1)] =
      𝒟[(authenticationPathLevels parameter secret epoch allMerkleLevels
          initialCache >>= fun pathResult =>
        (simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run pathResult.2) >>= fun rootResult =>
        pure (replayAuthenticationPathLevels rootResult.2 parameter secret epoch
          allMerkleLevels, rootResult.1)] := by
      rw [evalDist_bind,
        evalDist_rootTree_run_eq_allAuthenticationPathLevels_then_rootTree,
        ← evalDist_bind]
    _ = 𝒟[authenticationPathLevels parameter secret epoch allMerkleLevels
          initialCache >>= fun pathResult =>
        (simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run pathResult.2 >>= fun rootResult =>
        pure (pathResult.1, rootResult.1)] := by
      simp only [bind_assoc]
      apply evalDist_bind_congr
      intro pathResult hpathResult
      apply evalDist_bind_congr
      intro rootResult hrootResult
      have hpathLe : pathResult.2 ≤ rootResult.2 :=
        Concrete.CacheReplay.randomOracle_cache_le
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)
          pathResult.2 rootResult hrootResult
      have hreplay := authenticationPathLevels_eq_replay_in_largerCache
        parameter secret epoch allMerkleLevels initialCache pathResult
          hpathResult rootResult.2 hpathLe
      rw [← hreplay]

theorem evalDist_actualAuthenticationPathRootPairFromCache_eq_independent
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex)
    (trajectoryResult : List FullChainTrajectory × QueryCache HashSpec)
    (htrajectory : trajectoryResult ∈ support
      (programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs))
    (epoch : Epoch) :
    𝒟[actualAuthenticationPathRootPairFromCache parameter secret epoch
      trajectoryResult.2] =
    𝒟[independentAuthenticationPathRootPair] := by
  calc
    𝒟[actualAuthenticationPathRootPairFromCache parameter secret epoch
        trajectoryResult.2] =
      𝒟[programmedWarmedAuthenticationPathRootPair parameter secret
        trajectoryResult epoch] := by
      exact evalDist_actualAuthenticationPathRootPairFromCache_eq_warmed
        parameter secret epoch trajectoryResult.2
    _ = 𝒟[independentAuthenticationPathRootPair] :=
      evalDist_programmedWarmedAuthenticationPathRootPair_eq_independent
        parameter secret chain trajectoryResult htrajectory epoch

noncomputable def actualAuthenticationPathPublicTableView
    (chain : ChainIndex) (epoch : Epoch) :
    ProbComp (PublicKey × (List Digest × (ChainValueIndex → Digest))) := do
  let parameter ← Concrete.samplePublicParameter
  let material ← programmedWarmedTrajectoryMaterial parameter chain
  let pathRoot ← actualAuthenticationPathRootPairFromCache parameter
    (unflattenSecret material.1.2) epoch material.2.2
  pure (⟨pathRoot.2, parameter⟩,
    (pathRoot.1, chainValueTableOfList material.2.1))

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 100000 in
theorem evalDist_actualAuthenticationPathPublicTableView_eq_independent
    (chain : ChainIndex) (epoch : Epoch) :
    𝒟[actualAuthenticationPathPublicTableView chain epoch] =
      𝒟[independentAuthenticationPathPublicTableView chain] := by
  calc
    𝒟[actualAuthenticationPathPublicTableView chain epoch] =
      𝒟[programmedWarmedAuthenticationPathPublicTableView chain epoch] := by
      unfold actualAuthenticationPathPublicTableView
        programmedWarmedAuthenticationPathPublicTableView
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro parameter
      apply evalDist_bind_congr
      intro material _hmaterial
      let finish : (List Digest × Digest) →
          ProbComp (PublicKey × (List Digest ×
            (ChainValueIndex → Digest))) := fun pathRoot =>
        pure (⟨pathRoot.2, parameter⟩,
          (pathRoot.1, chainValueTableOfList material.2.1))
      unfold programmedWarmedAuthenticationPathRootPair
      change 𝒟[actualAuthenticationPathRootPairFromCache parameter
          (unflattenSecret material.1.2) epoch material.2.2 >>= finish] =
        𝒟[programmedWarmedAuthenticationPathRootPair parameter
          (unflattenSecret material.1.2) material.2 epoch >>= finish]
      rw [evalDist_bind,
        evalDist_actualAuthenticationPathRootPairFromCache_eq_warmed,
        ← evalDist_bind]
      rfl
    _ = 𝒟[independentAuthenticationPathPublicTableView chain] :=
      evalDist_programmedWarmedAuthenticationPathPublicTableView_eq_independent
        chain epoch

noncomputable def programmedWarmedFixedChainAuthenticationPathPublicTableView
    (chain : ChainIndex) (epoch : Epoch) :
    ProbComp (PublicKey × (List Digest × (ChainValueIndex → Digest))) :=
  (fun keyView : ProgrammedFixedChainKeygenView =>
    (keyView.publicKey,
      (replayAuthenticationPathLevels keyView.cache
        keyView.secretKey.parameter keyView.secretKey.chainStart epoch
          allMerkleLevels,
        keyView.table))) <$> programmedWarmedFixedChainKeygen chain

theorem programmedWarmedFixedChainAuthenticationPathPublicTableView_eq_actualView
    (chain : ChainIndex) (epoch : Epoch) :
    programmedWarmedFixedChainAuthenticationPathPublicTableView chain epoch =
      actualAuthenticationPathPublicTableView chain epoch := by
  simp [programmedWarmedFixedChainAuthenticationPathPublicTableView,
    programmedWarmedFixedChainKeygen, actualAuthenticationPathPublicTableView,
    actualAuthenticationPathRootPairFromCache,
    programmedWarmedTrajectoryMaterial, SecretKey.withoutPrecomputation,
    map_eq_bind_pure_comp, bind_assoc]

theorem evalDist_programmedWarmedFixedChainAuthenticationPathPublicTableView_eq_independent
    (chain : ChainIndex) (epoch : Epoch) :
    𝒟[programmedWarmedFixedChainAuthenticationPathPublicTableView chain epoch] =
      𝒟[independentAuthenticationPathPublicTableView chain] := by
  rw [programmedWarmedFixedChainAuthenticationPathPublicTableView_eq_actualView]
  exact evalDist_actualAuthenticationPathPublicTableView_eq_independent chain epoch

noncomputable def actualFixedChainAuthenticationPathPublicTableView
    (chain : ChainIndex) (epoch : Epoch) :
    ProbComp (PublicKey × (List Digest × (ChainValueIndex → Digest))) :=
  (fun keyView : ProgrammedFixedChainKeygenView =>
    (keyView.publicKey,
      (replayAuthenticationPathLevels keyView.cache
        keyView.secretKey.parameter keyView.secretKey.chainStart epoch
          allMerkleLevels,
        keyView.table))) <$> actualFixedChainKeygen chain

theorem evalDist_actualFixedChainAuthenticationPathPublicTableView_eq_independent
  (chain : ChainIndex) (epoch : Epoch) :
    𝒟[actualFixedChainAuthenticationPathPublicTableView chain epoch] =
      𝒟[independentAuthenticationPathPublicTableView chain] := by
  unfold actualFixedChainAuthenticationPathPublicTableView
  calc
    𝒟[(fun keyView : ProgrammedFixedChainKeygenView =>
          (keyView.publicKey,
            (replayAuthenticationPathLevels keyView.cache
              keyView.secretKey.parameter keyView.secretKey.chainStart epoch
                allMerkleLevels,
              keyView.table))) <$> actualFixedChainKeygen chain] =
      𝒟[(fun keyView : ProgrammedFixedChainKeygenView =>
          (keyView.publicKey,
            (replayAuthenticationPathLevels keyView.cache
              keyView.secretKey.parameter keyView.secretKey.chainStart epoch
                allMerkleLevels,
              keyView.table))) <$> programmedWarmedFixedChainKeygen chain] := by
      rw [evalDist_map,
        evalDist_actualFixedChainKeygen_eq_programmedWarmed chain,
        ← evalDist_map]
    _ = 𝒟[independentAuthenticationPathPublicTableView chain] :=
      evalDist_programmedWarmedFixedChainAuthenticationPathPublicTableView_eq_independent
        chain epoch

noncomputable def actualFixedChainConcreteAuthenticationPathPublicTableView
    (chain : ChainIndex) (epoch : Epoch) :
    ProbComp (PublicKey × (List Digest × (ChainValueIndex → Digest))) :=
  (fun keyView : ProgrammedFixedChainKeygenView =>
    (keyView.publicKey,
      (List.ofFn (Concrete.CacheReplay.authenticationPath keyView.cache
        keyView.secretKey epoch), keyView.table))) <$> actualFixedChainKeygen chain

theorem evalDist_actualFixedChainConcreteAuthenticationPathPublicTableView_eq_replay
    (chain : ChainIndex) (epoch : Epoch) :
    𝒟[actualFixedChainConcreteAuthenticationPathPublicTableView chain epoch] =
      𝒟[actualFixedChainAuthenticationPathPublicTableView chain epoch] := by
  unfold actualFixedChainConcreteAuthenticationPathPublicTableView
    actualFixedChainAuthenticationPathPublicTableView
  simp only [map_eq_bind_pure_comp]
  apply evalDist_bind_congr
  intro keyView _hkeyView
  simp only [Function.comp_apply]
  rw [replayAllAuthenticationPathLevels_eq_listOfFn]

theorem evalDist_actualFixedChainConcreteAuthenticationPathPublicTableView_eq_independent
    (chain : ChainIndex) (epoch : Epoch) :
    𝒟[actualFixedChainConcreteAuthenticationPathPublicTableView chain epoch] =
      𝒟[independentAuthenticationPathPublicTableView chain] := by
  rw [evalDist_actualFixedChainConcreteAuthenticationPathPublicTableView_eq_replay]
  exact evalDist_actualFixedChainAuthenticationPathPublicTableView_eq_independent
    chain epoch

end XmssSecurity
