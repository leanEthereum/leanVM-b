import XmssSecurity.Proof.CausalAuthenticationPathIndependence
import XmssSecurity.Proof.ChainOraclePresampling
import XmssSecurity.Proof.MerkleQueryPresence
import XmssSecurity.Proof.StatementLemmas
import XmssSecurity.Proof.CausalKeygenCoupling

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

noncomputable def programmedWarmedTrajectoryMaterial
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp ((List Digest × FlatSecret) ×
      (List FullChainTrajectory × QueryCache HashSpec)) := do
  let secretView ← extractFixedChainSeeds chain allEpochs
  let trajectoryResult ← programmedFixedSeedChainTrajectoriesFromCache parameter
    (unflattenSecret secretView.2) chain (chainLength - 1) ∅ allEpochs
  pure (secretView, trajectoryResult)

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


def TreeValueIndex :=
  (height : Fin (treeHeight + 1)) ×' Fin (2 ^ (treeHeight - height.val))

deriving instance DecidableEq for TreeValueIndex
deriving instance Fintype for TreeValueIndex

def TreeValueIndex.node (index : TreeValueIndex) : MerkleNode :=
  ⟨index.2.val, by
    apply index.2.isLt.trans_le
    unfold lifetime
    exact Nat.pow_le_pow_right (by omega) (Nat.sub_le treeHeight index.1.val)⟩

def TreeValueIndex.domain (index : TreeValueIndex) : HashDomain :=
  if hzero : index.1.val = 0 then
    .leaf ⟨index.node.val, by
      change index.2.val < lifetime
      exact index.node.isLt⟩
  else
    .merkle ⟨index.1.val - 1, by omega⟩ index.node

def TreeValueIndex.computation
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (index : TreeValueIndex) : OracleComp HashSpec Digest :=
  Concrete.treeNode parameter secret index.1.val index.node

def TreeValueIndex.Precedes (left right : TreeValueIndex) : Prop :=
  left.1.val < right.1.val ∨
    (left.1.val = right.1.val ∧ left.2.val < right.2.val)

instance : DecidableRel TreeValueIndex.Precedes := fun left right => by
  unfold TreeValueIndex.Precedes
  infer_instance

instance : IsTrans TreeValueIndex TreeValueIndex.Precedes where
  trans left middle right hleft hright := by
    unfold TreeValueIndex.Precedes at hleft hright ⊢
    rcases hleft with hheight | ⟨hheight, hnode⟩
    · rcases hright with hheight' | ⟨hheight', hnode'⟩
      · exact Or.inl (hheight.trans hheight')
      · exact Or.inl (hheight.trans_le (by omega))
    · rcases hright with hheight' | ⟨hheight', hnode'⟩
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, by omega⟩

def TreeValuesFresh (parameter : PublicParameter)
    (indices : List TreeValueIndex) (cache : QueryCache HashSpec) : Prop :=
  ∀ index ∈ indices, ∀ input,
    AtHashAddress parameter index.domain input → cache input = none

noncomputable def treeValues
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    List TreeValueIndex →
      QueryCache HashSpec → ProbComp (List Digest × QueryCache HashSpec)
  | [], cache => pure ([], cache)
  | index :: indices, cache => do
      let head ← (simulateQ randomOracle
        (index.computation parameter secret)).run cache
      let tail ← treeValues parameter secret indices head.2
      pure (head.1 :: tail.1, tail.2)

@[simp]
theorem treeValues_nil
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (cache : QueryCache HashSpec) :
    treeValues parameter secret [] cache = pure ([], cache) := rfl

theorem treeValues_cons
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (index : TreeValueIndex) (indices : List TreeValueIndex)
    (cache : QueryCache HashSpec) :
    treeValues parameter secret (index :: indices) cache = (do
      let head ← (simulateQ randomOracle
        (index.computation parameter secret)).run cache
      let tail ← treeValues parameter secret indices head.2
      pure (head.1 :: tail.1, tail.2)) := rfl

theorem TreeValueIndex.subtreeValid (index : TreeValueIndex) :
    TreeSubtreeValid index.1.val index.node := by
  have hfactor : 2 ^ (treeHeight - index.1.val) * 2 ^ index.1.val =
      2 ^ treeHeight := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
  have hnode : index.node.val + 1 ≤ 2 ^ (treeHeight - index.1.val) := by
    change index.2.val + 1 ≤ 2 ^ (treeHeight - index.1.val)
    omega
  unfold TreeSubtreeValid lifetime
  calc
    (index.node.val + 1) * 2 ^ index.1.val ≤
        2 ^ (treeHeight - index.1.val) * 2 ^ index.1.val :=
      Nat.mul_le_mul_right _ hnode
    _ = 2 ^ treeHeight := hfactor

theorem treeValue_preserves_fresh_later
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (current target : TreeValueIndex) (hbefore : current.Precedes target)
    (cache : QueryCache HashSpec)
    (result : Digest × QueryCache HashSpec)
    (hresult : result ∈ support
      ((simulateQ randomOracle
        (current.computation parameter secret)).run cache))
    (input : HashInput)
    (hinput : AtHashAddress parameter target.domain input)
    (hcache : cache input = none) :
    result.2 input = none := by
  apply Concrete.CacheReplay.cache_none_of_zero_query_bound
    (current.computation parameter secret) input cache result.2 result.1
  · by_cases htargetZero : target.1.val = 0
    · have hcurrentZero : current.1.val = 0 := by
        unfold TreeValueIndex.Precedes at hbefore
        omega
      let targetEpoch : Epoch := ⟨target.node.val, by
        change target.2.val < lifetime
        exact target.node.isLt⟩
      apply OracleComp.IsQueryBoundP.of_imp
          (p' := AtHashAddress parameter (.leaf targetEpoch))
      · intro candidate heq
        subst candidate
        unfold TreeValueIndex.domain at hinput
        rw [dif_pos htargetZero] at hinput
        exact hinput
      · have hbound := Concrete.treeNode_queryBound_leafAddress
          parameter secret targetEpoch current.1.val current.node
          (by omega) current.subtreeValid
        have hnot : ¬ TreeCovers current.1.val current.node targetEpoch := by
          rw [hcurrentZero, treeCovers_zero_iff]
          intro heq
          have hnodeEq : current.node.val = target.node.val := by
            exact congrArg Fin.val heq
          unfold TreeValueIndex.Precedes at hbefore
          change current.2.val = target.2.val at hnodeEq
          omega
        simpa [TreeValueIndex.computation, hnot] using hbound
    · let targetLevel : MerkleLevel := ⟨target.1.val - 1, by omega⟩
      apply OracleComp.IsQueryBoundP.of_imp
          (p' := AtHashAddress parameter
            (.merkle targetLevel target.node))
      · intro candidate heq
        subst candidate
        unfold TreeValueIndex.domain at hinput
        rw [dif_neg htargetZero] at hinput
        exact hinput
      · have hbound := Concrete.treeNode_queryBound_merkleAddress
          parameter secret targetLevel target.node current.1.val current.node
          (by omega) current.subtreeValid
        have hnot : ¬ MerkleAddressInSubtree targetLevel target.node
            current.1.val current.node := by
          intro hcontains
          unfold MerkleAddressInSubtree at hcontains
          unfold TreeValueIndex.Precedes at hbefore
          rcases hbefore with hheight | ⟨hheight, hnode⟩
          · change target.1.val - 1 < current.1.val ∧ _ at hcontains
            omega
          · have hexponent : current.1.val - (targetLevel.val + 1) = 0 := by
              dsimp [targetLevel]
              omega
            have hcover := hcontains.2
            rw [hexponent, treeCovers_zero_iff] at hcover
            have hnodeEq : current.node.val = target.node.val :=
              congrArg Fin.val hcover
            change current.2.val = target.2.val at hnodeEq
            omega
        simpa [TreeValueIndex.computation, hnot] using hbound
  · exact hcache
  · exact hresult

theorem treeValue_preserves_tail_fresh
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (current : TreeValueIndex) (indices : List TreeValueIndex)
    (hordered : ∀ target ∈ indices, current.Precedes target)
    (cache : QueryCache HashSpec)
    (hfresh : TreeValuesFresh parameter (current :: indices) cache)
    (result : Digest × QueryCache HashSpec)
    (hresult : result ∈ support
      ((simulateQ randomOracle
        (current.computation parameter secret)).run cache)) :
    TreeValuesFresh parameter indices result.2 := by
  intro target htarget input hinput
  apply treeValue_preserves_fresh_later parameter secret current target
    (hordered target htarget) cache result hresult input hinput
  exact hfresh target (by simp [htarget]) input hinput

theorem treeValues_cache_le
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    ∀ (indices : List TreeValueIndex) (cache : QueryCache HashSpec)
      (result : List Digest × QueryCache HashSpec),
      result ∈ support (treeValues parameter secret indices cache) →
      cache ≤ result.2 := by
  intro indices
  induction indices with
  | nil =>
      intro cache result hresult
      simp only [treeValues_nil, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact le_rfl
  | cons index indices ih =>
      intro cache result hresult
      rw [treeValues_cons, mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      rw [mem_support_bind_iff] at htail
      obtain ⟨tail, htail, hpure⟩ := htail
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      exact (Concrete.CacheReplay.randomOracle_cache_le
        (index.computation parameter secret) cache head hhead).trans
          (ih head.2 tail htail)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem evalDist_rootTree_run_eq_treeValues_then_rootTree
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    ∀ (indices : List TreeValueIndex) (initialCache : QueryCache HashSpec),
    𝒟[(simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run initialCache] =
    𝒟[treeValues parameter secret indices initialCache >>= fun tree =>
      (simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run tree.2] := by
  intro indices
  induction indices with
  | nil =>
      intro initialCache
      simp
  | cons index indices ih =>
      intro initialCache
      calc
        𝒟[(simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run initialCache] =
          𝒟[(simulateQ randomOracle
              (index.computation parameter secret)).run initialCache >>=
            fun head =>
              (simulateQ randomOracle
                (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                  OracleComp HashSpec Digest)).run head.2] :=
          evalDist_rootTree_run_eq_treeNode_then_rootTree parameter secret
            index.1.val index.node (by omega) index.subtreeValid initialCache
        _ = 𝒟[(simulateQ randomOracle
              (index.computation parameter secret)).run initialCache >>=
            fun head =>
              treeValues parameter secret indices head.2 >>= fun tree =>
                (simulateQ randomOracle
                  (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                    OracleComp HashSpec Digest)).run tree.2] := by
          apply evalDist_bind_congr
          intro head _hhead
          exact ih head.2
        _ = 𝒟[treeValues parameter secret (index :: indices) initialCache >>=
            fun tree =>
              (simulateQ randomOracle
                (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                  OracleComp HashSpec Digest)).run tree.2] := by
          rw [treeValues_cons]
          simp [bind_assoc]

def TreeValuesReplay
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (cache : QueryCache HashSpec) (indices : List TreeValueIndex)
    (values : List Digest) : Prop :=
  values.Forall₂ (fun value index =>
    Concrete.CacheReplay.treeNode cache parameter secret index.1.val
      index.node = value) indices

theorem treeValues_support_replay
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    ∀ (indices : List TreeValueIndex) (cache : QueryCache HashSpec)
      (result : List Digest × QueryCache HashSpec),
      result ∈ support (treeValues parameter secret indices cache) →
      TreeValuesReplay parameter secret result.2 indices result.1 := by
  intro indices
  induction indices with
  | nil =>
      intro cache result hresult
      simp only [treeValues_nil, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact List.Forall₂.nil
  | cons index indices ih =>
      intro cache result hresult
      rw [treeValues_cons, mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      rw [mem_support_bind_iff] at htail
      obtain ⟨tail, htail, hpure⟩ := htail
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      apply List.Forall₂.cons
      · have hreplay :=
          Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
            (index.computation parameter secret) cache head.2 tail.2 head.1
              hhead (treeValues_cache_le parameter secret indices head.2 tail htail)
        simpa [TreeValueIndex.computation] using hreplay
      · exact ih head.2 tail htail

set_option maxRecDepth 100000 in
theorem treeValues_rerun_index_eq_pure
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    ∀ (indices : List TreeValueIndex) (initialCache : QueryCache HashSpec)
      (result : List Digest × QueryCache HashSpec),
      result ∈ support (treeValues parameter secret indices initialCache) →
      ∀ index ∈ indices,
        (simulateQ randomOracle (index.computation parameter secret)).run
            result.2 =
          pure (Concrete.CacheReplay.treeNode result.2 parameter secret
            index.1.val index.node, result.2) := by
  intro indices
  induction indices with
  | nil =>
      intro initialCache result hresult index hindex
      simp at hindex
  | cons current indices ih =>
      intro initialCache result hresult index hindex
      rw [treeValues_cons, mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htailBind⟩ := hresult
      rw [mem_support_bind_iff] at htailBind
      obtain ⟨tail, htail, hpure⟩ := htailBind
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      simp only [List.mem_cons] at hindex
      rcases hindex with rfl | htailIndex
      · have hcacheLe : head.2 ≤ tail.2 :=
          treeValues_cache_le parameter secret indices head.2 tail htail
        have hrun :=
          Concrete.CacheReplay.randomOracle_rerun_largerCache_eq_pure_of_mem_support
            (index.computation parameter secret) initialCache head.2 tail.2
              head.1 hhead hcacheLe
        have hreplay : Concrete.CacheReplay.treeNode tail.2 parameter secret
            index.1.val index.node = head.1 := by
          simpa [TreeValueIndex.computation] using
            (Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
              (index.computation parameter secret) initialCache head.2 tail.2
                head.1 hhead hcacheLe)
        rw [hreplay]
        exact hrun
      · exact ih head.2 tail htail index htailIndex

theorem treeValuesReplay_eq_at_mem
    (leftParameter rightParameter : PublicParameter)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec)
    (indices : List TreeValueIndex) (values : List Digest)
    (hleft : TreeValuesReplay leftParameter leftSecret leftCache indices values)
    (hright : TreeValuesReplay rightParameter rightSecret rightCache indices values) :
    ∀ index ∈ indices,
      Concrete.CacheReplay.treeNode leftCache leftParameter leftSecret
          index.1.val index.node =
        Concrete.CacheReplay.treeNode rightCache rightParameter rightSecret
          index.1.val index.node := by
  intro index hindex
  induction hleft with
  | nil => simp at hindex
  | cons hleftHead hleftTail ih =>
      cases hright with
      | cons hrightHead hrightTail =>
          simp only [List.mem_cons] at hindex
          rcases hindex with rfl | htail
          · exact hleftHead.trans hrightHead.symm
          · exact ih hrightTail htail

def TreeValueIndex.ofSubtree
    (levels : Nat) (node : MerkleNode)
    (hlevels : levels ≤ treeHeight)
    (hvalid : TreeSubtreeValid levels node) : TreeValueIndex :=
  ⟨⟨levels, by omega⟩, ⟨node.val, by
    have hfactor : 2 ^ (treeHeight - levels) * 2 ^ levels =
        2 ^ treeHeight := by
      rw [← pow_add, Nat.sub_add_cancel hlevels]
    have hpow : 0 < 2 ^ levels := pow_pos (by omega) _
    unfold TreeSubtreeValid lifetime at hvalid
    change node.val < 2 ^ (treeHeight - levels)
    nlinarith⟩⟩

@[simp]
theorem TreeValueIndex.ofSubtree_height
    (levels : Nat) (node : MerkleNode)
    (hlevels : levels ≤ treeHeight)
    (hvalid : TreeSubtreeValid levels node) :
    (TreeValueIndex.ofSubtree levels node hlevels hvalid).1.val = levels := rfl

@[simp]
theorem TreeValueIndex.ofSubtree_node
    (levels : Nat) (node : MerkleNode)
    (hlevels : levels ≤ treeHeight)
    (hvalid : TreeSubtreeValid levels node) :
    (TreeValueIndex.ofSubtree levels node hlevels hvalid).node = node := by
  apply Fin.ext
  rfl

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
def treeValueIndicesAtHeight (height : Fin (treeHeight + 1)) :
    List TreeValueIndex :=
  List.ofFn fun node : Fin (2 ^ (treeHeight - height.val)) => ⟨height, node⟩

def allTreeValueIndices : List TreeValueIndex :=
  (List.ofFn fun height : Fin (treeHeight + 1) => height).flatMap
    treeValueIndicesAtHeight

theorem mem_allTreeValueIndices (index : TreeValueIndex) :
    index ∈ allTreeValueIndices := by
  rw [allTreeValueIndices, List.mem_flatMap]
  refine ⟨index.1, ?_, ?_⟩
  · exact List.mem_ofFn.mpr ⟨index.1, rfl⟩
  · unfold treeValueIndicesAtHeight
    exact List.mem_ofFn.mpr ⟨index.2, rfl⟩

attribute [irreducible] allTreeValueIndices

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
set_option linter.constructorNameAsVariable false in
theorem treeValues_rerun_root_eq_pure
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (initialCache : QueryCache HashSpec)
    (result : List Digest × QueryCache HashSpec)
    (hresult : result ∈ support
      (treeValues parameter secret allTreeValueIndices initialCache)) :
    (simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run result.2 =
      pure (Concrete.CacheReplay.treeNode result.2 parameter secret
        treeHeight Concrete.rootNode, result.2) := by
  let rootIndex := TreeValueIndex.ofSubtree treeHeight Concrete.rootNode
    le_rfl (by
      unfold TreeSubtreeValid Concrete.rootNode lifetime
      simp)
  have hrun := treeValues_rerun_index_eq_pure parameter secret
    allTreeValueIndices initialCache result hresult rootIndex
      (mem_allTreeValueIndices rootIndex)
  change (simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run result.2 =
    pure (Concrete.CacheReplay.treeNode result.2 parameter secret
      treeHeight Concrete.rootNode, result.2) at hrun
  exact hrun

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem evalDist_rootTree_run_eq_treeValues_root_cache
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (initialCache : QueryCache HashSpec) :
    𝒟[(simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run initialCache] =
    𝒟[(fun tree : List Digest × QueryCache HashSpec =>
      (Concrete.CacheReplay.treeNode tree.2 parameter secret
        treeHeight Concrete.rootNode, tree.2)) <$>
          treeValues parameter secret allTreeValueIndices initialCache] := by
  calc
    𝒟[(simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run initialCache] =
      𝒟[treeValues parameter secret allTreeValueIndices initialCache >>=
        fun tree =>
          (simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run tree.2] :=
      evalDist_rootTree_run_eq_treeValues_then_rootTree parameter secret
        allTreeValueIndices initialCache
    _ = 𝒟[treeValues parameter secret allTreeValueIndices initialCache >>=
        fun tree => pure
          (Concrete.CacheReplay.treeNode tree.2 parameter secret
            treeHeight Concrete.rootNode, tree.2)] := by
      apply evalDist_bind_congr
      intro tree htree
      rw [treeValues_rerun_root_eq_pure parameter secret initialCache tree htree]
    _ = 𝒟[(fun tree : List Digest × QueryCache HashSpec =>
        (Concrete.CacheReplay.treeNode tree.2 parameter secret
          treeHeight Concrete.rootNode, tree.2)) <$>
            treeValues parameter secret allTreeValueIndices initialCache] := by
      simp [map_eq_bind_pure_comp]

theorem globalTreeValuesReplay_eq_treeNode
    (leftParameter rightParameter : PublicParameter)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec) (values : List Digest)
    (hleft : TreeValuesReplay leftParameter leftSecret leftCache
      allTreeValueIndices values)
    (hright : TreeValuesReplay rightParameter rightSecret rightCache
      allTreeValueIndices values)
    (levels : Nat) (node : MerkleNode)
    (hlevels : levels ≤ treeHeight)
    (hvalid : TreeSubtreeValid levels node) :
    Concrete.CacheReplay.treeNode leftCache leftParameter leftSecret levels node =
      Concrete.CacheReplay.treeNode rightCache rightParameter rightSecret
        levels node := by
  let index := TreeValueIndex.ofSubtree levels node hlevels hvalid
  simpa [index] using treeValuesReplay_eq_at_mem
    leftParameter rightParameter leftSecret rightSecret leftCache rightCache
      allTreeValueIndices values hleft hright index
        (mem_allTreeValueIndices index)

theorem globalTreeValuesReplay_eq_authenticationPath
    (parameter : PublicParameter)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec) (values : List Digest)
    (hleft : TreeValuesReplay parameter leftSecret leftCache
      allTreeValueIndices values)
    (hright : TreeValuesReplay parameter rightSecret rightCache
      allTreeValueIndices values)
    (epoch : Epoch) :
    Concrete.CacheReplay.authenticationPath leftCache
        (SecretKey.withoutPrecomputation parameter leftSecret) epoch =
      Concrete.CacheReplay.authenticationPath rightCache
        (SecretKey.withoutPrecomputation parameter rightSecret) epoch := by
  funext level
  apply globalTreeValuesReplay_eq_treeNode parameter parameter
    leftSecret rightSecret leftCache rightCache values hleft hright
      level.val (Concrete.authenticationPathNode epoch level) (by omega)
        (authenticationPathNode_subtreeValid epoch level)

theorem globalTreeValuesReplay_eq_root
    (parameter : PublicParameter)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec) (values : List Digest)
    (hleft : TreeValuesReplay parameter leftSecret leftCache
      allTreeValueIndices values)
    (hright : TreeValuesReplay parameter rightSecret rightCache
      allTreeValueIndices values) :
    Concrete.CacheReplay.treeNode leftCache parameter leftSecret
        treeHeight Concrete.rootNode =
      Concrete.CacheReplay.treeNode rightCache parameter rightSecret
        treeHeight Concrete.rootNode := by
  exact globalTreeValuesReplay_eq_treeNode parameter parameter
    leftSecret rightSecret leftCache rightCache values hleft hright
      treeHeight Concrete.rootNode le_rfl (by
        unfold TreeSubtreeValid Concrete.rootNode lifetime
        simp)


structure CoupledWarmedKeygenView where
  secret : Epoch → ChainIndex → Digest
  table : ChainValueIndex → Digest
  values : List Digest
  cache : QueryCache HashSpec

def CoupledWarmedKeygenView.root
    (parameter : PublicParameter) (view : CoupledWarmedKeygenView) : Digest :=
  Concrete.CacheReplay.treeNode view.cache parameter view.secret
    treeHeight Concrete.rootNode

noncomputable def coupledWarmedKeygenExperiment
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp CoupledWarmedKeygenView := do
  let material ← programmedWarmedTrajectoryMaterial parameter chain
  let secret := unflattenSecret material.1.2
  let tree ← treeValues parameter secret allTreeValueIndices material.2.2
  pure {
    secret
    table := chainValueTableOfList material.2.1
    values := tree.1
    cache := tree.2
  }

def CoupledWarmedKeygenView.toProgrammedView
    (parameter : PublicParameter) (view : CoupledWarmedKeygenView) :
    ProgrammedFixedChainKeygenView := {
  publicKey := ⟨view.root parameter, parameter⟩
  secretKey := SecretKey.withoutPrecomputation parameter view.secret
  cache := view.cache
  table := view.table
}

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem evalDist_coupledWarmedKeygen_toProgrammedView_eq
    (parameter : PublicParameter) (chain : ChainIndex) :
    𝒟[CoupledWarmedKeygenView.toProgrammedView parameter <$>
      coupledWarmedKeygenExperiment parameter chain] =
    𝒟[programmedWarmedTrajectoryMaterial parameter chain >>= fun material =>
      (simulateQ randomOracle
        (Concrete.treeNode parameter (unflattenSecret material.1.2)
          treeHeight Concrete.rootNode : OracleComp HashSpec Digest)).run
            material.2.2 >>= fun rootResult =>
      pure ({
        publicKey := ⟨rootResult.1, parameter⟩
        secretKey := SecretKey.withoutPrecomputation parameter
          (unflattenSecret material.1.2)
        cache := rootResult.2
        table := chainValueTableOfList material.2.1
      } : ProgrammedFixedChainKeygenView)] := by
  unfold coupledWarmedKeygenExperiment
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  apply evalDist_bind_congr
  intro material _hmaterial
  let secret := unflattenSecret material.1.2
  let finish : Digest × QueryCache HashSpec →
      ProbComp ProgrammedFixedChainKeygenView := fun rootResult => pure {
    publicKey := ⟨rootResult.1, parameter⟩
    secretKey := (SecretKey.withoutPrecomputation parameter secret)
    cache := rootResult.2
    table := chainValueTableOfList material.2.1
  }
  symm
  calc
    𝒟[(simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run material.2.2 >>= finish] =
      𝒟[((fun tree : List Digest × QueryCache HashSpec =>
          (Concrete.CacheReplay.treeNode tree.2 parameter secret
            treeHeight Concrete.rootNode, tree.2)) <$>
            treeValues parameter secret allTreeValueIndices material.2.2) >>=
              finish] := by
        rw [evalDist_bind,
          evalDist_rootTree_run_eq_treeValues_root_cache,
          ← evalDist_bind]
    _ = 𝒟[treeValues parameter secret allTreeValueIndices material.2.2 >>=
          fun tree => pure (CoupledWarmedKeygenView.toProgrammedView parameter {
            secret
            table := chainValueTableOfList material.2.1
            values := tree.1
            cache := tree.2
          })] := by
      simp [finish, CoupledWarmedKeygenView.toProgrammedView,
        CoupledWarmedKeygenView.root, map_eq_bind_pure_comp, bind_assoc]

noncomputable def coupledWarmedFixedChainKeygen
    (chain : ChainIndex) : ProbComp ProgrammedFixedChainKeygenView := do
  let parameter ← Concrete.samplePublicParameter
  let view ← coupledWarmedKeygenExperiment parameter chain
  pure (view.toProgrammedView parameter)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem evalDist_coupledWarmedFixedChainKeygen_eq_programmed
    (chain : ChainIndex) :
    𝒟[coupledWarmedFixedChainKeygen chain] =
      𝒟[programmedWarmedFixedChainKeygen chain] := by
  unfold coupledWarmedFixedChainKeygen programmedWarmedFixedChainKeygen
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  simpa [programmedWarmedTrajectoryMaterial, map_eq_bind_pure_comp,
    bind_assoc] using
      (evalDist_coupledWarmedKeygen_toProgrammedView_eq parameter chain)

end XmssSecurity
