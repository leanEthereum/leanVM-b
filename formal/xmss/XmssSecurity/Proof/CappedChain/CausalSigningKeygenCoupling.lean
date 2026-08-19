import XmssSecurity.Proof.CausalKeygenCacheCoupling
import XmssSecurity.Proof.BoundedSignProbability
import XmssSecurity.Proof.PrecomputedBoundedSignProbability
import XmssSecurity.Proof.CappedChain.CausalSigningProjection
import XmssSecurity.Proof.CappedChain.CausalStrategyCoupling
import XmssSecurity.Proof.KeygenCache
import XmssSecurity.Proof.StatementLemmas

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

def ProgrammedFixedChainKeygenView.keyResult
    (view : ProgrammedFixedChainKeygenView) :
    (PublicKey × SecretKey) × QueryCache HashSpec :=
  ((view.publicKey, view.secretKey), view.cache)

theorem actualFixedChainKeygen_support_keyResult
    (chain : ChainIndex) (view : ProgrammedFixedChainKeygenView)
    (hview : view ∈ support (actualFixedChainKeygen chain)) :
    view.keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅) := by
  unfold actualFixedChainKeygen at hview
  rw [mem_support_bind_iff] at hview
  obtain ⟨keyResult, hkeyResult, hpure⟩ := hview
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst view
  exact hkeyResult

theorem programmedWarmedFixedChainKeygen_support_keyResult
    (chain : ChainIndex) (view : ProgrammedFixedChainKeygenView)
    (hview : view ∈ support (programmedWarmedFixedChainKeygen chain)) :
    view.keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅) := by
  apply actualFixedChainKeygen_support_keyResult chain view
  exact (mem_support_iff_of_evalDist_eq
    (evalDist_actualFixedChainKeygen_eq_programmedWarmed chain) view).mpr hview

def TreeCacheStable
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (cache : QueryCache HashSpec) : Prop :=
  ∀ (levels : Nat) (node : MerkleNode),
    levels ≤ treeHeight → TreeSubtreeValid levels node →
    ∀ (largerCache : QueryCache HashSpec), cache ≤ largerCache →
    (simulateQ randomOracle
      (Concrete.treeNode parameter secret levels node :
        OracleComp HashSpec Digest)).run largerCache =
      pure (Concrete.CacheReplay.treeNode cache parameter secret levels node,
        largerCache)

theorem treeCacheStable_of_treeValues_support
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (initialCache : QueryCache HashSpec)
    (tree : List Digest × QueryCache HashSpec)
    (htree : tree ∈ support
      (treeValues parameter secret allTreeValueIndices initialCache)) :
    TreeCacheStable parameter secret tree.2 := by
  intro levels node hlevels hvalid largerCache hle
  let index := TreeValueIndex.ofSubtree levels node hlevels hvalid
  have hrun := treeValues_rerun_index_eq_pure parameter secret
    allTreeValueIndices initialCache tree htree index
      (mem_allTreeValueIndices index)
  have hmem :
      (Concrete.CacheReplay.treeNode tree.2 parameter secret levels node,
        tree.2) ∈ support
          ((simulateQ randomOracle
            (Concrete.treeNode parameter secret levels node :
              OracleComp HashSpec Digest)).run tree.2) := by
    change (Concrete.CacheReplay.treeNode tree.2 parameter secret
        index.1.val index.node, tree.2) ∈ support
      ((simulateQ randomOracle (index.computation parameter secret)).run tree.2)
    rw [hrun]
    simp
  exact Concrete.CacheReplay.randomOracle_rerun_largerCache_eq_pure_of_mem_support
    (Concrete.treeNode parameter secret levels node :
      OracleComp HashSpec Digest)
    tree.2 tree.2 largerCache
      (Concrete.CacheReplay.treeNode tree.2 parameter secret levels node)
      hmem hle

theorem TreeCacheStable.treeNode_eq
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (cache : QueryCache HashSpec)
    (hstable : TreeCacheStable parameter secret cache)
    (levels : Nat) (node : MerkleNode)
    (hlevels : levels ≤ treeHeight) (hvalid : TreeSubtreeValid levels node)
    (largerCache : QueryCache HashSpec) (hle : cache ≤ largerCache) :
    Concrete.CacheReplay.treeNode cache parameter secret levels node =
      Concrete.CacheReplay.treeNode largerCache parameter secret levels node := by
  have hrun := hstable levels node hlevels hvalid largerCache hle
  have hmem :
      (Concrete.CacheReplay.treeNode cache parameter secret levels node,
        largerCache) ∈ support
          ((simulateQ randomOracle
            (Concrete.treeNode parameter secret levels node :
              OracleComp HashSpec Digest)).run largerCache) := by
    rw [hrun]
    simp
  have hreplay := Concrete.CacheReplay.eval_answerFn_finalCache_eq_of_mem_support
    (Concrete.treeNode parameter secret levels node :
      OracleComp HashSpec Digest)
    largerCache largerCache
      (Concrete.CacheReplay.treeNode cache parameter secret levels node) hmem
  rw [Concrete.CacheReplay.eval_treeNode] at hreplay
  exact hreplay.symm

theorem TreeCacheStable.authenticationPath_eq
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (hstable : TreeCacheStable secretKey.parameter secretKey.chainStart cache)
    (largerCache : QueryCache HashSpec) (hle : cache ≤ largerCache)
    (epoch : Epoch) :
    Concrete.CacheReplay.authenticationPath cache secretKey epoch =
      Concrete.CacheReplay.authenticationPath largerCache secretKey epoch := by
  funext level
  exact TreeCacheStable.treeNode_eq secretKey.parameter secretKey.chainStart
    cache hstable level.val (Concrete.authenticationPathNode epoch level)
      (by omega) (authenticationPathNode_subtreeValid epoch level)
        largerCache hle

theorem simulate_sequenceFin_run_eq_pure
    {n : Nat} (computation : Fin n → OracleComp HashSpec α)
    (cache : QueryCache HashSpec) (values : Fin n → α)
    (hrun : ∀ index,
      (simulateQ randomOracle (computation index)).run cache =
        pure (values index, cache)) :
    (simulateQ randomOracle (Concrete.sequenceFin computation)).run cache =
      pure (values, cache) := by
  induction n with
  | zero =>
      have hvalues : (Fin.elim0 : Fin 0 → α) = values := by
        funext index
        exact Fin.elim0 index
      simp [Concrete.sequenceFin, hvalues]
  | succ n ih =>
      rw [Concrete.sequenceFin, simulateQ_bind, StateT.run_bind, hrun 0]
      simp only [pure_bind]
      rw [simulateQ_bind, StateT.run_bind,
        ih (fun index => computation index.succ)
          (fun index => values index.succ) (fun index => hrun index.succ)]
      simp only [pure_bind, simulateQ_pure, StateT.run_pure]
      congr
      funext index
      exact Fin.cases rfl (fun _ => rfl) index

theorem Concrete.keygen_signedChainValues_run_eq_pure
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (epoch : Epoch) (encoding : Encoding) :
    (simulateQ randomOracle
      (Concrete.signedChainValues keyResult.1.2 epoch encoding)).run
        largerCache =
      pure (Concrete.CacheReplay.signedChainValues largerCache
        keyResult.1.2 epoch encoding, largerCache) := by
  let values : ChainIndex → Digest := fun chain =>
    keygenChainValueTable keyResult.2 keyResult.1.2 chain
      (epoch, encoding chain)
  have hrun : ∀ chain,
      (simulateQ randomOracle
        (Concrete.chainWalk keyResult.1.2.parameter epoch chain 0
          (encoding chain).val
          (keyResult.1.2.chainStart epoch chain))).run largerCache =
        pure (values chain, largerCache) := by
    intro chain
    exact simulate_chainWalk_run_eq_pure_of_table_matches largerCache
      keyResult.1.2 chain
      (keygenChainValueTable keyResult.2 keyResult.1.2 chain)
      (keygenChainValueTable_seedsMatch keyResult.2 keyResult.1.2 chain)
      ((Concrete.keygenChainValueTable_edgesMatch
        keyResult hkeyResult chain).mono hle)
      epoch (encoding chain).val (encoding chain).isLt
  have hsequence := simulate_sequenceFin_run_eq_pure
    (fun chain => Concrete.chainWalk keyResult.1.2.parameter epoch chain 0
      (encoding chain).val (keyResult.1.2.chainStart epoch chain))
    largerCache values hrun
  have hvalues : values = Concrete.CacheReplay.signedChainValues
      largerCache keyResult.1.2 epoch encoding := by
    funext chain
    exact Concrete.keygen_chainWalk_eq_of_cache_le keyResult hkeyResult
      largerCache hle epoch chain (encoding chain).val
        (Nat.le_pred_of_lt (encoding chain).isLt)
  simpa [Concrete.signedChainValues, hvalues] using hsequence

theorem TreeCacheStable.authenticationPath_run_eq_pure
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (hstable : TreeCacheStable secretKey.parameter secretKey.chainStart cache)
    (largerCache : QueryCache HashSpec) (hle : cache ≤ largerCache)
    (epoch : Epoch) :
    (simulateQ randomOracle
      (Concrete.authenticationPath secretKey epoch)).run largerCache =
      pure (Concrete.CacheReplay.authenticationPath largerCache secretKey epoch,
        largerCache) := by
  have hrun : ∀ level,
      (simulateQ randomOracle
        (Concrete.treeNode secretKey.parameter secretKey.chainStart level.val
          (Concrete.authenticationPathNode epoch level) :
          OracleComp HashSpec Digest)).run largerCache =
        pure (Concrete.CacheReplay.treeNode cache secretKey.parameter
          secretKey.chainStart level.val
            (Concrete.authenticationPathNode epoch level), largerCache) := by
    intro level
    exact hstable level.val (Concrete.authenticationPathNode epoch level)
      (by omega) (authenticationPathNode_subtreeValid epoch level)
        largerCache hle
  have hsequence := simulate_sequenceFin_run_eq_pure
    (fun level => Concrete.treeNode secretKey.parameter secretKey.chainStart
      level.val (Concrete.authenticationPathNode epoch level)) largerCache
    (Concrete.CacheReplay.authenticationPath cache secretKey epoch) hrun
  rw [hstable.authenticationPath_eq secretKey cache largerCache hle epoch]
    at hsequence
  simpa [Concrete.authenticationPath] using hsequence

theorem Concrete.keygen_signWithEncoding_run_eq_pure
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅))
    (hstable : TreeCacheStable keyResult.1.2.parameter
      keyResult.1.2.chainStart keyResult.2)
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (epoch : Epoch) (randomness : Randomness) (encoding : Encoding) :
    (simulateQ randomOracle
      (Concrete.signWithEncoding keyResult.1.2 epoch randomness encoding)).run
        largerCache =
      pure (Concrete.CacheReplay.signWithEncoding largerCache keyResult.1.2
        epoch randomness encoding, largerCache) := by
  unfold Concrete.signWithEncoding
  rw [simulateQ_bind, StateT.run_bind,
    Concrete.keygen_signedChainValues_run_eq_pure keyResult hkeyResult
      largerCache hle epoch encoding]
  simp only [pure_bind]
  rw [simulateQ_bind, StateT.run_bind,
    hstable.authenticationPath_run_eq_pure keyResult.1.2 keyResult.2
      largerCache hle epoch]
  simp [Concrete.CacheReplay.signWithEncoding]

theorem Concrete.precomputedSignAttempt_materialized_run_eq_signAttempt
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅))
    (hstable : TreeCacheStable keyResult.1.2.parameter
      keyResult.1.2.chainStart keyResult.2)
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (epoch : Epoch) (message : Message) (randomness : Randomness) :
    evalDist ((simulateQ randomOracle
      (Concrete.precomputedSignAttempt
        (Concrete.materializePrecomputation keyResult.2 keyResult.1.2)
          epoch message randomness : OracleComp HashSpec (Option Signature))).run
        largerCache) =
      evalDist ((simulateQ randomOracle
        (Concrete.signAttempt keyResult.1.2 epoch message randomness :
          OracleComp HashSpec (Option Signature))).run largerCache) := by
  have hmaterialized :=
    Concrete.oldKeygen_support_materializedPrecomputedKeygen keyResult hkeyResult
  have hconsistent := Concrete.precomputedKeygen_support_consistent
    (Concrete.materializeCachedKeyResult keyResult) hmaterialized
  unfold Concrete.precomputedSignAttempt Concrete.signAttempt
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]
  simp only [Concrete.materializePrecomputation,
    Concrete.precomputedSecretKey]
  apply evalDist_bind_congr
  intro digestResult hdigestResult
  have hdigestLe := Concrete.CacheReplay.randomOracle_cache_le
    (Concrete.encodingHash keyResult.1.2.parameter epoch message randomness)
      largerCache digestResult (by
        simpa [Concrete.materializePrecomputation] using hdigestResult)
  cases hdecode : TargetSum.decodeDigest digestResult.1 with
  | none =>
    simp only
  | some encoding =>
    simp only
    rw [simulateQ_map, StateT.run_map]
    rw [Concrete.keygen_signWithEncoding_run_eq_pure keyResult hkeyResult
      hstable digestResult.2 (hle.trans hdigestLe)
      epoch randomness encoding]
    simp only [Functor.map]
    have hsignature := hconsistent digestResult.2 (hle.trans hdigestLe)
      epoch randomness encoding
    change Concrete.precomputedSignWithEncoding
      (Concrete.materializePrecomputation keyResult.2 keyResult.1.2)
        epoch randomness encoding =
      Concrete.CacheReplay.signWithEncoding digestResult.2 keyResult.1.2
        epoch randomness encoding at hsignature
    simp only [Concrete.materializePrecomputation,
      Concrete.precomputedSecretKey] at hsignature
    rw [hsignature]
    rfl

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem Concrete.evalDist_precomputedSignBoundedAttempts_materialized_eq
    (attempts : Nat)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅))
    (hstable : TreeCacheStable keyResult.1.2.parameter
      keyResult.1.2.chainStart keyResult.2)
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (epoch : Epoch) (message : Message) :
    evalDist ((simulateQ xmssRomImpl
      (Concrete.precomputedSignBoundedAttempts attempts
        (Concrete.materializePrecomputation keyResult.2 keyResult.1.2)
          epoch message)).run largerCache) =
      evalDist ((simulateQ xmssRomImpl
        (Concrete.signBoundedAttempts attempts keyResult.1.2 epoch message)).run
          largerCache) := by
  induction attempts generalizing largerCache with
  | zero => rfl
  | succ attempts ih =>
      rw [Concrete.precomputedSignBoundedAttempts_run_succ_eq,
        Concrete.signBoundedAttempts_run_succ_eq]
      apply evalDist_bind_congr
      intro randomness _hrandomness
      calc
        evalDist ((simulateQ randomOracle
              (Concrete.precomputedSignAttempt
                (Concrete.materializePrecomputation keyResult.2 keyResult.1.2)
                  epoch message randomness :
                    OracleComp HashSpec (Option Signature))).run largerCache >>=
            Concrete.precomputedSignBoundedAttemptsContinuation attempts
              (Concrete.materializePrecomputation keyResult.2 keyResult.1.2)
                epoch message) =
            evalDist ((simulateQ randomOracle
              (Concrete.signAttempt keyResult.1.2 epoch message randomness :
                OracleComp HashSpec (Option Signature))).run largerCache >>=
              Concrete.precomputedSignBoundedAttemptsContinuation attempts
                (Concrete.materializePrecomputation keyResult.2 keyResult.1.2)
                  epoch message) := by
          rw [evalDist_bind, evalDist_bind,
            Concrete.precomputedSignAttempt_materialized_run_eq_signAttempt
              keyResult hkeyResult hstable largerCache hle epoch message randomness]
        _ = evalDist ((simulateQ randomOracle
              (Concrete.signAttempt keyResult.1.2 epoch message randomness :
                OracleComp HashSpec (Option Signature))).run largerCache >>=
              Concrete.signBoundedAttemptsContinuation attempts keyResult.1.2
                epoch message) := by
          apply evalDist_bind_congr
          intro result hresult
          cases hoption : result.1 with
          | none =>
              simp only [Concrete.precomputedSignBoundedAttemptsContinuation,
                Concrete.signBoundedAttemptsContinuation]
              rw [hoption]
              apply ih result.2
              exact hle.trans (Concrete.CacheReplay.randomOracle_cache_le
                (Concrete.signAttempt keyResult.1.2 epoch message randomness :
                  OracleComp HashSpec (Option Signature)) largerCache result hresult)
          | some signature =>
              simp only [Concrete.precomputedSignBoundedAttemptsContinuation,
                Concrete.signBoundedAttemptsContinuation]
              rw [hoption]

theorem Concrete.evalDist_precomputedCappedSign_materialized_eq_cappedSign
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅))
    (hstable : TreeCacheStable keyResult.1.2.parameter
      keyResult.1.2.chainStart keyResult.2)
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (epoch : Epoch) (message : Message) :
    evalDist ((simulateQ xmssRomImpl
      (Concrete.precomputedCappedSign keyResult.1.1
        (Concrete.materializePrecomputation keyResult.2 keyResult.1.2)
          epoch message)).run largerCache) =
      evalDist ((simulateQ xmssRomImpl
        (Concrete.cappedSign keyResult.1.1 keyResult.1.2 epoch message)).run
          largerCache) := by
  rw [Concrete.precomputedCappedSign, Concrete.cappedSign_eq]
  exact Concrete.evalDist_precomputedSignBoundedAttempts_materialized_eq
    signingAttemptLimit keyResult hkeyResult hstable largerCache hle epoch message

theorem coupledWarmedKeygenExperiment_support_treeCacheStable
    (parameter : PublicParameter) (chain : ChainIndex)
    (view : CoupledWarmedKeygenView)
    (hview : view ∈ support
      (coupledWarmedKeygenExperiment parameter chain)) :
    TreeCacheStable parameter view.secret view.cache := by
  unfold coupledWarmedKeygenExperiment at hview
  rw [mem_support_bind_iff] at hview
  obtain ⟨material, _hmaterial, htreeBind⟩ := hview
  rw [mem_support_bind_iff] at htreeBind
  obtain ⟨tree, htree, hpure⟩ := htreeBind
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst view
  exact treeCacheStable_of_treeValues_support parameter
    (unflattenSecret material.1.2) material.2.2 tree htree

theorem coupledWarmedFixedChainKeygen_support_treeCacheStable
    (chain : ChainIndex) (view : ProgrammedFixedChainKeygenView)
    (hview : view ∈ support (coupledWarmedFixedChainKeygen chain)) :
    TreeCacheStable view.secretKey.parameter view.secretKey.chainStart
      view.cache := by
  unfold coupledWarmedFixedChainKeygen at hview
  rw [mem_support_bind_iff] at hview
  obtain ⟨parameter, _hparameter, hviewBind⟩ := hview
  rw [mem_support_bind_iff] at hviewBind
  obtain ⟨coupledView, hcoupledView, hpure⟩ := hviewBind
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst view
  exact coupledWarmedKeygenExperiment_support_treeCacheStable
    parameter chain coupledView hcoupledView

theorem programmedWarmedFixedChainKeygen_support_treeCacheStable
    (chain : ChainIndex) (view : ProgrammedFixedChainKeygenView)
    (hview : view ∈ support (programmedWarmedFixedChainKeygen chain)) :
    TreeCacheStable view.secretKey.parameter view.secretKey.chainStart
      view.cache := by
  apply coupledWarmedFixedChainKeygen_support_treeCacheStable chain view
  exact (mem_support_iff_of_evalDist_eq
    (evalDist_coupledWarmedFixedChainKeygen_eq_programmed chain) view).mpr hview

theorem actualFixedChainKeygen_support_treeCacheStable
    (chain : ChainIndex) (view : ProgrammedFixedChainKeygenView)
    (hview : view ∈ support (actualFixedChainKeygen chain)) :
    TreeCacheStable view.secretKey.parameter view.secretKey.chainStart
      view.cache := by
  apply programmedWarmedFixedChainKeygen_support_treeCacheStable chain view
  exact (mem_support_iff_of_evalDist_eq
    (evalDist_actualFixedChainKeygen_eq_programmedWarmed chain) view).mp hview

def ProgrammedActualKeygenStableRelation
    (chain : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) : Prop :=
  ProgrammedActualKeygenCacheRelation chain left right ∧
    TreeCacheStable left.secretKey.parameter left.secretKey.chainStart
      left.cache ∧
    TreeCacheStable right.1.secretKey.parameter right.1.secretKey.chainStart
      right.1.cache

theorem actualWithBase_support_keyView
    (chain : ChainIndex)
    (result : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hresult : result ∈ support
      (actualFixedChainKeygen chain >>= fun keyView =>
        uniformChainValueTable chain >>= fun base => pure (keyView, base))) :
    result.1 ∈ support (actualFixedChainKeygen chain) := by
  rw [mem_support_bind_iff] at hresult
  obtain ⟨keyView, hkeyView, hbaseBind⟩ := hresult
  rw [mem_support_bind_iff] at hbaseBind
  obtain ⟨base, _hbase, hpure⟩ := hbaseBind
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact hkeyView

theorem relTriple_programmedWarmedFixedChainKeygen_withBase_stable
    (chain : ChainIndex) :
    RelTriple
      (programmedWarmedFixedChainKeygen chain)
      (actualFixedChainKeygen chain >>= fun keyView =>
        uniformChainValueTable chain >>= fun base => pure (keyView, base))
      (ProgrammedActualKeygenStableRelation chain) := by
  apply relTriple_post_mono
    (relTriple_with_support
      (relTriple_programmedWarmedFixedChainKeygen_withBase_cache chain))
  intro left right hrel
  refine ⟨hrel.1, ?_, ?_⟩
  · exact programmedWarmedFixedChainKeygen_support_treeCacheStable
      chain left hrel.2.1
  · exact actualFixedChainKeygen_support_treeCacheStable chain right.1
      (actualWithBase_support_keyView chain right hrel.2.2)

theorem ProgrammedFixedChainKeygenView.parameter_eq
    (view : ProgrammedFixedChainKeygenView)
    (hkeyResult : view.keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅)) :
    view.publicKey.parameter = view.secretKey.parameter := by
  obtain ⟨parameter, secret, root, hkey, _hroot⟩ :=
    Concrete.keygen_support_rootTree view.keyResult hkeyResult
  exact congrArg (fun result => result.1.parameter = result.2.parameter) hkey ▸ rfl

theorem ProgrammedFixedChainKeygenView.chainTableMatches
    (chain : ChainIndex) (view : ProgrammedFixedChainKeygenView)
    (hkeyResult : view.keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅))
    (htable : keygenChainValueTable view.cache view.secretKey chain =
      view.table) :
    ChainTableSeedsMatch view.secretKey chain view.table ∧
      ChainTableEdgesMatch view.cache view.secretKey.parameter chain
        view.table := by
  constructor
  · rw [← htable]
    exact keygenChainValueTable_seedsMatch view.cache view.secretKey chain
  · rw [← htable]
    exact Concrete.keygenChainValueTable_edgesMatch
      view.keyResult hkeyResult chain

theorem relTriple_signingChainWalk_run
    (parameter : PublicParameter) (selected candidate : ChainIndex)
    (epoch : Epoch) (steps : Nat) (hsteps : steps < chainLength)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftTable rightTable : ChainValueIndex → Digest)
    (initialLeft initialRight left right : QueryCache HashSpec)
    (houtside : secretOutsideChain selected leftSecret =
      secretOutsideChain selected rightSecret)
    (hleftSeeds : ChainTableSeedsMatch
      (SecretKey.withoutPrecomputation parameter leftSecret) selected leftTable)
    (hleftEdges : ChainTableEdgesMatch initialLeft parameter selected leftTable)
    (hrightSeeds : ChainTableSeedsMatch
      (SecretKey.withoutPrecomputation parameter rightSecret) selected rightTable)
    (hrightEdges : ChainTableEdgesMatch initialRight parameter selected rightTable)
    (hagrees : HashCachesAgreeOn
      (OutsideChainHashInput parameter selected) left right)
    (hleftLe : initialLeft ≤ left) (hrightLe : initialRight ≤ right) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.chainWalk parameter epoch candidate 0 steps
          (leftSecret epoch candidate))).run left)
      ((simulateQ randomOracle
        (Concrete.chainWalk parameter epoch candidate 0 steps
          (rightSecret epoch candidate))).run right)
      (fun leftResult rightResult =>
        (candidate = selected →
          leftResult.1 = leftTable (epoch, ⟨steps, hsteps⟩)) ∧
        (candidate ≠ selected → leftResult.1 = rightResult.1) ∧
        HashCachesAgreeOn (OutsideChainHashInput parameter selected)
          leftResult.2 rightResult.2 ∧
        initialLeft ≤ leftResult.2 ∧ initialRight ≤ rightResult.2) := by
  by_cases hcandidate : candidate = selected
  · subst candidate
    have hleftRun := simulate_chainWalk_run_eq_pure_of_table_matches left
      (SecretKey.withoutPrecomputation parameter leftSecret) selected leftTable
        hleftSeeds (hleftEdges.mono hleftLe) epoch steps hsteps
    have hrightRun := simulate_chainWalk_run_eq_pure_of_table_matches right
      (SecretKey.withoutPrecomputation parameter rightSecret) selected rightTable
        hrightSeeds (hrightEdges.mono hrightLe) epoch steps hsteps
    simp only [SecretKey.withoutPrecomputation] at hleftRun hrightRun
    rw [hleftRun, hrightRun]
    exact relTriple_pure_pure
      ⟨fun _ => rfl, fun hne => (hne rfl).elim, hagrees,
        hleftLe, hrightLe⟩
  · have hsecret : leftSecret epoch candidate =
        rightSecret epoch candidate :=
      secret_eq_of_outsideChain_eq selected leftSecret rightSecret
        houtside epoch candidate hcandidate
    rw [← hsecret]
    apply relTriple_post_mono
      (relTriple_chainWalk_run_outside parameter selected candidate
        hcandidate epoch 0 steps (leftSecret epoch candidate)
          left right hagrees)
    intro leftResult rightResult hresult
    exact ⟨fun heq => (hcandidate heq).elim, fun _ => hresult.1,
      hresult.2.1, hleftLe.trans hresult.2.2.1,
      hrightLe.trans hresult.2.2.2⟩

theorem relTriple_signedChainValues_run
    (parameter : PublicParameter) (selected : ChainIndex)
    (epoch : Epoch) (encoding : Encoding)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftTable rightTable : ChainValueIndex → Digest)
    (initialLeft initialRight left right : QueryCache HashSpec)
    (houtside : secretOutsideChain selected leftSecret =
      secretOutsideChain selected rightSecret)
    (hleftSeeds : ChainTableSeedsMatch
      (SecretKey.withoutPrecomputation parameter leftSecret) selected leftTable)
    (hleftEdges : ChainTableEdgesMatch initialLeft parameter selected leftTable)
    (hrightSeeds : ChainTableSeedsMatch
      (SecretKey.withoutPrecomputation parameter rightSecret) selected rightTable)
    (hrightEdges : ChainTableEdgesMatch initialRight parameter selected rightTable)
    (hagrees : HashCachesAgreeOn
      (OutsideChainHashInput parameter selected) left right)
    (hleftLe : initialLeft ≤ left) (hrightLe : initialRight ≤ right) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.signedChainValues (SecretKey.withoutPrecomputation parameter leftSecret) epoch encoding)).run
          left)
      ((simulateQ randomOracle
        (Concrete.signedChainValues (SecretKey.withoutPrecomputation parameter rightSecret) epoch encoding)).run
          right)
      (fun leftResult rightResult =>
        leftResult.1 selected = leftTable (epoch, encoding selected) ∧
        (∀ candidate, candidate ≠ selected →
          leftResult.1 candidate = rightResult.1 candidate) ∧
        HashCachesAgreeOn (OutsideChainHashInput parameter selected)
          leftResult.2 rightResult.2 ∧
        initialLeft ≤ leftResult.2 ∧ initialRight ≤ rightResult.2) := by
  let StateRelation := fun (currentLeft currentRight : QueryCache HashSpec) =>
    HashCachesAgreeOn (OutsideChainHashInput parameter selected)
        currentLeft currentRight ∧
      initialLeft ≤ currentLeft ∧ initialRight ≤ currentRight
  let ValueRelation := fun (candidate : ChainIndex)
      (leftValue rightValue : Digest) =>
    (candidate = selected →
      leftValue = leftTable (epoch, encoding candidate)) ∧
    (candidate ≠ selected → leftValue = rightValue)
  have hstep : ∀ candidate currentLeft currentRight,
      StateRelation currentLeft currentRight →
      RelTriple
        ((simulateQ randomOracle
          (Concrete.chainWalk parameter epoch candidate 0
            (encoding candidate).val (leftSecret epoch candidate))).run
              currentLeft)
        ((simulateQ randomOracle
          (Concrete.chainWalk parameter epoch candidate 0
            (encoding candidate).val (rightSecret epoch candidate))).run
              currentRight)
        (fun leftResult rightResult =>
          ValueRelation candidate leftResult.1 rightResult.1 ∧
            StateRelation leftResult.2 rightResult.2) := by
    intro candidate currentLeft currentRight hstate
    apply relTriple_post_mono
      (relTriple_signingChainWalk_run parameter selected candidate epoch
        (encoding candidate).val (encoding candidate).isLt
        leftSecret rightSecret leftTable rightTable initialLeft initialRight
        currentLeft currentRight houtside hleftSeeds hleftEdges
        hrightSeeds hrightEdges hstate.1 hstate.2.1 hstate.2.2)
    intro leftResult rightResult hresult
    exact ⟨⟨hresult.1, hresult.2.1⟩,
      hresult.2.2.1, hresult.2.2.2.1, hresult.2.2.2.2⟩
  have hsequence := relTriple_simulate_sequenceFin_run
    (fun candidate => Concrete.chainWalk parameter epoch candidate 0
      (encoding candidate).val (leftSecret epoch candidate))
    (fun candidate => Concrete.chainWalk parameter epoch candidate 0
      (encoding candidate).val (rightSecret epoch candidate))
    StateRelation ValueRelation hstep left right
      ⟨hagrees, hleftLe, hrightLe⟩
  apply relTriple_post_mono hsequence
  intro leftResult rightResult hresult
  refine ⟨(hresult.1 selected).1 rfl, ?_, hresult.2.1,
    hresult.2.2.1, hresult.2.2.2⟩
  intro candidate hne
  exact (hresult.1 candidate).2 hne

theorem relTriple_signedChainValues_run_keys
    (selected : ChainIndex) (epoch : Epoch) (encoding : Encoding)
    (leftSecret rightSecret : SecretKey)
    (leftTable rightTable : ChainValueIndex → Digest)
    (initialLeft initialRight left right : QueryCache HashSpec)
    (hparameter : leftSecret.parameter = rightSecret.parameter)
    (houtside : secretOutsideChain selected leftSecret.chainStart =
      secretOutsideChain selected rightSecret.chainStart)
    (hleftSeeds : ChainTableSeedsMatch leftSecret selected leftTable)
    (hleftEdges : ChainTableEdgesMatch initialLeft
      leftSecret.parameter selected leftTable)
    (hrightSeeds : ChainTableSeedsMatch rightSecret selected rightTable)
    (hrightEdges : ChainTableEdgesMatch initialRight
      rightSecret.parameter selected rightTable)
    (hagrees : HashCachesAgreeOn
      (OutsideChainHashInput leftSecret.parameter selected) left right)
    (hleftLe : initialLeft ≤ left) (hrightLe : initialRight ≤ right) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.signedChainValues leftSecret epoch encoding)).run left)
      ((simulateQ randomOracle
        (Concrete.signedChainValues rightSecret epoch encoding)).run right)
      (fun leftResult rightResult =>
        leftResult.1 selected = leftTable (epoch, encoding selected) ∧
        (∀ candidate, candidate ≠ selected →
          leftResult.1 candidate = rightResult.1 candidate) ∧
        HashCachesAgreeOn
          (OutsideChainHashInput leftSecret.parameter selected)
          leftResult.2 rightResult.2 ∧
        initialLeft ≤ leftResult.2 ∧ initialRight ≤ rightResult.2) := by
  obtain ⟨leftParameter, leftChainStart⟩ := leftSecret
  obtain ⟨rightParameter, rightChainStart⟩ := rightSecret
  dsimp only at hparameter
  subst rightParameter
  exact relTriple_signedChainValues_run leftParameter selected epoch encoding
    leftChainStart rightChainStart leftTable rightTable initialLeft initialRight
    left right houtside hleftSeeds hleftEdges hrightSeeds hrightEdges hagrees
    hleftLe hrightLe

theorem relTriple_keygenViews_signedChainValues_run
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenCacheRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1 ∈ support (actualFixedChainKeygen selected))
    (epoch : Epoch) (encoding : Encoding)
    (leftCache rightCache : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (OutsideChainHashInput left.secretKey.parameter selected)
        leftCache rightCache)
    (hleftLe : left.cache ≤ leftCache)
    (hrightLe : right.1.cache ≤ rightCache) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.signedChainValues left.secretKey epoch encoding)).run
          leftCache)
      ((simulateQ randomOracle
        (Concrete.signedChainValues right.1.secretKey epoch encoding)).run
          rightCache)
      (fun leftResult rightResult =>
        leftResult.1 selected = right.2 (epoch, encoding selected) ∧
        (∀ candidate, candidate ≠ selected →
          leftResult.1 candidate = rightResult.1 candidate) ∧
        HashCachesAgreeOn
          (OutsideChainHashInput left.secretKey.parameter selected)
          leftResult.2 rightResult.2 ∧
        left.cache ≤ leftResult.2 ∧ right.1.cache ≤ rightResult.2) := by
  have hleftKey := programmedWarmedFixedChainKeygen_support_keyResult
    selected left hleftSupport
  have hrightKey := actualFixedChainKeygen_support_keyResult
    selected right.1 hrightSupport
  have hleftParameter := left.parameter_eq hleftKey
  have hrightParameter := right.1.parameter_eq hrightKey
  have hparameter : left.secretKey.parameter =
      right.1.secretKey.parameter := by
    calc
      left.secretKey.parameter = left.publicKey.parameter := hleftParameter.symm
      _ = right.1.publicKey.parameter :=
        congrArg PublicKey.parameter hrel.1.2.1
      _ = right.1.secretKey.parameter := hrightParameter
  have hleftTable := programmedWarmedFixedChainKeygen_support_table
    selected left hleftSupport
  have hrightTable := actualFixedChainKeygen_support_table
    selected right.1 hrightSupport
  have hleftMatches := left.chainTableMatches selected hleftKey hleftTable
  have hrightMatches := right.1.chainTableMatches
    selected hrightKey hrightTable
  have houtside := hrel.1.2.2.1
  apply relTriple_post_mono
    (relTriple_signedChainValues_run_keys selected epoch encoding
      left.secretKey right.1.secretKey
      left.table right.1.table left.cache right.1.cache leftCache rightCache
      hparameter houtside hleftMatches.1 hleftMatches.2
      hrightMatches.1 hrightMatches.2 hagrees hleftLe hrightLe)
  intro leftResult rightResult hresult
  exact ⟨hresult.1.trans (congrFun hrel.1.1 (epoch, encoding selected)),
    hresult.2.1,
    hresult.2.2.1, hresult.2.2.2.1, hresult.2.2.2.2⟩

theorem Concrete.CacheReplay.chainStep_eq_of_outsideChainCachesAgree
    (parameter : PublicParameter) (selected candidate : ChainIndex)
    (hne : candidate ≠ selected)
    (left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (OutsideChainHashInput parameter selected) left right)
    (epoch : Epoch) :
    Concrete.CacheView.chainStep left parameter epoch candidate =
      Concrete.CacheView.chainStep right parameter epoch candidate := by
  funext position value
  unfold Concrete.CacheView.chainStep
  split
  · rename_i hposition
    unfold Concrete.CacheView.digestAt
    rw [hagrees _ ⟨epoch, candidate, ⟨position, hposition⟩, hne,
      by simp [Concrete.CacheView.chainInput]⟩]
  · rfl

theorem Concrete.CacheReplay.signedChainValues_other_eq
    (parameter : PublicParameter) (selected candidate : ChainIndex)
    (hne : candidate ≠ selected)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (houtside : secretOutsideChain selected leftSecret =
      secretOutsideChain selected rightSecret)
    (left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (OutsideChainHashInput parameter selected) left right)
    (epoch : Epoch) (encoding : Encoding) :
    Concrete.CacheReplay.signedChainValues left
        (SecretKey.withoutPrecomputation parameter leftSecret) epoch encoding candidate =
    Concrete.CacheReplay.signedChainValues right
        (SecretKey.withoutPrecomputation parameter rightSecret) epoch encoding candidate := by
  unfold Concrete.CacheReplay.signedChainValues
  simp only [SecretKey.withoutPrecomputation]
  rw [secret_eq_of_outsideChain_eq selected leftSecret rightSecret
      houtside epoch candidate hne,
    Concrete.CacheReplay.chainStep_eq_of_outsideChainCachesAgree
      parameter selected candidate hne left right hagrees epoch]

theorem Concrete.CacheReplay.signedChainValues_other_eq_keys
    (selected candidate : ChainIndex) (hne : candidate ≠ selected)
    (leftSecret rightSecret : SecretKey)
    (hparameter : leftSecret.parameter = rightSecret.parameter)
    (houtside : secretOutsideChain selected leftSecret.chainStart =
      secretOutsideChain selected rightSecret.chainStart)
    (left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (OutsideChainHashInput leftSecret.parameter selected) left right)
    (epoch : Epoch) (encoding : Encoding) :
    Concrete.CacheReplay.signedChainValues left leftSecret epoch encoding candidate =
      Concrete.CacheReplay.signedChainValues right rightSecret
        epoch encoding candidate := by
  obtain ⟨leftParameter, leftChainStart⟩ := leftSecret
  obtain ⟨rightParameter, rightChainStart⟩ := rightSecret
  dsimp only at hparameter
  subst rightParameter
  exact Concrete.CacheReplay.signedChainValues_other_eq leftParameter
    selected candidate hne leftChainStart rightChainStart houtside
      left right hagrees epoch encoding

theorem keygenViews_signWithEncoding_eq_replaced
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenCacheRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1 ∈ support (actualFixedChainKeygen selected))
    (epoch : Epoch) (randomness : Randomness) (encoding : Encoding) :
    Concrete.CacheReplay.signWithEncoding left.cache left.secretKey
        epoch randomness encoding =
      replaceSignatureChainValue
        (Concrete.CacheReplay.signWithEncoding right.1.cache
          right.1.secretKey epoch randomness encoding)
        selected (right.2 (epoch, encoding selected)) := by
  have hleftKey := programmedWarmedFixedChainKeygen_support_keyResult
    selected left hleftSupport
  have hrightKey := actualFixedChainKeygen_support_keyResult
    selected right.1 hrightSupport
  have hleftParameter := left.parameter_eq hleftKey
  have hparameter : left.secretKey.parameter =
      right.1.secretKey.parameter := by
    calc
      left.secretKey.parameter = left.publicKey.parameter :=
        hleftParameter.symm
      _ = right.1.publicKey.parameter :=
        congrArg PublicKey.parameter hrel.1.2.1
      _ = right.1.secretKey.parameter := right.1.parameter_eq hrightKey
  have hcacheAgreement : HashCachesAgreeOn
      (OutsideChainHashInput left.secretKey.parameter selected)
      left.cache right.1.cache := by
    rw [← hleftParameter]
    exact hrel.2
  have hselected :
      (Concrete.CacheReplay.signWithEncoding left.cache left.secretKey
        epoch randomness encoding).chainValue selected =
        right.2 (epoch, encoding selected) := by
    have hvalue :=
      Concrete.CacheReplay.signWithEncoding_chainValue_eq_keygenChainValueTable
        left.keyResult hleftKey left.cache le_rfl epoch randomness encoding selected
    change (Concrete.CacheReplay.signWithEncoding left.cache left.secretKey
        epoch randomness encoding).chainValue selected =
      keygenChainValueTable left.cache left.secretKey selected
        (epoch, encoding selected) at hvalue
    calc
      _ = keygenChainValueTable left.cache left.secretKey selected
          (epoch, encoding selected) := hvalue
      _ = left.table (epoch, encoding selected) :=
        congrFun (programmedWarmedFixedChainKeygen_support_table
          selected left hleftSupport) (epoch, encoding selected)
      _ = right.2 (epoch, encoding selected) :=
        congrFun hrel.1.1 (epoch, encoding selected)
  unfold Concrete.CacheReplay.signWithEncoding replaceSignatureChainValue
  congr 1
  · funext candidate
    by_cases heq : candidate = selected
    · subst candidate
      rw [Function.update_self]
      exact hselected
    · rw [Function.update_of_ne heq]
      exact Concrete.CacheReplay.signedChainValues_other_eq_keys
        selected candidate heq left.secretKey right.1.secretKey hparameter
        hrel.1.2.2.1 left.cache right.1.cache hcacheAgreement epoch encoding
  · exact hrel.1.2.2.2 epoch

theorem keygenViews_signWithEncoding_larger_eq_replaced
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenStableRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1 ∈ support (actualFixedChainKeygen selected))
    (leftCache rightCache : QueryCache HashSpec)
    (hcacheAgreement : HashCachesAgreeOn
      (OutsideChainHashInput left.secretKey.parameter selected)
      leftCache rightCache)
    (hleftLe : left.cache ≤ leftCache)
    (hrightLe : right.1.cache ≤ rightCache)
    (epoch : Epoch) (randomness : Randomness) (encoding : Encoding) :
    Concrete.CacheReplay.signWithEncoding leftCache left.secretKey
        epoch randomness encoding =
      replaceSignatureChainValue
        (Concrete.CacheReplay.signWithEncoding rightCache
          right.1.secretKey epoch randomness encoding)
        selected (right.2 (epoch, encoding selected)) := by
  have hleftKey := programmedWarmedFixedChainKeygen_support_keyResult
    selected left hleftSupport
  have hrightKey := actualFixedChainKeygen_support_keyResult
    selected right.1 hrightSupport
  have hparameter : left.secretKey.parameter =
      right.1.secretKey.parameter := by
    calc
      left.secretKey.parameter = left.publicKey.parameter :=
        (left.parameter_eq hleftKey).symm
      _ = right.1.publicKey.parameter :=
        congrArg PublicKey.parameter hrel.1.1.2.1
      _ = right.1.secretKey.parameter := right.1.parameter_eq hrightKey
  have hselected :
      (Concrete.CacheReplay.signWithEncoding leftCache left.secretKey
        epoch randomness encoding).chainValue selected =
        right.2 (epoch, encoding selected) := by
    have hvalue :=
      Concrete.CacheReplay.signWithEncoding_chainValue_eq_keygenChainValueTable
        left.keyResult hleftKey leftCache hleftLe
          epoch randomness encoding selected
    change (Concrete.CacheReplay.signWithEncoding leftCache left.secretKey
        epoch randomness encoding).chainValue selected =
      keygenChainValueTable left.cache left.secretKey selected
        (epoch, encoding selected) at hvalue
    calc
      _ = keygenChainValueTable left.cache left.secretKey selected
          (epoch, encoding selected) := hvalue
      _ = left.table (epoch, encoding selected) :=
        congrFun (programmedWarmedFixedChainKeygen_support_table
          selected left hleftSupport) (epoch, encoding selected)
      _ = right.2 (epoch, encoding selected) :=
        congrFun hrel.1.1.1 (epoch, encoding selected)
  have hauthenticationPath :
      Concrete.CacheReplay.authenticationPath leftCache left.secretKey epoch =
        Concrete.CacheReplay.authenticationPath
          rightCache right.1.secretKey epoch := by
    calc
      _ = Concrete.CacheReplay.authenticationPath
          left.cache left.secretKey epoch :=
        (TreeCacheStable.authenticationPath_eq left.secretKey left.cache
          hrel.2.1 leftCache hleftLe epoch).symm
      _ = Concrete.CacheReplay.authenticationPath
          right.1.cache right.1.secretKey epoch := hrel.1.1.2.2.2 epoch
      _ = _ := TreeCacheStable.authenticationPath_eq right.1.secretKey
        right.1.cache hrel.2.2 rightCache hrightLe epoch
  unfold Concrete.CacheReplay.signWithEncoding replaceSignatureChainValue
  congr 1
  · funext candidate
    by_cases heq : candidate = selected
    · subst candidate
      rw [Function.update_self]
      exact hselected
    · rw [Function.update_of_ne heq]
      exact Concrete.CacheReplay.signedChainValues_other_eq_keys
        selected candidate heq left.secretKey right.1.secretKey hparameter
        hrel.1.1.2.2.1 leftCache rightCache hcacheAgreement epoch encoding

def SigningComparableHashInput
    (parameter : PublicParameter) (selected : ChainIndex)
    (input : HashInput) : Prop :=
  OutsideChainHashInput parameter selected input ∨
    ∃ epoch message randomness,
      input = Concrete.CacheView.encodingInput parameter epoch
        (message, randomness)

theorem encodingHash_run_cache_eq
    (parameter : PublicParameter) (initialCache finalCache : QueryCache HashSpec)
    (epoch : Epoch) (message : Message) (randomness : Randomness)
    (digest : Digest)
    (hresult : (digest, finalCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.encodingHash parameter epoch message randomness)).run
          initialCache)) :
    Concrete.CacheView.encodingHash finalCache parameter epoch
      (message, randomness) = digest := by
  have hmapped : (digest, finalCache) ∈ support
      ((fun result : HashOutput × QueryCache HashSpec =>
        (truncateHash result.1, result.2)) <$> (randomOracle
          (Concrete.CacheView.encodingInput parameter epoch
            (message, randomness))).run initialCache) := by
    simpa [Concrete.encodingHash, Concrete.tweakableHash,
      Concrete.oracleHash, Concrete.CacheView.encodingInput,
      map_eq_bind_pure_comp] using hresult
  rw [support_map] at hmapped
  obtain ⟨result, hquery, heq⟩ := hmapped
  have hcached := Concrete.CacheReplay.randomOracle_query_caches
    (Concrete.CacheView.encodingInput parameter epoch (message, randomness))
    initialCache result.1 result.2 hquery
  rw [show result.2 = finalCache from congrArg Prod.snd heq] at hcached
  rw [Concrete.CacheView.encodingHash,
    Concrete.CacheView.digestAt_eq_of_cache_eq_some hcached]
  exact congrArg Prod.fst heq

theorem relTriple_encodingHash_run_of_signingComparableCaches
    (parameter : PublicParameter) (selected : ChainIndex)
    (left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (SigningComparableHashInput parameter selected) left right)
    (epoch : Epoch) (message : Message) (randomness : Randomness) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.encodingHash parameter epoch message randomness)).run left)
      ((simulateQ randomOracle
        (Concrete.encodingHash parameter epoch message randomness)).run right)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          HashCachesAgreeOn
            (SigningComparableHashInput parameter selected)
            leftResult.2 rightResult.2 ∧
          left ≤ leftResult.2 ∧ right ≤ rightResult.2 ∧
          Concrete.CacheView.encodingHash leftResult.2 parameter epoch
            (message, randomness) = leftResult.1 ∧
          Concrete.CacheView.encodingHash rightResult.2 parameter epoch
            (message, randomness) = rightResult.1) := by
  have hquery := relTriple_randomOracle_run_of_cachesAgreeOn
    (SigningComparableHashInput parameter selected) left right
    (Concrete.CacheView.encodingInput parameter epoch (message, randomness))
    (Or.inr ⟨epoch, message, randomness, rfl⟩) hagrees
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
          HashCachesAgreeOn
            (SigningComparableHashInput parameter selected)
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

def SignAttemptResultRelation
    (table : ChainValueIndex → Digest) (selected : ChainIndex)
    (parameter : PublicParameter) (epoch : Epoch) (message : Message)
    (randomness : Randomness) (initialLeft initialRight : QueryCache HashSpec)
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
          leftResult.1 = some (replaceSignatureChainValue signature selected
            (table (epoch, encoding selected)))) ∧
    HashCachesAgreeOn (SigningComparableHashInput parameter selected)
      leftResult.2 rightResult.2 ∧
    initialLeft ≤ leftResult.2 ∧ initialRight ≤ rightResult.2

theorem relTriple_keygenViews_signAttempt_run
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenStableRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1 ∈ support (actualFixedChainKeygen selected))
    (leftCache rightCache : QueryCache HashSpec)
    (hcacheAgreement : HashCachesAgreeOn
      (SigningComparableHashInput left.secretKey.parameter selected)
      leftCache rightCache)
    (hleftLe : left.cache ≤ leftCache)
    (hrightLe : right.1.cache ≤ rightCache)
    (epoch : Epoch) (message : Message) (randomness : Randomness) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.signAttempt left.secretKey epoch message randomness)).run
          leftCache)
      ((simulateQ randomOracle
        (Concrete.signAttempt right.1.secretKey epoch message randomness)).run
          rightCache)
      (SignAttemptResultRelation right.2 selected left.secretKey.parameter
        epoch message randomness left.cache right.1.cache) := by
  have hleftKey := programmedWarmedFixedChainKeygen_support_keyResult
    selected left hleftSupport
  have hrightKey := actualFixedChainKeygen_support_keyResult
    selected right.1 hrightSupport
  have hparameter : left.secretKey.parameter =
      right.1.secretKey.parameter := by
    calc
      left.secretKey.parameter = left.publicKey.parameter :=
        (left.parameter_eq hleftKey).symm
      _ = right.1.publicKey.parameter :=
        congrArg PublicKey.parameter hrel.1.1.2.1
      _ = right.1.secretKey.parameter := right.1.parameter_eq hrightKey
  unfold Concrete.signAttempt
  simp only [simulateQ_bind, StateT.run_bind]
  rw [← hparameter]
  apply relTriple_bind
    (relTriple_encodingHash_run_of_signingComparableCaches
      left.secretKey.parameter selected leftCache rightCache hcacheAgreement
      epoch message randomness)
  intro leftDigestResult rightDigestResult hdigest
  have hdigestEq : leftDigestResult.1 = rightDigestResult.1 := hdigest.1
  rw [← hdigestEq]
  cases hdecode : TargetSum.decodeDigest leftDigestResult.1 with
  | none =>
      simp only [simulateQ_pure, StateT.run_pure]
      apply relTriple_pure_pure
      unfold SignAttemptResultRelation
      refine ⟨none, ?_, ⟨rfl, rfl⟩, hdigest.2.1,
        hleftLe.trans hdigest.2.2.1,
        hrightLe.trans hdigest.2.2.2.1⟩
      simpa [hdigest.2.2.2.2.1] using hdecode
  | some encoding =>
      have hleftRun :
          (simulateQ randomOracle
            (Concrete.signWithEncoding left.secretKey epoch randomness encoding)).run
              leftDigestResult.2 =
            pure (Concrete.CacheReplay.signWithEncoding leftDigestResult.2
              left.secretKey epoch randomness encoding, leftDigestResult.2) := by
        simpa [ProgrammedFixedChainKeygenView.keyResult] using
          (Concrete.keygen_signWithEncoding_run_eq_pure left.keyResult hleftKey
            hrel.2.1 leftDigestResult.2
            (hleftLe.trans hdigest.2.2.1) epoch randomness encoding)
      have hrightRun :
          (simulateQ randomOracle
            (Concrete.signWithEncoding right.1.secretKey epoch randomness encoding)).run
              rightDigestResult.2 =
            pure (Concrete.CacheReplay.signWithEncoding rightDigestResult.2
              right.1.secretKey epoch randomness encoding,
                rightDigestResult.2) := by
        simpa [ProgrammedFixedChainKeygenView.keyResult] using
          (Concrete.keygen_signWithEncoding_run_eq_pure right.1.keyResult hrightKey
            hrel.2.2 rightDigestResult.2
            (hrightLe.trans hdigest.2.2.2.1) epoch randomness encoding)
      rw [simulateQ_map, StateT.run_map, simulateQ_map, StateT.run_map]
      rw [hleftRun, hrightRun]
      simp only [Functor.map]
      apply relTriple_pure_pure
      unfold SignAttemptResultRelation
      refine ⟨some encoding, ?_, ?_, hdigest.2.1,
        hleftLe.trans hdigest.2.2.1,
        hrightLe.trans hdigest.2.2.2.1⟩
      · simpa [hdigest.2.2.2.2.1] using hdecode
      · refine ⟨Concrete.CacheReplay.signWithEncoding rightDigestResult.2
          right.1.secretKey epoch randomness encoding, rfl, rfl, ?_⟩
        exact congrArg some
          (keygenViews_signWithEncoding_larger_eq_replaced selected left
          right hrel hleftSupport hrightSupport leftDigestResult.2
          rightDigestResult.2
          (fun input hinput => hdigest.2.1 input (Or.inl hinput))
          (hleftLe.trans hdigest.2.2.1)
          (hrightLe.trans hdigest.2.2.2.1) epoch randomness encoding)

def SignResultRelation
    (table : ChainValueIndex → Digest) (selected : ChainIndex)
    (parameter : PublicParameter) (epoch : Epoch) (message : Message)
    (initialLeft initialRight : QueryCache HashSpec)
    (leftResult rightResult : Option Signature × QueryCache HashSpec) : Prop :=
  ∃ randomness,
    SignAttemptResultRelation table selected parameter epoch message randomness
      initialLeft initialRight leftResult rightResult

noncomputable def sampledBoundedSignStep
    (attempts : Nat) (secretKey : SecretKey) (request : SignRequest)
    (cache : QueryCache HashSpec) :
    ProbComp (Option Signature × QueryCache HashSpec) :=
  (simulateQ xmssRomImpl
    (Concrete.signBoundedAttempts (attempts + 1) secretKey
      request.epoch request.message)).run cache

set_option maxRecDepth 100000 in
theorem Concrete.signBoundedAttempts_run_succ_eq_sampledStep
    (attempts : Nat) (secretKey : SecretKey) (request : SignRequest)
    (cache : QueryCache HashSpec) :
    (simulateQ xmssRomImpl
      (Concrete.signBoundedAttempts (attempts + 1) secretKey
        request.epoch request.message)).run cache =
      sampledBoundedSignStep attempts secretKey request cache := by
  rfl

set_option maxRecDepth 100000 in
theorem relTriple_keygenViews_sampledSignAttemptBind
    (continuationLeft :
      (Option Signature × QueryCache HashSpec) → ProbComp α)
    (continuationRight :
      (Option Signature × QueryCache HashSpec) → ProbComp β)
    (postcondition : α → β → Prop)
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenStableRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1 ∈ support (actualFixedChainKeygen selected))
    (leftCache rightCache : QueryCache HashSpec)
    (hcacheAgreement : HashCachesAgreeOn
      (SigningComparableHashInput left.secretKey.parameter selected)
      leftCache rightCache)
    (hleftLe : left.cache ≤ leftCache)
    (hrightLe : right.1.cache ≤ rightCache)
    (request : SignRequest)
    (hcontinuation : ∀ randomness leftResult rightResult,
      SignAttemptResultRelation right.2 selected left.secretKey.parameter
        request.epoch request.message randomness left.cache right.1.cache
        leftResult rightResult →
      RelTriple (continuationLeft leftResult) (continuationRight rightResult)
        postcondition) :
    RelTriple
      (($ᵗ Randomness) >>= fun randomness =>
        (simulateQ randomOracle
          (Concrete.signAttempt left.secretKey request.epoch request.message
            randomness : OracleComp HashSpec (Option Signature))).run
              leftCache >>= continuationLeft)
      (($ᵗ Randomness) >>= fun randomness =>
        (simulateQ randomOracle
          (Concrete.signAttempt right.1.secretKey request.epoch request.message
            randomness : OracleComp HashSpec (Option Signature))).run
              rightCache >>= continuationRight)
      postcondition := by
  refine relTriple_bind
    (R := fun leftRandomness rightRandomness : Randomness =>
      leftRandomness = rightRandomness)
    (S := postcondition)
    (fa := fun randomness =>
      (simulateQ randomOracle
        (Concrete.signAttempt left.secretKey request.epoch request.message
          randomness)).run leftCache >>= continuationLeft)
    (fb := fun randomness =>
      (simulateQ randomOracle
        (Concrete.signAttempt right.1.secretKey request.epoch request.message
          randomness)).run rightCache >>= continuationRight)
    (relTriple_refl ($ᵗ Randomness)) ?_
  intro leftRandomness rightRandomness heq
  subst rightRandomness
  apply relTriple_bind
    (S := postcondition)
    (fa := continuationLeft)
    (fb := continuationRight)
    (relTriple_keygenViews_signAttempt_run selected left right hrel
      hleftSupport hrightSupport leftCache rightCache hcacheAgreement
      hleftLe hrightLe request.epoch request.message leftRandomness)
  exact hcontinuation leftRandomness

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
theorem relTriple_keygenViews_sampledBoundedSignStep
    (attempts : Nat) (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenStableRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1 ∈ support (actualFixedChainKeygen selected))
    (leftCache rightCache : QueryCache HashSpec)
    (hcacheAgreement : HashCachesAgreeOn
      (SigningComparableHashInput left.secretKey.parameter selected)
      leftCache rightCache)
    (hleftLe : left.cache ≤ leftCache)
    (hrightLe : right.1.cache ≤ rightCache)
    (request : SignRequest)
    (postcondition :
      (Option Signature × QueryCache HashSpec) →
      (Option Signature × QueryCache HashSpec) → Prop)
    (hcontinuation : ∀ randomness leftResult rightResult,
      SignAttemptResultRelation right.2 selected left.secretKey.parameter
        request.epoch request.message randomness left.cache right.1.cache
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
    (relTriple_keygenViews_signAttempt_run selected left right hrel
      hleftSupport hrightSupport leftCache rightCache hcacheAgreement
      hleftLe hrightLe request.epoch request.message leftRandomness)
  exact hcontinuation leftRandomness

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
theorem relTriple_keygenViews_signBoundedAttempts_succ_run
    (attempts : Nat) (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenStableRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1 ∈ support (actualFixedChainKeygen selected))
    (leftCache rightCache : QueryCache HashSpec)
    (hcacheAgreement : HashCachesAgreeOn
      (SigningComparableHashInput left.secretKey.parameter selected)
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
      (SignResultRelation right.2 selected left.secretKey.parameter
        request.epoch request.message left.cache right.1.cache) := by
  induction attempts generalizing leftCache rightCache with
  | zero =>
      rw [Concrete.signBoundedAttempts_run_succ_eq_sampledStep,
        Concrete.signBoundedAttempts_run_succ_eq_sampledStep]
      refine relTriple_keygenViews_sampledBoundedSignStep 0 selected left right
        hrel hleftSupport hrightSupport leftCache rightCache hcacheAgreement
          hleftLe hrightLe request
          (SignResultRelation right.2 selected left.secretKey.parameter
            request.epoch request.message left.cache right.1.cache) ?_
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
          rw [hleftSome, hrightSome]
          simp only [simulateQ_pure, StateT.run_pure]
          apply relTriple_pure_pure
          exact ⟨randomness, some encoding, hdecode,
            ⟨signature, hrandomness, rfl, rfl⟩, hcaches,
            hleftFinal, hrightFinal⟩
  | succ attempts ih =>
      rw [Concrete.signBoundedAttempts_run_succ_eq_sampledStep,
        Concrete.signBoundedAttempts_run_succ_eq_sampledStep]
      refine relTriple_keygenViews_sampledBoundedSignStep (attempts + 1)
        selected left right hrel hleftSupport hrightSupport leftCache rightCache
          hcacheAgreement hleftLe hrightLe request
          (SignResultRelation right.2 selected left.secretKey.parameter
            request.epoch request.message left.cache right.1.cache) ?_
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
          rw [hleftSome, hrightSome]
          simp only [simulateQ_pure, StateT.run_pure]
          apply relTriple_pure_pure
          exact ⟨randomness, some encoding, hdecode,
            ⟨signature, hrandomness, rfl, rfl⟩, hcaches,
            hleftFinal, hrightFinal⟩

set_option maxRecDepth 100000 in
theorem relTriple_keygenViews_sign_run
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenStableRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1 ∈ support (actualFixedChainKeygen selected))
    (leftCache rightCache : QueryCache HashSpec)
    (hcacheAgreement : HashCachesAgreeOn
      (SigningComparableHashInput left.secretKey.parameter selected)
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
      (SignResultRelation right.2 selected left.secretKey.parameter
        request.epoch request.message left.cache right.1.cache) := by
  simp only [Concrete.scheme]
  have hleftKey := programmedWarmedFixedChainKeygen_support_keyResult
    selected left hleftSupport
  have hrightKey := actualFixedChainKeygen_support_keyResult
    selected right.1 hrightSupport
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
  exact relTriple_keygenViews_signBoundedAttempts_succ_run
    (signingAttemptLimit - 1) selected left right hrel hleftSupport
      hrightSupport leftCache rightCache hcacheAgreement hleftLe hrightLe request

def SigningQueryResultRelation
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftBase rightBase : QueryCache HashSpec)
    (table : ChainValueIndex → Digest)
    (leftResult : Option Signature × QueryCache HashSpec)
    (rightResult : (Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) : Prop :=
  leftResult.1 = rightResult.1.1 ∧
    HashCachesAgreeOn (SigningComparableHashInput parameter selected)
      leftResult.2 rightResult.1.2.cache ∧
    leftBase ≤ leftResult.2 ∧ rightBase ≤ rightResult.1.2.cache ∧
    CausalRevealsAgree table rightResult.1.2 ∧
    CausalCacheExtendsKeygen rightResult.1.2

set_option maxRecDepth 100000 in
theorem relTriple_keygenViews_causalSigningQuery_run
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenStableRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1 ∈ support (actualFixedChainKeygen selected))
    (leftCache : QueryCache HashSpec) (rightState : CausalHashState)
    (hcacheAgreement : HashCachesAgreeOn
      (SigningComparableHashInput left.secretKey.parameter selected)
      leftCache rightState.cache)
    (hleftLe : left.cache ≤ leftCache)
    (hrightLe : right.1.cache ≤ rightState.cache)
    (hkeygenCache : rightState.keygenCache = right.1.cache)
    (hreveals : CausalRevealsAgree right.2 rightState)
    (request : SignRequest) :
    RelTriple
      ((simulateQ xmssRomImpl
        (Concrete.scheme.sign left.publicKey
          (Concrete.materializePrecomputation left.cache left.secretKey)
          request.epoch request.message)).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.2)
        (causalSigningQueryAfterRealRom right.1.publicKey
          (Concrete.materializePrecomputation right.1.cache right.1.secretKey)
            selected request rightState)).run)
      (SigningQueryResultRelation left.secretKey.parameter selected
        left.cache right.1.cache right.2) := by
  have hsign := relTriple_keygenViews_sign_run selected left right hrel
    hleftSupport hrightSupport leftCache rightState.cache hcacheAgreement
    hleftLe hrightLe request
  unfold causalSigningQueryAfterRealRom
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, List.nil_append]
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
  rcases hsigned with ⟨randomness, decoded, hdecode, hoptions,
    hcaches, hleftFinal, hrightFinal⟩
  cases decoded with
  | none =>
      rcases hoptions with ⟨hleftNone, hrightNone⟩
      rw [hrightNone]
      simp only [revealFixedChainSignatureOption_run, simulateQ_pure,
        WriterT.run_pure]
      apply relTriple_pure_pure
      unfold SigningQueryResultRelation
      refine ⟨hleftNone, hcaches, hleftFinal, hrightFinal,
        hreveals.setCache rightSigned.2, ?_⟩
      rw [CausalCacheExtendsKeygen, hkeygenCache]
      exact hrightFinal
  | some encoding =>
      rcases hoptions with ⟨signature, hrandomness, hrightSome, hleftSome⟩
      rw [hrightSome]
      have hparameter : left.secretKey.parameter =
          right.1.secretKey.parameter := by
        have hleftKey := programmedWarmedFixedChainKeygen_support_keyResult
          selected left hleftSupport
        have hrightKey := actualFixedChainKeygen_support_keyResult
          selected right.1 hrightSupport
        calc
          left.secretKey.parameter = left.publicKey.parameter :=
            (left.parameter_eq hleftKey).symm
          _ = right.1.publicKey.parameter :=
            congrArg PublicKey.parameter hrel.1.1.2.1
          _ = right.1.secretKey.parameter :=
            right.1.parameter_eq hrightKey
      have hencodingHash :
          Concrete.CacheView.encodingHash leftSigned.2
              left.secretKey.parameter request.epoch
                (request.message, randomness) =
            Concrete.CacheView.encodingHash rightSigned.2
              right.1.secretKey.parameter request.epoch
                (request.message, randomness) := by
        rw [← hparameter]
        unfold Concrete.CacheView.encodingHash Concrete.CacheView.digestAt
        rw [hcaches _ (Or.inr
          ⟨request.epoch, request.message, randomness, rfl⟩)]
      have hdecodeRight : TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash rightSigned.2
            right.1.secretKey.parameter request.epoch
              (request.message, signature.randomness)) = some encoding := by
        rw [hrandomness, ← hencodingHash]
        exact hdecode
      have hreveal :
          revealFixedChainSignatureOption
              (Concrete.materializePrecomputation right.1.cache right.1.secretKey)
                selected request (some signature) =
            revealFixedChainSignatureOption right.1.secretKey selected request
              (some signature) := by
        unfold revealFixedChainSignatureOption
        rfl
      rw [hreveal]
      rw [simulate_eagerTrace_revealFixedChainSignatureOption_some_of_decode
        right.2 right.1.secretKey selected request signature
          { rightState with cache := rightSigned.2 } encoding hdecodeRight]
      apply relTriple_pure_pure
      unfold SigningQueryResultRelation
      have hsignature :
          leftSigned.1 = some (replaceSignatureChainValue signature selected
            (right.2 (request.epoch, encoding selected))) := hleftSome
      refine ⟨hsignature, hcaches, hleftFinal, hrightFinal, ?_, ?_⟩
      · apply (hreveals.setCache rightSigned.2).recordReveal
        rfl
      · rw [CausalCacheExtendsKeygen, hkeygenCache]
        exact hrightFinal

end XmssSecurity.CappedChain
