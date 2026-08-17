import XmssSecurity.CausalTreeWarmup
import XmssSecurity.MarginalCoupling

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

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

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem treeValue_probability_from_cache
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (index : TreeValueIndex) (cache : QueryCache HashSpec)
    (hfresh : ∀ input,
      AtHashAddress parameter index.domain input → cache input = none)
    (target : Digest) :
    Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
      (simulateQ randomOracle (index.computation parameter secret)).run cache] =
      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  by_cases hzero : index.1.val = 0
  · unfold TreeValueIndex.computation
    rw [hzero, Concrete.treeNode_zero_eq]
    apply Concrete.leafAt_probability_from_cache
    intro input hinput
    apply hfresh input
    unfold TreeValueIndex.domain
    rw [dif_pos hzero]
    exact hinput
  · have hsucc : index.1.val = (index.1.val - 1) + 1 := by omega
    unfold TreeValueIndex.computation
    rw [hsucc]
    apply Concrete.treeNode_positive_probability_from_cache
      (parameter := parameter) (secret := secret)
      (levels := index.1.val - 1) (node := index.node)
      (hlevel := by omega) (hvalid := by
        simpa [← hsucc] using index.subtreeValid)
      (initialCache := cache)
    intro input hinput
    apply hfresh input
    unfold TreeValueIndex.domain
    rw [dif_neg hzero]
    exact hinput

set_option maxRecDepth 100000 in
theorem evalDist_treeValue_eq_uniform
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (index : TreeValueIndex) (cache : QueryCache HashSpec)
    (hfresh : ∀ input,
      AtHashAddress parameter index.domain input → cache input = none) :
    𝒟[Prod.fst <$> (simulateQ randomOracle
      (index.computation parameter secret)).run cache] =
      𝒟[$ᵗ Digest] := by
  apply SPMF.ext
  intro target
  change Pr[= target | Prod.fst <$> (simulateQ randomOracle
      (index.computation parameter secret)).run cache] =
    Pr[= target | $ᵗ Digest]
  rw [← probEvent_eq_eq_probOutput, probEvent_map]
  calc
    Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
        (simulateQ randomOracle
          (index.computation parameter secret)).run cache] =
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
      treeValue_probability_from_cache parameter secret index cache hfresh target
    _ = Pr[= target | $ᵗ Digest] := by
      rw [probOutput_uniformSample, HiddenValue.card_digest]

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
theorem evalDist_treeValues_values_eq_drawList
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    ∀ (indices : List TreeValueIndex) (cache : QueryCache HashSpec),
      indices.Pairwise TreeValueIndex.Precedes →
      TreeValuesFresh parameter indices cache →
      𝒟[Prod.fst <$> treeValues parameter secret indices cache] =
      𝒟[OracleComp.drawList ($ᵗ Digest) indices.length] := by
  intro indices
  induction indices with
  | nil =>
      intro cache _hordered _hfresh
      simp [OracleComp.drawList]
  | cons current indices ih =>
      intro cache hordered hfresh
      have hcurrentOrdered : ∀ target ∈ indices,
          current.Precedes target :=
        (List.pairwise_cons.mp hordered).1
      have htailOrdered : indices.Pairwise TreeValueIndex.Precedes :=
        (List.pairwise_cons.mp hordered).2
      have hcurrentFresh : ∀ input,
          AtHashAddress parameter current.domain input →
          cache input = none := by
        intro input hinput
        exact hfresh current (by simp) input hinput
      rw [treeValues_cons, map_eq_bind_pure_comp]
      simp only [bind_assoc, pure_bind, Function.comp_apply]
      calc
        𝒟[(simulateQ randomOracle
              (current.computation parameter secret)).run cache >>=
            fun headResult =>
              treeValues parameter secret indices headResult.2 >>=
                fun tailResult =>
                  pure (headResult.1 :: tailResult.1)] =
          𝒟[(simulateQ randomOracle
              (current.computation parameter secret)).run cache >>=
            fun headResult =>
              OracleComp.drawList ($ᵗ Digest) indices.length >>= fun tail =>
                pure (headResult.1 :: tail)] := by
            apply evalDist_bind_congr
            intro headResult hheadResult
            have htailFresh := treeValue_preserves_tail_fresh
              parameter secret current indices hcurrentOrdered cache hfresh
                headResult hheadResult
            calc
              𝒟[treeValues parameter secret indices headResult.2 >>=
                  fun tailResult =>
                    pure (headResult.1 :: tailResult.1)] =
                𝒟[(Prod.fst <$> treeValues parameter secret indices
                    headResult.2) >>= fun tail =>
                      pure (headResult.1 :: tail)] := by
                    simp [map_eq_bind_pure_comp, bind_assoc]
              _ = 𝒟[OracleComp.drawList ($ᵗ Digest) indices.length >>=
                    fun tail => pure (headResult.1 :: tail)] := by
                    rw [evalDist_bind,
                      ih headResult.2 htailOrdered htailFresh,
                      ← evalDist_bind]
        _ = 𝒟[(Prod.fst <$> (simulateQ randomOracle
              (current.computation parameter secret)).run cache) >>=
            fun head =>
              OracleComp.drawList ($ᵗ Digest) indices.length >>= fun tail =>
                pure (head :: tail)] := by
            simp [map_eq_bind_pure_comp, bind_assoc]
        _ = 𝒟[($ᵗ Digest) >>= fun head =>
            OracleComp.drawList ($ᵗ Digest) indices.length >>= fun tail =>
              pure (head :: tail)] := by
            rw [evalDist_bind,
              evalDist_treeValue_eq_uniform parameter secret current cache
                hcurrentFresh,
              ← evalDist_bind]
        _ = 𝒟[OracleComp.drawList ($ᵗ Digest)
            (current :: indices).length] := by
            rfl

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem relTriple_treeValues_same_values
    (leftParameter rightParameter : PublicParameter)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (indices : List TreeValueIndex)
    (leftCache rightCache : QueryCache HashSpec)
    (hordered : indices.Pairwise TreeValueIndex.Precedes)
    (hleftFresh : TreeValuesFresh leftParameter indices leftCache)
    (hrightFresh : TreeValuesFresh rightParameter indices rightCache) :
    RelTriple
      (treeValues leftParameter leftSecret indices leftCache)
      (treeValues rightParameter rightSecret indices rightCache)
      (fun left right =>
        left.1 = right.1 ∧
          TreeValuesReplay leftParameter leftSecret left.2 indices left.1 ∧
          TreeValuesReplay rightParameter rightSecret right.2 indices right.1) := by
  have hvalues :
      𝒟[Prod.fst <$> treeValues leftParameter leftSecret indices leftCache] =
        𝒟[Prod.fst <$> treeValues rightParameter rightSecret indices rightCache] := by
    calc
      𝒟[Prod.fst <$> treeValues leftParameter leftSecret indices leftCache] =
          𝒟[OracleComp.drawList ($ᵗ Digest) indices.length] :=
        evalDist_treeValues_values_eq_drawList leftParameter leftSecret
          indices leftCache hordered hleftFresh
      _ = 𝒟[Prod.fst <$> treeValues rightParameter rightSecret indices
          rightCache] :=
        (evalDist_treeValues_values_eq_drawList rightParameter rightSecret
          indices rightCache hordered hrightFresh).symm
  apply relTriple_post_mono
    (relTriple_of_evalDist_map_eq_with_support_general
      (treeValues leftParameter leftSecret indices leftCache)
      (treeValues rightParameter rightSecret indices rightCache)
      Prod.fst Prod.fst hvalues)
  intro left right hrelation
  exact ⟨hrelation.1,
    treeValues_support_replay leftParameter leftSecret indices leftCache left
      hrelation.2.1,
    treeValues_support_replay rightParameter rightSecret indices rightCache right
      hrelation.2.2⟩

def treeValueIndicesAtHeight (height : Fin (treeHeight + 1)) :
    List TreeValueIndex :=
  List.ofFn fun node : Fin (2 ^ (treeHeight - height.val)) => ⟨height, node⟩

def allTreeValueIndices : List TreeValueIndex :=
  (List.ofFn fun height : Fin (treeHeight + 1) => height).flatMap
    treeValueIndicesAtHeight

theorem allTreeValueIndices_pairwise :
    allTreeValueIndices.Pairwise TreeValueIndex.Precedes := by
  simp only [allTreeValueIndices, List.pairwise_flatMap,
    List.pairwise_ofFn]
  constructor
  · intro height _hheight
    simp only [treeValueIndicesAtHeight, List.pairwise_ofFn]
    intro left right hlt
    unfold TreeValueIndex.Precedes
    right
    constructor
    · rfl
    · exact hlt
  · intro left right hlt current hcurrent target htarget
    rw [treeValueIndicesAtHeight, List.mem_ofFn] at hcurrent htarget
    obtain ⟨currentNode, rfl⟩ := hcurrent
    obtain ⟨targetNode, rfl⟩ := htarget
    unfold TreeValueIndex.Precedes
    exact Or.inl hlt

theorem allTreeValueIndices_nodup : allTreeValueIndices.Nodup := by
  apply allTreeValueIndices_pairwise.imp
  intro left right hbefore heq
  subst right
  unfold TreeValueIndex.Precedes at hbefore
  omega

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

theorem programmedWarmedTrajectory_treeValues_fresh
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex)
    (trajectoryResult : List FullChainTrajectory × QueryCache HashSpec)
    (htrajectory : trajectoryResult ∈ support
      (programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs)) :
    TreeValuesFresh parameter allTreeValueIndices trajectoryResult.2 := by
  intro index _hindex input hinput
  by_cases hzero : index.1.val = 0
  · unfold TreeValueIndex.domain at hinput
    rw [dif_pos hzero] at hinput
    exact programmedFixedSeedChainTrajectories_avoids_leaf
      parameter secret chain trajectoryResult htrajectory index.node input hinput
  · unfold TreeValueIndex.domain at hinput
    rw [dif_neg hzero] at hinput
    exact programmedFixedSeedChainTrajectories_avoids_merkle
      parameter secret chain trajectoryResult htrajectory
        ⟨index.1.val - 1, by omega⟩ index.node input hinput

set_option maxRecDepth 1000000 in
theorem evalDist_programmedWarmedTreeValues_eq_drawList
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex)
    (trajectoryResult : List FullChainTrajectory × QueryCache HashSpec)
    (htrajectory : trajectoryResult ∈ support
      (programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs)) :
    𝒟[Prod.fst <$> treeValues parameter secret allTreeValueIndices
      trajectoryResult.2] =
      𝒟[OracleComp.drawList ($ᵗ Digest) allTreeValueIndices.length] := by
  exact evalDist_treeValues_values_eq_drawList parameter secret
    allTreeValueIndices trajectoryResult.2 allTreeValueIndices_pairwise
      (programmedWarmedTrajectory_treeValues_fresh parameter secret chain
        trajectoryResult htrajectory)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem relTriple_programmedWarmedTreeValues_same_root_and_paths
    (parameter : PublicParameter)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex)
    (leftTrajectory rightTrajectory :
      List FullChainTrajectory × QueryCache HashSpec)
    (hleft : leftTrajectory ∈ support
      (programmedFixedSeedChainTrajectoriesFromCache parameter leftSecret chain
        (chainLength - 1) ∅ allEpochs))
    (hright : rightTrajectory ∈ support
      (programmedFixedSeedChainTrajectoriesFromCache parameter rightSecret chain
        (chainLength - 1) ∅ allEpochs)) :
    RelTriple
      (treeValues parameter leftSecret allTreeValueIndices leftTrajectory.2)
      (treeValues parameter rightSecret allTreeValueIndices rightTrajectory.2)
      (fun left right =>
        left.1 = right.1 ∧
          TreeValuesReplay parameter leftSecret left.2
            allTreeValueIndices left.1 ∧
          TreeValuesReplay parameter rightSecret right.2
            allTreeValueIndices right.1 ∧
          Concrete.CacheReplay.treeNode left.2 parameter leftSecret
              treeHeight Concrete.rootNode =
            Concrete.CacheReplay.treeNode right.2 parameter rightSecret
              treeHeight Concrete.rootNode ∧
          ∀ epoch,
            Concrete.CacheReplay.authenticationPath left.2
                (SecretKey.withoutPrecomputation parameter leftSecret) epoch =
              Concrete.CacheReplay.authenticationPath right.2
                (SecretKey.withoutPrecomputation parameter rightSecret) epoch) := by
  apply relTriple_post_mono
    (relTriple_treeValues_same_values parameter parameter leftSecret rightSecret
      allTreeValueIndices leftTrajectory.2 rightTrajectory.2
      allTreeValueIndices_pairwise
      (programmedWarmedTrajectory_treeValues_fresh parameter leftSecret chain
        leftTrajectory hleft)
      (programmedWarmedTrajectory_treeValues_fresh parameter rightSecret chain
        rightTrajectory hright))
  intro left right hrelation
  obtain ⟨hvalues, hleftReplay, hrightReplay⟩ := hrelation
  refine ⟨hvalues, hleftReplay, hrightReplay, ?_, ?_⟩
  · exact globalTreeValuesReplay_eq_root parameter leftSecret rightSecret
      left.2 right.2 left.1 hleftReplay (hvalues ▸ hrightReplay)
  · intro epoch
    exact globalTreeValuesReplay_eq_authenticationPath parameter
      leftSecret rightSecret left.2 right.2 left.1 hleftReplay
        (hvalues ▸ hrightReplay) epoch

end XmssSecurity
