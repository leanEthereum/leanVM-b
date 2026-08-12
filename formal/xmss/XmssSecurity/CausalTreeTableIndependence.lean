import XmssSecurity.CausalTreeWarmup

open OracleComp OracleSpec ENNReal

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

end XmssSecurity
