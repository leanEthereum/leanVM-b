import SphincsSecurity.Proof.FtsProbeSimulation

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open OracleComp OracleSpec

theorem ftsNode_leaf_query_mem
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index)
    (tree : FtsTree) (secret : FtsLeaf → Digest) (level nodeIdx : Nat)
    (leafIdx : FtsLeaf)
    (hlower : nodeIdx * 2 ^ level ≤ leafIdx.val)
    (hupper : leafIdx.val < (nodeIdx + 1) * 2 ^ level) :
    tweakableHashInput parameter (.ftsLeaf index tree leafIdx)
        (digestBytes (secret leafIdx)) ∈
      queriedInputs f (ftsNode parameter index tree secret level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero =>
      have hnodeIdx : nodeIdx = leafIdx.val := by
        norm_num at hlower hupper
        omega
      subst nodeIdx
      rw [ftsNode_zero_eq, ftsLeafOfNat_val]
      exact Concrete.ftsLeafHash_query_mem f parameter index tree leafIdx (secret leafIdx)
  | succ level ih =>
      rw [ftsNode_succ_eq]
      rw [pow_succ] at hlower hupper
      by_cases hleft : leafIdx.val < (2 * nodeIdx + 1) * 2 ^ level
      · apply queriedInputs_mono_bind_left
        exact ih (2 * nodeIdx) (by nlinarith [Nat.two_pow_pos level]) hleft
      · apply queriedInputs_mono_bind_right
        apply queriedInputs_mono_bind_left
        exact ih (2 * nodeIdx + 1) (by omega)
          (by nlinarith [Nat.two_pow_pos level])

theorem ftsKey_leaf_query_mem
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index)
    (secret : FtsTree → FtsLeaf → Digest) (tree : FtsTree) (leafIdx : FtsLeaf) :
    tweakableHashInput parameter (.ftsLeaf index tree leafIdx)
        (digestBytes (secret tree leafIdx)) ∈
      queriedInputs f (ftsKey parameter index secret) := by
  unfold ftsKey
  apply queriedInputs_mono_bind_left
  apply Concrete.sequenceFin_component_query_mem f _ tree
  exact ftsNode_leaf_query_mem f parameter index tree (secret tree) ftsTreeHeight 0 leafIdx
    (by simp) (by simp)

set_option maxHeartbeats 800000 in
theorem hiddenLeaves_cached_of_mem_runDetailed_maskedFtsKey
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache finalCache : SplitHashCache) (index : Index) (value : Digest)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hresult : .done false finalState (value, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((maskedFtsKey parameter index).run cache))) :
    ∀ tree leafIdx, ∃ output,
      finalCache (.hiddenLeaf (index, tree, leafIdx)) = some output := by
  have hmapped : some (value, mergedCache parameter table finalCache) ∈ support
      (projectDetailedCache parameter table <$>
        AdaptiveRevealProbe.runDetailed table state fuel
          ((maskedFtsKey parameter index).run cache)) := by
    rw [support_map, Set.mem_image]
    exact ⟨.done false finalState (value, finalCache), hresult, rfl⟩
  rw [coupled_maskedFtsKey parameter table state fuel index hclean cache] at hmapped
  obtain ⟨ordinaryResult, hordinaryResult, hresultEq⟩ :=
    OracleComp.mem_support_map_peel some
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (ftsKey parameter index (fun tree leafIdx => table (index, tree, leafIdx)))).run
          (mergedCache parameter table cache)) hmapped
  have hordinaryEq : ordinaryResult =
      (value, mergedCache parameter table finalCache) :=
    Option.some.inj hresultEq.symm
  subst ordinaryResult
  obtain ⟨answerFn, hagrees⟩ := QueryCache.exists_agreesWithFn
    (spec := HashSpec) (mergedCache parameter table finalCache)
  have hreplay := replay_of_mem_support
    (ftsKey parameter index (fun tree leafIdx => table (index, tree, leafIdx)))
    (mergedCache parameter table cache) value (mergedCache parameter table finalCache)
    hordinaryResult answerFn hagrees
  intro tree leafIdx
  have hcached := hreplay.2.2
    (hiddenInput parameter table (index, tree, leafIdx))
    (ftsKey_leaf_query_mem answerFn parameter index
      (fun tree leafIdx => table (index, tree, leafIdx)) tree leafIdx)
  rw [mergedCache_hiddenInput] at hcached
  cases hlookup : finalCache (.hiddenLeaf (index, tree, leafIdx)) with
  | none => exact (hcached hlookup).elim
  | some output => exact ⟨output, rfl⟩

end SphincsSecurity.Concrete.FtsProbeSimulation
