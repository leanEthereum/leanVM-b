import XmssSecurity.Proof.ChainValueUniformity
import XmssSecurity.Proof.MerkleQueryBound

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

noncomputable def Concrete.treeChildren (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (levels : Nat)
    (node : MerkleNode) : OracleComp HashSpec (Digest × Digest) := do
  let left ← Concrete.treeNode parameter secret levels
    (Concrete.childNode node false)
  let right ← Concrete.treeNode parameter secret levels
    (Concrete.childNode node true)
  return (left, right)

theorem Concrete.treeChildren_queryBound_parentAddress
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (levels : Nat) (node : MerkleNode) (hlevel : levels < treeHeight)
    (hvalid : TreeSubtreeValid (levels + 1) node) :
    (Concrete.treeChildren parameter secret levels node).IsQueryBoundP
      (AtHashAddress parameter (.merkle ⟨levels, hlevel⟩ node)) 0 := by
  unfold Concrete.treeChildren
  have hleft := Concrete.treeNode_queryBound_merkleAddress parameter secret
    ⟨levels, hlevel⟩ node levels (Concrete.childNode node false)
    (Nat.le_of_lt hlevel) (childNode_subtreeValid levels node false hvalid)
  have hright := Concrete.treeNode_queryBound_merkleAddress parameter secret
    ⟨levels, hlevel⟩ node levels (Concrete.childNode node true)
    (Nat.le_of_lt hlevel) (childNode_subtreeValid levels node true hvalid)
  have hleftZero :
      (Concrete.treeNode parameter secret levels (Concrete.childNode node false) :
        OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.merkle ⟨levels, hlevel⟩ node)) 0 := by
    simpa [MerkleAddressInSubtree] using hleft
  have hrightZero :
      (Concrete.treeNode parameter secret levels (Concrete.childNode node true) :
        OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.merkle ⟨levels, hlevel⟩ node)) 0 := by
    simpa [MerkleAddressInSubtree] using hright
  refine OracleComp.isQueryBoundP_bind (n := 0) (m := 0) hleftZero ?_
  intro left _
  refine OracleComp.isQueryBoundP_bind (n := 0) (m := 0) hrightZero ?_
  intro right _
  exact OracleComp.isQueryBoundP_pure
    (p := AtHashAddress parameter (.merkle ⟨levels, hlevel⟩ node))
    (left, right) 0

/-- The root of a valid positive-height subtree is uniform because its final Merkle query is fresh. -/
theorem Concrete.treeNode_positive_probability_from_cache
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (levels : Nat) (node : MerkleNode) (hlevel : levels < treeHeight)
    (hvalid : TreeSubtreeValid (levels + 1) node)
    (initialCache : QueryCache HashSpec)
    (habsent : ∀ input,
      AtHashAddress parameter (.merkle ⟨levels, hlevel⟩ node) input →
        initialCache input = none)
    (target : Digest) :
    Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
      (simulateQ randomOracle
        (Concrete.treeNode parameter secret (levels + 1) node :
          OracleComp HashSpec Digest)).run initialCache] =
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [Concrete.treeNode_succ_eq]
  simp only [hlevel, ↓reduceDIte]
  have hfactor :
      (do
        let left ← Concrete.treeNode parameter secret levels
          (Concrete.childNode node false)
        let right ← Concrete.treeNode parameter secret levels
          (Concrete.childNode node true)
        Concrete.nodeHash parameter ⟨levels, hlevel⟩ node left right :
          OracleComp HashSpec Digest) =
        (Concrete.treeChildren parameter secret levels node >>= fun children =>
          Concrete.nodeHash parameter ⟨levels, hlevel⟩ node
            children.1 children.2) := by
    simp [Concrete.treeChildren]
  rw [hfactor]
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  have hchildrenBound := Concrete.treeChildren_queryBound_parentAddress
    parameter secret levels node hlevel hvalid
  have hconditional : ∀ childrenResult ∈ support
      ((simulateQ randomOracle
        (Concrete.treeChildren parameter secret levels node)).run initialCache),
      Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
        (simulateQ randomOracle
          (Concrete.nodeHash parameter ⟨levels, hlevel⟩ node
            childrenResult.1.1 childrenResult.1.2 :
            OracleComp HashSpec Digest)).run childrenResult.2] =
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
    intro childrenResult hchildren
    apply Concrete.tweakableHash_fresh_probability
    apply Concrete.CacheReplay.cache_none_of_zero_query_bound
      (Concrete.treeChildren parameter secret levels node)
      (tweakableHashInput parameter (.merkle ⟨levels, hlevel⟩ node)
        (Concrete.nodePayload childrenResult.1.1 childrenResult.1.2))
      initialCache childrenResult.2 childrenResult.1
    · apply OracleComp.IsQueryBoundP.of_imp
        (p := fun input => input =
          tweakableHashInput parameter (.merkle ⟨levels, hlevel⟩ node)
            (Concrete.nodePayload childrenResult.1.1 childrenResult.1.2))
        (p' := AtHashAddress parameter (.merkle ⟨levels, hlevel⟩ node))
      · intro input heq
        subst input
        exact (atHashAddress_tweakableHashInput_iff parameter _ _ _).2 rfl
      · exact hchildrenBound
    · exact habsent _ ((atHashAddress_tweakableHashInput_iff parameter _ _ _).2 rfl)
    · exact hchildren
  calc
    ∑' childrenResult,
        Pr[= childrenResult |
          (simulateQ randomOracle
            (Concrete.treeChildren parameter secret levels node)).run initialCache] *
          Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
            (simulateQ randomOracle
              (Concrete.nodeHash parameter ⟨levels, hlevel⟩ node
                childrenResult.1.1 childrenResult.1.2 :
                OracleComp HashSpec Digest)).run childrenResult.2] =
      ∑' childrenResult,
        Pr[= childrenResult |
          (simulateQ randomOracle
            (Concrete.treeChildren parameter secret levels node)).run initialCache] *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      apply tsum_congr
      intro childrenResult
      by_cases hchildren : childrenResult ∈ support
          ((simulateQ randomOracle
            (Concrete.treeChildren parameter secret levels node)).run initialCache)
      · rw [hconditional childrenResult hchildren]
      · rw [probOutput_eq_zero_of_not_mem_support hchildren, zero_mul, zero_mul]
    _ = (∑' childrenResult,
        Pr[= childrenResult |
          (simulateQ randomOracle
            (Concrete.treeChildren parameter secret levels node)).run initialCache]) *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
      ENNReal.tsum_mul_right
    _ = ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      rw [tsum_probOutput_eq_one']
      · exact one_mul _
      · exact probFailure_eq_zero'
          (neverFail_simulateQ_randomOracle_run
            (Concrete.treeChildren parameter secret levels node) initialCache)

end XmssSecurity
