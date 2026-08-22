import XmssSecurity.Proof.CausalTreeCoupling
import XmssSecurity.Proof.StatementLemmas

open OracleComp OracleSpec

namespace XmssSecurity

theorem treeValues_append
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    ∀ (left right : List TreeValueIndex) (cache : QueryCache HashSpec),
      treeValues parameter secret (left ++ right) cache = (do
        let leftResult ← treeValues parameter secret left cache
        let rightResult ← treeValues parameter secret right leftResult.2
        pure (leftResult.1 ++ rightResult.1, rightResult.2)) := by
  intro left
  induction left with
  | nil =>
      intro right cache
      simp
  | cons current left ih =>
      intro right cache
      rw [List.cons_append, treeValues_cons, treeValues_cons]
      simp [ih, bind_assoc]

theorem treeValues_append_support
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (left right : List TreeValueIndex) (cache : QueryCache HashSpec)
    (leftResult rightResult : List Digest × QueryCache HashSpec)
    (hleft : leftResult ∈ support
      (treeValues parameter secret left cache))
    (hright : rightResult ∈ support
      (treeValues parameter secret right leftResult.2)) :
    (leftResult.1 ++ rightResult.1, rightResult.2) ∈ support
      (treeValues parameter secret (left ++ right) cache) := by
  rw [treeValues_append, mem_support_bind_iff]
  refine ⟨leftResult, hleft, ?_⟩
  rw [mem_support_bind_iff]
  exact ⟨rightResult, hright, by simp⟩

theorem treeValues_singleton_support
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (index : TreeValueIndex) (cache : QueryCache HashSpec)
    (result : Digest × QueryCache HashSpec)
    (hresult : result ∈ support
      ((simulateQ randomOracle
        (index.computation parameter secret)).run cache)) :
    ([result.1], result.2) ∈ support
      (treeValues parameter secret [index] cache) := by
  rw [treeValues_cons, mem_support_bind_iff]
  refine ⟨result, hresult, ?_⟩
  simp

set_option maxRecDepth 100000 in
def treeValueIndicesBelow : Nat → List TreeValueIndex
  | 0 => []
  | height + 1 =>
      treeValueIndicesBelow height ++
        if hheight : height < treeHeight + 1 then
          treeValueIndicesAtHeight ⟨height, hheight⟩
        else []

theorem treeValueIndicesBelow_succ (height : Nat)
    (hheight : height < treeHeight + 1) :
    treeValueIndicesBelow (height + 1) =
      treeValueIndicesBelow height ++
        treeValueIndicesAtHeight ⟨height, hheight⟩ := by
  rw [treeValueIndicesBelow, dif_pos hheight]

theorem mem_treeValueIndicesAtHeight_iff
    (height : Fin (treeHeight + 1)) (index : TreeValueIndex) :
    index ∈ treeValueIndicesAtHeight height ↔ index.1 = height := by
  constructor
  · intro hindex
    rw [treeValueIndicesAtHeight, List.mem_ofFn] at hindex
    obtain ⟨node, rfl⟩ := hindex
    rfl
  · intro hheight
    cases index with
    | mk indexHeight node =>
        dsimp only at hheight
        subst indexHeight
        rw [treeValueIndicesAtHeight, List.mem_ofFn]
        exact ⟨node, rfl⟩

def TreeValueIndex.child (current : TreeValueIndex)
    (hpositive : 0 < current.1.val) (right : Bool) : TreeValueIndex :=
  TreeValueIndex.ofSubtree (current.1.val - 1)
    (Concrete.childNode current.node right) (by omega)
    (childNode_subtreeValid (current.1.val - 1) current.node right
      (by simpa [Nat.sub_add_cancel hpositive] using current.subtreeValid))

theorem childTreeValueIndex_mem_below
    (current : TreeValueIndex) (hpositive : 0 < current.1.val)
    (right : Bool) :
    current.child hpositive right ∈
      treeValueIndicesBelow current.1.val := by
  let child := current.child hpositive right
  have hbound : current.1.val - 1 < treeHeight + 1 := by omega
  have hdecompose : current.1.val = (current.1.val - 1) + 1 := by omega
  have hbelow := congrArg treeValueIndicesBelow hdecompose
  rw [treeValueIndicesBelow_succ _ hbound] at hbelow
  rw [hbelow, List.mem_append]
  right
  apply (mem_treeValueIndicesAtHeight_iff
    ⟨current.1.val - 1, hbound⟩ child).2
  apply Fin.ext
  simp [child, TreeValueIndex.child]

theorem treeValues_preserves_fresh_after
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    ∀ (processed future : List TreeValueIndex),
      (∀ current ∈ processed, ∀ target ∈ future,
        current.Precedes target) →
      ∀ (cache : QueryCache HashSpec),
        TreeValuesFresh parameter future cache →
        ∀ result ∈ support
          (treeValues parameter secret processed cache),
          TreeValuesFresh parameter future result.2 := by
  intro processed
  induction processed with
  | nil =>
      intro future _hbefore cache hfresh result hresult
      simp only [treeValues_nil, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact hfresh
  | cons current processed ih =>
      intro future hbefore cache hfresh result hresult
      rw [treeValues_cons, mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htailBind⟩ := hresult
      rw [mem_support_bind_iff] at htailBind
      obtain ⟨tail, htail, hpure⟩ := htailBind
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      have hheadFresh : TreeValuesFresh parameter future head.2 := by
        intro target htarget input hinput
        exact treeValue_preserves_fresh_later parameter secret current target
          (hbefore current (by simp) target htarget) cache head hhead
          input hinput (hfresh target htarget input hinput)
      apply ih future
        (fun candidate hcandidate target htarget =>
          hbefore candidate (by simp [hcandidate]) target htarget)
        head.2 hheadFresh tail htail

theorem treeValueIndicesBelow_height_lt :
    ∀ (height : Nat), height ≤ treeHeight + 1 →
      ∀ index ∈ treeValueIndicesBelow height, index.1.val < height := by
  intro height
  induction height with
  | zero => simp [treeValueIndicesBelow]
  | succ height ih =>
      intro hbound index hindex
      have hheight : height < treeHeight + 1 := by omega
      rw [treeValueIndicesBelow_succ height hheight,
        List.mem_append] at hindex
      rcases hindex with hprior | hcurrent
      · exact (ih (by omega) index hprior).trans (by omega)
      · have heq :=
          (mem_treeValueIndicesAtHeight_iff ⟨height, hheight⟩ index).1
            hcurrent
        simp [congrArg Fin.val heq]

theorem treeValueIndicesBelow_eq_flatMap
    (height : Nat) (hheight : height ≤ treeHeight + 1) :
    treeValueIndicesBelow height =
      (List.ofFn fun index : Fin height =>
        (⟨index.val, index.isLt.trans_le hheight⟩ :
          Fin (treeHeight + 1))).flatMap treeValueIndicesAtHeight := by
  induction height with
  | zero => simp [treeValueIndicesBelow]
  | succ height ih =>
      have hlt : height < treeHeight + 1 := by omega
      rw [treeValueIndicesBelow_succ height hlt, ih (by omega),
        List.ofFn_succ']
      simp

theorem treeValueIndicesBelow_all :
    treeValueIndicesBelow (treeHeight + 1) = allTreeValueIndices := by
  rw [treeValueIndicesBelow_eq_flatMap (treeHeight + 1) le_rfl]
  unfold allTreeValueIndices
  apply congrArg (List.flatMap treeValueIndicesAtHeight)
  apply List.ofFn_inj.2
  funext index
  apply Fin.ext
  rfl


end XmssSecurity
