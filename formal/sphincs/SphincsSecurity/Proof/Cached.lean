import SphincsSecurity.Proof.Queried
import SphincsSecurity.Proof.Settled

/-!
# Cached honest computations settle positions

An executed computation is cached when every input in its answer-function trace occurs in the
cache. Honest chain and tree computations then settle every structural position they compute.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

def CachedRun {alpha : Type} (cache : QueryCache HashSpec) (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec alpha) : Prop :=
  ∀ input ∈ queriedInputs f oa, cache input ≠ none

theorem CachedRun.bind_left {alpha beta : Type} {cache : QueryCache HashSpec}
    {f : QueryImpl HashSpec Id} {oa : OracleComp HashSpec alpha}
    {next : alpha → OracleComp HashSpec beta} (h : CachedRun cache f (oa >>= next)) :
    CachedRun cache f oa := by
  intro input hinput
  exact h input (queriedInputs_mono_bind_left f oa next hinput)

theorem CachedRun.bind_right {alpha beta : Type} {cache : QueryCache HashSpec}
    {f : QueryImpl HashSpec Id} {oa : OracleComp HashSpec alpha}
    {next : alpha → OracleComp HashSpec beta} (h : CachedRun cache f (oa >>= next)) :
    CachedRun cache f (next (evalWithAnswerFn f oa)) := by
  intro input hinput
  exact h input (queriedInputs_mono_bind_right f oa next hinput)

theorem CachedRun.mono {alpha : Type} {cache cache' : QueryCache HashSpec}
    {f : QueryImpl HashSpec Id} {oa : OracleComp HashSpec alpha}
    (hle : cache ≤ cache') (h : CachedRun cache f oa) :
    CachedRun cache' f oa := by
  intro input hinput
  obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp (h input hinput)
  rw [hle hanswer]
  simp

theorem CachedRun.eval_eq {alpha : Type} {cache : QueryCache HashSpec}
    {f g : QueryImpl HashSpec Id} {oa : OracleComp HashSpec alpha}
    (hf : cache.AgreesWithFn f) (hg : cache.AgreesWithFn g)
    (hrun : CachedRun cache f oa) :
    evalWithAnswerFn f oa = evalWithAnswerFn g oa := by
  induction oa using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      have hcached : cache input ≠ none := by
        apply hrun input
        rw [queriedInputs_query_bind]
        exact List.mem_cons_self
      obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hcached
      have hfg : f input = g input := (hf hanswer).trans (hg hanswer).symm
      rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind,
        show evalWithAnswerFn f (liftM (HashSpec.query input)) = f input from
          simulateQ_spec_query f input,
        show evalWithAnswerFn g (liftM (HashSpec.query input)) = g input from
          simulateQ_spec_query g input, hfg]
      apply ih (g input)
      intro queried hqueried
      rw [← hfg] at hqueried
      apply hrun queried
      rw [queriedInputs_query_bind]
      exact List.mem_cons_of_mem input hqueried

theorem CachedRun.queriedInputs_eq {alpha : Type} {cache : QueryCache HashSpec}
    {f g : QueryImpl HashSpec Id} {oa : OracleComp HashSpec alpha}
    (hf : cache.AgreesWithFn f) (hg : cache.AgreesWithFn g)
    (hrun : CachedRun cache f oa) : queriedInputs f oa = queriedInputs g oa := by
  induction oa using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      have hcached : cache input ≠ none := by
        apply hrun input
        rw [queriedInputs_query_bind]
        exact List.mem_cons_self
      obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hcached
      have hfg : f input = g input := (hf hanswer).trans (hg hanswer).symm
      rw [queriedInputs_query_bind, queriedInputs_query_bind, ← hfg]
      congr 1
      apply ih (f input)
      intro queried hqueried
      apply hrun queried
      rw [queriedInputs_query_bind]
      exact List.mem_cons_of_mem input hqueried

theorem CachedRun.changeAnswerFn {alpha : Type} {cache : QueryCache HashSpec}
    {f g : QueryImpl HashSpec Id} {oa : OracleComp HashSpec alpha}
    (hf : cache.AgreesWithFn f) (hg : cache.AgreesWithFn g)
    (hrun : CachedRun cache f oa) : CachedRun cache g oa := by
  intro input hinput
  apply hrun input
  rw [hrun.queriedInputs_eq hf hg]
  exact hinput

theorem CachedRun.sequenceFin_component {alpha : Type} {n : Nat}
    {cache : QueryCache HashSpec} {f : QueryImpl HashSpec Id}
    (computation : Fin n → OracleComp HashSpec alpha)
    (h : CachedRun cache f (Concrete.sequenceFin computation)) (index : Fin n) :
    CachedRun cache f (computation index) := by
  intro input hinput
  apply h input
  exact Concrete.sequenceFin_component_query_mem f computation index hinput

namespace Concrete

variable {f : QueryImpl HashSpec Id} {parameter : PublicParameter}
  {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
  {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
  {cache : QueryCache HashSpec}

def TreeRange (level nodeIdx : Nat) : Prop :=
  2 ^ level * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight

private theorem TreeRange.index_lt {level nodeIdx : Nat} (h : TreeRange level nodeIdx) :
    nodeIdx < 2 ^ maxLayerHeight := by
  have hpow : 1 ≤ 2 ^ level := one_le_pow₀ (by omega)
  simp only [TreeRange] at h
  nlinarith

private theorem TreeRange.left {level nodeIdx : Nat} (h : TreeRange (level + 1) nodeIdx) :
    TreeRange level (2 * nodeIdx) := by
  simp only [TreeRange, pow_succ] at h ⊢
  nlinarith [Nat.zero_le (2 ^ level), Nat.zero_le nodeIdx]

private theorem TreeRange.right {level nodeIdx : Nat} (h : TreeRange (level + 1) nodeIdx) :
    TreeRange level (2 * nodeIdx + 1) := by
  simp only [TreeRange, pow_succ] at h ⊢
  nlinarith [Nat.zero_le (2 ^ level), Nat.zero_le nodeIdx]

def FtsRange (level nodeIdx : Nat) : Prop :=
  2 ^ level * (nodeIdx + 1) ≤ 2 ^ ftsTreeHeight

private theorem FtsRange.index_lt {level nodeIdx : Nat} (h : FtsRange level nodeIdx) :
    nodeIdx < 2 ^ ftsTreeHeight := by
  have hpow : 1 ≤ 2 ^ level := one_le_pow₀ (by omega)
  simp only [FtsRange] at h
  nlinarith

private theorem FtsRange.left {level nodeIdx : Nat} (h : FtsRange (level + 1) nodeIdx) :
    FtsRange level (2 * nodeIdx) := by
  simp only [FtsRange, pow_succ] at h ⊢
  nlinarith [Nat.zero_le (2 ^ level), Nat.zero_le nodeIdx]

private theorem FtsRange.right {level nodeIdx : Nat} (h : FtsRange (level + 1) nodeIdx) :
    FtsRange level (2 * nodeIdx + 1) := by
  simp only [FtsRange, pow_succ] at h ⊢
  nlinarith [Nat.zero_le (2 ^ level), Nat.zero_le nodeIdx]

theorem settled_chain_of_cachedRun (hf : cache.AgreesWithFn f) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (position : Nat)
    (hposition : position < chainLength - 1)
    (hrun : CachedRun cache f (chainWalk parameter lay tree leafIdx chainIdx 0 (position + 1)
      (otsSecret lay tree leafIdx chainIdx))) :
    Settled parameter otsSecret ftsSecret cache
      (.chain lay tree leafIdx chainIdx ⟨position, hposition⟩) := by
  induction position with
  | zero =>
      apply settled_of_honestInput_cached hf (by trivial)
      · apply hrun
        have hmem := chainWalk_query_mem f parameter lay tree leafIdx chainIdx 0 1
          (otsSecret lay tree leafIdx chainIdx) 0 (by omega) hposition
        convert hmem using 1
        all_goals simp [honestInput, honestPayload, honestChain, Position.domain, walkValue]
      · simp [Position.children]
  | succ position ih =>
      have hposition' : position < chainLength - 1 := by omega
      have hprefix : CachedRun cache f
          (chainWalk parameter lay tree leafIdx chainIdx 0 (position + 1)
            (otsSecret lay tree leafIdx chainIdx)) := by
        intro input hinput
        apply hrun input
        rw [show position + 1 + 1 = (position + 1) + 1 by omega, chainWalk,
          queriedInputs_bind]
        exact List.mem_append_left _ hinput
      have hchild := ih hposition' hprefix
      apply settled_of_honestInput_cached hf (by trivial)
      · apply hrun
        have hmem := chainWalk_query_mem f parameter lay tree leafIdx chainIdx 0 (position + 2)
          (otsSecret lay tree leafIdx chainIdx) (position + 1) (by omega) (by omega)
        convert hmem using 1
        all_goals simp [honestInput, honestPayload, honestChain, Position.domain, walkValue]
      · intro c hc
        rw [Position.children, dif_pos (Nat.zero_lt_succ position), List.mem_singleton] at hc
        subst c
        convert hchild using 1
        all_goals simp

theorem settled_leaf_of_cachedRun (hf : cache.AgreesWithFn f) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex)
    (hrun : CachedRun cache f (do
      let endpoints ← oneTimePublicKey parameter lay tree leafIdx (otsSecret lay tree leafIdx)
      leafHash parameter lay tree leafIdx endpoints)) :
    Settled parameter otsSecret ftsSecret cache (.leaf lay tree leafIdx) := by
  have hpublic : CachedRun cache f
      (oneTimePublicKey parameter lay tree leafIdx (otsSecret lay tree leafIdx)) := hrun.bind_left
  have hchains : ∀ chainIdx : ChainIndex, Settled parameter otsSecret ftsSecret cache
      (.chain lay tree leafIdx chainIdx Position.lastChainStep) := by
    intro chainIdx
    have hchain : CachedRun cache f
        (chainWalk parameter lay tree leafIdx chainIdx 0 (chainLength - 1)
          (otsSecret lay tree leafIdx chainIdx)) := by
      intro input hinput
      apply hpublic input
      exact sequenceFin_component_query_mem f _ chainIdx hinput
    convert settled_chain_of_cachedRun hf lay tree leafIdx chainIdx (chainLength - 2) (by decide)
      hchain using 1
    all_goals simp [Position.lastChainStep]
  apply settled_of_honestInput_cached hf (by trivial)
  · apply hrun
    apply queriedInputs_mono_bind_right
    simpa only [eval_oneTimePublicKey, honestEndpoints_def, honestInput, honestPayload,
      Position.domain] using
      leafHash_query_mem f parameter lay tree leafIdx
        (evalWithAnswerFn f
          (oneTimePublicKey parameter lay tree leafIdx (otsSecret lay tree leafIdx)))
  · intro c hc
    simp only [Position.children, List.mem_ofFn] at hc
    obtain ⟨chainIdx, rfl⟩ := hc
    exact hchains chainIdx

theorem settled_treeNode_zero_of_cachedRun (hf : cache.AgreesWithFn f) (lay : Layer)
    (tree : TreeIndex) (nodeIdx : Nat)
    (hrun : CachedRun cache f (treeNode parameter lay tree (otsSecret lay tree) 0 nodeIdx)) :
    Settled parameter otsSecret ftsSecret cache (.leaf lay tree (leafOfNat nodeIdx)) := by
  rw [treeNode_zero_eq] at hrun
  exact settled_leaf_of_cachedRun hf lay tree (leafOfNat nodeIdx) hrun

theorem settled_treeNode_succ_of_cachedRun (hf : cache.AgreesWithFn f) (lay : Layer)
    (tree : TreeIndex) (level nodeIdx : Nat) (hlevel : level < maxLayerHeight)
    (hrange : TreeRange (level + 1) nodeIdx)
    (hrun : CachedRun cache f
      (treeNode parameter lay tree (otsSecret lay tree) (level + 1) nodeIdx)) :
    Settled parameter otsSecret ftsSecret cache
      (.node lay tree ⟨level, hlevel⟩ ⟨nodeIdx, hrange.index_lt⟩) := by
  induction level generalizing nodeIdx with
  | zero =>
      rw [treeNode_succ_eq] at hrun
      have hleft := settled_treeNode_zero_of_cachedRun (ftsSecret := ftsSecret) hf lay tree
        (2 * nodeIdx) hrun.bind_left
      have hright := settled_treeNode_zero_of_cachedRun (ftsSecret := ftsSecret) hf lay tree (2 * nodeIdx + 1)
        hrun.bind_right.bind_left
      have hvalid : 2 * nodeIdx + 1 < 2 ^ maxLayerHeight := (TreeRange.right hrange).index_lt
      apply settled_of_honestInput_cached
        (p := .node lay tree ⟨0, hlevel⟩ ⟨nodeIdx, hrange.index_lt⟩) hf hvalid
      · apply hrun
        apply queriedInputs_mono_bind_right
        apply queriedInputs_mono_bind_right
        simp only [queriedInputs_tweakableHash, List.mem_singleton, honestInput, honestPayload,
          Position.domain, honestNode]
      · intro c hc
        rw [Position.children, dif_pos hvalid, dif_neg (by simp)] at hc
        rcases List.mem_pair.mp hc with hc | hc
        · subst c
          convert hleft using 1
          all_goals simp [leafOfNat, Nat.mod_eq_of_lt (TreeRange.left hrange).index_lt]
        · subst c
          convert hright using 1
          all_goals simp [leafOfNat, Nat.mod_eq_of_lt (TreeRange.right hrange).index_lt]
  | succ level ih =>
      rw [treeNode_succ_eq] at hrun
      have hleft := ih (2 * nodeIdx) (by omega) (TreeRange.left hrange) hrun.bind_left
      have hright := ih (2 * nodeIdx + 1) (by omega) (TreeRange.right hrange)
        hrun.bind_right.bind_left
      have hvalid : 2 * nodeIdx + 1 < 2 ^ maxLayerHeight := (TreeRange.right hrange).index_lt
      apply settled_of_honestInput_cached
        (p := .node lay tree ⟨level + 1, hlevel⟩ ⟨nodeIdx, hrange.index_lt⟩) hf hvalid
      · apply hrun
        apply queriedInputs_mono_bind_right
        apply queriedInputs_mono_bind_right
        simp only [queriedInputs_tweakableHash, List.mem_singleton, honestInput, honestPayload,
          Position.domain, honestNode]
      · intro c hc
        rw [Position.children, dif_pos hvalid, dif_pos (Nat.zero_lt_succ level)] at hc
        rcases List.mem_pair.mp hc with hc | hc
        · subst c
          convert hleft using 1
          all_goals simp
        · subst c
          convert hright using 1
          all_goals simp

theorem settled_treeRoot_of_cachedRun (hf : cache.AgreesWithFn f) (lay : Layer)
    (tree : TreeIndex)
    (hrun : CachedRun cache f (treeRoot parameter lay tree (otsSecret lay tree))) :
    Settled parameter otsSecret ftsSecret cache
      (.node lay tree ⟨layerHeight lay - 1, by
        have hpos : 0 < layerHeight lay := by unfold layerHeight; split <;> norm_num [maxLayerHeight]
        have hle := layerHeight_le lay
        omega⟩ ⟨0, by positivity⟩) := by
  have hpos : 0 < layerHeight lay := by unfold layerHeight; split <;> norm_num [maxLayerHeight]
  have heq : layerHeight lay - 1 + 1 = layerHeight lay := by omega
  have hlevel : layerHeight lay - 1 < maxLayerHeight := by
    have hle := layerHeight_le lay
    omega
  have hrange : TreeRange (layerHeight lay) 0 := by
    simp only [TreeRange, zero_add, mul_one]
    exact pow_le_pow_right' (by omega) (layerHeight_le lay)
  apply settled_treeNode_succ_of_cachedRun hf lay tree (layerHeight lay - 1) 0
    hlevel
  · simpa only [heq] using hrange
  · simpa only [treeRoot, heq] using hrun

theorem settled_ftsLeaf_of_cachedRun (hf : cache.AgreesWithFn f) (index : Index)
    (tree : FtsTree) (leafIdx : FtsLeaf)
    (hrun : CachedRun cache f
      (ftsLeafHash parameter index tree leafIdx (ftsSecret index tree leafIdx))) :
    Settled parameter otsSecret ftsSecret cache (.ftsLeaf index tree leafIdx) := by
  apply settled_of_honestInput_cached hf (by trivial)
  · apply hrun
    simpa only [honestInput, honestPayload, Position.domain] using
      ftsLeafHash_query_mem f parameter index tree leafIdx (ftsSecret index tree leafIdx)
  · simp [Position.children]

theorem settled_ftsNode_zero_of_cachedRun (hf : cache.AgreesWithFn f) (index : Index)
    (tree : FtsTree) (nodeIdx : Nat)
    (hrun : CachedRun cache f (ftsNode parameter index tree (ftsSecret index tree) 0 nodeIdx)) :
    Settled parameter otsSecret ftsSecret cache (.ftsLeaf index tree (ftsLeafOfNat nodeIdx)) := by
  rw [ftsNode_zero_eq] at hrun
  exact settled_ftsLeaf_of_cachedRun hf index tree (ftsLeafOfNat nodeIdx) hrun

theorem settled_ftsNode_succ_of_cachedRun (hf : cache.AgreesWithFn f) (index : Index)
    (tree : FtsTree) (level nodeIdx : Nat) (hlevel : level < ftsTreeHeight)
    (hrange : FtsRange (level + 1) nodeIdx)
    (hrun : CachedRun cache f
      (ftsNode parameter index tree (ftsSecret index tree) (level + 1) nodeIdx)) :
    Settled parameter otsSecret ftsSecret cache
      (.ftsNode index tree ⟨level, hlevel⟩ ⟨nodeIdx, hrange.index_lt⟩) := by
  induction level generalizing nodeIdx with
  | zero =>
      rw [ftsNode_succ_eq] at hrun
      have hleft := settled_ftsNode_zero_of_cachedRun (otsSecret := otsSecret) hf index tree
        (2 * nodeIdx) hrun.bind_left
      have hright := settled_ftsNode_zero_of_cachedRun (otsSecret := otsSecret) hf index tree
        (2 * nodeIdx + 1) hrun.bind_right.bind_left
      have hvalid : 2 * nodeIdx + 1 < 2 ^ ftsTreeHeight := (FtsRange.right hrange).index_lt
      apply settled_of_honestInput_cached
        (p := .ftsNode index tree ⟨0, hlevel⟩ ⟨nodeIdx, hrange.index_lt⟩) hf hvalid
      · apply hrun
        apply queriedInputs_mono_bind_right
        apply queriedInputs_mono_bind_right
        simp only [queriedInputs_tweakableHash, List.mem_singleton, honestInput, honestPayload,
          Position.domain, honestFtsNode]
      · intro c hc
        rw [Position.children, dif_pos hvalid, dif_neg (by simp)] at hc
        rcases List.mem_pair.mp hc with hc | hc
        · subst c
          convert hleft using 1
          all_goals simp [ftsLeafOfNat, Nat.mod_eq_of_lt (FtsRange.left hrange).index_lt]
        · subst c
          convert hright using 1
          all_goals simp [ftsLeafOfNat, Nat.mod_eq_of_lt (FtsRange.right hrange).index_lt]
  | succ level ih =>
      rw [ftsNode_succ_eq] at hrun
      have hleft := ih (2 * nodeIdx) (by omega) (FtsRange.left hrange) hrun.bind_left
      have hright := ih (2 * nodeIdx + 1) (by omega) (FtsRange.right hrange)
        hrun.bind_right.bind_left
      have hvalid : 2 * nodeIdx + 1 < 2 ^ ftsTreeHeight := (FtsRange.right hrange).index_lt
      apply settled_of_honestInput_cached
        (p := .ftsNode index tree ⟨level + 1, hlevel⟩ ⟨nodeIdx, hrange.index_lt⟩) hf hvalid
      · apply hrun
        apply queriedInputs_mono_bind_right
        apply queriedInputs_mono_bind_right
        simp only [queriedInputs_tweakableHash, List.mem_singleton, honestInput, honestPayload,
          Position.domain, honestFtsNode]
      · intro c hc
        rw [Position.children, dif_pos hvalid, dif_pos (Nat.zero_lt_succ level)] at hc
        rcases List.mem_pair.mp hc with hc | hc
        · subst c
          convert hleft using 1
          all_goals simp
        · subst c
          convert hright using 1
          all_goals simp

theorem settled_ftsRoots_of_cachedRun (hf : cache.AgreesWithFn f) (index : Index)
    (hrun : CachedRun cache f (ftsKey parameter index (ftsSecret index))) :
    Settled parameter otsSecret ftsSecret cache (.ftsRoots index) := by
  have hroots : ∀ tree : FtsTree, Settled parameter otsSecret ftsSecret cache
      (.ftsNode index tree ⟨ftsTreeHeight - 1, by decide⟩ ⟨0, by positivity⟩) := by
    intro tree
    have htree : CachedRun cache f
        (ftsNode parameter index tree (ftsSecret index tree) ftsTreeHeight 0) := by
      intro input hinput
      apply hrun.bind_left input
      exact sequenceFin_component_query_mem f _ tree hinput
    have hrange : FtsRange ftsTreeHeight 0 := by simp [FtsRange]
    convert settled_ftsNode_succ_of_cachedRun hf index tree (ftsTreeHeight - 1) 0 (by decide)
      (by simpa [ftsTreeHeight] using hrange) (by simpa [ftsTreeHeight] using htree) using 1
  apply settled_of_honestInput_cached hf (by trivial)
  · apply hrun
    apply queriedInputs_mono_bind_right
    simpa only [evalWithAnswerFn_sequenceFin, honestInput, honestPayload, Position.domain,
      honestFtsNode] using
      (show tweakableHashInput parameter (.ftsRoots index)
          (ftsRootsPayload fun tree => evalWithAnswerFn f
            (ftsNode parameter index tree (ftsSecret index tree) ftsTreeHeight 0))
        ∈ queriedInputs f
          (tweakableHash parameter (.ftsRoots index)
            (ftsRootsPayload fun tree => evalWithAnswerFn f
              (ftsNode parameter index tree (ftsSecret index tree) ftsTreeHeight 0))) by simp)
  · intro c hc
    simp only [Position.children, List.mem_ofFn] at hc
    obtain ⟨tree, rfl⟩ := hc
    exact hroots tree

end Concrete

end SphincsSecurity
