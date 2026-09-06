import SphincsSecurity.Proof.SettlingTrace

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

attribute [local irreducible] instFintypePosition

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (f : QueryImpl HashSpec Id)

theorem settlingRun_chainWalk (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (steps : Nat) :
    SettlingRun parameter otsSecret ftsSecret f
      (chainWalk parameter lay tree leafIdx chainIdx 0 steps (otsSecret lay tree leafIdx chainIdx)) := by
  induction steps with
  | zero => exact SettlingRun.pure _
  | succ steps ih =>
      rw [chainWalk]
      by_cases hstep : steps < chainLength - 1
      · simp only [Nat.zero_add, dif_pos hstep]
        apply SettlingRun.tweakableHash_after (.chain lay tree leafIdx chainIdx ⟨steps, hstep⟩) _ digestBytes ih
        intro cache hf hcached
        apply settled_chain_of_cachedRun hf lay tree leafIdx chainIdx steps hstep
        simpa only [chainWalk, Nat.zero_add, dif_pos hstep, Position.domain] using hcached
      · simp only [Nat.zero_add, dif_neg hstep]
        exact ih.bind (SettlingRun.pure _)

theorem settlingRun_oneTimePublicKey (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    SettlingRun parameter otsSecret ftsSecret f
      (oneTimePublicKey parameter lay tree leafIdx (otsSecret lay tree leafIdx)) := by
  apply SettlingRun.sequenceFin
  intro chainIdx
  exact settlingRun_chainWalk parameter otsSecret ftsSecret f lay tree leafIdx chainIdx _

theorem settlingRun_leaf (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    SettlingRun parameter otsSecret ftsSecret f (do
      let endpoints ← oneTimePublicKey parameter lay tree leafIdx (otsSecret lay tree leafIdx)
      leafHash parameter lay tree leafIdx endpoints) := by
  apply SettlingRun.tweakableHash_after (.leaf lay tree leafIdx) _ leafPayload
    (settlingRun_oneTimePublicKey parameter otsSecret ftsSecret f lay tree leafIdx)
  intro cache hf hcached
  exact settled_leaf_of_cachedRun hf lay tree leafIdx hcached

theorem settlingRun_treeNode (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat)
    (hlevel : level ≤ maxLayerHeight) (hrange : TreeRange level nodeIdx) :
    SettlingRun parameter otsSecret ftsSecret f
      (treeNode parameter lay tree (otsSecret lay tree) level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero =>
      rw [treeNode_zero_eq]
      exact settlingRun_leaf parameter otsSecret ftsSecret f lay tree _
  | succ level ih =>
      have hleft : TreeRange level (2 * nodeIdx) := by
        simp only [TreeRange, pow_succ] at hrange ⊢
        nlinarith [Nat.zero_le (2 ^ level)]
      have hright : TreeRange level (2 * nodeIdx + 1) := by
        simp only [TreeRange, pow_succ] at hrange ⊢
        nlinarith
      have hindex : nodeIdx < 2 ^ maxLayerHeight := by
        have hpow : 1 ≤ 2 ^ (level + 1) := one_le_pow₀ (by omega)
        dsimp only [TreeRange] at hrange
        nlinarith
      let position : Position := .node lay tree ⟨level, by omega⟩ ⟨nodeIdx, hindex⟩
      have hbefore : SettlingRun parameter otsSecret ftsSecret f (do
          let left ← treeNode parameter lay tree (otsSecret lay tree) level (2 * nodeIdx)
          let right ← treeNode parameter lay tree (otsSecret lay tree) level (2 * nodeIdx + 1)
          pure (left, right)) :=
        (ih (2 * nodeIdx) (by omega) hleft).bind
          ((ih (2 * nodeIdx + 1) (by omega) hright).bind (SettlingRun.pure _))
      have h := SettlingRun.tweakableHash_after position _ (fun values => nodePayload values.1 values.2) hbefore (by
        intro cache hf hcached
        apply settled_treeNode_succ_of_cachedRun hf lay tree level nodeIdx (by omega) hrange
        simpa only [treeNode_succ_eq, bind_assoc, pure_bind, position, Position.domain] using hcached)
      simpa only [treeNode_succ_eq, bind_assoc, pure_bind, position, Position.domain] using h

theorem settlingRun_treeRoot (lay : Layer) (tree : TreeIndex) :
    SettlingRun parameter otsSecret ftsSecret f (treeRoot parameter lay tree (otsSecret lay tree)) := by
  apply settlingRun_treeNode parameter otsSecret ftsSecret f lay tree _ _ (layerHeight_le lay)
  simp only [TreeRange, zero_add, mul_one]
  exact pow_le_pow_right' (by omega) (layerHeight_le lay)

theorem settlingRun_ftsLeaf (index : Index) (tree : FtsTree) (leafIdx : FtsLeaf) :
    SettlingRun parameter otsSecret ftsSecret f
      (ftsLeafHash parameter index tree leafIdx (ftsSecret index tree leafIdx)) := by
  have h := SettlingRun.tweakableHash_after (parameter := parameter) (otsSecret := otsSecret)
    (ftsSecret := ftsSecret) (f := f) (.ftsLeaf index tree leafIdx) (pure ())
    (fun _ => digestBytes (ftsSecret index tree leafIdx)) (SettlingRun.pure ()) (by
      intro cache hf hcached
      apply settled_ftsLeaf_of_cachedRun hf index tree leafIdx
      simpa only [pure_bind, Position.domain, ftsLeafHash] using hcached)
  simpa only [pure_bind, Position.domain, ftsLeafHash] using h

theorem settlingRun_ftsNode (index : Index) (tree : FtsTree) (level nodeIdx : Nat)
    (hlevel : level ≤ ftsTreeHeight) (hrange : FtsRange level nodeIdx) :
    SettlingRun parameter otsSecret ftsSecret f
      (ftsNode parameter index tree (ftsSecret index tree) level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero =>
      rw [ftsNode_zero_eq]
      exact settlingRun_ftsLeaf parameter otsSecret ftsSecret f index tree _
  | succ level ih =>
      have hleft : FtsRange level (2 * nodeIdx) := by
        simp only [FtsRange, pow_succ] at hrange ⊢
        nlinarith [Nat.zero_le (2 ^ level)]
      have hright : FtsRange level (2 * nodeIdx + 1) := by
        simp only [FtsRange, pow_succ] at hrange ⊢
        nlinarith
      have hindex : nodeIdx < 2 ^ ftsTreeHeight := by
        have hpow : 1 ≤ 2 ^ (level + 1) := one_le_pow₀ (by omega)
        dsimp only [FtsRange] at hrange
        nlinarith
      let position : Position := .ftsNode index tree ⟨level, by omega⟩ ⟨nodeIdx, hindex⟩
      have hbefore : SettlingRun parameter otsSecret ftsSecret f (do
          let left ← ftsNode parameter index tree (ftsSecret index tree) level (2 * nodeIdx)
          let right ← ftsNode parameter index tree (ftsSecret index tree) level (2 * nodeIdx + 1)
          pure (left, right)) :=
        (ih (2 * nodeIdx) (by omega) hleft).bind
          ((ih (2 * nodeIdx + 1) (by omega) hright).bind (SettlingRun.pure _))
      have h := SettlingRun.tweakableHash_after position _ (fun values => nodePayload values.1 values.2) hbefore (by
        intro cache hf hcached
        apply settled_ftsNode_succ_of_cachedRun hf index tree level nodeIdx (by omega) hrange
        simpa only [ftsNode_succ_eq, bind_assoc, pure_bind, position, Position.domain] using hcached)
      simpa only [ftsNode_succ_eq, bind_assoc, pure_bind, position, Position.domain] using h

theorem settlingRun_ftsKey (index : Index) :
    SettlingRun parameter otsSecret ftsSecret f (ftsKey parameter index (ftsSecret index)) := by
  apply SettlingRun.tweakableHash_after (.ftsRoots index) _ ftsRootsPayload
  · apply SettlingRun.sequenceFin
    intro tree
    apply settlingRun_ftsNode parameter otsSecret ftsSecret f index tree _ _ le_rfl
    simp [FtsRange]
  · intro cache hf hcached
    exact settled_ftsRoots_of_cachedRun hf index hcached

end SphincsSecurity.Concrete
