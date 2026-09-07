import SphincsSecurity.Proof.HonestSettlingTrace

namespace SphincsSecurity

open OracleComp OracleSpec

def HonestStructuralQueries (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (f : QueryImpl HashSpec Id)
    (computation : OracleComp HashSpec α) : Prop :=
  ∀ input ∈ queriedInputs f computation,
    ∃ position : Position, position.Valid ∧ input = honestInput f parameter otsSecret ftsSecret position

variable {parameter : PublicParameter}
  {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
  {ftsSecret : Index → FtsTree → FtsLeaf → Digest} {f : QueryImpl HashSpec Id}

theorem HonestStructuralQueries.pure (value : α) :
    HonestStructuralQueries parameter otsSecret ftsSecret f (pure value) := by
  simp [HonestStructuralQueries]

theorem HonestStructuralQueries.bind
    {computation : OracleComp HashSpec α} {next : α → OracleComp HashSpec β}
    (hleft : HonestStructuralQueries parameter otsSecret ftsSecret f computation)
    (hright : HonestStructuralQueries parameter otsSecret ftsSecret f (next (evalWithAnswerFn f computation))) :
    HonestStructuralQueries parameter otsSecret ftsSecret f (computation >>= next) := by
  intro input hinput
  rw [queriedInputs_bind] at hinput
  exact (List.mem_append.mp hinput).elim (hleft input) (hright input)

theorem HonestStructuralQueries.sequenceFin {n : Nat}
    (computation : Fin n → OracleComp HashSpec α)
    (h : ∀ i, HonestStructuralQueries parameter otsSecret ftsSecret f (computation i)) :
    HonestStructuralQueries parameter otsSecret ftsSecret f (Concrete.sequenceFin computation) := by
  induction n with
  | zero => exact HonestStructuralQueries.pure _
  | succ n ih =>
      rw [Concrete.sequenceFin]
      exact (h 0).bind ((ih (fun i => computation i.succ) (fun i => h i.succ)).bind (HonestStructuralQueries.pure _))

namespace Concrete

variable (parameter otsSecret ftsSecret f)
attribute [local irreducible] instFintypePosition

theorem honestStructuralQueries_chainWalk (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (steps : Nat) :
    HonestStructuralQueries parameter otsSecret ftsSecret f
      (chainWalk parameter lay tree leafIdx chainIdx 0 steps (otsSecret lay tree leafIdx chainIdx)) := by
  induction steps with
  | zero => exact HonestStructuralQueries.pure _
  | succ steps ih =>
      rw [chainWalk]
      apply ih.bind
      by_cases hstep : steps < chainLength - 1
      · simp only [Nat.zero_add, dif_pos hstep]
        intro input hinput
        simp only [queriedInputs_tweakableHash, List.mem_singleton] at hinput
        refine ⟨.chain lay tree leafIdx chainIdx ⟨steps, hstep⟩, by trivial, ?_⟩
        exact hinput
      · simp only [Nat.zero_add, dif_neg hstep]
        exact HonestStructuralQueries.pure _

theorem honestStructuralQueries_oneTimePublicKey (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    HonestStructuralQueries parameter otsSecret ftsSecret f
      (oneTimePublicKey parameter lay tree leafIdx (otsSecret lay tree leafIdx)) := by
  apply HonestStructuralQueries.sequenceFin
  intro chainIdx
  exact honestStructuralQueries_chainWalk parameter otsSecret ftsSecret f lay tree leafIdx chainIdx _

theorem honestStructuralQueries_leaf (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    HonestStructuralQueries parameter otsSecret ftsSecret f (do
      let endpoints ← oneTimePublicKey parameter lay tree leafIdx (otsSecret lay tree leafIdx)
      leafHash parameter lay tree leafIdx endpoints) := by
  apply (honestStructuralQueries_oneTimePublicKey parameter otsSecret ftsSecret f lay tree leafIdx).bind
  intro input hinput
  simp only [leafHash, queriedInputs_tweakableHash, List.mem_singleton] at hinput
  refine ⟨.leaf lay tree leafIdx, by trivial, ?_⟩
  simpa only [honestInput, honestPayload, Position.domain, eval_oneTimePublicKey, honestEndpoints_def] using hinput

theorem honestStructuralQueries_treeNode (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat)
    (hlevel : level ≤ maxLayerHeight) (hrange : TreeRange level nodeIdx) :
    HonestStructuralQueries parameter otsSecret ftsSecret f
      (treeNode parameter lay tree (otsSecret lay tree) level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero =>
      rw [treeNode_zero_eq]
      exact honestStructuralQueries_leaf parameter otsSecret ftsSecret f lay tree _
  | succ level ih =>
      have hleft : TreeRange level (2 * nodeIdx) := by
        simp only [TreeRange, pow_succ] at hrange ⊢
        nlinarith [Nat.zero_le (2 ^ level)]
      have hright : TreeRange level (2 * nodeIdx + 1) := by
        simp only [TreeRange, pow_succ] at hrange ⊢
        nlinarith
      have hindices : 2 * nodeIdx + 1 < 2 ^ maxLayerHeight := by
        have hpow : 1 ≤ 2 ^ level := one_le_pow₀ (by omega)
        simp only [TreeRange] at hright
        nlinarith
      rw [treeNode_succ_eq]
      apply (ih (2 * nodeIdx) (by omega) hleft).bind
      apply (ih (2 * nodeIdx + 1) (by omega) hright).bind
      intro input hinput
      simp only [queriedInputs_tweakableHash, List.mem_singleton] at hinput
      refine ⟨.node lay tree ⟨level, by omega⟩ ⟨nodeIdx, by omega⟩, hindices, ?_⟩
      exact hinput

theorem honestStructuralQueries_treeRoot (lay : Layer) (tree : TreeIndex) :
    HonestStructuralQueries parameter otsSecret ftsSecret f (treeRoot parameter lay tree (otsSecret lay tree)) := by
  apply honestStructuralQueries_treeNode parameter otsSecret ftsSecret f lay tree _ _ (layerHeight_le lay)
  simp only [TreeRange, zero_add, mul_one]
  exact pow_le_pow_right' (by omega) (layerHeight_le lay)

end Concrete
end SphincsSecurity
