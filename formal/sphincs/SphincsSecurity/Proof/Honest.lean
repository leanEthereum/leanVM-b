import SphincsSecurity.Proof.Position
import SphincsSecurity.Proof.ExtractOts
import SphincsSecurity.Proof.ExtractFts

/-!
# The honest key at a position

One payload per position, one input, one value, all as functions of an answer function and the
sampled secrets. Nothing here is a recursion: each family reads the honest computation the statement
already defines, `honestChain`, `honestNode` and `honestFtsNode`, so the value at a position is
whatever those say. What the accounting needs of them is `honestPayload_congr`: the payload at a
position is a function of the values at its children, so two answer functions that agree on the
children agree on the input, which is what pins the honest structure to a cache.

`Valid` excludes the positions `Position` over-approximates, a node whose children would fall
outside the index width. They carry no honest meaning, and excluding them is what keeps
`honestPayload_congr` true of every position the accounting settles.
-/

namespace SphincsSecurity

open OracleComp

namespace Concrete

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter)

/-- The value the honest forest's root hash carries. -/
def honestFtsKey (index : Index) (secret : FtsTree → FtsLeaf → Digest) : Digest :=
  evalWithAnswerFn f (ftsKey parameter index secret)

theorem honestFtsKey_eq (index : Index) (secret : FtsTree → FtsLeaf → Digest) :
    honestFtsKey f parameter index secret
      = truncateHash (f (tweakableHashInput parameter (.ftsRoots index)
          (ftsRootsPayload fun tree =>
            honestFtsNode f parameter index tree (secret tree) ftsTreeHeight 0))) := by
  simp only [honestFtsKey, ftsKey, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin,
    eval_tweakableHash, honestFtsNode]

theorem honestChain_zero (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (secret : Digest) :
    honestChain f parameter lay tree leafIdx chainIdx secret 0 = secret := by
  simp [honestChain, chainWalk]

end Concrete

variable (f g : QueryImpl HashSpec Id) (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)

/-- The payload the honest key hashes at a position. -/
noncomputable def honestPayload : Position → HashInput
  | .chain lay tree leafIdx chainIdx step =>
      Concrete.digestBytes (Concrete.honestChain f parameter lay tree leafIdx chainIdx
        (otsSecret lay tree leafIdx chainIdx) step.val)
  | .leaf lay tree leafIdx =>
      Concrete.leafPayload
        (Concrete.honestEndpoints f parameter lay tree (otsSecret lay tree) leafIdx)
  | .node lay tree level nodeIdx =>
      Concrete.nodePayload
        (Concrete.honestNode f parameter lay tree (otsSecret lay tree) level.val (2 * nodeIdx.val))
        (Concrete.honestNode f parameter lay tree (otsSecret lay tree) level.val
          (2 * nodeIdx.val + 1))
  | .ftsLeaf index tree leafIdx => Concrete.digestBytes (ftsSecret index tree leafIdx)
  | .ftsNode index tree level nodeIdx =>
      Concrete.nodePayload
        (Concrete.honestFtsNode f parameter index tree (ftsSecret index tree) level.val
          (2 * nodeIdx.val))
        (Concrete.honestFtsNode f parameter index tree (ftsSecret index tree) level.val
          (2 * nodeIdx.val + 1))
  | .ftsRoots index =>
      Concrete.ftsRootsPayload fun tree =>
        Concrete.honestFtsNode f parameter index tree (ftsSecret index tree) ftsTreeHeight 0

/-- The input the honest key hashes at a position. -/
noncomputable def honestInput (p : Position) : HashInput :=
  tweakableHashInput parameter p.domain (honestPayload f parameter otsSecret ftsSecret p)

/-- The value the honest key carries at a position. -/
noncomputable def honestValue (p : Position) : Digest :=
  truncateHash (f (honestInput f parameter otsSecret ftsSecret p))

/-! ### What the value at a position is

The honest computations of the statement, read off the definitions above. -/

theorem honestValue_chain (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (step : ChainStep) :
    honestValue f parameter otsSecret ftsSecret (.chain lay tree leafIdx chainIdx step)
      = Concrete.honestChain f parameter lay tree leafIdx chainIdx
          (otsSecret lay tree leafIdx chainIdx) (step.val + 1) := by
  rw [Concrete.honestChain_succ f parameter lay tree leafIdx chainIdx _ step.val step.isLt]
  rfl

theorem honestValue_leaf (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    honestValue f parameter otsSecret ftsSecret (.leaf lay tree leafIdx)
      = Concrete.honestNode f parameter lay tree (otsSecret lay tree) 0 leafIdx.val := by
  rw [Concrete.honestNode_zero_eq_leafHash f parameter lay tree (otsSecret lay tree) leafIdx]
  rfl

theorem honestValue_node (lay : Layer) (tree : TreeIndex) (level : Fin maxLayerHeight)
    (nodeIdx : LeafIndex) :
    honestValue f parameter otsSecret ftsSecret (.node lay tree level nodeIdx)
      = Concrete.honestNode f parameter lay tree (otsSecret lay tree) (level.val + 1)
          nodeIdx.val := by
  rw [Concrete.honestNode_succ f parameter lay tree (otsSecret lay tree) level.val nodeIdx.val]
  rfl

theorem honestValue_ftsLeaf (index : Index) (tree : FtsTree) (leafIdx : FtsLeaf) :
    honestValue f parameter otsSecret ftsSecret (.ftsLeaf index tree leafIdx)
      = Concrete.honestFtsNode f parameter index tree (ftsSecret index tree) 0 leafIdx.val := by
  rw [Concrete.honestFtsNode_zero f parameter index tree (ftsSecret index tree) leafIdx]
  rfl

theorem honestValue_ftsNode (index : Index) (tree : FtsTree) (level : Fin ftsTreeHeight)
    (nodeIdx : FtsLeaf) :
    honestValue f parameter otsSecret ftsSecret (.ftsNode index tree level nodeIdx)
      = Concrete.honestFtsNode f parameter index tree (ftsSecret index tree) (level.val + 1)
          nodeIdx.val := by
  rw [Concrete.honestFtsNode_succ f parameter index tree (ftsSecret index tree) level.val
    nodeIdx.val]
  rfl

theorem honestValue_ftsRoots (index : Index) :
    honestValue f parameter otsSecret ftsSecret (.ftsRoots index)
      = Concrete.honestFtsKey f parameter index (ftsSecret index) := by
  rw [Concrete.honestFtsKey_eq f parameter index (ftsSecret index)]
  rfl

/-! ### The payload is a function of the children's values -/

/-- The positions `Position` over-approximates: a node whose children would fall outside the index
width. Nothing honest lives there, and the accounting never settles one. -/
def Position.Valid : Position → Prop
  | .node _ _ _ nodeIdx => 2 * nodeIdx.val + 1 < 2 ^ maxLayerHeight
  | .ftsNode _ _ _ nodeIdx => 2 * nodeIdx.val + 1 < 2 ^ ftsTreeHeight
  | _ => True

/-- **The payload is local.** Two answer functions agreeing on the values at a position's children
agree on its payload, and so on its input. -/
theorem honestPayload_congr {p : Position} (hvalid : p.Valid)
    (hchildren : ∀ c ∈ p.children, honestValue f parameter otsSecret ftsSecret c
      = honestValue g parameter otsSecret ftsSecret c) :
    honestPayload f parameter otsSecret ftsSecret p
      = honestPayload g parameter otsSecret ftsSecret p := by
  cases p with
  | chain lay tree leafIdx chainIdx step =>
      rcases Nat.eq_zero_or_pos step.val with hstep | hstep
      · simp only [honestPayload, hstep, Concrete.honestChain_zero]
      · obtain ⟨s, hs⟩ : ∃ s, step.val = s + 1 := ⟨step.val - 1, by omega⟩
        have hmem : (Position.chain lay tree leafIdx chainIdx ⟨s, by have := step.isLt; omega⟩)
            ∈ (Position.chain lay tree leafIdx chainIdx step).children := by
          rw [Position.children, dif_pos hstep]
          simp only [List.mem_singleton, Position.chain.injEq, Fin.ext_iff, true_and]
          omega
        have := hchildren _ hmem
        rw [honestValue_chain, honestValue_chain] at this
        simp only [honestPayload, hs]
        rw [this]
    | leaf lay tree leafIdx =>
        simp only [honestPayload, Concrete.leafPayload]
        refine congrArg _ (congrArg _ (funext fun chainIdx => ?_))
        have hmem : (Position.chain lay tree leafIdx chainIdx Position.lastChainStep)
            ∈ (Position.leaf lay tree leafIdx).children := by
          simp only [Position.children, List.mem_ofFn]
          exact ⟨chainIdx, rfl⟩
        have := hchildren _ hmem
        rw [honestValue_chain, honestValue_chain] at this
        simpa only [Concrete.honestEndpoints, Position.lastChainStep,
          show chainLength - 2 + 1 = chainLength - 1 from rfl] using this
    | node lay tree level nodeIdx =>
        simp only [Position.Valid] at hvalid
        rcases Nat.eq_zero_or_pos level.val with hlevel | hlevel
        · have hleft := hchildren (Position.leaf lay tree ⟨2 * nodeIdx.val, by omega⟩) (by
            rw [Position.children, dif_pos hvalid, dif_neg (by omega)]
            exact List.mem_pair.mpr (Or.inl rfl))
          have hright := hchildren (Position.leaf lay tree ⟨2 * nodeIdx.val + 1, by omega⟩) (by
            rw [Position.children, dif_pos hvalid, dif_neg (by omega)]
            exact List.mem_pair.mpr (Or.inr rfl))
          rw [honestValue_leaf, honestValue_leaf] at hleft hright
          simp only [honestPayload, hlevel]
          rw [hleft, hright]
        · have hleft := hchildren (Position.node lay tree ⟨level.val - 1, by
            have := level.isLt; omega⟩ ⟨2 * nodeIdx.val, by omega⟩) (by
              rw [Position.children, dif_pos hvalid, dif_pos hlevel]
              exact List.mem_pair.mpr (Or.inl rfl))
          have hright := hchildren (Position.node lay tree ⟨level.val - 1, by
            have := level.isLt; omega⟩ ⟨2 * nodeIdx.val + 1, by omega⟩) (by
              rw [Position.children, dif_pos hvalid, dif_pos hlevel]
              exact List.mem_pair.mpr (Or.inr rfl))
          rw [honestValue_node, honestValue_node] at hleft hright
          rw [show level.val - 1 + 1 = level.val from by omega] at hleft hright
          simp only [honestPayload]
          rw [hleft, hright]
    | ftsLeaf => rfl
    | ftsNode index tree level nodeIdx =>
        simp only [Position.Valid] at hvalid
        rcases Nat.eq_zero_or_pos level.val with hlevel | hlevel
        · have hleft := hchildren (Position.ftsLeaf index tree ⟨2 * nodeIdx.val, by omega⟩) (by
            rw [Position.children, dif_pos hvalid, dif_neg (by omega)]
            exact List.mem_pair.mpr (Or.inl rfl))
          have hright := hchildren (Position.ftsLeaf index tree ⟨2 * nodeIdx.val + 1, by omega⟩) (by
            rw [Position.children, dif_pos hvalid, dif_neg (by omega)]
            exact List.mem_pair.mpr (Or.inr rfl))
          rw [honestValue_ftsLeaf, honestValue_ftsLeaf] at hleft hright
          simp only [honestPayload, hlevel]
          rw [hleft, hright]
        · have hleft := hchildren (Position.ftsNode index tree ⟨level.val - 1, by
            have := level.isLt; omega⟩ ⟨2 * nodeIdx.val, by omega⟩) (by
              rw [Position.children, dif_pos hvalid, dif_pos hlevel]
              exact List.mem_pair.mpr (Or.inl rfl))
          have hright := hchildren (Position.ftsNode index tree ⟨level.val - 1, by
            have := level.isLt; omega⟩ ⟨2 * nodeIdx.val + 1, by omega⟩) (by
              rw [Position.children, dif_pos hvalid, dif_pos hlevel]
              exact List.mem_pair.mpr (Or.inr rfl))
          rw [honestValue_ftsNode, honestValue_ftsNode] at hleft hright
          rw [show level.val - 1 + 1 = level.val from by omega] at hleft hright
          simp only [honestPayload]
          rw [hleft, hright]
    | ftsRoots index =>
        simp only [honestPayload, Concrete.ftsRootsPayload]
        refine congrArg _ (congrArg _ (funext fun tree => ?_))
        have hmem : (Position.ftsNode index tree ⟨ftsTreeHeight - 1, by decide⟩
            ⟨0, by positivity⟩) ∈ (Position.ftsRoots index).children := by
          simp only [Position.children, List.mem_ofFn]
          exact ⟨tree, rfl⟩
        have := hchildren _ hmem
        rw [honestValue_ftsNode, honestValue_ftsNode] at this
        simpa only [show ftsTreeHeight - 1 + 1 = ftsTreeHeight from rfl] using this

theorem honestInput_congr {p : Position} (hvalid : p.Valid)
    (hchildren : ∀ c ∈ p.children, honestValue f parameter otsSecret ftsSecret c
      = honestValue g parameter otsSecret ftsSecret c) :
    honestInput f parameter otsSecret ftsSecret p = honestInput g parameter otsSecret ftsSecret p :=
  congrArg _ (honestPayload_congr f g parameter otsSecret ftsSecret hvalid hchildren)

end SphincsSecurity
