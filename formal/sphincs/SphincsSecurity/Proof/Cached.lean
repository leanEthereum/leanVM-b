import SphincsSecurity.Proof.Prelude
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

theorem CachedRun.pure {alpha : Type} (cache : QueryCache HashSpec)
    (f : QueryImpl HashSpec Id) (value : alpha) :
    CachedRun cache f (pure value) := by
  simp [CachedRun]

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

namespace Concrete

variable {f : QueryImpl HashSpec Id} {parameter : PublicParameter}
  {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
  {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
  {cache : QueryCache HashSpec}

def TreeRange (level nodeIdx : Nat) : Prop :=
  2 ^ level * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight

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

private theorem FtsRange.left {level nodeIdx : Nat} (h : FtsRange (level + 1) nodeIdx) :
    FtsRange level (2 * nodeIdx) := by
  simp only [FtsRange, pow_succ] at h ⊢
  nlinarith [Nat.zero_le (2 ^ level), Nat.zero_le nodeIdx]

private theorem FtsRange.right {level nodeIdx : Nat} (h : FtsRange (level + 1) nodeIdx) :
    FtsRange level (2 * nodeIdx + 1) := by
  simp only [FtsRange, pow_succ] at h ⊢
  nlinarith [Nat.zero_le (2 ^ level), Nat.zero_le nodeIdx]

end Concrete

end SphincsSecurity
