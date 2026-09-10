import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.Slot

/-!
# Adaptive probes into a sampled secret table

A hash input names one structural coordinate and carries one candidate value. Up to the first
correct candidate, an adaptive strategy sees only misses. Its coordinate and candidate at every
such step are therefore fixed by the all-miss history, so a table with per-cell mass at most
`epsilon` is hit with probability at most `q * epsilon`. There is no union over table coordinates.
-/

namespace SphincsSecurity

open OracleComp ENNReal

variable {D R : Type} [DecidableEq R]

noncomputable local instance instSampleableTypeOfFintypeOfNonempty_sphincsSecurity_1 {T : Type} [Fintype T] [Nonempty T] : SampleableType T :=
  SampleableType.ofFintype T

namespace Concrete

structure FtsSecretProbe where
  index : Index
  tree : FtsTree
  leafIdx : FtsLeaf
  candidate : Digest
deriving DecidableEq

def FtsSecretProbe.input (parameter : PublicParameter) (probe : FtsSecretProbe) : HashInput :=
  tweakableHashInput parameter (.ftsLeaf probe.index probe.tree probe.leafIdx)
    (digestBytes probe.candidate)

def FtsSecretProbe.Hits
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (probe : FtsSecretProbe) : Prop :=
  ftsSecret probe.index probe.tree probe.leafIdx = probe.candidate

theorem FtsSecretProbe.input_injective (parameter : PublicParameter) :
    Function.Injective (FtsSecretProbe.input parameter) := by
  intro left right heq
  have hparts := tweakableHashInput_injective parameter (by trivial) (by trivial) heq
  have hdomain : left.index = right.index ∧ left.tree = right.tree ∧
      left.leafIdx = right.leafIdx := by
    simpa only [HashDomain.ftsLeaf.injEq] using hparts.1
  have hcandidate : left.candidate = right.candidate := digestBytes_injective hparts.2
  cases left
  cases right
  simp only [FtsSecretProbe.mk.injEq] at hdomain hcandidate ⊢
  exact ⟨hdomain.1, hdomain.2.1, hdomain.2.2, hcandidate⟩

structure OtsValueProbe where
  lay : Layer
  tree : TreeIndex
  leafIdx : LeafIndex
  chainIdx : ChainIndex
  digit : Digit
  candidate : Digest
deriving DecidableEq

def OtsValueProbe.target (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (probe : OtsValueProbe) : Digest :=
  honestChain f parameter probe.lay probe.tree probe.leafIdx probe.chainIdx
    (otsSecret probe.lay probe.tree probe.leafIdx probe.chainIdx) probe.digit.val

def OtsValueProbe.Hits (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (probe : OtsValueProbe) : Prop :=
  probe.candidate = probe.target f parameter otsSecret

def OtsValueProbe.MatchesInput (parameter : PublicParameter)
    (probe : OtsValueProbe) (input : HashInput) : Prop :=
  (∃ step : ChainStep,
      probe.digit.val = step.val ∧
        input = tweakableHashInput parameter
          (.chain probe.lay probe.tree probe.leafIdx probe.chainIdx step)
          (digestBytes probe.candidate)) ∨
    (probe.digit.val = chainLength - 1 ∧ probe.chainIdx.val = 0 ∧
      ∃ payload : HashInput,
        input = tweakableHashInput parameter
          (.leaf probe.lay probe.tree probe.leafIdx) payload ∧
        slotDigest 0 input = probe.candidate)

theorem OtsValueProbe.target_zero {f : QueryImpl HashSpec Id} {parameter : PublicParameter}
    {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
    {probe : OtsValueProbe} (hzero : probe.digit.val = 0) :
    probe.target f parameter otsSecret =
      otsSecret probe.lay probe.tree probe.leafIdx probe.chainIdx := by
  simp only [OtsValueProbe.target, hzero, honestChain_zero]

theorem OtsValueProbe.target_succ {f : QueryImpl HashSpec Id} {parameter : PublicParameter}
    {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
    {probe : OtsValueProbe} {step : ChainStep} (hdigit : probe.digit.val = step.val + 1) :
    probe.target f parameter otsSecret =
      honestValue f parameter otsSecret (fun _ _ _ => 0)
        (.chain probe.lay probe.tree probe.leafIdx probe.chainIdx step) := by
  rw [OtsValueProbe.target, honestValue_chain, hdigit]

end Concrete

end SphincsSecurity
