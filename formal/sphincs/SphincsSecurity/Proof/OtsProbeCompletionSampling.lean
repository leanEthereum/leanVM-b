import SphincsSecurity.Proof.OtsProbeCoupling

/-!
# Finite boundary of one-time completion

The concrete retained game observes a completed hidden table only through its chain-start values.
Those values form the finite `OtsSecretIndex` table already used by the concrete sampler transport.
Structural positions remain dynamic on the masked side and do not enter the distributional target.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def baseStartsOfTable (table : OtsSecretIndex → HashOutput) :
    Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput :=
  fun lay tree leafIdx chainIdx => table ⟨lay, tree, leafIdx, chainIdx⟩

def completedStartTable (state : LazyRevealProbe.State Coordinate)
    (base : OtsSecretIndex → HashOutput) : OtsSecretIndex → HashOutput :=
  fun index => (state.values index.coordinate).getD (base index)

def extendStartTable (table : OtsSecretIndex → HashOutput) : Coordinate → HashOutput
  | .chainStart lay tree leafIdx chainIdx => table ⟨lay, tree, leafIdx, chainIdx⟩
  | .position _ => 0

@[simp] theorem tableOtsSecret_extendStartTable
    (table : OtsSecretIndex → HashOutput) :
    tableOtsSecret (extendStartTable table) =
      otsSecretTableEquiv.symm (fun index => truncateHash (table index)) := by
  funext lay tree leafIdx chainIdx
  rfl

theorem tableOtsSecret_retainedCompletionTable_eq_completedStartTable
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache) (base : OtsSecretIndex → HashOutput) :
    tableOtsSecret
        (retainedCompletionTable parameter state cache (baseStartsOfTable base)) =
      otsSecretTableEquiv.symm
        (fun index => truncateHash (completedStartTable state base index)) := by
  funext lay tree leafIdx chainIdx
  rfl

theorem tableOtsSecret_retainedCompletionTable_eq_extendStartTable
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache) (base : OtsSecretIndex → HashOutput) :
    tableOtsSecret
        (retainedCompletionTable parameter state cache (baseStartsOfTable base)) =
      tableOtsSecret (extendStartTable (completedStartTable state base)) := by
  rw [tableOtsSecret_retainedCompletionTable_eq_completedStartTable,
    tableOtsSecret_extendStartTable]

theorem actualRetainedGameAfterTable_congr_tableOtsSecret
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (left right : Coordinate → HashOutput)
    (hsecret : tableOtsSecret left = tableOtsSecret right) :
    actualRetainedGameAfterTable adversary parameter ftsSecret left =
      actualRetainedGameAfterTable adversary parameter ftsSecret right := by
  unfold actualRetainedGameAfterTable
  rw [hsecret]

theorem actualRetainedGameAfterTable_retainedCompletion_eq_finite
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache)
    (base : OtsSecretIndex → HashOutput) :
    actualRetainedGameAfterTable adversary parameter ftsSecret
        (retainedCompletionTable parameter state cache (baseStartsOfTable base)) =
      actualRetainedGameAfterTable adversary parameter ftsSecret
        (extendStartTable (completedStartTable state base)) := by
  apply actualRetainedGameAfterTable_congr_tableOtsSecret
  exact tableOtsSecret_retainedCompletionTable_eq_extendStartTable parameter state cache base

noncomputable def actualRetainedGameAfterOtsSecret (adversary : Adversary)
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :
    ProbComp (RetainedGameResult × QueryCache HashSpec) := do
  let (root, rootCache) ←
    (simulateQ (randomOracle : QueryImpl HashSpec _)
      (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅
  let secretKey : SecretKey := ⟨parameter, root, otsSecret, ftsSecret⟩
  let (result, finalCache) ←
    (simulateQ (unloggedMappedAdversaryImpl secretKey)
      (retainedGameRestComputation adversary ⟨root, parameter⟩)).run rootCache
  pure ((root, result), finalCache)

theorem actualRetainedGameAfterTable_eq_afterOtsSecret
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : Coordinate → HashOutput) :
    actualRetainedGameAfterTable adversary parameter ftsSecret table =
      actualRetainedGameAfterOtsSecret adversary parameter ftsSecret
        (tableOtsSecret table) := by
  rfl

noncomputable local instance completionSampleableOtsHashTable :
    SampleableType (OtsSecretIndex → HashOutput) :=
  SampleableType.ofFintype (OtsSecretIndex → HashOutput)

noncomputable def sampledActualRetainedOtsHashTable (adversary : Adversary)
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    ProbComp ((OtsSecretIndex → HashOutput) ×
      (RetainedGameResult × QueryCache HashSpec)) := do
  let table ← ($ᵗ (OtsSecretIndex → HashOutput) :
    ProbComp (OtsSecretIndex → HashOutput))
  let result ← actualRetainedGameAfterTable adversary parameter ftsSecret
    (extendStartTable table)
  pure (table, result)

noncomputable def sampledActualRetainedOtsSecrets (adversary : Adversary)
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    ProbComp ((Layer → TreeIndex → LeafIndex → ChainIndex → Digest) ×
      (RetainedGameResult × QueryCache HashSpec)) := do
  let otsSecret ← sampleOtsSecrets
  let result ← actualRetainedGameAfterOtsSecret adversary parameter ftsSecret otsSecret
  pure (otsSecret, result)

set_option maxRecDepth 10000 in
theorem relTriple_sampledActualRetainedOtsHashTable_secrets
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    RelTriple
      (sampledActualRetainedOtsHashTable adversary parameter ftsSecret)
      (sampledActualRetainedOtsSecrets adversary parameter ftsSecret)
      fun left right =>
        otsSecretTableEquiv.symm
            (fun index => truncateHash (left.1 index)) = right.1 ∧
          left.2 = right.2 := by
  unfold sampledActualRetainedOtsHashTable sampledActualRetainedOtsSecrets
  apply relTriple_bind relTriple_uniformOtsHashTable_sampleOtsSecrets
  intro table otsSecret hsecret
  have hgame :
      actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table) =
        actualRetainedGameAfterOtsSecret adversary parameter ftsSecret otsSecret := by
    rw [actualRetainedGameAfterTable_eq_afterOtsSecret,
      tableOtsSecret_extendStartTable, hsecret]
  rw [hgame]
  have hrun := relTriple_refl
    (actualRetainedGameAfterOtsSecret adversary parameter ftsSecret otsSecret)
  have hpre : RelTriple
      (actualRetainedGameAfterOtsSecret adversary parameter ftsSecret otsSecret)
      (actualRetainedGameAfterOtsSecret adversary parameter ftsSecret otsSecret)
      (fun left right =>
        otsSecretTableEquiv.symm (fun index => truncateHash (table index)) = otsSecret ∧
          left = right) := by
    apply relTriple_post_mono hrun
    intro left right heq
    exact ⟨hsecret, heq⟩
  exact relTriple_map
    (R := fun left right =>
      otsSecretTableEquiv.symm (fun index => truncateHash (left.1 index)) = right.1 ∧
        left.2 = right.2)
    (f := fun result => (table, result)) (g := fun result => (otsSecret, result)) hpre

theorem probEvent_sampledActualRetainedOtsHashTable_eq_secrets
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (event : (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) →
      (RetainedGameResult × QueryCache HashSpec) → Prop) :
    Pr[fun result => event
        (otsSecretTableEquiv.symm
          (fun index => truncateHash (result.1 index))) result.2 |
      sampledActualRetainedOtsHashTable adversary parameter ftsSecret] =
    Pr[fun result => event result.1 result.2 |
      sampledActualRetainedOtsSecrets adversary parameter ftsSecret] := by
  have hrel := relTriple_sampledActualRetainedOtsHashTable_secrets
    adversary parameter ftsSecret
  apply le_antisymm
  · apply probEvent_le_of_relTriple hrel
    intro left right hrelation hevent
    rw [hrelation.1, hrelation.2] at hevent
    exact hevent
  · apply probEvent_le_of_relTriple (relTriple_symm hrel)
    intro right left hrelation hevent
    rw [hrelation.1, hrelation.2]
    exact hevent

end SphincsSecurity.Concrete.OtsProbeSimulation
