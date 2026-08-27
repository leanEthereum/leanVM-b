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

theorem completedStartTable_complete_coordinate
    (state : LazyRevealProbe.State Coordinate) (base : OtsSecretIndex → HashOutput)
    (index : OtsSecretIndex) (output : HashOutput) :
    completedStartTable (state.complete index.coordinate output) base =
      Function.update (completedStartTable state base) index output := by
  funext other
  by_cases heq : other = index
  · subst other
    simp [completedStartTable, LazyRevealProbe.State.complete]
  · have hcoordinate : other.coordinate ≠ index.coordinate :=
      fun h => heq (OtsSecretIndex.coordinate_injective h)
    simp [completedStartTable, LazyRevealProbe.State.complete, heq, hcoordinate]

theorem completedStartTable_materialize_coordinate
    (state : LazyRevealProbe.State Coordinate) (base : OtsSecretIndex → HashOutput)
    (index : OtsSecretIndex) (output : HashOutput) :
    completedStartTable (state.materialize index.coordinate output) base =
      Function.update (completedStartTable state base) index output := by
  funext other
  by_cases heq : other = index
  · subst other
    simp [completedStartTable, LazyRevealProbe.State.materialize]
  · have hcoordinate : other.coordinate ≠ index.coordinate :=
      fun h => heq (OtsSecretIndex.coordinate_injective h)
    simp [completedStartTable, LazyRevealProbe.State.materialize, heq, hcoordinate]

@[simp] theorem completedStartTable_complete_position
    (state : LazyRevealProbe.State Coordinate) (base : OtsSecretIndex → HashOutput)
    (position : Position) (output : HashOutput) :
    completedStartTable (state.complete (.position position) output) base =
      completedStartTable state base := by
  funext index
  simp [completedStartTable, LazyRevealProbe.State.complete, OtsSecretIndex.coordinate]

@[simp] theorem completedStartTable_materialize_position
    (state : LazyRevealProbe.State Coordinate) (base : OtsSecretIndex → HashOutput)
    (position : Position) (output : HashOutput) :
    completedStartTable (state.materialize (.position position) output) base =
      completedStartTable state base := by
  funext index
  simp [completedStartTable, LazyRevealProbe.State.materialize, OtsSecretIndex.coordinate]

theorem completedStartTable_update_base_of_missing
    (state : LazyRevealProbe.State Coordinate) (base : OtsSecretIndex → HashOutput)
    (index : OtsSecretIndex) (output : HashOutput)
    (hmissing : state.values index.coordinate = none) :
    completedStartTable state (Function.update base index output) =
      Function.update (completedStartTable state base) index output := by
  funext other
  by_cases heq : other = index
  · subst other
    simp [completedStartTable, hmissing]
  · simp [completedStartTable, heq]

@[simp] theorem completedStartTable_clearPending
    (state : LazyRevealProbe.State Coordinate) (base : OtsSecretIndex → HashOutput)
    (coordinate : Coordinate) :
    completedStartTable (state.clearPending coordinate) base =
      completedStartTable state base := by
  rfl

@[simp] theorem completedStartTable_ensure
    (state : LazyRevealProbe.State Coordinate) (base : OtsSecretIndex → HashOutput)
    (coordinate : Coordinate) :
    completedStartTable (state.ensure coordinate) base = completedStartTable state base := by
  rfl

@[simp] theorem completedStartTable_publish
    (state : LazyRevealProbe.State Coordinate) (base : OtsSecretIndex → HashOutput)
    (coordinate : Coordinate) :
    completedStartTable (state.publish coordinate) base = completedStartTable state base := by
  rfl

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

set_option maxRecDepth 10000 in
theorem evalDist_complete_missing_start
    (state : LazyRevealProbe.State Coordinate) (index : OtsSecretIndex)
    (hmissing : state.values index.coordinate = none) :
    𝒟[do
        let output ← LazyRevealProbe.sampleHashOutput
        let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
          ProbComp (OtsSecretIndex → HashOutput))
        pure (completedStartTable (state.complete index.coordinate output) base)] =
      𝒟[completedStartTable state <$>
        ($ᵗ (OtsSecretIndex → HashOutput) :
          ProbComp (OtsSecretIndex → HashOutput))] := by
  have hupdate := evalDist_uniformSample_bind_update
    (R := HashOutput) index
  calc
    _ = 𝒟[do
        let output ← ($ᵗ HashOutput : ProbComp HashOutput)
        let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
          ProbComp (OtsSecretIndex → HashOutput))
        pure (completedStartTable state (Function.update base index output))] := by
      apply congrArg evalDist
      simp only [LazyRevealProbe.sampleHashOutput]
      apply bind_congr
      intro output
      apply bind_congr
      intro base
      rw [completedStartTable_complete_coordinate,
        completedStartTable_update_base_of_missing state base index output hmissing]
    _ = 𝒟[completedStartTable state <$> (do
        let output ← ($ᵗ HashOutput : ProbComp HashOutput)
        let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
          ProbComp (OtsSecretIndex → HashOutput))
        pure (Function.update base index output))] := by
      simp [map_eq_bind_pure_comp, bind_assoc]
    _ = _ := by
      rw [evalDist_map, hupdate, ← evalDist_map]

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

noncomputable def hashOutputOfDigest (digest : Digest) : HashOutput :=
  (splitHashOutputEquiv digestBits (by decide)).symm (digest, 0)

@[simp] theorem truncateHash_hashOutputOfDigest (digest : Digest) :
    truncateHash (hashOutputOfDigest digest) = digest := by
  change (splitHashOutput digestBits
    ((splitHashOutputEquiv digestBits (by decide)).symm (digest, 0))).1 = digest
  rw [show splitHashOutput digestBits = splitHashOutputEquiv digestBits (by decide) from rfl,
    Equiv.apply_symm_apply]

noncomputable def tableOfOtsSecret
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :
    Coordinate → HashOutput :=
  extendStartTable fun index => hashOutputOfDigest (otsSecretTableEquiv otsSecret index)

@[simp] theorem tableOtsSecret_tableOfOtsSecret
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :
    tableOtsSecret (tableOfOtsSecret otsSecret) = otsSecret := by
  rw [tableOfOtsSecret, tableOtsSecret_extendStartTable]
  simp

theorem winningRetainedVerifyProbe_congr_tableOtsSecret
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (left right : Coordinate → HashOutput)
    (hsecret : tableOtsSecret left = tableOtsSecret right)
    (result : RetainedGameResult × QueryCache HashSpec) :
    WinningRetainedVerifyProbeWitness parameter left ftsSecret result ↔
      WinningRetainedVerifyProbeWitness parameter right ftsSecret result := by
  unfold WinningRetainedVerifyProbeWitness WinningRetainedWitnessFor
  rw [hsecret]

def WinningRetainedVerifyProbeAfterOtsSecret
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : RetainedGameResult × QueryCache HashSpec) : Prop :=
  WinningRetainedVerifyProbeWitness parameter (tableOfOtsSecret otsSecret) ftsSecret result

theorem probEvent_sampledWinningRetainedVerifyProbe_eq_secrets
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Pr[fun result => WinningRetainedVerifyProbeWitness parameter
        (extendStartTable result.1) ftsSecret result.2 |
      sampledActualRetainedOtsHashTable adversary parameter ftsSecret] =
    Pr[fun result => WinningRetainedVerifyProbeAfterOtsSecret parameter result.1
        ftsSecret result.2 |
      sampledActualRetainedOtsSecrets adversary parameter ftsSecret] := by
  let toSecret := fun table : OtsSecretIndex → HashOutput =>
    otsSecretTableEquiv.symm (fun index => truncateHash (table index))
  calc
    _ = Pr[fun result => WinningRetainedVerifyProbeAfterOtsSecret parameter
          (toSecret result.1) ftsSecret result.2 |
        sampledActualRetainedOtsHashTable adversary parameter ftsSecret] := by
      apply OracleComp.probEvent_congr' fun result _ =>
        winningRetainedVerifyProbe_congr_tableOtsSecret parameter ftsSecret
          (extendStartTable result.1) (tableOfOtsSecret (toSecret result.1))
          (by simp [toSecret]) result.2
      rfl
    _ = _ := probEvent_sampledActualRetainedOtsHashTable_eq_secrets adversary parameter
      ftsSecret (fun otsSecret result =>
        WinningRetainedVerifyProbeAfterOtsSecret parameter otsSecret ftsSecret result)

end SphincsSecurity.Concrete.OtsProbeSimulation
