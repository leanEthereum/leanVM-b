import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeSampling

/-!
# Finite boundary of one-time completion

The concrete retained game observes a completed hidden table only through its chain-start values.
Those values form the finite `OtsSecretIndex` table already used by the concrete sampler transport.
Structural positions remain dynamic on the masked side and do not enter the distributional target.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def completedStartTable (state : LazyRevealProbe.State Coordinate)
    (base : OtsSecretIndex → HashOutput) : OtsSecretIndex → HashOutput :=
  fun index => (state.values index.coordinate).getD (base index)

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

@[simp] theorem completedStartTable_addPending
    (state : LazyRevealProbe.State Coordinate) (base : OtsSecretIndex → HashOutput)
    (coordinate : Coordinate) (candidate : Digest) :
    completedStartTable (state.addPending coordinate candidate) base =
      completedStartTable state base := by
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

noncomputable local instance completionSampleableOtsHashTable :
    SampleableType (OtsSecretIndex → HashOutput) :=
  SampleableType.ofFintype (OtsSecretIndex → HashOutput)

set_option maxRecDepth 100000 in
theorem evalDist_completionTable_bind_cell_extract {β : Type}
    (index : OtsSecretIndex)
    (cont : (OtsSecretIndex → HashOutput) → HashOutput → ProbComp β) :
    𝒟[do
      let table ← ($ᵗ (OtsSecretIndex → HashOutput) :
        ProbComp (OtsSecretIndex → HashOutput))
      cont table (table index)] =
    𝒟[do
      let output ← ($ᵗ HashOutput : ProbComp HashOutput)
      let table ← ($ᵗ (OtsSecretIndex → HashOutput) :
        ProbComp (OtsSecretIndex → HashOutput))
      cont (Function.update table index output) output] := by
  classical
  have hleft :
      (do
        let table ← ($ᵗ (OtsSecretIndex → HashOutput) :
          ProbComp (OtsSecretIndex → HashOutput))
        cont table (table index)) =
      ((do
          let table ← ($ᵗ (OtsSecretIndex → HashOutput) :
            ProbComp (OtsSecretIndex → HashOutput))
          pure (table, table index)) >>= fun pair => cont pair.1 pair.2) := by
    simp
  have hright :
      (do
        let output ← ($ᵗ HashOutput : ProbComp HashOutput)
        let table ← ($ᵗ (OtsSecretIndex → HashOutput) :
          ProbComp (OtsSecretIndex → HashOutput))
        cont (Function.update table index output) output) =
      ((do
          let output ← ($ᵗ HashOutput : ProbComp HashOutput)
          let table ← ($ᵗ (OtsSecretIndex → HashOutput) :
            ProbComp (OtsSecretIndex → HashOutput))
          pure (Function.update table index output, output)) >>=
        fun pair => cont pair.1 pair.2) := by
    simp
  rw [hleft, hright]
  have hpureEq : ∀ (table : OtsSecretIndex → HashOutput) (output : HashOutput),
      (Function.update table index output, output) =
        ((fun table' : OtsSecretIndex → HashOutput => (table', table' index))
          (Function.update table index output)) := fun _ _ => by simp
  have hcore :
      𝒟[do
        let output ← ($ᵗ HashOutput : ProbComp HashOutput)
        let table ← ($ᵗ (OtsSecretIndex → HashOutput) :
          ProbComp (OtsSecretIndex → HashOutput))
        pure (Function.update table index output, output)] =
      𝒟[do
        let table ← ($ᵗ (OtsSecretIndex → HashOutput) :
          ProbComp (OtsSecretIndex → HashOutput))
        pure (table, table index)] := by
    have hrw :
        (do
          let output ← ($ᵗ HashOutput : ProbComp HashOutput)
          let table ← ($ᵗ (OtsSecretIndex → HashOutput) :
            ProbComp (OtsSecretIndex → HashOutput))
          pure (Function.update table index output, output)) =
        (do
          let output ← ($ᵗ HashOutput : ProbComp HashOutput)
          let table ← ($ᵗ (OtsSecretIndex → HashOutput) :
            ProbComp (OtsSecretIndex → HashOutput))
          pure ((fun table' : OtsSecretIndex → HashOutput => (table', table' index))
            (Function.update table index output))) :=
      bind_congr fun output => bind_congr fun table => by rw [hpureEq table output]
    rw [hrw]
    exact OracleComp.evalDist_uniformSample_bind_update_map
      (R := HashOutput) index (fun table' => (table', table' index))
  refine evalDist_ext fun output => ?_
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun pair => ?_
  have hprob := OracleComp.probOutput_congr (x := pair) rfl hcore.symm
  rw [hprob]

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

end SphincsSecurity.Concrete.OtsProbeSimulation
