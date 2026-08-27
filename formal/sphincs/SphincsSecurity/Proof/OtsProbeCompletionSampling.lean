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

set_option maxRecDepth 10000 in
theorem evalDist_materialize_missing_start
    (state : LazyRevealProbe.State Coordinate) (index : OtsSecretIndex)
    (hmissing : state.values index.coordinate = none) :
    𝒟[do
        let output ← LazyRevealProbe.sampleHashOutput
        let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
          ProbComp (OtsSecretIndex → HashOutput))
        pure (completedStartTable (state.materialize index.coordinate output) base)] =
      𝒟[completedStartTable state <$>
        ($ᵗ (OtsSecretIndex → HashOutput) :
          ProbComp (OtsSecretIndex → HashOutput))] := by
  calc
    _ = 𝒟[do
        let output ← LazyRevealProbe.sampleHashOutput
        let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
          ProbComp (OtsSecretIndex → HashOutput))
        pure (completedStartTable (state.complete index.coordinate output) base)] := by
      apply congrArg evalDist
      apply bind_congr
      intro output
      apply bind_congr
      intro base
      rw [completedStartTable_materialize_coordinate,
        completedStartTable_complete_coordinate]
    _ = _ := evalDist_complete_missing_start state index hmissing

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

set_option maxRecDepth 100000 in
theorem evalDist_complete_missing_start_clean
    (state : LazyRevealProbe.State Coordinate) (index : OtsSecretIndex)
    (hmissing : state.values index.coordinate = none) :
    𝒟[do
        let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
          ProbComp (OtsSecretIndex → HashOutput))
        let table := completedStartTable state base
        let output := table index
        if state.hitAt index.coordinate output then
          pure none
        else
          pure (some (state.complete index.coordinate output, table))] =
      𝒟[do
        let output ← LazyRevealProbe.sampleHashOutput
        let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
          ProbComp (OtsSecretIndex → HashOutput))
        if state.hitAt index.coordinate output then
          pure none
        else
          pure (some (state.complete index.coordinate output,
            completedStartTable (state.complete index.coordinate output) base))] := by
  let cont := fun table : OtsSecretIndex → HashOutput => fun output : HashOutput =>
    if state.hitAt index.coordinate output then
      (pure none : ProbComp (Option
        (LazyRevealProbe.State Coordinate × (OtsSecretIndex → HashOutput))))
    else
      pure (some (state.complete index.coordinate output,
        completedStartTable state table))
  have hcell := evalDist_completionTable_bind_cell_extract
    (β := Option
      (LazyRevealProbe.State Coordinate × (OtsSecretIndex → HashOutput))) index cont
  calc
    _ = 𝒟[do
        let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
          ProbComp (OtsSecretIndex → HashOutput))
        cont base (base index)] := by
      apply congrArg evalDist
      apply bind_congr
      intro base
      simp [cont, completedStartTable, hmissing]
    _ = 𝒟[do
        let output ← ($ᵗ HashOutput : ProbComp HashOutput)
        let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
          ProbComp (OtsSecretIndex → HashOutput))
        cont (Function.update base index output) output] := hcell
    _ = _ := by
      apply congrArg evalDist
      simp only [LazyRevealProbe.sampleHashOutput]
      apply bind_congr
      intro output
      apply bind_congr
      intro base
      by_cases hhit : state.hitAt index.coordinate output
      · simp [cont, hhit]
      · simp only [cont, hhit, ↓reduceIte]
        rw [completedStartTable_update_base_of_missing state base index output hmissing,
          ← completedStartTable_complete_coordinate]

set_option maxRecDepth 100000 in
theorem evalDist_complete_missing_start_clean_cont {β : Type}
    (state : LazyRevealProbe.State Coordinate) (index : OtsSecretIndex)
    (hmissing : state.values index.coordinate = none)
    (next : LazyRevealProbe.State Coordinate → (OtsSecretIndex → HashOutput) →
      ProbComp (Option β)) :
    𝒟[do
        let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
          ProbComp (OtsSecretIndex → HashOutput))
        let table := completedStartTable state base
        let output := table index
        if state.hitAt index.coordinate output then
          pure none
        else
          next (state.complete index.coordinate output) table] =
      𝒟[do
        let output ← LazyRevealProbe.sampleHashOutput
        let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
          ProbComp (OtsSecretIndex → HashOutput))
        if state.hitAt index.coordinate output then
          pure none
        else
          next (state.complete index.coordinate output)
            (completedStartTable (state.complete index.coordinate output) base)] := by
  let cont := fun table : OtsSecretIndex → HashOutput => fun output : HashOutput =>
    if state.hitAt index.coordinate output then
      (pure none : ProbComp (Option β))
    else
      next (state.complete index.coordinate output) (completedStartTable state table)
  have hcell := evalDist_completionTable_bind_cell_extract
    (β := Option β) index cont
  calc
    _ = 𝒟[do
        let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
          ProbComp (OtsSecretIndex → HashOutput))
        cont base (base index)] := by
      apply congrArg evalDist
      apply bind_congr
      intro base
      by_cases hhit : state.hitAt index.coordinate
        (completedStartTable state base index)
      · simp [cont, completedStartTable, hmissing]
      · have hlookup : completedStartTable state base index = base index := by
          simp [completedStartTable, hmissing]
        simp only [cont, hlookup]
    _ = 𝒟[do
        let output ← ($ᵗ HashOutput : ProbComp HashOutput)
        let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
          ProbComp (OtsSecretIndex → HashOutput))
        cont (Function.update base index output) output] := hcell
    _ = _ := by
      apply congrArg evalDist
      simp only [LazyRevealProbe.sampleHashOutput]
      apply bind_congr
      intro output
      apply bind_congr
      intro base
      by_cases hhit : state.hitAt index.coordinate output
      · simp [cont, hhit]
      · simp only [cont, hhit, ↓reduceIte]
        rw [completedStartTable_update_base_of_missing state base index output hmissing,
          ← completedStartTable_complete_coordinate]

set_option maxRecDepth 100000 in
theorem evalDist_materialize_missing_start_clean
    (state : LazyRevealProbe.State Coordinate) (index : OtsSecretIndex)
    (hmissing : state.values index.coordinate = none) :
    𝒟[do
        let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
          ProbComp (OtsSecretIndex → HashOutput))
        let table := completedStartTable state base
        let output := table index
        if state.hitAt index.coordinate output then
          pure none
        else
          pure (some (state.materialize index.coordinate output, table))] =
      𝒟[do
        let output ← LazyRevealProbe.sampleHashOutput
        let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
          ProbComp (OtsSecretIndex → HashOutput))
        if state.hitAt index.coordinate output then
          pure none
        else
          pure (some (state.materialize index.coordinate output,
            completedStartTable (state.materialize index.coordinate output) base))] := by
  let cont := fun table : OtsSecretIndex → HashOutput => fun output : HashOutput =>
    if state.hitAt index.coordinate output then
      (pure none : ProbComp (Option
        (LazyRevealProbe.State Coordinate × (OtsSecretIndex → HashOutput))))
    else
      pure (some (state.materialize index.coordinate output,
        completedStartTable state table))
  have hcell := evalDist_completionTable_bind_cell_extract
    (β := Option
      (LazyRevealProbe.State Coordinate × (OtsSecretIndex → HashOutput))) index cont
  calc
    _ = 𝒟[do
        let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
          ProbComp (OtsSecretIndex → HashOutput))
        cont base (base index)] := by
      apply congrArg evalDist
      apply bind_congr
      intro base
      simp [cont, completedStartTable, hmissing]
    _ = 𝒟[do
        let output ← ($ᵗ HashOutput : ProbComp HashOutput)
        let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
          ProbComp (OtsSecretIndex → HashOutput))
        cont (Function.update base index output) output] := hcell
    _ = _ := by
      apply congrArg evalDist
      simp only [LazyRevealProbe.sampleHashOutput]
      apply bind_congr
      intro output
      apply bind_congr
      intro base
      by_cases hhit : state.hitAt index.coordinate output
      · simp [cont, hhit]
      · simp only [cont, hhit, ↓reduceIte]
        rw [completedStartTable_update_base_of_missing state base index output hmissing,
          ← completedStartTable_materialize_coordinate]

noncomputable def finalizeCleanFromTable :
    List Coordinate → LazyRevealProbe.State Coordinate →
      (OtsSecretIndex → HashOutput) →
        ProbComp (Option
          (LazyRevealProbe.State Coordinate × (OtsSecretIndex → HashOutput)))
  | [], state, table => pure (some (state, table))
  | coordinate :: remaining, state, table =>
      match state.values coordinate with
      | some _ => finalizeCleanFromTable remaining (state.clearPending coordinate) table
      | none =>
          match coordinate with
          | .chainStart lay tree leafIdx chainIdx =>
              let output := table ⟨lay, tree, leafIdx, chainIdx⟩
              if state.hitAt coordinate output then
                pure none
              else
                finalizeCleanFromTable remaining (state.complete coordinate output) table
          | .position _ => do
              let output ← LazyRevealProbe.sampleHashOutput
              if state.hitAt coordinate output then
                pure none
              else
                finalizeCleanFromTable remaining (state.complete coordinate output) table

noncomputable def finalizeCleanWithCompletionTable
    (coordinates : List Coordinate) (state : LazyRevealProbe.State Coordinate) :
    ProbComp (Option
      (LazyRevealProbe.State Coordinate × (OtsSecretIndex → HashOutput))) := do
  let result ← LazyRevealProbe.finalizeDetailedFrom coordinates state
  if result.1 then
    pure none
  else
    let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
      ProbComp (OtsSecretIndex → HashOutput))
    pure (some (result.2, completedStartTable result.2 base))

theorem finalizeCleanWithCompletionTable_cons_of_some
    (coordinate : Coordinate) (remaining : List Coordinate)
    (state : LazyRevealProbe.State Coordinate) (output : HashOutput)
    (hvalue : state.values coordinate = some output) :
    finalizeCleanWithCompletionTable (coordinate :: remaining) state =
      finalizeCleanWithCompletionTable remaining (state.clearPending coordinate) := by
  unfold finalizeCleanWithCompletionTable
  rw [LazyRevealProbe.finalizeDetailedFrom, hvalue]

theorem finalizeCleanWithCompletionTable_cons_of_none
    (coordinate : Coordinate) (remaining : List Coordinate)
    (state : LazyRevealProbe.State Coordinate)
    (hvalue : state.values coordinate = none) :
    finalizeCleanWithCompletionTable (coordinate :: remaining) state = (do
      let output ← LazyRevealProbe.sampleHashOutput
      if state.hitAt coordinate output then
        pure none
      else
        finalizeCleanWithCompletionTable remaining (state.complete coordinate output)) := by
  unfold finalizeCleanWithCompletionTable
  rw [LazyRevealProbe.finalizeDetailedFrom, hvalue, bind_assoc]
  apply bind_congr
  intro output
  by_cases hhit : state.hitAt coordinate output
  · simp [hhit]
  · simp [hhit]

set_option maxRecDepth 100000 in
theorem evalDist_finalizeCleanFromTable_eq_lazy :
    ∀ (coordinates : List Coordinate) (state : LazyRevealProbe.State Coordinate),
      𝒟[do
        let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
          ProbComp (OtsSecretIndex → HashOutput))
        finalizeCleanFromTable coordinates state (completedStartTable state base)] =
      𝒟[finalizeCleanWithCompletionTable coordinates state] := by
  intro coordinates
  induction coordinates with
  | nil =>
      intro state
      simp [finalizeCleanFromTable, finalizeCleanWithCompletionTable,
        LazyRevealProbe.finalizeDetailedFrom]
  | cons coordinate remaining ih =>
      intro state
      cases hvalue : state.values coordinate with
      | some output =>
          have hleft :
              (do
                let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
                  ProbComp (OtsSecretIndex → HashOutput))
                finalizeCleanFromTable (coordinate :: remaining) state
                  (completedStartTable state base)) =
              (do
                let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
                  ProbComp (OtsSecretIndex → HashOutput))
                finalizeCleanFromTable remaining (state.clearPending coordinate)
                  (completedStartTable (state.clearPending coordinate) base)) := by
            apply bind_congr
            intro base
            simp [finalizeCleanFromTable, hvalue]
          rw [congrArg evalDist hleft]
          rw [finalizeCleanWithCompletionTable_cons_of_some coordinate remaining state output
            hvalue]
          exact ih (state.clearPending coordinate)
      | none =>
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
              calc
                _ = 𝒟[do
                    let output ← LazyRevealProbe.sampleHashOutput
                    let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
                      ProbComp (OtsSecretIndex → HashOutput))
                    if state.hitAt index.coordinate output then
                      pure none
                    else
                      finalizeCleanFromTable remaining
                        (state.complete index.coordinate output)
                        (completedStartTable
                          (state.complete index.coordinate output) base)] := by
                    simpa [finalizeCleanFromTable, hvalue, index,
                      OtsSecretIndex.coordinate] using
                        evalDist_complete_missing_start_clean_cont
                          state index hvalue (fun nextState table =>
                            finalizeCleanFromTable remaining nextState table)
                _ = _ := by
                  rw [finalizeCleanWithCompletionTable_cons_of_none
                    (.chainStart lay tree leafIdx chainIdx) remaining state hvalue]
                  rw [evalDist_bind, evalDist_bind]
                  apply congrArg
                  funext freshOutput
                  simp only [index, OtsSecretIndex.coordinate]
                  by_cases hhit : state.hitAt
                    (.chainStart lay tree leafIdx chainIdx) freshOutput
                  ·
                    simp only [hhit, ↓reduceIte]
                    have hdrop :=
                      OracleComp.DeferredSampling.evalDist_bind_const_neverFails
                        ($ᵗ (OtsSecretIndex → HashOutput) :
                          ProbComp (OtsSecretIndex → HashOutput))
                        (by simp) (pure none : ProbComp (Option
                          (LazyRevealProbe.State Coordinate ×
                            (OtsSecretIndex → HashOutput))))
                    simpa [finalizeCleanWithCompletionTable] using hdrop
                  ·
                    simp only [hhit, ↓reduceIte]
                    exact ih (state.complete
                      (.chainStart lay tree leafIdx chainIdx) freshOutput)
          | position position =>
              let coordinate : Coordinate := .position position
              let tableSample := ($ᵗ (OtsSecretIndex → HashOutput) :
                ProbComp (OtsSecretIndex → HashOutput))
              let outputSample := LazyRevealProbe.sampleHashOutput
              calc
                _ = 𝒟[tableSample >>= fun base => outputSample >>= fun freshOutput =>
                    if state.hitAt coordinate freshOutput then
                      pure none
                    else
                      finalizeCleanFromTable remaining
                        (state.complete coordinate freshOutput)
                        (completedStartTable state base)] := by
                      apply congrArg evalDist
                      simp [finalizeCleanFromTable, hvalue, coordinate, tableSample,
                        outputSample]
                _ = 𝒟[outputSample >>= fun freshOutput => tableSample >>= fun base =>
                    if state.hitAt coordinate freshOutput then
                      pure none
                    else
                      finalizeCleanFromTable remaining
                        (state.complete coordinate freshOutput)
                        (completedStartTable state base)] :=
                  OracleComp.DeferredSampling.evalDist_bind_comm tableSample outputSample _
                _ = _ := by
                  rw [finalizeCleanWithCompletionTable_cons_of_none coordinate remaining state
                    (by simpa [coordinate] using hvalue)]
                  rw [evalDist_bind, evalDist_bind]
                  apply congrArg
                  funext freshOutput
                  by_cases hhit : state.hitAt coordinate freshOutput
                  · simp only [hhit, ↓reduceIte]
                    have hdrop :=
                      OracleComp.DeferredSampling.evalDist_bind_const_neverFails
                        tableSample (by simp [tableSample])
                        (pure none : ProbComp (Option
                          (LazyRevealProbe.State Coordinate ×
                            (OtsSecretIndex → HashOutput))))
                    simpa [finalizeCleanWithCompletionTable] using hdrop
                  · simp only [hhit, ↓reduceIte]
                    have hleft :
                        (tableSample >>= fun base =>
                          finalizeCleanFromTable remaining
                            (state.complete coordinate freshOutput)
                            (completedStartTable state base)) =
                        (tableSample >>= fun base =>
                          finalizeCleanFromTable remaining
                            (state.complete coordinate freshOutput)
                            (completedStartTable
                              (state.complete coordinate freshOutput) base)) := by
                      apply bind_congr
                      intro base
                      rw [completedStartTable_complete_position]
                    rw [congrArg evalDist hleft]
                    exact ih (state.complete coordinate freshOutput)

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
