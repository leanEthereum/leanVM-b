import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelectionFamily

/-!
# Root-neutral initial cache

Public top-root construction touches only hidden split-cache keys. Its completed cache is therefore
neutral under every later layer-root encoding-key swap.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.constructorNameAsVariable false

theorem ordinaryCachePreserving_maskedPublishedTreeRoot :
    OrdinaryCachePreserving maskedPublishedTreeRoot := by
  unfold maskedPublishedTreeRoot
  exact (OrdinaryCachePreserving.of_splitCachePreserving
    (splitCachePreserving_ensureTreeNode topLayer rootTree (layerHeight topLayer) 0)).bind fun _ =>
      ordinaryCachePreserving_revealPublishedCoordinate
        (.position (.node topLayer rootTree
          ⟨layerHeight topLayer - 1,
            by norm_num [layerHeight, topLayer, maxLayerHeight]⟩ 0))

theorem preservesCoordinate_maskedTreeRoot_of_ne
    (position : Position) (lay : Layer) (tree : TreeIndex)
    (hne : position ≠ layerRootPosition lay tree) :
    PreservesCoordinate (.position position) (maskedTreeRoot lay tree) := by
  have hpos : 0 < layerHeight lay := by
    unfold layerHeight
    split <;> norm_num [maxLayerHeight]
  have hlevel : layerHeight lay - 1 < maxLayerHeight := by
    have hle := layerHeight_le lay
    omega
  have hcoordinate : Coordinate.position position ≠
      .position (.node lay tree ⟨layerHeight lay - 1, hlevel⟩ (leafOfNat 0)) := by
    intro heq
    apply hne
    apply Coordinate.position.inj at heq
    calc
      position = .node lay tree ⟨layerHeight lay - 1, hlevel⟩ (leafOfNat 0) := heq
      _ = layerRootPosition lay tree := by
        simp [layerRootPosition, leafOfNat]
  unfold maskedTreeRoot
  rw [show layerHeight lay = (layerHeight lay - 1) + 1 by omega, maskedTreeNode]
  exact (preservesCoordinate_ensureTreeNode (.position position) lay tree
    (layerHeight lay - 1 + 1) 0).bind fun _ => by
      rw [dif_pos hlevel]
      exact preservesCoordinate_revealPosition_of_ne (.position position)
        (.node lay tree ⟨layerHeight lay - 1, hlevel⟩ (leafOfNat 0)) hcoordinate

theorem preservesCoordinate_maskedPublishedTreeRoot_of_ne
    (position : Position)
    (hne : position ≠ layerRootPosition topLayer rootTree) :
    PreservesCoordinate (.position position) maskedPublishedTreeRoot := by
  rw [maskedPublishedTreeRoot_eq]
  exact (preservesCoordinate_maskedTreeRoot_of_ne position topLayer rootTree hne).bind fun _ =>
    (preservesCoordinate_publishCoordinate_of_ne (.position position)
      (.position (layerRootPosition topLayer rootTree)) (by
        intro heq
        exact hne (Coordinate.position.inj heq))).bind fun _ =>
      preservesCoordinate_pure (.position position) _

theorem layerRootPosition_ne_top_of_parent
    {target : Position} (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent) :
    target ≠ layerRootPosition topLayer rootTree := by
  obtain ⟨parent, hparentOf⟩ := hparent
  obtain ⟨lay, tree, hlay, htarget⟩ :=
    isShortLayerRoot_of_isLayerRoot_of_parent hroot hparentOf
  subst target
  intro heq
  simp only [layerRootPosition, Position.node.injEq] at heq
  exact hlay heq.1

theorem NoEncodingRootGuessCached.of_ordinaryCachePreserving
    (parameter : PublicParameter) (target : Position) (root : Digest)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hpreserves : OrdinaryCachePreserving computation)
    (state finalState : LazyRevealProbe.State Coordinate)
    (initialCache finalCache : SplitHashCache)
    (fuel remaining : Nat) (value : α)
    (hinitial : NoEncodingRootGuessCached parameter target root initialCache)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel (computation.run initialCache))) :
    NoEncodingRootGuessCached parameter target root finalCache := by
  have hordinary := hpreserves state initialCache fuel finalState remaining value finalCache hresult
  intro input hguess
  change ordinaryQueryCache finalCache input = none
  rw [hordinary]
  exact hinitial input hguess

theorem noEncodingRootGuessCached_empty
    (parameter : PublicParameter) (target : Position) (root : Digest) :
    NoEncodingRootGuessCached parameter target root emptySplitHashCache := by
  intro input _hguess
  rfl

set_option maxRecDepth 100000 in
theorem mem_support_runRaw_done_of_mem_runCleanFromTable_some
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : CleanRunResult α)
    (hresult : some result ∈ support (runCleanFromTable state fuel table computation)) :
    LazyRevealProbe.RawResult.done result.state result.remaining result.value ∈
      support (LazyRevealProbe.runRaw state fuel computation) := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value =>
      simp [runCleanFromTable, LazyRevealProbe.runRaw] at hresult ⊢
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      simp
  | query_bind query next ih =>
      cases query with
      | uniform n =>
          rw [runCleanFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, houtput, hrest⟩ := hresult
          rw [LazyRevealProbe.runRaw_uniform_query_bind, mem_support_bind_iff]
          exact ⟨output, houtput, ih output state fuel hrest⟩
      | hashOutput =>
          rw [runCleanFromTable_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, houtput, hrest⟩ := hresult
          rw [LazyRevealProbe.runRaw_hashOutput_query_bind, mem_support_bind_iff]
          exact ⟨output, houtput, ih output state fuel hrest⟩
      | ensure coordinate =>
          rw [runCleanFromTable_ensure_query_bind] at hresult
          rw [LazyRevealProbe.runRaw_ensure_query_bind]
          exact ih () (state.ensure coordinate) fuel hresult
      | probe coordinate candidate =>
          rw [runCleanFromTable_probe_query_bind] at hresult
          rw [LazyRevealProbe.runRaw_probe_query_bind]
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [hrevealed, ↓reduceIte] at hresult ⊢
                exact ih () state remaining hresult
              · simp only [hrevealed, ↓reduceIte] at hresult ⊢
                exact ih () (state.addPending coordinate candidate) remaining hresult
      | peek coordinate =>
          rw [runCleanFromTable_peek_query_bind] at hresult
          rw [LazyRevealProbe.runRaw_peek_query_bind]
          exact ih (state.values coordinate) state fuel hresult
      | publish coordinate =>
          rw [runCleanFromTable_publish_query_bind] at hresult
          rw [LazyRevealProbe.runRaw_publish_query_bind]
          exact ih () (state.publish coordinate) fuel hresult
      | reveal coordinate =>
          rw [runCleanFromTable_reveal_query_bind] at hresult
          rw [LazyRevealProbe.runRaw_reveal_query_bind]
          cases hvalue : state.values coordinate with
          | some output =>
              simp only [hvalue] at hresult ⊢
              exact ih output state fuel hresult
          | none =>
              simp only [hvalue] at hresult ⊢
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : state.hitAt (.chainStart lay tree leafIdx chainIdx) output
                  · simp [output, hhit] at hresult
                  · simp only [output, hhit, ↓reduceIte] at hresult
                    rw [mem_support_bind_iff]
                    refine ⟨output, ?_, ?_⟩
                    · simp [LazyRevealProbe.sampleHashOutput]
                    · simp only [hhit, ↓reduceIte]
                      exact ih output
                        (state.materialize (.chainStart lay tree leafIdx chainIdx) output) fuel
                        hresult
              | position position =>
                  rw [mem_support_bind_iff] at hresult ⊢
                  obtain ⟨output, houtput, hrest⟩ := hresult
                  refine ⟨output, houtput, ?_⟩
                  by_cases hhit : state.hitAt (.position position) output
                  · simp [hhit] at hrest
                  · simp only [hhit, ↓reduceIte] at hrest ⊢
                    exact ih output (state.materialize (.position position) output) fuel hrest

attribute [local irreducible] maskedPublishedTreeRoot

theorem noEncodingRootGuessCached_of_mem_runCleanFromTable_maskedPublishedTreeRoot
    (parameter : PublicParameter) (target : Position) (root : Digest)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (result : CleanRunResult (Digest × SplitHashCache))
    (hresult : some result ∈ support
      (runCleanFromTable state fuel table
        (maskedPublishedTreeRoot.run emptySplitHashCache))) :
    NoEncodingRootGuessCached parameter target root result.value.2 := by
  have hraw := mem_support_runRaw_done_of_mem_runCleanFromTable_some
    (maskedPublishedTreeRoot.run emptySplitHashCache) state fuel table result hresult
  exact NoEncodingRootGuessCached.of_ordinaryCachePreserving parameter target root
    maskedPublishedTreeRoot ordinaryCachePreserving_maskedPublishedTreeRoot state result.state
    emptySplitHashCache result.value.2 fuel result.remaining result.value.1
    (noEncodingRootGuessCached_empty parameter target root) hraw

theorem swapCanonicalRootEncodingCache_of_mem_runCleanFromTable_maskedPublishedTreeRoot
    (parameter : PublicParameter) (target : Position) (leftRoot rightRoot : Digest)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (result : CleanRunResult (Digest × SplitHashCache))
    (hresult : some result ∈ support
      (runCleanFromTable state fuel table
        (maskedPublishedTreeRoot.run emptySplitHashCache))) :
    swapCanonicalRootEncodingCache parameter target leftRoot rightRoot result.value.2 =
      result.value.2 :=
  swapCanonicalRootEncodingCache_eq_of_no_guesses parameter target leftRoot rightRoot
    result.value.2
    (noEncodingRootGuessCached_of_mem_runCleanFromTable_maskedPublishedTreeRoot parameter target
      leftRoot state fuel table result hresult)
    (noEncodingRootGuessCached_of_mem_runCleanFromTable_maskedPublishedTreeRoot parameter target
      rightRoot state fuel table result hresult)

theorem target_absent_of_mem_runCleanFromTable_maskedPublishedTreeRoot
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (result : CleanRunResult (Digest × SplitHashCache))
    (hresult : some result ∈ support
      (runCleanFromTable (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        fuel table (maskedPublishedTreeRoot.run emptySplitHashCache))) :
    result.state.values (.position target) = none ∧
      Coordinate.position target ∉ result.state.revealed := by
  have hraw := mem_support_runRaw_done_of_mem_runCleanFromTable_some
    (maskedPublishedTreeRoot.run emptySplitHashCache)
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table result hresult
  have hne := layerRootPosition_ne_top_of_parent hroot hparent
  have hsame := preservesCoordinate_maskedPublishedTreeRoot_of_ne target hne
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) emptySplitHashCache fuel
    result.state result.remaining result.value.1 result.value.2 hraw
  constructor
  · rw [hsame.1]
    rfl
  · intro hrevealed
    have : Coordinate.position target ∈
        (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate).revealed :=
      hsame.2.mp hrevealed
    simp [LazyRevealProbe.State.empty] at this

noncomputable def materializedRootSelectionAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (high : RootOutputHigh)
    (rootResult : CleanRunResult (Digest × SplitHashCache))
    (leftRoot rightRoot : Digest) : ProbComp (Option Probe) :=
  let output := fun root => rootOutputOfParts root high
  let context : DeferredContext := directDeferredContext rootResult.state
  let rootContext :=
    { context with values := context.values.install target (output leftRoot) }
  materializedActualRootAvoidingOrdinalSelection ordinal parameter rootResult.value.1 target
    leftRoot rightRoot ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
    (materializedDeferredState rootContext) rootResult.remaining rootResult.table
    (rootInstalledCache target output rootResult.value.2 leftRoot)

set_option maxRecDepth 100000 in
theorem probEvent_uniformActualRoot_materializedSelectionAfterRootResult_le_mul
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (high : RootOutputHigh) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (rootResult : CleanRunResult (Digest × SplitHashCache))
    (hresult : some rootResult ∈ support
      (runCleanFromTable (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        fuel table (maskedPublishedTreeRoot.run emptySplitHashCache))) :
    Pr[fun result : Digest × Digest × Option Probe =>
        materializedOrdinalSelectionMatches target result.1 result.2.2 | do
      let leftRoot ← ($ᵗ Digest : ProbComp Digest)
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      let selection ← materializedRootSelectionAfterRootResult ordinal adversary parameter
        ftsSecret target high rootResult leftRoot rightRoot
      pure (leftRoot, rightRoot, selection)] ≤
      Pr[fun result : Digest × Option Probe =>
          materializedOrdinalSelectionAt target result.2 | do
        let leftRoot ← ($ᵗ Digest : ProbComp Digest)
        let selection ← materializedRootSelectionAfterRootResult ordinal adversary parameter
          ftsSecret target high rootResult leftRoot leftRoot
        pure (leftRoot, selection)] *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  let output := fun root => rootOutputOfParts root high
  let context : DeferredContext := directDeferredContext rootResult.state
  have habsent := target_absent_of_mem_runCleanFromTable_maskedPublishedTreeRoot target hroot
    hparent fuel table rootResult hresult
  unfold materializedRootSelectionAfterRootResult
  apply probEvent_uniformActualRoot_materializedRootInstalledMatches_le_mul ordinal parameter
    rootResult.value.1 target hroot output (fun root => by
      exact truncateHash_rootOutputOfParts root high)
    ftsSecret (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
    context habsent.1 habsent.2 rootResult.remaining rootResult.table rootResult.value.2
  intro leftRoot rightRoot
  exact swapCanonicalRootEncodingCache_of_mem_runCleanFromTable_maskedPublishedTreeRoot parameter
    target leftRoot rightRoot (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
    fuel table rootResult hresult

theorem probEvent_bind_le_bind_mul_of_forall
    (first : ProbComp ι) (left : ι → ProbComp α) (right : ι → ProbComp β)
    (event : α → Prop) (gate : β → Prop) (epsilon : ENNReal)
    (hbound : ∀ index ∈ support first,
      Pr[event | left index] ≤ Pr[gate | right index] * epsilon) :
    Pr[event | first >>= left] ≤ Pr[gate | first >>= right] * epsilon := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' index, Pr[= index | first] *
          (Pr[gate | right index] * epsilon) := by
      apply ENNReal.tsum_le_tsum
      intro index
      by_cases hindex : index ∈ support first
      · gcongr
        exact hbound index hindex
      · rw [probOutput_eq_zero_of_not_mem_support hindex]
        simp
    _ = (∑' index, Pr[= index | first] * Pr[gate | right index]) * epsilon := by
      simp_rw [← mul_assoc]
      rw [ENNReal.tsum_mul_right]

noncomputable def sampledHighMaterializedRootSelectionAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    ProbComp (Digest × Digest × Option Probe) := do
  let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
  let leftRoot ← ($ᵗ Digest : ProbComp Digest)
  let rightRoot ← ($ᵗ Digest : ProbComp Digest)
  let selection ← materializedRootSelectionAfterRootResult ordinal adversary parameter
    ftsSecret target high rootResult leftRoot rightRoot
  pure (leftRoot, rightRoot, selection)

noncomputable def sampledHighMaterializedRootSelectionProductionAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    ProbComp (Digest × Option Probe) := do
  let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
  let leftRoot ← ($ᵗ Digest : ProbComp Digest)
  let selection ← materializedRootSelectionAfterRootResult ordinal adversary parameter
    ftsSecret target high rootResult leftRoot leftRoot
  pure (leftRoot, selection)

set_option maxRecDepth 100000 in
theorem probEvent_sampledHigh_materializedSelectionAfterRootResult_le_mul
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (rootResult : CleanRunResult (Digest × SplitHashCache))
    (hresult : some rootResult ∈ support
      (runCleanFromTable (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        fuel table (maskedPublishedTreeRoot.run emptySplitHashCache))) :
    Pr[fun result => materializedOrdinalSelectionMatches target result.1 result.2.2 |
        sampledHighMaterializedRootSelectionAfterRootResult ordinal adversary parameter ftsSecret
          target rootResult] ≤
      Pr[fun result => materializedOrdinalSelectionAt target result.2 |
          sampledHighMaterializedRootSelectionProductionAfterRootResult ordinal adversary parameter
            ftsSecret target rootResult] *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  unfold sampledHighMaterializedRootSelectionAfterRootResult
    sampledHighMaterializedRootSelectionProductionAfterRootResult
  apply probEvent_bind_le_bind_mul_of_forall
  intro high _hhigh
  exact probEvent_uniformActualRoot_materializedSelectionAfterRootResult_le_mul ordinal adversary
    parameter ftsSecret target hroot hparent high fuel table rootResult hresult

noncomputable def materializedRootOrdinalMatchExperimentAfterTable
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    ProbComp (Digest × Digest × Option Probe) := do
  let rootResult ← runCleanFromTable
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
    (maskedPublishedTreeRoot.run emptySplitHashCache)
  match rootResult with
  | none => pure (0, 0, none)
  | some result =>
      sampledHighMaterializedRootSelectionAfterRootResult ordinal adversary parameter ftsSecret
        target result

noncomputable def materializedRootOrdinalProductionExperimentAfterTable
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    ProbComp (Digest × Option Probe) := do
  let rootResult ← runCleanFromTable
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
    (maskedPublishedTreeRoot.run emptySplitHashCache)
  match rootResult with
  | none => pure (0, none)
  | some result =>
      sampledHighMaterializedRootSelectionProductionAfterRootResult ordinal adversary parameter
        ftsSecret target result

set_option maxRecDepth 100000 in
theorem probEvent_materializedRootOrdinalMatchExperimentAfterTable_le_mul
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    Pr[fun result => materializedOrdinalSelectionMatches target result.1 result.2.2 |
        materializedRootOrdinalMatchExperimentAfterTable ordinal adversary parameter ftsSecret
          target fuel table] ≤
      Pr[fun result => materializedOrdinalSelectionAt target result.2 |
          materializedRootOrdinalProductionExperimentAfterTable ordinal adversary parameter
            ftsSecret target fuel table] *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  classical
  unfold materializedRootOrdinalMatchExperimentAfterTable
    materializedRootOrdinalProductionExperimentAfterTable
  apply probEvent_bind_le_bind_mul_of_forall
  intro rootResult hrootResult
  cases rootResult with
  | none =>
      rw [probEvent_pure, probEvent_pure]
      simp [materializedOrdinalSelectionMatches, materializedOrdinalSelectionAt]
  | some result =>
      exact probEvent_sampledHigh_materializedSelectionAfterRootResult_le_mul ordinal adversary
        parameter ftsSecret target hroot hparent fuel table result hrootResult

end SphincsSecurity.Concrete.OtsProbeSimulation
