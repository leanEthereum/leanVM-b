import SphincsSecurity.Proof.OtsProbeProbeFreeRisk
import SphincsSecurity.Proof.OtsProbeEnsuredInitialization

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def DeferredContext.enlargeEnsured (context : DeferredContext) (extra : Finset Coordinate) : DeferredContext :=
  { context with state := { context.state with ensured := context.state.ensured ∪ extra } }

def DeferredResolution.enlargeEnsured (result : DeferredResolution) (extra : Finset Coordinate) : DeferredResolution :=
  ⟨result.toDeferredContext.enlargeEnsured extra, result.output⟩

def ResolvedRunResult.enlargeEnsured (result : ResolvedRunResult α) (extra : Finset Coordinate) : ResolvedRunResult α :=
  { result with context := result.context.enlargeEnsured extra }

theorem DeferredContext.coreEq_enlargeEnsured (context : DeferredContext) (extra : Finset Coordinate) :
    context.CoreEq (context.enlargeEnsured extra) := ⟨rfl, rfl, rfl⟩

theorem resolveDeferredPositionValue_enlargeEnsured
    (position : Position) (context : DeferredContext) (extra : Finset Coordinate) :
    resolveDeferredPositionValue position (context.enlargeEnsured extra) =
      Option.map (fun result => result.enlargeEnsured extra) <$> resolveDeferredPositionValue position context := by
  unfold resolveDeferredPositionValue
  cases hstate : context.state.values (.position position) with
  | some output =>
      by_cases hhit : context.state.hitAt (.position position) output <;>
        simp_all [DeferredContext.enlargeEnsured, DeferredResolution.enlargeEnsured,
          LazyRevealProbe.State.clearPending, LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt,
          LazyRevealProbe.State.pendingAway]
  | none =>
      cases hvalue : context.values position with
      | some output =>
          by_cases hhit : context.state.hitAt (.position position) output <;>
            simp_all [DeferredContext.enlargeEnsured, DeferredResolution.enlargeEnsured,
              LazyRevealProbe.State.clearPending, LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt,
              LazyRevealProbe.State.pendingAway]
      | none =>
          simp only [DeferredContext.enlargeEnsured, hstate, hvalue]
          rw [map_bind]
          apply bind_congr
          intro output
          by_cases hhit : context.state.hitAt (.position position) output <;>
            simp_all [DeferredResolution.enlargeEnsured, DeferredContext.enlargeEnsured,
              LazyRevealProbe.State.clearPending, LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt,
              LazyRevealProbe.State.pendingAway]

theorem resolveDeferredChainStart_enlargeEnsured
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (context : DeferredContext) (extra : Finset Coordinate) :
    resolveDeferredChainStart table index (context.enlargeEnsured extra) =
      (resolveDeferredChainStart table index context).map (fun result => result.enlargeEnsured extra) := by
  unfold resolveDeferredChainStart
  cases hvalue : context.state.values index.coordinate with
  | none =>
      by_cases hhit : context.state.hitAt index.coordinate (table index) <;>
        simp_all [DeferredContext.enlargeEnsured, DeferredResolution.enlargeEnsured,
          LazyRevealProbe.State.clearPending, LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt,
          LazyRevealProbe.State.pendingAway]
  | some output =>
      by_cases hhit : context.state.hitAt index.coordinate output <;>
        simp_all [DeferredContext.enlargeEnsured, DeferredResolution.enlargeEnsured,
          LazyRevealProbe.State.clearPending, LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt,
          LazyRevealProbe.State.pendingAway]

theorem resolveDeferredChainPrefix_enlargeEnsured
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (steps : Nat) (hsteps : steps ≤ chainLength - 1)
    (context : DeferredContext) (extra : Finset Coordinate) :
    resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps hsteps (context.enlargeEnsured extra) =
      Option.map (fun result => result.enlargeEnsured extra) <$>
        resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps hsteps context := by
  induction steps generalizing context with
  | zero => simp only [resolveDeferredChainPrefix, resolveDeferredChainStart_enlargeEnsured, map_pure]
  | succ steps ih =>
      rw [resolveDeferredChainPrefix, ih, bind_map_left, resolveDeferredChainPrefix, map_bind]
      apply bind_congr
      intro result
      cases result with
      | none => simp
      | some result => exact resolveDeferredPositionValue_enlargeEnsured _ result.toDeferredContext extra

theorem resolveDeferredChains_enlargeEnsured
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chains : List ChainIndex) (context : DeferredContext) (extra : Finset Coordinate) :
    resolveDeferredChains table lay tree leafIdx chains (context.enlargeEnsured extra) =
      Option.map (fun result => result.enlargeEnsured extra) <$> resolveDeferredChains table lay tree leafIdx chains context := by
  induction chains generalizing context with
  | nil => simp [resolveDeferredChains]
  | cons chainIdx chains ih =>
      rw [resolveDeferredChains, resolveDeferredChainPrefix_enlargeEnsured, bind_map_left,
        resolveDeferredChains, map_bind]
      apply bind_congr
      intro result
      cases result with
      | none => simp
      | some result => exact ih result.toDeferredContext

theorem resolveDeferredOtsLeaf_enlargeEnsured
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (context : DeferredContext) (extra : Finset Coordinate) :
    resolveDeferredOtsLeaf table lay tree leafIdx (context.enlargeEnsured extra) =
      Option.map (fun result => result.enlargeEnsured extra) <$> resolveDeferredOtsLeaf table lay tree leafIdx context := by
  rw [resolveDeferredOtsLeaf, resolveDeferredChains_enlargeEnsured, bind_map_left, resolveDeferredOtsLeaf, map_bind]
  apply bind_congr
  intro result
  cases result with
  | none => simp
  | some result => exact resolveDeferredPositionValue_enlargeEnsured _ result extra

theorem resolveDeferredTreeNode_enlargeEnsured
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (level nodeIdx : Nat) (hlevel : level ≤ maxLayerHeight) (context : DeferredContext) (extra : Finset Coordinate) :
    resolveDeferredTreeNode table lay tree level nodeIdx hlevel (context.enlargeEnsured extra) =
      Option.map (fun result => result.enlargeEnsured extra) <$>
        resolveDeferredTreeNode table lay tree level nodeIdx hlevel context := by
  induction level generalizing nodeIdx context with
  | zero => exact resolveDeferredOtsLeaf_enlargeEnsured table lay tree (leafOfNat nodeIdx) context extra
  | succ level ih =>
      rw [resolveDeferredTreeNode, ih, bind_map_left, resolveDeferredTreeNode, map_bind]
      apply bind_congr
      intro left
      cases left with
      | none => simp
      | some left =>
          dsimp only [Option.map, DeferredResolution.enlargeEnsured, Function.comp_def]
          rw [ih, bind_map_left, map_bind]
          apply bind_congr
          intro right
          cases right with
          | none => simp
          | some right => exact resolveDeferredPositionValue_enlargeEnsured _ right.toDeferredContext extra

theorem resolveDeferredReveal_enlargeEnsured
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (context : DeferredContext) (extra : Finset Coordinate) :
    resolveDeferredReveal table position (context.enlargeEnsured extra) =
      Option.map (fun result => result.enlargeEnsured extra) <$> resolveDeferredReveal table position context := by
  unfold resolveDeferredReveal
  split_ifs with hposition
  · cases position <;> simp only [resolveDeferredPosition, resolveDeferredChainPrefix_enlargeEnsured,
      resolveDeferredOtsLeaf_enlargeEnsured, resolveDeferredTreeNode_enlargeEnsured, resolveDeferredPositionValue_enlargeEnsured]
  · exact resolveDeferredPositionValue_enlargeEnsured position context extra

theorem runResolvedFromTable_enlargeEnsured
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (extra : Finset Coordinate) :
    runResolvedFromTable (context.enlargeEnsured extra) fuel table computation =
      Option.map (fun result => result.enlargeEnsured extra) <$> runResolvedFromTable context fuel table computation := by
  induction computation using OracleComp.inductionOn generalizing context fuel table with
  | pure value => simp [runResolvedFromTable, ResolvedRunResult.enlargeEnsured]
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runResolvedFromTable_uniform_query_bind, runResolvedFromTable_uniform_query_bind, map_bind]
          exact bind_congr fun output => ih output context fuel table
      | hashOutput =>
          rw [runResolvedFromTable_hashOutput_query_bind, runResolvedFromTable_hashOutput_query_bind, map_bind]
          exact bind_congr fun output => ih output context fuel table
      | ensure coordinate =>
          rw [runResolvedFromTable_ensure_query_bind, runResolvedFromTable_ensure_query_bind]
          simpa only [DeferredContext.enlargeEnsured, LazyRevealProbe.State.ensure, Finset.insert_union] using
            ih () { context with state := context.state.ensure coordinate } fuel table
      | probe coordinate candidate =>
          rw [runResolvedFromTable_probe_query_bind, runResolvedFromTable_probe_query_bind]
          cases fuel with
          | zero => simp
          | succ fuel =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · simpa only [DeferredContext.enlargeEnsured, hrevealed, ↓reduceIte] using ih () context fuel table
              · simpa only [DeferredContext.enlargeEnsured, hrevealed, ↓reduceIte, LazyRevealProbe.State.addPending] using
                  ih () { context with state := context.state.addPending coordinate candidate } fuel table
      | peek coordinate =>
          rw [runResolvedFromTable_peek_query_bind, runResolvedFromTable_peek_query_bind]
          exact ih (context.state.values coordinate) context fuel table
      | publish coordinate =>
          rw [runResolvedFromTable_publish_query_bind, runResolvedFromTable_publish_query_bind]
          exact ih () { context with state := context.state.publish coordinate } fuel table
      | reveal coordinate =>
          rw [runResolvedFromTable_reveal_query_bind, runResolvedFromTable_reveal_query_bind]
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              simp only [resolveDeferredChainStart_enlargeEnsured, pure_bind]
              cases hresolved : resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ context with
              | none => simp
              | some result =>
                  simpa only [Option.map, DeferredResolution.enlargeEnsured, DeferredContext.enlargeEnsured,
                    LazyRevealProbe.State.materialize, LazyRevealProbe.State.pendingAway, Finset.insert_union] using
                    ih result.output ⟨context.state.materialize (.chainStart lay tree leafIdx chainIdx) result.output, result.values⟩ fuel table
          | position position =>
              dsimp only
              rw [resolveDeferredReveal_enlargeEnsured, bind_map_left, map_bind]
              apply bind_congr
              intro result
              cases result with
              | none => simp
              | some result =>
                  simpa only [Option.map, DeferredResolution.enlargeEnsured, DeferredContext.enlargeEnsured,
                    LazyRevealProbe.State.materialize, LazyRevealProbe.State.pendingAway, Finset.insert_union] using
                    ih result.output ⟨context.state.materialize (.position position) result.output, result.values⟩ fuel table

theorem evalDist_finishResolvedRunIsNone_enlargeEnsured
    (result : ResolvedRunResult α) (extra : Finset Coordinate)
    (hconsistent : result.context.ValuesConsistent) (hstarts : StartTableAgrees result.context.state result.table) :
    evalDist (finishResolvedRunIsNone (some (result.enlargeEnsured extra))) =
      evalDist (finishResolvedRunIsNone (some result)) := by
  have heq := result.context.coreEq_enlargeEnsured extra
  have hcompleteEq := deferredCompletable_iff_of_coreEq (table := result.table) heq
  by_cases hcomplete : DeferredCompletable result.table result.context
  · have hvalid := valid_of_resolvedCore_completable result.table result.context hconsistent hstarts hcomplete
    rw [finishResolvedRunIsNone_some_eq_finalize (result.enlargeEnsured extra) (hcompleteEq.mp hcomplete),
      finishResolvedRunIsNone_some_eq_finalize result hcomplete]
    exact (evalDist_finalize_failure_of_coreEq result.table _ _ hvalid hstarts hcomplete heq).symm
  · have hright : ¬DeferredCompletable result.table (result.context.enlargeEnsured extra) :=
      fun h => hcomplete (hcompleteEq.mpr h)
    rw [show finishResolvedRunIsNone (some (result.enlargeEnsured extra)) = pure true by
      simp [finishResolvedRunIsNone, finishResolvedRun, ResolvedRunResult.enlargeEnsured, hright]]
    simp [finishResolvedRunIsNone, finishResolvedRun, hcomplete]

theorem evalDist_runResolved_finish_enlargeEnsured
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (extra : Finset Coordinate)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    evalDist (runResolvedFromTable (context.enlargeEnsured extra) fuel table computation >>= finishResolvedRunIsNone) =
      evalDist (runResolvedFromTable context fuel table computation >>= finishResolvedRunIsNone) := by
  rw [runResolvedFromTable_enlargeEnsured, bind_map_left]
  apply evalDist_bind_congr
  intro result hresult
  cases result with
  | none => rfl
  | some result =>
      have hcore := resolvedCore_of_mem_runResolvedFromTable computation context fuel table result
        hconsistent hstarts hresult
      exact evalDist_finishResolvedRunIsNone_enlargeEnsured result extra hcore.2.1 (by rw [hcore.1]; exact hcore.2.2)

end SphincsSecurity.Concrete.OtsProbeSimulation
