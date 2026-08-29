import SphincsSecurity.Proof.OtsProbeResolvedDirect
import SphincsSecurity.Proof.OtsProbeResolvedPrivateObserver

/-! Erasure of the recursive work performed by one structural reveal. -/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

def DeferredAbsentOn (coordinates : List Coordinate) (context : DeferredContext) : Prop :=
  ∀ position : Position, Coordinate.position position ∈ coordinates →
    context.state.values (.position position) = none → context.values position = none

set_option maxRecDepth 100000 in
theorem finalizeResolvedCoordinates_projects_to_clean_of_absent
    (coordinates : List Coordinate) (context : DeferredContext)
    (table : OtsSecretIndex → HashOutput)
    (hnodup : coordinates.Nodup) (habsent : DeferredAbsentOn coordinates context) :
    (fun result => result.map fun finalContext => (finalContext.state, table)) <$>
        finalizeResolvedCoordinates coordinates context table =
      finalizeCleanFromTable coordinates context.state table := by
  induction coordinates generalizing context with
  | nil => simp [finalizeResolvedCoordinates, finalizeCleanFromTable]
  | cons coordinate remaining ih =>
      obtain ⟨hnotMem, htailNodup⟩ := List.nodup_cons.mp hnodup
      cases hstate : context.state.values coordinate with
      | some output =>
          rw [finalizeResolvedCoordinates, finalizeCleanFromTable.eq_def]
          simp only [hstate]
          apply ih { context with state := context.state.clearPending coordinate }
            htailNodup
          intro position hmem hmissing
          apply habsent position (List.mem_cons_of_mem coordinate hmem)
          exact hmissing
      | none =>
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
              have hstate' : context.state.values index.coordinate = none := by
                simpa [index, OtsSecretIndex.coordinate] using hstate
              rw [finalizeResolvedCoordinates, finalizeCleanFromTable.eq_def]
              simp only [hstate]
              rw [resolveDeferredChainStart_of_missing table index context hstate']
              by_cases hhit : context.state.hitAt
                  (.chainStart lay tree leafIdx chainIdx) (table index)
              · simp [index, OtsSecretIndex.coordinate, hhit]
              · simp only [index, OtsSecretIndex.coordinate, hhit, ↓reduceIte,
                    map_eq_bind_pure_comp, pure_bind]
                rw [clearPending_complete_self]
                simpa only [map_eq_bind_pure_comp] using ih
                  { state := context.state.complete (.chainStart lay tree leafIdx chainIdx)
                      (table index)
                    values := context.values }
                  htailNodup (by
                    intro position hmem hmissing
                    apply habsent position (List.mem_cons_of_mem _ hmem)
                    exact hmissing)
          | position position =>
              have hvalue : context.values position = none :=
                habsent position (by simp) hstate
              rw [finalizeResolvedCoordinates, finalizeCleanFromTable.eq_def]
              simp only [hstate]
              rw [resolveDeferredPositionValue_fresh position context hstate hvalue]
              simp only [map_eq_bind_pure_comp, bind_assoc]
              apply bind_congr
              intro output
              by_cases hhit : context.state.hitAt (.position position) output
              · simp [hhit]
              · simp only [hhit, ↓reduceIte, pure_bind]
                rw [clearPending_complete_self]
                simpa only [map_eq_bind_pure_comp] using ih
                  { state := context.state.complete (.position position) output
                    values := context.values.install position output }
                  htailNodup (by
                    intro other hmem hmissing
                    have hne : other ≠ position := by
                      intro heq
                      subst other
                      exact hnotMem hmem
                    have hmissingOriginal :
                        context.state.values (.position other) = none := by
                      simpa [LazyRevealProbe.State.complete, Function.update_of_ne,
                        show Coordinate.position other ≠ Coordinate.position position by
                          simpa using hne] using hmissing
                    simp [DeferredStructuralValues.install, hne,
                      habsent other (List.mem_cons_of_mem _ hmem) hmissingOriginal])

theorem directDeferredContext_absentOn
    (coordinates : List Coordinate) (state : LazyRevealProbe.State Coordinate) :
    DeferredAbsentOn coordinates (directDeferredContext state) := by
  intro position _hmem hvalue
  simpa [directDeferredContext, directDeferredValues] using hvalue

theorem finishResolvedRun_direct_projects_to_clean
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (value : α) (table : OtsSecretIndex → HashOutput)
    (hcompletable : DeferredCompletable table (directDeferredContext state)) :
    projectResolvedRunResult <$>
        finishResolvedRun
          (some ⟨directDeferredContext state, fuel, value, table⟩) =
      finishCleanRunFromTable (some ⟨state, fuel, value, table⟩) := by
  simp only [finishResolvedRun, hcompletable, ↓reduceIte, finishCleanRunFromTable]
  simp only [show (directDeferredContext state).state = state from rfl]
  have hfinal := finalizeResolvedCoordinates_projects_to_clean_of_absent
    state.coordinates.toList (directDeferredContext state) table state.coordinates.nodup_toList
      (directDeferredContext_absentOn state.coordinates.toList state)
  have hfinal' :
      (fun result => result.map fun finalContext => (finalContext.state, table)) <$>
          finalizeResolvedCoordinates state.coordinates.toList
            (directDeferredContext state) table =
        finalizeCleanFromTable state.coordinates.toList state table := by
    rw [show (directDeferredContext state).state = state from rfl] at hfinal
    exact hfinal
  rw [← hfinal']
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro finalized
  cases finalized <;> simp [projectResolvedRunResult]

theorem evalDist_finishResolvedRunIsNone_eq_finishDirectRunIsNone
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (value : α) (table : OtsSecretIndex → HashOutput)
    (hcompletable : DeferredCompletable table (directDeferredContext state)) :
    evalDist (finishResolvedRunIsNone
        (some ⟨directDeferredContext state, fuel, value, table⟩)) =
      evalDist (finishDirectRunIsNone
        (some ⟨directDeferredContext state, fuel, value, table⟩)) := by
  have hprojection := finishResolvedRun_direct_projects_to_clean state fuel value table
    hcompletable
  unfold finishResolvedRunIsNone finishDirectRunIsNone finishCleanRunIsNone
  simp only [projectResolvedRunResult]
  rw [show (directDeferredContext state).state = state from rfl]
  rw [← hprojection]
  rw [Functor.map_map]
  apply congrArg evalDist
  apply congrArg (fun f : Option (ResolvedRunResult α) → Bool =>
    f <$> finishResolvedRun
      (some ⟨directDeferredContext state, fuel, value, table⟩))
  funext result
  cases result <;> rfl

def RecursiveRevealEnsured (position : Position) (context : DeferredContext) : Prop :=
  match position with
  | .chain lay tree leafIdx chainIdx step =>
      ∀ current : ChainStep, current.val < step.val + 1 →
        Coordinate.position (.chain lay tree leafIdx chainIdx current) ∈
          context.state.ensured
  | .leaf lay tree leafIdx => OtsLeafEnsured lay tree leafIdx context
  | .node lay tree level nodeIdx =>
      TreeNodeEnsured lay tree (level.val + 1) nodeIdx context
  | _ => True

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredReveal_then_runResolvedObserve_of_resolvable
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (context : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    {observe : DeferredContext → Nat → α → ProbComp Bool}
    [ObserverDooms table observe] [ObserverSynchronized table observe]
    [ObserverPositionNeutral table observe]
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hresolvable : ResolvableOtsPosition position)
    (hensured : RecursiveRevealEnsured position context) :
    evalDist (do
      let resolved ← resolveDeferredReveal table position context
      match resolved with
      | none => pure true
      | some resolved =>
          runResolvedObserve observe resolved.toDeferredContext fuel table computation) =
      evalDist (runResolvedObserve observe context fuel table computation) := by
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      have hsteps : step.val + 1 ≤ chainLength - 1 := by
        have := step.isLt
        omega
      rw [resolveDeferredReveal, if_pos hresolvable]
      simp only [resolveDeferredPosition]
      change evalDist (do
        let resolved ← resolveDeferredChainPrefix table lay tree leafIdx chainIdx
          (step.val + 1) hsteps context
        match resolved with
        | none => pure true
        | some resolved =>
            runResolvedObserve observe resolved.toDeferredContext fuel table computation) = _
      exact evalDist_resolveDeferredChainPrefix_then_runResolvedObserve
        (observe := observe) table lay tree leafIdx chainIdx (step.val + 1)
          hsteps context fuel computation hvalid hcompletable hensured
  | leaf lay tree leafIdx =>
      rw [resolveDeferredReveal, if_pos hresolvable]
      exact evalDist_resolveDeferredOtsLeaf_then_runResolvedObserve
        (observe := observe) table lay tree leafIdx context fuel computation hvalid
          hcompletable hensured
  | node lay tree level nodeIdx =>
      have hlevel : level.val + 1 ≤ maxLayerHeight := by
        have := level.isLt
        omega
      rw [resolveDeferredReveal, if_pos hresolvable]
      simp only [resolveDeferredPosition]
      change evalDist (do
        let resolved ← resolveDeferredTreeNode table lay tree (level.val + 1) nodeIdx
          hlevel context
        match resolved with
        | none => pure true
        | some resolved =>
            runResolvedObserve observe resolved.toDeferredContext fuel table computation) = _
      exact evalDist_resolveDeferredTreeNode_then_runResolvedObserve
        (observe := observe) table lay tree (level.val + 1) nodeIdx
          hlevel context fuel computation hvalid hcompletable hensured
  | ftsLeaf index tree leafIdx =>
      simp [ResolvableOtsPosition] at hresolvable
  | ftsNode index tree level nodeIdx =>
      simp [ResolvableOtsPosition] at hresolvable
  | ftsRoots index =>
      simp [ResolvableOtsPosition] at hresolvable

end SphincsSecurity.Concrete.OtsProbeSimulation
