import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateSafe

/-!
# Private-boundary probe planning

The probing hash handler is factored into a probe-free planner, at most one probe, and a probe-free suffix. The planner depends only on public input and materialization presence, never on a deferred private value.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

inductive PlannedHashAction where
  | ordinary
  | resolve (coordinate : Coordinate)

structure PlannedHashQuery where
  candidate? : Option Probe
  action : PlannedHashAction

noncomputable def firstMissingInputCoordinatePlan (state : LazyRevealProbe.State Coordinate)
    (input : HashInput) : Nat → List Coordinate → Option Probe
  | _, [] => none
  | slot, coordinate :: remaining =>
      match state.values coordinate with
      | none => some ⟨coordinate, slotDigest slot input⟩
      | some _ => firstMissingInputCoordinatePlan state input (slot + 1) remaining

noncomputable def leafInputProbePlan (state : LazyRevealProbe.State Coordinate)
    (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) : Option Probe :=
  match state.values candidate.coordinate with
  | none => some candidate
  | some _ =>
      firstMissingInputCoordinatePlan state input 0
        ((Position.leaf lay tree leafIdx).children.map Coordinate.position)

noncomputable def probingHashQueryPlan (state : LazyRevealProbe.State Coordinate)
    (parameter : PublicParameter) (input : HashInput) : PlannedHashQuery :=
  match decodeProbe? parameter input with
  | some candidate =>
      match decodePosition? parameter input with
      | some (.leaf lay tree leafIdx) =>
          ⟨leafInputProbePlan state input candidate lay tree leafIdx,
            .resolve candidate.outputCoordinate⟩
      | _ => ⟨some candidate, .resolve candidate.outputCoordinate⟩
  | none =>
      match decodePosition? parameter input with
      | some position@(.chain _ _ _ _ _) => ⟨none, .resolve (.position position)⟩
      | some position@(.leaf _ _ _) => ⟨none, .resolve (.position position)⟩
      | some position@(.node _ _ _ _) =>
          ⟨firstMissingInputCoordinatePlan state input 0
              (position.children.map Coordinate.position),
            .resolve (.position position)⟩
      | _ => ⟨none, .ordinary⟩

noncomputable def planFirstMissingInputCoordinate (input : HashInput) :
    Nat → List Coordinate →
      StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) (Option Probe)
  | _, [] => pure none
  | slot, coordinate :: remaining => do
      match ← peekCoordinate coordinate with
      | none => pure (some ⟨coordinate, slotDigest slot input⟩)
      | some _ => planFirstMissingInputCoordinate input (slot + 1) remaining

noncomputable def planLeafInputProbe (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Probe) := do
  match ← peekCoordinate candidate.coordinate with
  | none => pure (some candidate)
  | some _ =>
      planFirstMissingInputCoordinate input 0
        ((Position.leaf lay tree leafIdx).children.map Coordinate.position)

noncomputable def planProbingHashQuery (parameter : PublicParameter) (input : HashInput) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) PlannedHashQuery :=
  match decodeProbe? parameter input with
  | some candidate =>
      match decodePosition? parameter input with
      | some (.leaf lay tree leafIdx) => do
          let candidate? ← planLeafInputProbe input candidate lay tree leafIdx
          pure ⟨candidate?, .resolve candidate.outputCoordinate⟩
      | _ => pure ⟨some candidate, .resolve candidate.outputCoordinate⟩
  | none =>
      match decodePosition? parameter input with
      | some position@(.chain _ _ _ _ _) => pure ⟨none, .resolve (.position position)⟩
      | some position@(.leaf _ _ _) => pure ⟨none, .resolve (.position position)⟩
      | some position@(.node _ _ _ _) => do
          let candidate? ← planFirstMissingInputCoordinate input 0
            (position.children.map Coordinate.position)
          pure ⟨candidate?, .resolve (.position position)⟩
      | _ => pure ⟨none, .ordinary⟩

@[simp] noncomputable def executeCandidate? : Option Probe →
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) Unit
  | none => pure ()
  | some candidate => probe candidate

noncomputable def executePlannedHashQuery
    (parameter : PublicParameter) (input : HashInput) (plan : PlannedHashQuery) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) HashOutput := do
  executeCandidate? plan.candidate?
  match plan.action with
  | .ordinary => splitHashQuery (.ordinary input)
  | .resolve coordinate => resolveKnownInput parameter coordinate input

theorem planFirstMissingInputCoordinate_execute
    (input : HashInput) : ∀ slot coordinates,
    (do
      let candidate? ← planFirstMissingInputCoordinate input slot coordinates
      executeCandidate? candidate?) =
      probeFirstMissingInputCoordinate input slot coordinates := by
  intro slot coordinates
  induction coordinates generalizing slot with
  | nil => simp [planFirstMissingInputCoordinate, probeFirstMissingInputCoordinate]
  | cons coordinate remaining ih =>
      simp only [planFirstMissingInputCoordinate, probeFirstMissingInputCoordinate, bind_assoc]
      apply bind_congr
      intro value
      cases value with
      | none => simp
      | some output => simpa using ih (slot + 1)

theorem planLeafInputProbe_execute
    (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    (do
      let candidate? ← planLeafInputProbe input candidate lay tree leafIdx
      executeCandidate? candidate?) =
      prepareLeafInputProbe input candidate lay tree leafIdx := by
  unfold planLeafInputProbe prepareLeafInputProbe
  simp only [bind_assoc]
  apply bind_congr
  intro value
  cases value with
  | none => simp
  | some output =>
      simpa using planFirstMissingInputCoordinate_execute input 0
        ((Position.leaf lay tree leafIdx).children.map Coordinate.position)

theorem planFirstMissingInputCoordinate_probeFree
    (input : HashInput) (slot : Nat) (coordinates : List Coordinate) :
    ProbeFree (planFirstMissingInputCoordinate input slot coordinates) := by
  induction coordinates generalizing slot with
  | nil => exact ProbeFree.pure none
  | cons coordinate remaining ih =>
      rw [planFirstMissingInputCoordinate]
      apply (peekCoordinate_probeFree coordinate).bind
      intro value
      cases value with
      | none =>
          simpa using (ProbeFree.pure
            (some (⟨coordinate, slotDigest slot input⟩ : Probe) : Option Probe))
      | some output => simpa using ih (slot + 1)

theorem planLeafInputProbe_probeFree
    (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    ProbeFree (planLeafInputProbe input candidate lay tree leafIdx) := by
  unfold planLeafInputProbe
  apply (peekCoordinate_probeFree candidate.coordinate).bind
  intro value
  cases value with
  | none => simpa using (ProbeFree.pure (some candidate : Option Probe))
  | some output =>
      simpa using planFirstMissingInputCoordinate_probeFree input 0
        ((Position.leaf lay tree leafIdx).children.map Coordinate.position)

theorem planProbingHashQuery_probeFree
    (parameter : PublicParameter) (input : HashInput) :
    ProbeFree (planProbingHashQuery parameter input) := by
  unfold planProbingHashQuery
  cases decodeProbe? parameter input with
  | some candidate =>
      cases hposition : decodePosition? parameter input with
      | none => exact ProbeFree.pure _
      | some position =>
          cases position with
          | leaf lay tree leafIdx =>
              exact (planLeafInputProbe_probeFree input candidate lay tree leafIdx).bind
                fun candidate? => ProbeFree.pure
                  (⟨candidate?, .resolve candidate.outputCoordinate⟩ : PlannedHashQuery)
          | chain | node | ftsLeaf | ftsNode | ftsRoots => exact ProbeFree.pure _
  | none =>
      cases hposition : decodePosition? parameter input with
      | none => exact ProbeFree.pure _
      | some position =>
          cases position with
          | node lay tree level nodeIdx =>
              exact (planFirstMissingInputCoordinate_probeFree input 0
                ((Position.node lay tree level nodeIdx).children.map Coordinate.position)).bind
                  fun candidate? => ProbeFree.pure
                    (⟨candidate?, .resolve (.position
                      (.node lay tree level nodeIdx))⟩ : PlannedHashQuery)
          | chain | leaf | ftsLeaf | ftsNode | ftsRoots => exact ProbeFree.pure _

theorem runDirectResolvedDetailed_planFirstMissingInputCoordinate
    (state : LazyRevealProbe.State Coordinate) (input : HashInput) :
    ∀ slot coordinates context fuel table cache,
      context.state = state →
      runDirectResolvedDetailedFromTable context fuel table
          ((planFirstMissingInputCoordinate input slot coordinates).run cache) =
        pure (.done ⟨context, fuel,
          (firstMissingInputCoordinatePlan state input slot coordinates, cache), table⟩) := by
  intro slot coordinates
  induction coordinates generalizing slot with
  | nil =>
      intro context fuel table cache hstate
      simp [planFirstMissingInputCoordinate, firstMissingInputCoordinatePlan,
        runDirectResolvedDetailedFromTable_pure]
  | cons coordinate remaining ih =>
      intro context fuel table cache hstate
      rw [planFirstMissingInputCoordinate, StateT.run_bind,
        runDirectResolvedDetailedFromTable_bind,
        runDirectResolvedDetailedFromTable_peekCoordinate]
      simp only [pure_bind]
      rw [hstate]
      cases hvalue : state.values coordinate with
      | none =>
          simp [hvalue, firstMissingInputCoordinatePlan,
            runDirectResolvedDetailedFromTable_pure]
      | some output =>
          change runDirectResolvedDetailedFromTable context fuel table
            ((planFirstMissingInputCoordinate input (slot + 1) remaining).run cache) = _
          rw [ih (slot + 1) context fuel table cache hstate]
          simp [firstMissingInputCoordinatePlan, hvalue]

theorem runDirectResolvedDetailed_planLeafInputProbe
    (state : LazyRevealProbe.State Coordinate)
    (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hstate : context.state = state) :
    runDirectResolvedDetailedFromTable context fuel table
        ((planLeafInputProbe input candidate lay tree leafIdx).run cache) =
      pure (.done ⟨context, fuel,
        (leafInputProbePlan state input candidate lay tree leafIdx, cache), table⟩) := by
  rw [planLeafInputProbe, StateT.run_bind,
    runDirectResolvedDetailedFromTable_bind,
    runDirectResolvedDetailedFromTable_peekCoordinate]
  simp only [pure_bind]
  rw [hstate]
  cases hvalue : state.values candidate.coordinate with
  | none =>
      simp [hvalue, leafInputProbePlan, runDirectResolvedDetailedFromTable_pure]
  | some output =>
      change runDirectResolvedDetailedFromTable context fuel table
        ((planFirstMissingInputCoordinate input 0
          ((Position.leaf lay tree leafIdx).children.map Coordinate.position)).run cache) = _
      rw [runDirectResolvedDetailed_planFirstMissingInputCoordinate state input 0
        ((Position.leaf lay tree leafIdx).children.map Coordinate.position)
        context fuel table cache hstate]
      simp [leafInputProbePlan, hvalue]

end SphincsSecurity.Concrete.OtsProbeSimulation
