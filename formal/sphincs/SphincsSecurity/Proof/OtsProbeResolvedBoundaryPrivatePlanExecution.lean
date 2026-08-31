import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivatePreparationInterpreter

/-!
# Single-execution planned hash handler

The concrete probing hash handler is factored into its state-neutral planner, execution of the one recorded candidate, and a probe-free suffix. This avoids executing the finite scan twice in the plan-traced game.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

theorem isUncoveredProbe_imp_isProbe (candidates : List Probe)
    (query : (LazyRevealProbe.World Coordinate).Domain) :
    IsUncoveredProbe candidates query → LazyRevealProbe.IsProbe query := by
  cases query <;> simp [IsUncoveredProbe, LazyRevealProbe.IsProbe]

noncomputable def purePlanProbingHashQuery (parameter : PublicParameter)
    (input : HashInput) (state : LazyRevealProbe.State Coordinate) : PlannedHashQuery :=
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

set_option maxRecDepth 100000 in
theorem runDirectResolvedDetailed_planProbingHashQuery
    (parameter : PublicParameter) (input : HashInput)
    (state : LazyRevealProbe.State Coordinate) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hstate : context.state = state) :
    runDirectResolvedDetailedFromTable context fuel table
        ((planProbingHashQuery parameter input).run cache) =
      pure (.done ⟨context, fuel,
        (purePlanProbingHashQuery parameter input state, cache), table⟩) := by
  unfold planProbingHashQuery purePlanProbingHashQuery
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      cases hposition : decodePosition? parameter input with
      | none => simp [runDirectResolvedDetailedFromTable_pure]
      | some position =>
          cases position with
          | leaf lay tree leafIdx =>
              rw [StateT.run_bind,
                runDirectResolvedDetailedFromTable_bind,
                runDirectResolvedDetailed_planLeafInputProbe state input candidate lay tree
                  leafIdx context fuel table cache hstate]
              simp [runDirectResolvedDetailedFromTable_pure]
          | chain | node | ftsLeaf | ftsNode | ftsRoots =>
              simp [runDirectResolvedDetailedFromTable_pure]
  | none =>
      cases hposition : decodePosition? parameter input with
      | none => simp [runDirectResolvedDetailedFromTable_pure]
      | some position =>
          cases position with
          | node lay tree level nodeIdx =>
              rw [StateT.run_bind,
                runDirectResolvedDetailedFromTable_bind,
                runDirectResolvedDetailed_planFirstMissingInputCoordinate state input 0
                  ((Position.node lay tree level nodeIdx).children.map Coordinate.position)
                  context fuel table cache hstate]
              simp [runDirectResolvedDetailedFromTable_pure]
          | chain | leaf | ftsLeaf | ftsNode | ftsRoots =>
              simp [runDirectResolvedDetailedFromTable_pure]

noncomputable def probingHashQueryAfterPlan
    (parameter : PublicParameter) (input : HashInput) (plan : PlannedHashQuery) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) HashOutput :=
  executePlannedHashQuery parameter input plan

theorem probingHashQueryAfterPlan_probeBound
    (parameter : PublicParameter) (input : HashInput) (plan : PlannedHashQuery)
    (candidates : List Probe) (hplanned : ∀ candidate, plan.candidate? = some candidate →
      candidate ∈ candidates) (cache : SplitHashCache) :
    ((probingHashQueryAfterPlan parameter input plan).run cache).IsQueryBoundP
      (IsUncoveredProbe candidates) 0 := by
  unfold probingHashQueryAfterPlan executePlannedHashQuery
  rw [StateT.run_bind]
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
  · cases hopt : plan.candidate? with
    | none => simp [executeCandidate?]
    | some candidate =>
        have hmem := hplanned candidate hopt
        change (LazyRevealProbe.probeQuery candidate.coordinate candidate.candidate).IsQueryBoundP
          (IsUncoveredProbe candidates) 0
        unfold LazyRevealProbe.probeQuery
        rw [OracleComp.isQueryBoundP_query_iff]
        simp [IsUncoveredProbe, hmem]
  · intro result _hresult
    cases plan.action with
    | ordinary =>
        exact OracleComp.IsQueryBoundP.of_imp
          (isUncoveredProbe_imp_isProbe candidates)
          (splitHashQuery_probeFree (.ordinary input) result.2)
    | resolve coordinate =>
        exact OracleComp.IsQueryBoundP.of_imp
          (isUncoveredProbe_imp_isProbe candidates)
          (resolveKnownInput_probeFree parameter coordinate input result.2)

end SphincsSecurity.Concrete.OtsProbeSimulation
