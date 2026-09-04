import SphincsSecurity.Proof.OtsProbeResidual125

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot

def PermissiveCleanFuelRel (leftFuel rightFuel : Nat) :
    Option (CleanRunResult α) → Option (CleanRunResult α) → Prop
  | some left, some right => PermissiveStateRel left.state right.state ∧
      left.remaining = leftFuel ∧ right.remaining = rightFuel ∧
      left.value = right.value ∧ left.table = right.table
  | _, _ => False

set_option maxRecDepth 100000 in
theorem relTriple_runPermissive_probeFree_of_stateRel
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (left right : LazyRevealProbe.State Coordinate) (leftFuel rightFuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hstate : PermissiveStateRel left right)
    (hfree : computation.IsQueryBoundP LazyRevealProbe.IsProbe 0) :
    RelTriple
      (runPermissiveFromTable left leftFuel table computation)
      (runPermissiveFromTable right rightFuel table computation)
      (PermissiveCleanFuelRel leftFuel rightFuel) := by
  induction computation using OracleComp.inductionOn generalizing left right leftFuel rightFuel with
  | pure value =>
      simp [runPermissiveFromTable, PermissiveCleanFuelRel, hstate]
  | query_bind query next ih =>
      rw [runPermissiveFromTable, OracleComp.construct_query_bind,
        runPermissiveFromTable, OracleComp.construct_query_bind]
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hfree
      have hnext : ∀ output, (next output).IsQueryBoundP LazyRevealProbe.IsProbe 0 := by
        intro output
        simpa using hfree.2 output
      have ih := fun output left right leftFuel rightFuel hstate =>
        ih output left right leftFuel rightFuel hstate (hnext output)
      cases query with
      | uniform n =>
          apply relTriple_bind (relTriple_refl (liftM (unifSpec.query n)))
          intro leftOutput rightOutput heq
          subst rightOutput
          exact ih leftOutput left right leftFuel rightFuel hstate
      | hashOutput =>
          apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
          intro leftOutput rightOutput heq
          subst rightOutput
          exact ih leftOutput left right leftFuel rightFuel hstate
      | ensure coordinate =>
          exact ih () (left.ensure coordinate) (right.ensure coordinate) leftFuel rightFuel
            (hstate.ensure coordinate)
      | probe coordinate candidate =>
          simpa [LazyRevealProbe.IsProbe] using hfree.1
      | peek coordinate =>
          have hvalue := congrFun hstate.values coordinate
          simp only
          rw [hvalue]
          exact ih (right.values coordinate) left right leftFuel rightFuel hstate
      | publish coordinate =>
          exact ih () (left.publish coordinate) (right.publish coordinate) leftFuel rightFuel
            (hstate.publish coordinate)
      | reveal coordinate =>
          have hvalue := congrFun hstate.values coordinate
          cases hleft : left.values coordinate with
          | some output =>
              have hright : right.values coordinate = some output := by
                rw [← hvalue]
                exact hleft
              simp only [hleft, hright]
              exact ih output left right leftFuel rightFuel hstate
          | none =>
              have hright : right.values coordinate = none := by
                rw [← hvalue]
                exact hleft
              simp only [hleft, hright]
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  exact ih (table ⟨lay, tree, leafIdx, chainIdx⟩)
                    (left.materialize (.chainStart lay tree leafIdx chainIdx)
                      (table ⟨lay, tree, leafIdx, chainIdx⟩))
                    (right.materialize (.chainStart lay tree leafIdx chainIdx)
                      (table ⟨lay, tree, leafIdx, chainIdx⟩)) leftFuel rightFuel
                    (hstate.materialize (.chainStart lay tree leafIdx chainIdx)
                      (table ⟨lay, tree, leafIdx, chainIdx⟩))
              | position position =>
                  apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
                  intro leftOutput rightOutput heq
                  subst rightOutput
                  exact ih leftOutput (left.materialize (.position position) leftOutput)
                    (right.materialize (.position position) leftOutput) leftFuel rightFuel
                    (hstate.materialize (.position position) leftOutput)

noncomputable def afterOptionalPermissiveProbe
    (state : LazyRevealProbe.State Coordinate) : Option Probe → LazyRevealProbe.State Coordinate
  | none => state
  | some candidate =>
      if candidate.coordinate ∈ state.revealed then state
      else state.addPending candidate.coordinate candidate.candidate

theorem afterOptionalPermissiveProbe_stateRel
    (left right : LazyRevealProbe.State Coordinate) (leftCandidate rightCandidate : Option Probe)
    (hstate : PermissiveStateRel left right) :
    PermissiveStateRel (afterOptionalPermissiveProbe left leftCandidate)
      (afterOptionalPermissiveProbe right rightCandidate) := by
  classical
  cases leftCandidate <;> cases rightCandidate <;>
    simp only [afterOptionalPermissiveProbe] <;>
    (try split_ifs) <;> exact ⟨hstate.values, hstate.revealed⟩

set_option maxRecDepth 100000 in
theorem runPermissive_optionalProbe
    (candidate : Option Probe)
    (computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hfuel : candidate.isSome.toNat ≤ fuel) :
    runPermissiveFromTable state fuel table ((executeCandidate? candidate >>= fun _ => computation).run cache) =
      runPermissiveFromTable (afterOptionalPermissiveProbe state candidate)
        (fuel - candidate.isSome.toNat) table (computation.run cache) := by
  classical
  cases candidate with
  | none => simp [afterOptionalPermissiveProbe]
  | some candidate =>
      cases fuel with
      | zero => simp at hfuel
      | succ remaining =>
          change runPermissiveFromTable state (remaining + 1) table
              (LazyRevealProbe.probeQuery candidate.coordinate candidate.candidate >>= fun _ =>
                computation.run cache) = _
          simp only [LazyRevealProbe.probeQuery, runPermissiveFromTable,
            OracleComp.construct_query_bind, Option.isSome_some, Bool.toNat_true,
            Nat.add_sub_cancel, afterOptionalPermissiveProbe]
          split_ifs <;> rfl

def PermissiveStepRel (leftFuel rightFuel charge : Nat) :
    Option (CleanRunResult α) → Option (CleanRunResult α) → Prop
  | some left, some right => PermissiveStateRel left.state right.state ∧
      leftFuel ≤ left.remaining + charge ∧ rightFuel ≤ right.remaining + charge ∧
      left.value = right.value ∧ left.table = right.table
  | _, _ => False

set_option maxRecDepth 100000 in
theorem relTriple_permissive_optionalProbe
    (leftCandidate rightCandidate : Option Probe)
    (computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (left right : LazyRevealProbe.State Coordinate) (leftFuel rightFuel charge : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hstate : PermissiveStateRel left right)
    (hfree : (computation.run cache).IsQueryBoundP LazyRevealProbe.IsProbe 0)
    (hleftCost : leftCandidate.isSome.toNat ≤ charge)
    (hrightCost : rightCandidate.isSome.toNat ≤ charge)
    (hleftFuel : charge ≤ leftFuel) (hrightFuel : charge ≤ rightFuel) :
    RelTriple
      (runPermissiveFromTable left leftFuel table
        ((executeCandidate? leftCandidate >>= fun _ => computation).run cache))
      (runPermissiveFromTable right rightFuel table
        ((executeCandidate? rightCandidate >>= fun _ => computation).run cache))
      (PermissiveStepRel leftFuel rightFuel charge) := by
  rw [runPermissive_optionalProbe leftCandidate computation left leftFuel table cache
      (hleftCost.trans hleftFuel),
    runPermissive_optionalProbe rightCandidate computation right rightFuel table cache
      (hrightCost.trans hrightFuel)]
  apply relTriple_post_mono
    (relTriple_runPermissive_probeFree_of_stateRel (computation.run cache) _ _ _ _ table
      (afterOptionalPermissiveProbe_stateRel left right leftCandidate rightCandidate hstate) hfree)
  intro leftResult rightResult hresult
  cases leftResult with
  | none => exact False.elim hresult
  | some leftResult =>
      cases rightResult with
      | none => exact False.elim hresult
      | some rightResult =>
          rcases hresult with ⟨hstate, hleft, hright, hvalue, htable⟩
          exact ⟨hstate, by omega, by omega, hvalue, htable⟩

theorem appendPlannedCandidate_length
    (candidates : List Probe) (candidate : Option Probe) :
    (appendPlannedCandidate candidates candidate).length =
      candidates.length + candidate.isSome.toNat := by
  cases candidate <;> simp [appendPlannedCandidate]

set_option maxRecDepth 100000 in
theorem relTriple_delayed_rootAware_permissivePublicAction
    (parameter : PublicParameter) (input : HashInput)
    (left right : LazyRevealProbe.State Coordinate) (leftFuel rightFuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hstate : PermissiveStateRel left right)
    (hleftFuel : 1 ≤ leftFuel) (hrightFuel : 1 ≤ rightFuel) :
    RelTriple
      (runPermissiveFromTable left leftFuel table
        (delayedPermissivePublicAction parameter input table left cache))
      (runPermissiveFromTable right rightFuel table
        (permissiveRootAwarePublicAction parameter input table right cache))
      (PermissiveStepRel leftFuel rightFuel
        (rootAwareCandidateForPlan? parameter input
          (permissiveRootAwarePlan parameter input table left)).isSome.toNat) := by
  classical
  have hvalues := materializedCanonicalContext_values_eq_of_permissiveStateRel table hstate
  have hplan := purePlanProbingHashQuery_eq_of_values_eq hvalues parameter input
  let publicState := (materializedCanonicalContext table left).state
  let plan := permissiveRootAwarePlan parameter input table left
  have hrightAction : permissiveRootAwarePublicAction parameter input table right cache =
      (probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run cache := by
    unfold permissiveRootAwarePublicAction permissiveRootAwarePublicActionWithPlan
      permissiveRootAwarePlan
    rw [← hplan]
    exact congrArg (fun action => action.run cache)
      (probingHashQueryAfterRootAwarePublicPlan_eq_of_values_eq parameter input hvalues.symm _)
  rw [hrightAction]
  have hleftAction : delayedPermissivePublicAction parameter input table left cache =
      ((executeCandidate? plan.candidate? >>= fun _ =>
        probingHashQueryPublicAction parameter input publicState plan.action).run cache) := by
    unfold delayedPermissivePublicAction
    change (probingHashQueryAfterPublicPlan parameter input publicState plan).run cache = _
    unfold probingHashQueryAfterPublicPlan probingHashQueryPublicAction
    rfl
  rw [hleftAction]
  change RelTriple _
    (runPermissiveFromTable right rightFuel table
      ((executeCandidate? (rootAwareCandidateForPlan? parameter input plan) >>= fun _ =>
        probingHashQueryPublicAction parameter input publicState plan.action).run cache)) _
  have hcost : (rootAwareCandidateForPlan? parameter input plan).isSome.toNat ≤ 1 := by
    cases rootAwareCandidateForPlan? parameter input plan <;> simp
  apply relTriple_permissive_optionalProbe _ _ _ left right leftFuel rightFuel _ table cache
    hstate (probingHashQueryPublicAction_probeFree parameter input publicState plan.action cache)
  · unfold rootAwareCandidateForPlan?
    cases plan.candidate? <;> simp
  · exact le_rfl
  · exact hcost.trans hleftFuel
  · exact hcost.trans hrightFuel

end SphincsSecurity.Concrete.OtsProbeSimulation
