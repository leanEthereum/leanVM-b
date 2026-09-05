import SphincsSecurity.Proof.OtsProbeJointExecutionCharge
import SphincsSecurity.Proof.CoupledQueryCost

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

structure JointChargeStateRel (left right : LazyRevealProbe.State Coordinate) : Prop where
  values : left.values = right.values
  revealed : left.revealed = right.revealed
  pending : right.pending ⊆ left.pending

namespace JointChargeStateRel

variable {left right : LazyRevealProbe.State Coordinate} (h : JointChargeStateRel left right)

include h

theorem ensure (coordinate : Coordinate) : JointChargeStateRel (left.ensure coordinate) (right.ensure coordinate) :=
  ⟨h.values, h.revealed, h.pending⟩

theorem publish (coordinate : Coordinate) : JointChargeStateRel (left.publish coordinate) (right.publish coordinate) := by
  exact ⟨h.values, by simp [LazyRevealProbe.State.publish, h.revealed], h.pending⟩

theorem addPending (coordinate : Coordinate) (candidate : Digest) :
    JointChargeStateRel (left.addPending coordinate candidate) (right.addPending coordinate candidate) := by
  exact ⟨h.values, h.revealed, Finset.insert_subset_insert _ h.pending⟩

theorem materialize (coordinate : Coordinate) (output : HashOutput) :
    JointChargeStateRel (left.materialize coordinate output) (right.materialize coordinate output) := by
  refine ⟨by simp [LazyRevealProbe.State.materialize, h.values], h.revealed, ?_⟩
  intro pair hpair
  simp only [LazyRevealProbe.State.materialize, LazyRevealProbe.State.pendingAway, Finset.mem_filter] at hpair ⊢
  exact ⟨h.pending hpair.1, hpair.2⟩

theorem candidateCharge_le (candidate : Option Probe) :
    unmaterializedCandidateCharge left candidate + materializedCandidateCharge left candidate ≤
      unmaterializedCandidateCharge right candidate + materializedCandidateCharge right candidate := by
  cases candidate with
  | none => exact le_refl 0
  | some candidate =>
      rw [candidateCharge_sum_eq, candidateCharge_sum_eq]
      by_cases hright : candidate.coordinate ∈ right.revealed ∨
          (candidate.coordinate, candidate.candidate) ∈ right.pending
      · have hleft : candidate.coordinate ∈ left.revealed ∨
            (candidate.coordinate, candidate.candidate) ∈ left.pending := by
          rcases hright with hrevealed | hpending
          · exact Or.inl (h.revealed ▸ hrevealed)
          · exact Or.inr (h.pending hpending)
        simp [hleft, hright]
      · simp only [hright, ↓reduceIte]
        split_ifs <;> omega

end JointChargeStateRel

def JointChargeOptionRel : Option (CleanRunResult α) → Option (CleanRunResult α) → Prop
  | none, none => True
  | some left, some right => JointChargeStateRel left.state right.state ∧
      left.remaining = right.remaining ∧ left.value = right.value ∧ left.table = right.table
  | _, _ => False

def JointChargedRunRel (left right : Option (CleanRunResult α) × Nat) : Prop :=
  left.2 ≤ right.2 ∧ JointChargeOptionRel left.1 right.1

theorem relTriple_runPermissiveJointChargedFromTable_of_stateRel
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (left right : LazyRevealProbe.State Coordinate) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hstate : JointChargeStateRel left right) :
    RelTriple (runPermissiveJointChargedFromTable left fuel table computation)
      (runPermissiveJointChargedFromTable right fuel table computation) JointChargedRunRel := by
  induction computation using OracleComp.inductionOn generalizing left right fuel with
  | pure value =>
      simp only [runPermissiveJointChargedFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨le_refl 0, hstate, rfl, rfl, rfl⟩
  | query_bind input next ih =>
      rw [runPermissiveJointChargedFromTable, OracleComp.construct_query_bind,
        runPermissiveJointChargedFromTable, OracleComp.construct_query_bind]
      cases input with
      | uniform n =>
          apply relTriple_bind (relTriple_refl (liftM (unifSpec.query n)))
          intro output other heq
          subst other
          exact ih output left right fuel hstate
      | hashOutput =>
          apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
          intro output other heq
          subst other
          exact ih output left right fuel hstate
      | ensure coordinate => exact ih () _ _ fuel (hstate.ensure coordinate)
      | publish coordinate => exact ih () _ _ fuel (hstate.publish coordinate)
      | peek coordinate =>
          have hvalue := congrFun hstate.values coordinate
          simp only
          rw [hvalue]
          exact ih _ left right fuel hstate
      | probe coordinate candidate =>
          cases fuel with
          | zero => exact relTriple_pure_pure ⟨le_refl 0, trivial⟩
          | succ remaining =>
              have hrevealed : coordinate ∈ left.revealed ↔ coordinate ∈ right.revealed := by rw [hstate.revealed]
              by_cases hleft : coordinate ∈ left.revealed
              · have hright := hrevealed.mp hleft
                simp only [hleft, hright, ↓reduceIte]
                exact ih () left right remaining hstate
              · have hright : coordinate ∉ right.revealed := fun hright => hleft (hrevealed.mpr hright)
                simp only [hleft, hright, ↓reduceIte]
                apply relTriple_map
                apply relTriple_post_mono (ih () _ _ remaining (hstate.addPending coordinate candidate))
                intro leftResult rightResult hresult
                exact ⟨Nat.add_le_add hresult.1 (hstate.candidateCharge_le (some ⟨coordinate, candidate⟩)), hresult.2⟩
      | reveal coordinate =>
          have hvalue := congrFun hstate.values coordinate
          cases hleft : left.values coordinate with
          | some output =>
              have hright : right.values coordinate = some output := hvalue.symm.trans hleft
              simp only [hleft, hright]
              exact ih output left right fuel hstate
          | none =>
              have hright : right.values coordinate = none := hvalue.symm.trans hleft
              simp only [hleft, hright]
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  exact ih _ _ _ fuel (hstate.materialize (.chainStart lay tree leafIdx chainIdx) (table ⟨lay, tree, leafIdx, chainIdx⟩))
              | position position =>
                  apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
                  intro output other heq
                  subst other
                  exact ih output _ _ fuel (hstate.materialize (.position position) output)

theorem runPermissiveJointChargedFromTable_expectedCost_le_of_stateRel
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (left right : LazyRevealProbe.State Coordinate) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hstate : JointChargeStateRel left right) :
    (∑' result, Pr[= result | runPermissiveJointChargedFromTable left fuel table computation] *
      (result.2 : ℝ≥0∞)) ≤
    ∑' result, Pr[= result | runPermissiveJointChargedFromTable right fuel table computation] *
      (result.2 : ℝ≥0∞) := by
  simpa using SphincsSecurity.expected_cost_le_of_relTriple
    (relTriple_runPermissiveJointChargedFromTable_of_stateRel computation left right fuel table hstate)
    (fun result => (result.2 : ℝ≥0∞)) (fun result => (result.2 : ℝ≥0∞)) (fun _ => 0)
    (fun _ _ hresult => by simpa using (Nat.cast_le.mpr hresult.1 : (_ : ℝ≥0∞) ≤ _))

theorem jointChargeStateRel_preload_materialize
    (target : Position) (output : HashOutput) (state : LazyRevealProbe.State Coordinate) :
    JointChargeStateRel (preloadPositionValue target output state)
      (state.materialize (.position target) output) := by
  refine ⟨rfl, rfl, ?_⟩
  exact Finset.filter_subset _ _

theorem runPermissiveJointChargedFromTable_preload_expectedCost_le_materialize
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (target : Position) (output : HashOutput) (state : LazyRevealProbe.State Coordinate)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    (∑' result, Pr[= result | runPermissiveJointChargedFromTable
      (preloadPositionValue target output state) fuel table computation] * (result.2 : ℝ≥0∞)) ≤
    ∑' result, Pr[= result | runPermissiveJointChargedFromTable
      (state.materialize (.position target) output) fuel table computation] * (result.2 : ℝ≥0∞) :=
  runPermissiveJointChargedFromTable_expectedCost_le_of_stateRel computation _ _ fuel table
    (jointChargeStateRel_preload_materialize target output state)

end SphincsSecurity.Concrete.OtsProbeSimulation
