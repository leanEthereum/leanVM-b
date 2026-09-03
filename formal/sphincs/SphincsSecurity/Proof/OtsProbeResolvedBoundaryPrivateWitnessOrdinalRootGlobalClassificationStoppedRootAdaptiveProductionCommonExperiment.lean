import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveProductionCommonLift

/-!
# Target-independent detailed root production

The unresolved detailed permissive selector is one common experiment for every structural
position. Its optional position output partitions the successful layer-root selections into
disjoint fibers.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local irreducible] maskedPublishedTreeRoot

noncomputable def permissiveDetailedSelectionAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    ProbComp (Option PermissivePrivateOrdinalSelection) :=
  permissiveDetailedRootAwareOrdinalSelection ordinal parameter rootResult.value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) [] rootResult.state
    rootResult.remaining rootResult.table rootResult.value.2

noncomputable def permissiveDetailedSelectionExperimentAfterTable
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    ProbComp (Option PermissivePrivateOrdinalSelection) := do
  let rootResult ← rootAwareProductionInitialRun fuel table
  match rootResult with
  | none => pure none
  | some result =>
      permissiveDetailedSelectionAfterRootResult ordinal adversary parameter ftsSecret result

theorem probEvent_permissiveDetailedSelection_positionFiber_le_one
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (target : Position) :
    Pr[fun selection =>
        permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
      permissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter ftsSecret fuel
        table] ≤ 1 :=
  probEvent_le_one

theorem probEvent_le_of_common_position_fibers
    (left : ProbComp α) (event : α → Prop) (leftPosition : α → Option Position)
    (common : ProbComp β) (commonPosition : β → Option Position) (epsilon : ENNReal)
    (hnone : ∀ value, event value → leftPosition value ≠ none)
    (hfiber : ∀ target,
      Pr[fun value => event value ∧ leftPosition value = some target | left] ≤
        Pr[fun value => commonPosition value = some target | common] * epsilon) :
    Pr[event | left] ≤ epsilon := by
  rw [probEvent_eq_tsum_classify_fibers left event leftPosition]
  calc
    _ ≤ ∑' target : Option Position,
          Pr[fun value => commonPosition value = target | common] * epsilon := by
      apply ENNReal.tsum_le_tsum
      intro target
      cases target with
      | none =>
          have hzero : Pr[fun value => event value ∧ leftPosition value = none | left] = 0 := by
            apply probEvent_eq_zero
            intro value _hvalue hevent
            exact hnone value hevent.1 hevent.2
          rw [hzero]
          exact zero_le
      | some target => exact hfiber target
    _ = Pr[fun _ : β => True | common] * epsilon := by
      have hsum := probEvent_eq_tsum_classify_fibers common (fun _ : β => True) commonPosition
      simp only [true_and] at hsum
      rw [ENNReal.tsum_mul_right, ← hsum]
    _ ≤ epsilon := by
      simpa using mul_le_of_le_one_left (zero_le epsilon) (probEvent_le_one (oa := common))

end SphincsSecurity.Concrete.OtsProbeSimulation
