import SphincsSecurity.Proof.OtsProbeJointBound125

namespace SphincsSecurity.Concrete.OtsProbeSimulation.Range125

open OracleComp OracleSpec ENNReal

attribute [local irreducible] maskedPublishedTreeRoot
set_option linter.constructorNameAsVariable false

/-- Keep the selected-position mass when summing the disjoint target fibers. -/
theorem probEvent_le_common_selected_mass
    (left : ProbComp α) (event : α → Prop) (leftPosition : α → Option Position)
    (common : ProbComp β) (commonPosition : β → Option Position) (epsilon : ENNReal)
    (hnone : ∀ value, event value → leftPosition value ≠ none)
    (hfiber : ∀ target,
      Pr[fun value => event value ∧ leftPosition value = some target | left] ≤
        Pr[fun value => commonPosition value = some target | common] * epsilon) :
    Pr[event | left] ≤
      Pr[fun value => (commonPosition value).isSome = true | common] * epsilon := by
  rw [probEvent_eq_tsum_classify_fibers left event leftPosition]
  calc
    _ ≤ ∑' target : Option Position,
        Pr[fun value => (commonPosition value).isSome = true ∧
          commonPosition value = target | common] * epsilon := by
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
      | some target =>
          have heq : Pr[fun value => (commonPosition value).isSome = true ∧
                commonPosition value = some target | common] =
              Pr[fun value => commonPosition value = some target | common] := by
            apply OracleComp.probEvent_congr'
            · intro value _
              constructor
              · exact And.right
              · intro htarget
                exact ⟨by simp [htarget], htarget⟩
            · rfl
          rw [heq]
          exact hfiber target
    _ = _ := by
      rw [ENNReal.tsum_mul_right, ← probEvent_eq_tsum_classify_fibers]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_successfulDoomedFirstRoot_le_selected_mass
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (q : Nat) (hordinal : ordinal < q)
    (hfuel : 2 * q < Fintype.card Digest)
    (hbound : ∀ root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 125) :
    Pr[ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt table ordinal |
      observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] ≤
      Pr[fun selection =>
        (permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection).isSome = true |
        permissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter ftsSecret
          (2 * q) table] * ((8 / 7) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  apply probEvent_le_common_selected_mass
    (leftPosition := observedFirstLayerRootPosition? ordinal)
    (common := permissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
      ftsSecret (2 * q) table)
    (commonPosition := permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?)
  · intro observed hevent hnone
    exact not_successfulDoomedFirstRoot_of_position_eq_none hnone hevent
  · intro target
    by_cases hexists : ∃ observed ∈ support
        (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table),
        ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt table ordinal observed ∧
          observedFirstLayerRootPosition? ordinal observed = some target
    · have hstructure :=
        root_and_parent_of_existing_successfulDoomedFirstRootFiber hexists
      simpa [ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget] using
        probEvent_successfulDoomedFirstRootFiber_le_commonDetailedFiber ordinal adversary
          parameter table ftsSecret q target hstructure.1 hstructure.2 hordinal hfuel hbound hq
    · simp only [not_exists, not_and] at hexists
      have hzero : Pr[fun observed =>
          ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt
              table ordinal observed ∧
            observedFirstLayerRootPosition? ordinal observed = some target |
          observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] =
          0 := by
        apply probEvent_eq_zero
        intro observed hsupport hevent
        exact hexists observed hsupport hevent.1 hevent.2
      rw [hzero]
      exact zero_le


set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_granularAllCanonical_delayedOrdinal_le_selected_mass
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hordinal : ordinal < q) (hq : q ≤ 2 ^ 125) :
    Pr[WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal |
        granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q] ≤
      Pr[fun selection =>
        (permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection).isSome = true |
        delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
          ftsSecret q table] * ((8 / 7) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  apply probEvent_le_common_selected_mass
    (leftPosition := delayedSnapshotLayerRootPosition? ordinal)
    (common := delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
      ftsSecret q table)
    (commonPosition := permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?)
  · intro output hdelayed
    obtain ⟨target, htarget⟩ :=
      delayedSnapshotLayerRootPosition?_eq_some_of_delayed hdelayed
    rw [htarget]
    simp
  · intro target
    exact probEvent_delayedRootFiber_le_eight_sevenths_mul_common
      (granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q)
      (delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
        ftsSecret q table)
      ordinal q target hordinal hq (probEvent_delayedGoodComparison_le_common_mul_allTargets ordinal adversary parameter
        table ftsSecret q target)


end SphincsSecurity.Concrete.OtsProbeSimulation.Range125
