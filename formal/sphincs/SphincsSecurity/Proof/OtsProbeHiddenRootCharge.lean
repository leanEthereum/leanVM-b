import SphincsSecurity.Proof.OtsProbeResidualCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local irreducible] maskedPublishedTreeRoot

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 1000000 in
theorem probEvent_successfulDoomedFirstRootFiber_le_productionCharge126
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (q : Nat) (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (hordinal : ordinal < q)
    (hfuel : 2 * q < Fintype.card Digest)
    (hbound : ∀ root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 126) :
    Pr[fun observed =>
        ObservedCleanRunOption.SuccessfulFirstRootHitAtTarget
          table ordinal target observed |
      observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] ≤
      Pr[fun result ↦ materializedOrdinalSelectionAt target result.2 |
          materializedRootAwareOrdinalProductionExperimentAfterTable ordinal adversary parameter
            ftsSecret target (2 * q) table] *
        ((4 / 3) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  let run := observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table
  let probability := Pr[fun observed =>
      ObservedCleanRunOption.SuccessfulFirstRootHitAtTarget
        table ordinal target observed | run]
  let weight := Pr[fun result ↦ materializedOrdinalSelectionAt target result.2 |
      materializedRootAwareOrdinalProductionExperimentAfterTable ordinal adversary parameter
        ftsSecret target (2 * q) table]
  let epsilon := ((2 ^ digestBits : Nat) : ENNReal)⁻¹
  have hgood :
      Pr[fun result : Option
            (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest ↦
          ObservedCleanRunOption.SuccessfulFirstRootGoodForComparisonAt
            table ordinal target result.2 result.1 | do
        let observed ← run
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (observed, rightRoot)] ≤ weight * epsilon := by
    exact Range125.probEvent_observedRootComparison_le_production_mul ordinal adversary parameter table
      ftsSecret q target hroot hparent hfuel hbound hq
  have hsplit : probability ≤
      Pr[fun result : Option
            (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest =>
          ObservedCleanRunOption.SuccessfulFirstRootGoodForComparisonAt
            table ordinal target result.2 result.1 | do
        let observed ← run
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (observed, rightRoot)] +
      probability *
        ((ordinal : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
    exact probEvent_successfulDoomedFirstRootFiber_le_goodComparison_add_weightedException
      table run ordinal target
  have hcoefficient : ((ordinal : ℝ≥0∞) * epsilon) * (4 / 3 : ℝ≥0∞) + 1 ≤ 4 / 3 := by
    apply le_trans _ (rootBudget_four_thirds hq)
    dsimp only [epsilon]
    gcongr
  have habsorb : probability ≤ (4 / 3) * (weight * epsilon) := by
    have hweight : weight ≠ ∞ := ne_top_of_le_ne_top (by norm_num) probEvent_le_one
    have hepsilon : epsilon ≠ ∞ := by dsimp [epsilon]; norm_num [digestBits]
    apply le_mul_of_le_add_self_mul probability (weight * epsilon) ((ordinal : ℝ≥0∞) * epsilon)
      (4 / 3) probEvent_le_one
      (by finiteness) (by finiteness) (by finiteness) hcoefficient
    exact hsplit.trans (add_le_add hgood le_rfl)
  change probability ≤ weight * ((4 / 3) * epsilon)
  calc
    probability ≤ (4 / 3) * (weight * epsilon) := habsorb
    _ = weight * ((4 / 3) * epsilon) := by ac_rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 1000000 in
theorem probEvent_successfulDoomedFirstRootFiber_le_commonCharge126
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (q : Nat) (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (hordinal : ordinal < q)
    (hfuel : 2 * q < Fintype.card Digest)
    (hbound : ∀ root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 126) :
    Pr[fun observed =>
        ObservedCleanRunOption.SuccessfulFirstRootHitAtTarget
          table ordinal target observed |
      observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] ≤
      Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        permissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter ftsSecret
          (2 * q) table] *
        ((4 / 3) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  calc
    _ ≤ Pr[fun result => materializedOrdinalSelectionAt target result.2 |
          materializedRootAwareOrdinalProductionExperimentAfterTable ordinal adversary parameter
            ftsSecret target (2 * q) table] *
          ((4 / 3) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) :=
      probEvent_successfulDoomedFirstRootFiber_le_productionCharge126 ordinal adversary parameter
        table ftsSecret q target hroot hparent hordinal hfuel hbound hq
    _ ≤ _ := by
      gcongr
      exact probEvent_materializedRootAwareProduction_le_commonDetailedFiber ordinal adversary
        parameter ftsSecret target hroot hparent (2 * q) table


theorem probEvent_successfulDoomedFirstRoot_le_selectedCharge126
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
    (hq : q ≤ 2 ^ 126) :
    Pr[ObservedCleanRunOption.SuccessfulFirstExistingHiddenRootHitAt table ordinal |
      observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] ≤
      Pr[fun selection =>
        (permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection).isSome = true |
        permissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter ftsSecret
          (2 * q) table] * ((4 / 3) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  apply Range125.probEvent_le_common_selected_mass
    (leftPosition := observedFirstLayerRootPosition? ordinal)
    (common := permissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
      ftsSecret (2 * q) table)
    (commonPosition := permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?)
  · intro observed hevent hnone
    exact not_successfulDoomedFirstRoot_of_position_eq_none hnone hevent
  · intro target
    by_cases hexists : ∃ observed ∈ support
        (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table),
        ObservedCleanRunOption.SuccessfulFirstExistingHiddenRootHitAt table ordinal observed ∧
          observedFirstLayerRootPosition? ordinal observed = some target
    · have hstructure :=
        root_and_parent_of_existing_successfulDoomedFirstRootFiber hexists
      simpa [ObservedCleanRunOption.SuccessfulFirstRootHitAtTarget] using
        probEvent_successfulDoomedFirstRootFiber_le_commonCharge126 ordinal adversary
          parameter table ftsSecret q target hstructure.1 hstructure.2 hordinal hfuel hbound hq
    · simp only [not_exists, not_and] at hexists
      have hzero : Pr[fun observed =>
          ObservedCleanRunOption.SuccessfulFirstExistingHiddenRootHitAt
              table ordinal observed ∧
            observedFirstLayerRootPosition? ordinal observed = some target |
          observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] =
          0 := by
        apply probEvent_eq_zero
        intro observed hsupport hevent
        exact hexists observed hsupport hevent.1 hevent.2
      rw [hzero]
      exact zero_le



end SphincsSecurity.Concrete.OtsProbeSimulation
