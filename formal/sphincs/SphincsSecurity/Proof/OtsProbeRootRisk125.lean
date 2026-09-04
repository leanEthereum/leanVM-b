import SphincsSecurity.Proof.OtsProbeRootCoupling125

namespace SphincsSecurity.Concrete.OtsProbeSimulation.Range125

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot

set_option linter.constructorNameAsVariable false

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 1000000 in
theorem probEvent_successfulDoomedFirstRootFiber_le_eight_sevenths_mul_production
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
    (hq : q ≤ 2 ^ 125) :
    Pr[fun observed =>
        ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget
          table ordinal target observed |
      observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] ≤
      Pr[fun result ↦ materializedOrdinalSelectionAt target result.2 |
          materializedRootAwareOrdinalProductionExperimentAfterTable ordinal adversary parameter
            ftsSecret target (2 * q) table] *
        ((8 / 7) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  let run := observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table
  let probability := Pr[fun observed =>
      ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget
        table ordinal target observed | run]
  let weight := Pr[fun result ↦ materializedOrdinalSelectionAt target result.2 |
      materializedRootAwareOrdinalProductionExperimentAfterTable ordinal adversary parameter
        ftsSecret target (2 * q) table]
  let epsilon := ((2 ^ digestBits : Nat) : ENNReal)⁻¹
  have hgood :
      Pr[fun result : Option
            (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest ↦
          ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
            table ordinal target result.2 result.1 | do
        let observed ← run
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (observed, rightRoot)] ≤ weight * epsilon := by
    exact probEvent_observedRootComparison_le_production_mul ordinal adversary parameter table
      ftsSecret q target hroot hparent hfuel hbound hq
  have hsplit : probability ≤
      Pr[fun result : Option
            (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest =>
          ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
            table ordinal target result.2 result.1 | do
        let observed ← run
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (observed, rightRoot)] +
      probability *
        ((ordinal : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
    exact probEvent_successfulDoomedFirstRootFiber_le_goodComparison_add_weightedException
      table run ordinal target
  have hfraction :
      (ordinal : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ ≤
        (8 : ENNReal)⁻¹ :=
    ordinal_mul_inv_digest_le_inv_eight ordinal q hordinal hq
  have habsorb : probability ≤ (8 / 7) * (weight * epsilon) := by
    apply le_eight_sevenths_mul_of_le_add_mul_inv_eight probability (weight * epsilon)
    · exact probEvent_le_one
    · apply ne_top_of_le_ne_top (by norm_num : (1 : ENNReal) ≠ ∞)
      calc
        weight * epsilon ≤ 1 * 1 := by
          apply mul_le_mul probEvent_le_one
          · simp [epsilon, digestBits]
          · exact bot_le
          · exact bot_le
        _ = 1 := one_mul 1
    · have hweighted : probability * ((ordinal : ENNReal) * epsilon) ≤
          probability * (8 : ENNReal)⁻¹ := mul_le_mul' le_rfl hfraction
      exact hsplit.trans (add_le_add hgood hweighted)
  change probability ≤ weight * ((8 / 7) * epsilon)
  calc
    probability ≤ (8 / 7) * (weight * epsilon) := habsorb
    _ = weight * ((8 / 7) * epsilon) := by ac_rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 1000000 in
theorem probEvent_successfulDoomedFirstRootFiber_le_commonDetailedFiber
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
    (hq : q ≤ 2 ^ 125) :
    Pr[fun observed =>
        ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget
          table ordinal target observed |
      observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] ≤
      Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        permissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter ftsSecret
          (2 * q) table] *
        ((8 / 7) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  calc
    _ ≤ Pr[fun result => materializedOrdinalSelectionAt target result.2 |
          materializedRootAwareOrdinalProductionExperimentAfterTable ordinal adversary parameter
            ftsSecret target (2 * q) table] *
          ((8 / 7) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) :=
      probEvent_successfulDoomedFirstRootFiber_le_eight_sevenths_mul_production ordinal adversary parameter
        table ftsSecret q target hroot hparent hordinal hfuel hbound hq
    _ ≤ _ := by
      gcongr
      exact probEvent_materializedRootAwareProduction_le_commonDetailedFiber ordinal adversary
        parameter ftsSecret target hroot hparent (2 * q) table

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 1000000 in
theorem probEvent_successfulDoomedFirstRoot_le_commonDetailed
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
      (8 / 7) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  apply probEvent_le_of_common_position_fibers
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

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 1000000 in
theorem probEvent_sampledDiagnostic_successfulDoomed_firstRoot_le
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (q : Nat) (hordinal : ordinal < q)
    (hfuel : 2 * q < Fintype.card Digest)
    (hbound : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 125) :
    Pr[fun outcome => outcome.SuccessfulDoomed ∧
          outcome.FirstExistingHiddenRootHitAt ordinal |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] ≤
      (8 / 7) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  apply probEvent_sampledDiagnostic_successfulDoomed_firstExistingHiddenRootHitAt_le_of_forall
  intro table
  exact probEvent_successfulDoomedFirstRoot_le_commonDetailed ordinal adversary parameter table
    ftsSecret q hordinal hfuel (hbound table) hq

end SphincsSecurity.Concrete.OtsProbeSimulation.Range125
