import SphincsSecurity.Proof.OtsProbeSelectionTransport125

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot

def PermissiveSelectionNonRoot : Option PermissivePrivateOrdinalSelection → Prop
  | none => False
  | some selection => ¬selection.candidate.IsLayerRoot

set_option maxRecDepth 100000 in
theorem probEvent_canonicalNonRootSelection_le_delayedCommon
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[PrivateOrdinalSelectionNonRoot |
      granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter table ftsSecret
        fuel] ≤
    Pr[PermissiveSelectionNonRoot |
      delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
        ftsSecret fuel table] := by
  apply probEvent_le_of_relTriple
    (relTriple_granularAllCanonicalPrivateOrdinalSelection_preserved ordinal adversary parameter
      table ftsSecret fuel)
  intro left right hrelation hnonRoot
  cases left with
  | none => exact False.elim hnonRoot
  | some left =>
      cases right with
      | none => exact False.elim hrelation
      | some right =>
          change ¬right.candidate.IsLayerRoot
          change left.candidate = right.candidate at hrelation
          rwa [← hrelation]

theorem rootSelection_nonRootSelection_mass_le_one
    (common : ProbComp (Option PermissivePrivateOrdinalSelection)) :
    Pr[fun selection =>
      (permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection).isSome = true |
      common] + Pr[PermissiveSelectionNonRoot | common] ≤ 1 := by
  classical
  have hdisjoint : ∀ selection,
      (permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection).isSome = true →
      ¬PermissiveSelectionNonRoot selection := by
    intro selection hroot hnonRoot
    obtain ⟨target, htarget⟩ := Option.isSome_iff_exists.mp hroot
    obtain ⟨selected, rfl, hcandidate, _⟩ :=
      (permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?_eq_some_iff
        target selection).mp htarget
    exact hnonRoot ⟨target, (candidateLayerRootPosition?_eq_some_iff _ _).mp hcandidate⟩
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  apply le_trans (b := ∑' selection, Pr[= selection | common]) _ tsum_probOutput_le_one
  apply ENNReal.tsum_le_tsum
  intro selection
  by_cases hroot :
      (permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection).isSome = true
  · simp [hroot, hdisjoint selection hroot]
  · by_cases hnonRoot : PermissiveSelectionNonRoot selection
    · simp [hroot, hnonRoot]
    · simp [hroot, hnonRoot]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_granularAllCanonicalPlan_firstUsesNonRootOrdinal_le_selected_mass
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[WitnessFirstUsesNonLayerRootOrdinal ordinal |
        granularAllCanonicalPrivateWitnessPlan adversary parameter table ftsSecret fuel] ≤
      Pr[PrivateOrdinalSelectionNonRoot |
        granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter table ftsSecret
          fuel] * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ ≤ Pr[fun hit : Bool => hit = true |
        granularAllCanonicalPrivateOrdinalNonRootRisk ordinal adversary parameter table ftsSecret
          fuel] := by
      unfold granularAllCanonicalPrivateWitnessPlan
        granularAllCanonicalPrivateOrdinalNonRootRisk
      apply probEvent_runDirectWitnessPlanFirstUsesNonRootOrdinal_le_risk ordinal _ _ []
        emptyWitnessDeferredContext fuel table
        (maskedPublishedTreeRoot.run emptySplitHashCache) (by simp)
      intro result hresult
      apply probEvent_canonicalizeWitnessPlanFirstUsesNonRootOrdinal_le_risk table ordinal _ _
        result.context result.remaining result.value [] (by simp)
      dsimp only
      intro _hprivate hpublished _hcompletable
      have hdetailed : DirectDetailedResult.done result ∈ support
          (runDirectResolvedDetailedFromTable emptyWitnessDeferredContext fuel table
            (maskedPublishedTreeRoot.run emptySplitHashCache)) := by
        rw [← map_erase_runDirectResolvedWitnessFromTable
          (maskedPublishedTreeRoot.run emptySplitHashCache) emptyWitnessDeferredContext fuel table,
          support_map]
        exact ⟨DirectWitnessResult.done result, hresult, rfl⟩
      have hcore := resolvedCore_of_done_runDirectResolvedDetailedFromTable
        (maskedPublishedTreeRoot.run emptySplitHashCache) emptyWitnessDeferredContext fuel table
        result DeferredContext.valid_empty.valuesConsistent (startTableAgrees_empty table) hdetailed
      exact probEvent_granularDetailedRetainedRestWitnessFirstUsesNonRootOrdinal_le_nonRootRisk
        adversary parameter table ftsSecret ordinal
        (canonicalizeMaterializedValues table result.context) result.remaining result.value []
        (by simp) (canonicalizeMaterializedValues_valuesConsistent table result.context hcore.2.1)
        (canonicalizeMaterializedValues_startTableAgrees table result.context)
        hpublished.to_canonicalizedMaterializedValues
    _ ≤ _ := probEvent_granularNonRootRisk_le_selected_mass ordinal adversary
      parameter table ftsSecret fuel

set_option maxRecDepth 100000 in
theorem probEvent_granularNonRootOrdinal_le_common_mass
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[fun output => WitnessFirstUsesNonLayerRootOrdinal ordinal
        (erasePrivateWitnessSnapshotOutput output) |
      granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret fuel] ≤
    Pr[PermissiveSelectionNonRoot |
      delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
        ftsSecret fuel table] * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  have hprojection :
      Pr[fun output => WitnessFirstUsesNonLayerRootOrdinal ordinal
          (erasePrivateWitnessSnapshotOutput output) |
        granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret fuel] =
      Pr[WitnessFirstUsesNonLayerRootOrdinal ordinal |
        granularAllCanonicalPrivateWitnessPlan adversary parameter table ftsSecret fuel] := by
    rw [← map_erase_granularAllCanonicalPrivateWitnessSnapshot, probEvent_map]
    rfl
  rw [hprojection]
  exact (probEvent_granularAllCanonicalPlan_firstUsesNonRootOrdinal_le_selected_mass ordinal
    adversary parameter table ftsSecret fuel).trans
    (mul_le_mul' (probEvent_canonicalNonRootSelection_le_delayedCommon ordinal adversary parameter
      table ftsSecret fuel) le_rfl)

namespace Range125

set_option maxRecDepth 100000 in
theorem probEvent_granularResidualOrdinal_pair_le_eight_sevenths
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hordinal : ordinal < q) (hq : q ≤ 2 ^ 125) :
    Pr[WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal |
      granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q] +
    Pr[fun output => WitnessFirstUsesNonLayerRootOrdinal ordinal
        (erasePrivateWitnessSnapshotOutput output) |
      granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q] ≤
    (8 / 7 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  let common := delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
    ftsSecret q table
  let rootMass := Pr[fun selection =>
    (permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection).isSome = true | common]
  let nonRootMass := Pr[PermissiveSelectionNonRoot | common]
  let epsilon := ((2 ^ digestBits : Nat) : ENNReal)⁻¹
  have hroot := probEvent_granularAllCanonical_delayedOrdinal_le_selected_mass ordinal adversary
    parameter table ftsSecret q hordinal hq
  have hnonRoot := probEvent_granularNonRootOrdinal_le_common_mass ordinal adversary parameter
    table ftsSecret q
  have hcoefficient : epsilon ≤ (8 / 7 : ENNReal) * epsilon := by
    calc
      epsilon = 1 * epsilon := (one_mul _).symm
      _ ≤ _ := mul_le_mul' (by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        norm_num) le_rfl
  calc
    _ ≤ rootMass * ((8 / 7) * epsilon) + nonRootMass * epsilon :=
      add_le_add hroot hnonRoot
    _ ≤ rootMass * ((8 / 7) * epsilon) + nonRootMass * ((8 / 7) * epsilon) :=
      add_le_add le_rfl (mul_le_mul' le_rfl hcoefficient)
    _ = (rootMass + nonRootMass) * ((8 / 7) * epsilon) := (add_mul ..).symm
    _ ≤ 1 * ((8 / 7) * epsilon) :=
      mul_le_mul' (rootSelection_nonRootSelection_mass_le_one common) le_rfl
    _ = _ := one_mul _

set_option maxRecDepth 100000 in
theorem probEvent_sampledResidualOrdinal_pair_le_eight_sevenths
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hordinal : ordinal < q) (hq : q ≤ 2 ^ 125) :
    Pr[WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal |
      sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] +
    Pr[fun output => WitnessFirstUsesNonLayerRootOrdinal ordinal
        (erasePrivateWitnessSnapshotOutput output) |
      sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] ≤
    (8 / 7 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  let epsilon := (8 / 7 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹
  unfold sampledGranularAllCanonicalPrivateWitnessSnapshot
  simp only [probEvent_bind_eq_tsum, ← ENNReal.tsum_add, ← mul_add]
  calc
    _ ≤ ∑' table, Pr[= table | sampleOtsHashTable] * epsilon := by
      apply ENNReal.tsum_le_tsum
      intro table
      exact mul_le_mul' le_rfl
        (probEvent_granularResidualOrdinal_pair_le_eight_sevenths ordinal adversary parameter
          table ftsSecret q hordinal hq)
    _ = (∑' table, Pr[= table | sampleOtsHashTable]) * epsilon := ENNReal.tsum_mul_right
    _ ≤ 1 * epsilon := mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = _ := one_mul _

set_option maxRecDepth 100000 in
theorem probEvent_jointResidual_le_eight_sevenths_mul
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 125) :
    Pr[JointSnapshotResidual |
      sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary parameter ftsSecret q] ≤
    ((8 / 7 : ENNReal) * q) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  rw [probEvent_jointResidual_eq_snapshot]
  apply (probEvent_or_le _ _ _).trans
  calc
    _ ≤ (∑ ordinal : Fin q,
        Pr[WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal.val |
          sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q]) +
      ∑ ordinal : Fin q,
        Pr[fun output => WitnessFirstUsesNonLayerRootOrdinal ordinal.val
            (erasePrivateWitnessSnapshotOutput output) |
          sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] :=
      add_le_add
        (probEvent_sampledCanonical_delayed_le_sum_ordinals adversary parameter ftsSecret q hbound)
        (probEvent_sampledCanonical_nonRoot_le_sum_ordinals adversary parameter ftsSecret q hbound)
    _ = ∑ ordinal : Fin q,
      (Pr[WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal.val |
          sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] +
        Pr[fun output => WitnessFirstUsesNonLayerRootOrdinal ordinal.val
            (erasePrivateWitnessSnapshotOutput output) |
          sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q]) :=
      Finset.sum_add_distrib.symm
    _ ≤ ∑ _ordinal : Fin q,
        (8 / 7 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
      apply Finset.sum_le_sum
      intro ordinal _
      exact probEvent_sampledResidualOrdinal_pair_le_eight_sevenths ordinal.val adversary
        parameter ftsSecret q ordinal.isLt hq
    _ = _ := by simp; ring

set_option maxRecDepth 100000 in
theorem probEvent_jointBoundary_failed_le_thirty_sevenths_mul
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 125) :
    Pr[fun output => output.outcome.failed = true |
        sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary parameter ftsSecret q] ≤
      ((30 / 7 : ENNReal) * q) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  have hfuel : 2 * q < Fintype.card Digest := by
    rw [show Fintype.card Digest = 2 ^ digestBits by simp]
    norm_num [digestBits] at hq ⊢
    omega
  apply (probEvent_sampledJointSnapshot_failed_le_diagnostic_add_residual adversary parameter
    ftsSecret q hbound).trans
  calc
    _ ≤ ((22 / 7 : ENNReal) * q) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
        ((8 / 7 : ENNReal) * q) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
      add_le_add
        (probEvent_sampledDiagnostic_bad_le_twenty_two_sevenths_mul adversary parameter
          ftsSecret q hfuel hbound hq)
        (probEvent_jointResidual_le_eight_sevenths_mul adversary parameter ftsSecret q hbound hq)
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_natCast,
        ENNReal.toReal_inv, ENNReal.toReal_ofNat]
      ring

set_option maxRecDepth 100000 in
theorem probEvent_sampledActualRetained_verifyProbe_le_thirty_sevenths_mul
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 125) :
    Pr[fun result => WinningRetainedVerifyProbeWitness parameter
        (extendStartTable result.1) ftsSecret result.2 |
      sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤
      ((30 / 7 : ENNReal) * q) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
  (probEvent_sampledActualRetained_verifyProbe_le_jointBoundaryFailed adversary parameter
    ftsSecret q).trans
      (probEvent_jointBoundary_failed_le_thirty_sevenths_mul adversary parameter
        ftsSecret q hbound hq)

end Range125
end SphincsSecurity.Concrete.OtsProbeSimulation
