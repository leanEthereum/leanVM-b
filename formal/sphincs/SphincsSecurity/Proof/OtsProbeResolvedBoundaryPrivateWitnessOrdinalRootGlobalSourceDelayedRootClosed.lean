import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSourceDelayedRootEndpoint
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSourceStructuralParentTop

/-!
# Closed delayed-root bound

Source snapshots retain the structural-parent fact supplied by the root-aware candidate planner.
Consequently every nonempty delayed root fiber satisfies the hypotheses of the tagged root exchange.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local irreducible] maskedPublishedTreeRoot

theorem root_and_parent_of_delayedRootGoodForComparisonAt
    {adversary : Adversary} {parameter : PublicParameter}
    {table : OtsSecretIndex → HashOutput}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {fuel ordinal : Nat} {target : Position} {rightRoot : Digest}
    {source : PrivateWitnessSnapshotOutput}
    (hsource : source ∈ support
      (granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret fuel))
    (hgood : DelayedRootGoodForComparisonAt source ordinal target rightRoot) :
    IsLayerRoot target ∧ ∃ parent, Position.parentOf target = some parent := by
  obtain ⟨_witness, selected, _hwitness, _hordinal, _hfirst, _hselection, hactual, hroot⟩ :=
    delayedOrdinal_goodForActualRoot hgood.1 hgood.2.1
  have hparents :=
    snapshotsHaveStructuralParents_of_mem_granularAllCanonicalPrivateWitnessSnapshot adversary
      parameter table ftsSecret fuel source hsource
  have hcandidateParent :
      (privateOrdinalSelectionOfSnapshot selected).candidate.HasStructuralParent := by
    rw [privateOrdinalSelectionOfSnapshot_candidate]
    exact candidateHasStructuralParent_get hparents selected.val (by
      simp only [List.length_map]
      exact selected.isLt)
  refine ⟨hroot, ?_⟩
  rw [hactual.1] at hcandidateParent
  simpa [Probe.HasStructuralParent] using hcandidateParent

theorem root_and_parent_of_existing_delayedRootGoodComparisonFiber
    {adversary : Adversary} {parameter : PublicParameter}
    {table : OtsSecretIndex → HashOutput}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {fuel ordinal : Nat} {target : Position}
    (hexists : ∃ result ∈ support (do
        let source ← granularAllCanonicalPrivateWitnessSnapshot adversary parameter table
          ftsSecret fuel
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (source, rightRoot)),
      DelayedRootGoodForComparisonAt result.1 ordinal target result.2) :
    IsLayerRoot target ∧ ∃ parent, Position.parentOf target = some parent := by
  obtain ⟨result, hresult, hgood⟩ := hexists
  rw [mem_support_bind_iff] at hresult
  obtain ⟨source, hsource, hresult⟩ := hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨rightRoot, _hrightRoot, hreturn⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hreturn
  subst result
  exact root_and_parent_of_delayedRootGoodForComparisonAt hsource hgood

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem probEvent_delayedGoodComparison_le_common_mul_allTargets
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (target : Position) :
    Pr[fun result : PrivateWitnessSnapshotOutput × Digest =>
        DelayedRootGoodForComparisonAt result.1 ordinal target result.2 | do
      let source ← granularAllCanonicalPrivateWitnessSnapshot adversary parameter table
        ftsSecret fuel
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (source, rightRoot)] ≤
      Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
          ftsSecret fuel table] * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  by_cases hexists : ∃ result ∈ support (do
      let source ← granularAllCanonicalPrivateWitnessSnapshot adversary parameter table
        ftsSecret fuel
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (source, rightRoot)),
    DelayedRootGoodForComparisonAt result.1 ordinal target result.2
  · have hstructure := root_and_parent_of_existing_delayedRootGoodComparisonFiber hexists
    exact probEvent_delayedGoodComparison_le_common_mul ordinal adversary parameter table
      ftsSecret fuel target hstructure.1 hstructure.2
  · simp only [not_exists, not_and] at hexists
    have hzero : Pr[fun result : PrivateWitnessSnapshotOutput × Digest =>
        DelayedRootGoodForComparisonAt result.1 ordinal target result.2 | do
      let source ← granularAllCanonicalPrivateWitnessSnapshot adversary parameter table
        ftsSecret fuel
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (source, rightRoot)] = 0 := by
      apply probEvent_eq_zero
      intro result hsupport hevent
      exact hexists result hsupport hevent
    rw [hzero]
    exact zero_le

theorem probEvent_sampledCanonical_delayed_le_two_mul_closed
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q)
    (hq : q ≤ 2 ^ securityBits) :
    Pr[WitnessFirstUsesSomeDelayedLayerRootSnapshot |
        sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] ≤
      (2 * q : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  apply probEvent_sampledCanonical_delayed_le_two_mul adversary parameter ftsSecret q hbound hq
  intro ordinal table target
  exact probEvent_delayedGoodComparison_le_common_mul_allTargets ordinal.val adversary parameter
    table ftsSecret q target

end SphincsSecurity.Concrete.OtsProbeSimulation
