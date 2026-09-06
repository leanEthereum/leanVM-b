import SphincsSecurity.Proof.JointProbeMaterializedQueryBound
import SphincsSecurity.Proof.JointProbeMaterializedRetained

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] expectedJointMaterializedCharge OtsProbeSimulation.maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 512

theorem expectedJointMaterializedCharge_retained_le_potential
    (adversary : Adversary) (parameter : PublicParameter) (q : Nat) (targets : Finset Position)
    (table : Coordinate → Digest) (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel fuel : Nat)
    (otsTable : OtsSecretIndex → HashOutput) :
    expectedJointMaterializedCharge table ((jointSourceRetained adversary parameter q).run
      (OtsProbeSimulation.emptySplitHashCache, emptySplitHashCache)) state ftsFuel
      (OtsProbeSimulation.ensuredInitialContext targets) fuel otsTable ≤
        (q : ENNReal) * encodingExhaustionTotalPotential ∅ := by
  have hconsistent := (OtsProbeSimulation.ensuredInitialContext_valid targets).valuesConsistent
  have hstarts := OtsProbeSimulation.startTableAgrees_of_deferredCompletable
    (OtsProbeSimulation.ensuredInitialContext_completable targets otsTable)
  unfold jointSourceRetained
  rw [← zero_add (q : ENNReal)]
  apply expectedJointMaterializedCharge_bind_le_potential encodingExhaustionTotalPotential _ _ 0 q
    (jointCachePotentialBound_totalEncoding _ (fun _ _ _ => jointCachePotentialBound_nativeBlock _ _
      (OtsProbeSimulation.resolvedCachePotentialBound_publishedTreeRoot_encoding _)))
    table state ftsFuel (OtsProbeSimulation.ensuredInitialContext targets) fuel otsTable
    (OtsProbeSimulation.emptySplitHashCache, emptySplitHashCache) hconsistent hstarts
  · rw [expectedJointMaterializedCharge_eq_zero_of_probeFree table _
      (jointSourceNativeBlock_probeBound _ 0 OtsProbeSimulation.maskedPublishedTreeRoot_probeFree _) state ftsFuel
      (OtsProbeSimulation.ensuredInitialContext targets) fuel otsTable]
    exact bot_le
  · intro finalState remaining entry hresult
    have hcore := resolvedCore_of_mem_jointRaw table _ state finalState ftsFuel remaining
      (OtsProbeSimulation.ensuredInitialContext targets) fuel otsTable entry hconsistent hstarts hresult
    obtain ⟨native, hnative, _, _, rfl⟩ := mem_support_jointSourceNativeBlock_raw_done
      table state finalState ftsFuel remaining _ (OtsProbeSimulation.ensuredInitialContext targets) fuel otsTable _ entry hresult
    have hempty : prepareNativeCache emptySplitHashCache OtsProbeSimulation.emptySplitHashCache = OtsProbeSimulation.emptySplitHashCache := by
      funext key
      cases key <;> rfl
    dsimp only at hnative
    rw [hempty] at hnative
    apply expectedJointMaterializedCharge_computation_le parameter native.value.1 _ q _ table finalState remaining
      native.context native.remaining native.table (native.value.2, withNativeOrdinaryCache emptySplitHashCache native.value.2)
      hcore.2.1 (hcore.1 ▸ hcore.2.2)
      (Or.inl (OtsProbeSimulation.materializedChainsPublished_of_mem_initializedRoot targets fuel otsTable native hnative))
    rw [isQueryBoundP_map_iff]
    exact OtsProbeSimulation.capOuterHashQueries_hashBound _ q

theorem expectedJointMaterializedCharge_retained_le_inv216
    (adversary : Adversary) (parameter : PublicParameter) (q : Nat) (targets : Finset Position)
    (table : Coordinate → Digest) (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel fuel : Nat)
    (otsTable : OtsSecretIndex → HashOutput) :
    expectedJointMaterializedCharge table ((jointSourceRetained adversary parameter q).run
      (OtsProbeSimulation.emptySplitHashCache, emptySplitHashCache)) state ftsFuel
      (OtsProbeSimulation.ensuredInitialContext targets) fuel otsTable ≤
        (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) := by
  apply (expectedJointMaterializedCharge_retained_le_potential adversary parameter q targets table state ftsFuel fuel otsTable).trans
  rw [div_eq_mul_inv]
  exact mul_le_mul' le_rfl encodingExhaustionTotalPotential_empty_le_inv216

end SphincsSecurity.Concrete.FtsProbeSimulation

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 512

theorem sampledNativeFtsMaterializedProbeRisk_le_inv216 (adversary : Adversary) (q fuel : Nat) :
    sampledNativeFtsMaterializedProbeRisk adversary q fuel ≤ (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) := by
  rw [sampledNativeFtsMaterializedProbeRisk_eq_jointCharge]
  have average_le {α : Type} (computation : ProbComp α) (weight : α → ENNReal) (bound : ENNReal)
      (h : ∀ value, weight value ≤ bound) : (∑' value, Pr[= value | computation] * weight value) ≤ bound := by
    calc
      _ ≤ ∑' value, Pr[= value | computation] * bound := ENNReal.tsum_le_tsum (fun value => mul_le_mul' le_rfl (h value))
      _ ≤ _ := by
        rw [ENNReal.tsum_mul_right]
        exact mul_le_of_le_one_left bot_le tsum_probOutput_le_one
  apply average_le
  intro parameter
  apply average_le
  intro ftsSecret
  apply average_le
  intro otsTable
  exact FtsProbeSimulation.expectedJointMaterializedCharge_retained_le_inv216 adversary parameter q Finset.univ
    (FtsProbeSimulation.curryFtsTableEquiv ftsSecret) AdaptiveRevealProbe.State.empty q fuel otsTable

end SphincsSecurity.Concrete
