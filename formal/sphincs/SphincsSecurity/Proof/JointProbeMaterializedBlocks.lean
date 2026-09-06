import SphincsSecurity.Proof.JointProbeMaterializedCharge

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expectedJointMaterializedCharge_nativeBlock
    (table : Coordinate → Digest)
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (hconsistent : context.ValuesConsistent) (hstarts : OtsProbeSimulation.StartTableAgrees context.state otsTable) :
    expectedJointMaterializedCharge table ((jointSourceNativeBlock computation).run cache) state ftsFuel context fuel otsTable =
      OtsProbeSimulation.liveMaterializedProbeAllowance (computation.run (prepareNativeCache cache.2 cache.1)) context fuel otsTable := by
  conv_lhs => dsimp only [jointSourceNativeBlock, StateT.run]
  rw [expectedJointMaterializedCharge_map _ _ _ _ _ _ _ _ hconsistent hstarts, expectedJointMaterializedCharge,
    runJointFtsRaw_native]
  exact OtsProbeSimulation.liveSourceCharge_map _ _ _ context fuel otsTable hconsistent hstarts

theorem expectedJointMaterializedCharge_ftsBlock
    (table : Coordinate → Digest)
    (computation : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (hconsistent : context.ValuesConsistent) (hstarts : OtsProbeSimulation.StartTableAgrees context.state otsTable) :
    expectedJointMaterializedCharge table ((jointSourceFtsBlock computation).run cache) state ftsFuel context fuel otsTable = 0 := by
  conv_lhs => dsimp only [jointSourceFtsBlock, StateT.run]
  rw [expectedJointMaterializedCharge_map _ _ _ _ _ _ _ _ hconsistent hstarts]
  exact OtsProbeSimulation.liveMaterializedProbeAllowance_eq_zero_of_probeFree _ context fuel otsTable
    (runJointFtsRaw_fts_probeFree table _ state ftsFuel)

theorem expectedJointMaterializedCharge_hashQuery
    (table : Coordinate → Digest) (parameter : PublicParameter) (input : HashInput)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (hconsistent : context.ValuesConsistent) (hstarts : OtsProbeSimulation.StartTableAgrees context.state otsTable) :
    expectedJointMaterializedCharge table ((jointSourceHashQuery parameter input).run cache) state ftsFuel context fuel otsTable =
      if decodeProbe? parameter input = none ∧ OtsProbeSimulation.DeferredCompletable otsTable context then
        OtsProbeSimulation.materializedCandidateAllowance otsTable context
          (OtsProbeSimulation.purePlanProbingHashQuery parameter input context.state).candidate?
      else 0 := by
  unfold jointSourceHashQuery
  cases decodeProbe? parameter input with
  | none =>
      rw [expectedJointMaterializedCharge_nativeBlock _ _ _ _ _ _ _ _ hconsistent hstarts,
        OtsProbeSimulation.materializedAllowance_probingHashQuery parameter input _ context fuel otsTable hconsistent hstarts]
      simp
  | some candidate =>
      rw [expectedJointMaterializedCharge_ftsBlock _ _ _ _ _ _ _ _ hconsistent hstarts]
      simp

theorem expectedJointMaterializedCharge_hashQuery_eq_zero_of_chainsPublished
    (table : Coordinate → Digest) (parameter : PublicParameter) (input : HashInput)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (hconsistent : context.ValuesConsistent) (hstarts : OtsProbeSimulation.StartTableAgrees context.state otsTable)
    (hpublic : OtsProbeSimulation.MaterializedChainsPublished context) :
    expectedJointMaterializedCharge table ((jointSourceHashQuery parameter input).run cache) state ftsFuel context fuel otsTable = 0 := by
  rw [expectedJointMaterializedCharge_hashQuery _ _ _ _ _ _ _ _ _ hconsistent hstarts,
    OtsProbeSimulation.materializedCandidateAllowance_plan_eq_zero_of_chainsPublished parameter input otsTable context hpublic]
  simp

theorem expectedJointMaterializedCharge_sign
    (table : Coordinate → Digest) (parameter : PublicParameter) (root : Digest) (message : Message)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache) :
    expectedJointMaterializedCharge table ((jointSourceSign parameter root message).run cache) state ftsFuel context fuel otsTable = 0 :=
  expectedJointMaterializedCharge_eq_zero_of_probeFree table _ (jointSourceSign_probeFree parameter root message cache)
    state ftsFuel context fuel otsTable

theorem expectedJointMaterializedCharge_outerQuery_eq_zero_of_chainsPublished
    (table : Coordinate → Digest) (parameter : PublicParameter) (root : Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (hconsistent : context.ValuesConsistent) (hstarts : OtsProbeSimulation.StartTableAgrees context.state otsTable)
    (hpublic : OtsProbeSimulation.MaterializedChainsPublished context) :
    expectedJointMaterializedCharge table ((jointSourceOuterQuery parameter root input).run cache) state ftsFuel context fuel otsTable = 0 := by
  cases input with
  | inl input =>
      cases input with
      | inl n =>
          exact expectedJointMaterializedCharge_eq_zero_of_probeFree table _
            (jointSourceNativeBlock_probeBound _ 0 (OtsProbeSimulation.splitUniformImpl_probeFree n) cache)
            state ftsFuel context fuel otsTable
      | inr input =>
          exact expectedJointMaterializedCharge_hashQuery_eq_zero_of_chainsPublished
            table parameter input state ftsFuel context fuel otsTable cache hconsistent hstarts hpublic
  | inr message => exact expectedJointMaterializedCharge_sign table parameter root message state ftsFuel context fuel otsTable cache

theorem expectedJointMaterializedCharge_outerQuery_le_hashIndicator
    (table : Coordinate → Digest) (parameter : PublicParameter) (root : Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (hconsistent : context.ValuesConsistent) (hstarts : OtsProbeSimulation.StartTableAgrees context.state otsTable) :
    expectedJointMaterializedCharge table ((jointSourceOuterQuery parameter root input).run cache) state ftsFuel context fuel otsTable ≤
      if OtsProbeSimulation.IsOuterHash input then 1 else 0 := by
  cases input with
  | inl input =>
      cases input with
      | inl n =>
          have hz := expectedJointMaterializedCharge_eq_zero_of_probeFree table _
            (jointSourceNativeBlock_probeBound _ 0 (OtsProbeSimulation.splitUniformImpl_probeFree n) cache)
            state ftsFuel context fuel otsTable
          change expectedJointMaterializedCharge table ((jointSourceNativeBlock (OtsProbeSimulation.splitUniformImpl n)).run cache)
            state ftsFuel context fuel otsTable ≤ _
          rw [hz]
          exact bot_le
      | inr input =>
          change expectedJointMaterializedCharge table ((jointSourceHashQuery parameter input).run cache)
            state ftsFuel context fuel otsTable ≤ 1
          rw [expectedJointMaterializedCharge_hashQuery _ _ _ _ _ _ _ _ _ hconsistent hstarts]
          split_ifs
          · exact OtsProbeSimulation.materializedCandidateAllowance_le_one otsTable context _
          · exact bot_le
  | inr message =>
      change expectedJointMaterializedCharge table ((jointSourceSign parameter root message).run cache)
        state ftsFuel context fuel otsTable ≤ _
      rw [expectedJointMaterializedCharge_sign]
      exact bot_le

end SphincsSecurity.Concrete.FtsProbeSimulation
