import SphincsSecurity.Proof.AdaptiveRevealProbeRawRemaining
import SphincsSecurity.Proof.OtsProbeSourceMaterializedHash
import SphincsSecurity.Proof.JointProbeResolvedOrder
import SphincsSecurity.Proof.JointProbeNativeBlockCost

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def expectedJointMaterializedCharge
    (table : Coordinate → Digest) (computation : OracleComp JointProbeWorld α)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) : ENNReal :=
  OtsProbeSimulation.liveMaterializedProbeAllowance (runJointFtsRaw table computation state ftsFuel) context fuel otsTable

theorem expectedJointMaterializedCharge_eq_finalized
    (table : Coordinate → Digest) (computation : OracleComp JointProbeWorld α)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : OtsProbeSimulation.StartTableAgrees context.state otsTable) :
    expectedJointMaterializedCharge table computation state ftsFuel context fuel otsTable =
      OtsProbeSimulation.liveMaterializedProbeAllowance (runJointFts table computation state ftsFuel) context fuel otsTable := by
  rw [runJointFts_eq_finalize_raw]
  exact (OtsProbeSimulation.liveSourceCharge_map _ _ _ context fuel otsTable hconsistent hstarts).symm

theorem expectedJointMaterializedCharge_bind
    (table : Coordinate → Digest) (left : OracleComp JointProbeWorld α) (next : α → OracleComp JointProbeWorld β)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : OtsProbeSimulation.StartTableAgrees context.state otsTable) :
    expectedJointMaterializedCharge table (left >>= next) state ftsFuel context fuel otsTable =
      expectedJointMaterializedCharge table left state ftsFuel context fuel otsTable +
        ∑' result, Pr[= result | AdaptiveRevealProbe.runRaw table state ftsFuel (runJointResolved left context fuel otsTable)] *
          match result with
          | .stopped _ => 0
          | .done finalState remaining result => match result with
            | none => 0
            | some entry => expectedJointMaterializedCharge table (next entry.value) finalState remaining
                entry.context entry.remaining entry.table := by
  let tailCharge : Option (ResolvedRunResult (AdaptiveRevealProbe.State Coordinate × Nat × α)) → ENNReal
    | none => 0
    | some entry => expectedJointMaterializedCharge table (next entry.value.2.2) entry.value.1 entry.value.2.1
        entry.context entry.remaining entry.table
  unfold expectedJointMaterializedCharge at ⊢
  rw [runJointFtsRaw_bind, OtsProbeSimulation.liveMaterializedProbeAllowance_bind _ _ context fuel otsTable hconsistent hstarts]
  congr 1
  calc
    _ = ∑' result, Pr[= result | flattenRawResolved <$>
        OtsProbeSimulation.runResolvedFromTable context fuel otsTable (runJointFtsRaw table left state ftsFuel)] * tailCharge result := by
      rw [tsum_probOutput_map_mul]
      apply tsum_congr
      intro result
      congr 1
      cases result with
      | none => rfl
      | some entry =>
          cases hvalue : entry.value with
          | stopped hit =>
              simp [flattenRawResolved, tailCharge, hvalue, OtsProbeSimulation.sourceContinuationCharge,
                OtsProbeSimulation.liveSourceCharge]
          | done finalState remaining value =>
              simp [flattenRawResolved, tailCharge, hvalue, expectedJointMaterializedCharge,
                OtsProbeSimulation.sourceContinuationCharge, OtsProbeSimulation.liveMaterializedProbeAllowance]
    _ = ∑' result, Pr[= result | rawJointResolved <$>
        AdaptiveRevealProbe.runRaw table state ftsFuel (runJointResolved left context fuel otsTable)] * tailCharge result := by
      rw [runJointFtsRaw_resolved_commute]
    _ = _ := by
      rw [tsum_probOutput_map_mul]
      apply tsum_congr
      intro result
      congr 1
      cases result with
      | stopped hit => rfl
      | done finalState remaining entry => cases entry <;> rfl

theorem runJointFtsRaw_map
    (table : Coordinate → Digest) (computation : OracleComp JointProbeWorld α) (f : α → β)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) :
    runJointFtsRaw table (f <$> computation) state fuel =
      AdaptiveRevealProbe.RawResult.mapValue f <$> runJointFtsRaw table computation state fuel := by
  rw [map_eq_bind_pure_comp, runJointFtsRaw_bind, map_eq_bind_pure_comp]
  apply bind_congr
  intro result
  cases result <;> rfl

theorem expectedJointMaterializedCharge_map
    (table : Coordinate → Digest) (computation : OracleComp JointProbeWorld α) (f : α → β)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : OtsProbeSimulation.StartTableAgrees context.state otsTable) :
    expectedJointMaterializedCharge table (f <$> computation) state ftsFuel context fuel otsTable =
      expectedJointMaterializedCharge table computation state ftsFuel context fuel otsTable := by
  unfold expectedJointMaterializedCharge OtsProbeSimulation.liveMaterializedProbeAllowance
  rw [runJointFtsRaw_map, OtsProbeSimulation.liveSourceCharge_map _ _ _ context fuel otsTable hconsistent hstarts]

theorem expectedJointMaterializedCharge_eq_zero_of_probeFree
    (table : Coordinate → Digest) (computation : OracleComp JointProbeWorld α)
    (hbound : computation.IsQueryBoundP JointProbeIsProbe 0)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) :
    expectedJointMaterializedCharge table computation state ftsFuel context fuel otsTable = 0 :=
  OtsProbeSimulation.liveMaterializedProbeAllowance_eq_zero_of_probeFree _ context fuel otsTable
    (runJointFtsRaw_probeBound table computation 0 hbound state ftsFuel)

end SphincsSecurity.Concrete.FtsProbeSimulation
