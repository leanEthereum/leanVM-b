import SphincsSecurity.Proof.FtsProbeJointChargeObserver

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def jointOtsQueryCharge (parameter : PublicParameter) : JointQueryCharge
  | .inl (.inr input), context, cache, _, ftsCache =>
      OtsProbeSimulation.expectedErasedHistoryProbeCost
        ((OtsProbeSimulation.probingHashQuery parameter input).run (prepareNativeCache ftsCache cache)) context
  | _, _, _, _, _ => 0

noncomputable def jointFtsQueryCharge (parameter : PublicParameter) : JointQueryCharge
  | .inl (.inr input), _, _, state, _ => jointHashProbeCharge parameter input state
  | _, _, _, _, _ => 0

theorem jointOts_add_fts_queryCharge_le_one (parameter : PublicParameter)
    (input : (OracleWorld + SigningSpec).Domain) (context : OtsProbeSimulation.DeferredContext)
    (cache : OtsProbeSimulation.SplitHashCache) (state : AdaptiveRevealProbe.State Coordinate) (ftsCache : SplitHashCache) :
    jointOtsQueryCharge parameter input context cache state ftsCache + jointFtsQueryCharge parameter input context cache state ftsCache ≤
      if OtsProbeSimulation.IsOuterHash input then 1 else 0 := by
  cases input with
  | inl input =>
      cases input with
      | inl n => simp [jointOtsQueryCharge, jointFtsQueryCharge, OtsProbeSimulation.IsOuterHash]
      | inr input => exact joint_erased_probe_step_cost_le_one parameter input context (prepareNativeCache ftsCache cache) state
  | inr message => simp [jointOtsQueryCharge, jointFtsQueryCharge, OtsProbeSimulation.IsOuterHash]

theorem expectedJointOts_add_fts_charge_le_outerBound
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (hbound : computation.IsQueryBoundP OtsProbeSimulation.IsOuterHash q)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache) :
    expectedJointQueryCharge parameter root table (jointOtsQueryCharge parameter) computation state ftsFuel context fuel history cache ftsCache +
      expectedJointQueryCharge parameter root table (jointFtsQueryCharge parameter) computation state ftsFuel context fuel history cache ftsCache ≤ q := by
  rw [← expectedJointQueryCharge_add]
  exact expectedJointQueryCharge_le_outerBound parameter root table _ (jointOts_add_fts_queryCharge_le_one parameter)
    computation q hbound state ftsFuel context fuel history cache ftsCache

theorem expectedJointOts_add_fts_charge_capped
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache) :
    expectedJointQueryCharge parameter root table (jointOtsQueryCharge parameter)
        (OtsProbeSimulation.capOuterHashQueries computation q) state ftsFuel context fuel history cache ftsCache +
      expectedJointQueryCharge parameter root table (jointFtsQueryCharge parameter)
        (OtsProbeSimulation.capOuterHashQueries computation q) state ftsFuel context fuel history cache ftsCache ≤ q :=
  expectedJointOts_add_fts_charge_le_outerBound parameter root table _ q
    (OtsProbeSimulation.capOuterHashQueries_hashBound computation q) state ftsFuel context fuel history cache ftsCache

end SphincsSecurity.Concrete.FtsProbeSimulation
