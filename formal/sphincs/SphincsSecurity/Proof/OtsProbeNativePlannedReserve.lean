import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeLiveJointCharge
import SphincsSecurity.Proof.OtsProbeLiveNativeComposition
import SphincsSecurity.Proof.OtsProbeNativeQueryCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem probingHashQueryAfterPlan_probeFree_of_none
    (parameter : PublicParameter) (input : HashInput) (plan : PlannedHashQuery)
    (hnone : plan.candidate? = none) (cache : SplitHashCache) :
    ((probingHashQueryAfterPlan parameter input plan).run cache).IsQueryBoundP LazyRevealProbe.IsProbe 0 := by
  simp only [probingHashQueryAfterPlan, executePlannedHashQuery, hnone, executeCandidate?, pure_bind]
  cases plan.action with
  | ordinary => exact splitHashQuery_probeFree _ cache
  | resolve coordinate => exact resolveKnownInput_probeFree parameter coordinate input cache

theorem expectedResolvedProbeCharge_eq_zero_of_probeFree
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hfree : computation.IsQueryBoundP LazyRevealProbe.IsProbe 0) :
    expectedResolvedQueryCharge nativeProbeQueryCharge computation context fuel table = 0 :=
  le_antisymm (by simpa only [Nat.cast_zero] using
    expectedResolvedProbeCharge_le_probeBound computation 0 context fuel table hfree) zero_le

theorem probingHashQuery_expectedResolvedProbeCharge_eq_zero_of_no_candidate
    (parameter : PublicParameter) (input : HashInput) (context : DeferredContext)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hnone : (purePlanProbingHashQuery parameter input context.state).candidate? = none) :
    expectedResolvedQueryCharge nativeProbeQueryCharge ((probingHashQuery parameter input).run cache)
      context fuel table = 0 := by
  rw [probingHashQuery_eq_plan_then_afterPlan, StateT.run_bind, expectedResolvedQueryCharge_bind,
    expectedResolvedProbeCharge_eq_zero_of_probeFree _ context fuel table
      (planProbingHashQuery_probeFree parameter input cache), zero_add,
    runResolved_planProbingHashQuery parameter input context.state context fuel table cache rfl,
    tsum_probOutput_pure_mul]
  simp only [resolvedContinuationCharge]
  exact expectedResolvedProbeCharge_eq_zero_of_probeFree _ context fuel table
    (probingHashQueryAfterPlan_probeFree_of_none parameter input _ hnone cache)

noncomputable def nativePlannedProbeOuterCharge (parameter : PublicParameter)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext)
    (_fuel : Nat) (_cache : SplitHashCache) : ENNReal :=
  match input with
  | .inl (.inr input) =>
      if (purePlanProbingHashQuery parameter input context.state).candidate? = none then 0
      else otsHashInputCharge parameter input
  | _ => 0

noncomputable def nativeUnusedProbeOuterCharge (parameter : PublicParameter)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext)
    (_fuel : Nat) (_cache : SplitHashCache) : ENNReal :=
  match input with
  | .inl (.inr input) =>
      if (purePlanProbingHashQuery parameter input context.state).candidate? = none then otsHashInputCharge parameter input
      else 0
  | _ => 0

theorem nativePlanned_add_unusedProbeOuterCharge
    (parameter : PublicParameter) (input : (OracleWorld + SigningSpec).Domain)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    nativePlannedProbeOuterCharge parameter input context fuel cache +
      nativeUnusedProbeOuterCharge parameter input context fuel cache = otsOuterQueryCharge parameter input := by
  cases input with
  | inl input =>
      cases input with
      | inl n => simp [nativePlannedProbeOuterCharge, nativeUnusedProbeOuterCharge, otsOuterQueryCharge]
      | inr input =>
          simp only [nativePlannedProbeOuterCharge, nativeUnusedProbeOuterCharge, otsOuterQueryCharge]
          split_ifs <;> simp
  | inr message => simp [nativePlannedProbeOuterCharge, nativeUnusedProbeOuterCharge, otsOuterQueryCharge]

theorem chronologicalAdversaryImpl_expectedResolvedProbeCharge_le_planned
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (cache : SplitHashCache)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    expectedResolvedQueryCharge nativeProbeQueryCharge
      ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache) context fuel table ≤
      nativePlannedProbeOuterCharge parameter input context fuel cache := by
  have hbase := chronologicalAdversaryImpl_expectedResolvedProbeCharge_le parameter root ftsSecret input cache context fuel table
  cases input with
  | inl query =>
      cases query with
      | inl n => exact hbase
      | inr input =>
          change expectedResolvedQueryCharge nativeProbeQueryCharge ((probingHashQuery parameter input).run cache)
            context fuel table ≤ _
          simp only [nativePlannedProbeOuterCharge]
          split_ifs with hnone
          · rw [probingHashQuery_expectedResolvedProbeCharge_eq_zero_of_no_candidate parameter input context fuel table cache hnone]
          · exact hbase
  | inr message => exact hbase

theorem chronologicalAdversaryImpl_probeCharge_add_unused_le_ots
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (cache : SplitHashCache)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    expectedLiveResolvedQueryCharge nativeProbeQueryCharge
        ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache) context fuel table +
      nativeUnusedProbeOuterCharge parameter input context fuel cache ≤ otsOuterQueryCharge parameter input := by
  apply (add_le_add ((expectedLiveResolvedQueryCharge_le_raw nativeProbeQueryCharge _ context fuel table).trans
    (chronologicalAdversaryImpl_expectedResolvedProbeCharge_le_planned parameter root ftsSecret input cache context fuel table)) le_rfl).trans_eq
  exact nativePlanned_add_unusedProbeOuterCharge parameter input context fuel cache

end SphincsSecurity.Concrete.OtsProbeSimulation
