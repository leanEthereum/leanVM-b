import SphincsSecurity.Proof.OtsProbeHistoryErasureBridge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
attribute [local irreducible] sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def sampledCanonicalHistoryTrace
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (cache : SplitHashCache) :
    ProbComp (Option (ResolvedRunResult (α × SplitHashCache)) × Bool) := do
  let base ← sampleOtsHashTable
  if ChainStartHistoryHit context history base then pure (none, false)
  else
    runCanonicalStartErasureTrace parameter root (completedStartTable context.state base) ftsSecret
      computation context fuel cache false

theorem evalDist_eraseFlagged_historyTrace_eq_guarded
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hpublished : PublishedValues context.state)
    (hcanonical : ∀ base, CanonicalMaterializedValues (completedStartTable context.state base) context) :
    evalDist (eraseFlaggedResult <$> sampledCanonicalHistoryTrace parameter root ftsSecret computation context fuel history cache) =
      evalDist (sampledGuardedCanonicalNative parameter root ftsSecret computation context fuel history cache) := by
  simp only [sampledCanonicalHistoryTrace, sampledGuardedCanonicalNative, map_bind]
  apply evalDist_bind_congr
  intro base _
  split_ifs
  · simp [eraseFlaggedResult]
  · exact evalDist_eraseFlagged_trace_eq_guardedCanonicalNative parameter root (completedStartTable context.state base)
      ftsSecret computation context fuel cache hconsistent (startTableAgrees_completedStartTable context.state base)
      hpublished (hcanonical base)

theorem expected_sampledGuardedCanonical_le_historyTrace
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (cache : SplitHashCache)
    (cost : Option (ResolvedRunResult (α × SplitHashCache)) → ENNReal) (hnone : cost none = 0)
    (hconsistent : context.ValuesConsistent) (hpublished : PublishedValues context.state)
    (hcanonical : ∀ base, CanonicalMaterializedValues (completedStartTable context.state base) context) :
    (∑' result, Pr[= result | sampledGuardedCanonicalNative parameter root ftsSecret computation context fuel history cache] * cost result) ≤
      ∑' result, Pr[= result | Prod.fst <$> sampledCanonicalHistoryTrace parameter root ftsSecret computation context fuel history cache] *
        cost result := by
  have hdist := evalDist_eraseFlagged_historyTrace_eq_guarded parameter root ftsSecret computation context fuel history cache
    hconsistent hpublished hcanonical
  have heq :
      (∑' result, Pr[= result | sampledGuardedCanonicalNative parameter root ftsSecret computation context fuel history cache] * cost result) =
      ∑' result, Pr[= result | eraseFlaggedResult <$> sampledCanonicalHistoryTrace parameter root ftsSecret computation context fuel history cache] *
        cost result := by
    apply tsum_congr
    intro result
    rw [_root_.OracleComp.probOutput_congr rfl hdist]
  rw [heq]
  exact expected_erased_le_fst _ cost hnone

theorem probEvent_historyCanonical_unresolvedStart_le_charge_add_erasure
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel bound : Nat) (history : List Probe) (cache : SplitHashCache)
    (candidate : DeferredContext → (α × SplitHashCache) → Option Probe)
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context)
    (hpublished : PublishedValues context.state)
    (hcanonical : ∀ base, CanonicalMaterializedValues (completedStartTable context.state base) context)
    (hbound : computation.IsQueryBoundP IsOuterHash bound) (hbudget : history.length + bound ≤ 2 ^ 126) :
    Pr[LiveUnresolvedStartHit candidate |
      Prod.fst <$> sampledCanonicalHistoryTrace parameter root ftsSecret computation context fuel history cache] ≤
      (∑' result, Pr[= result | Prod.fst <$>
        sampledCanonicalHistoryTrace parameter root ftsSecret computation context fuel history cache] *
        historyUnresolvedStartCharge candidate result) * ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) +
      Pr[fun result => result.2 = true |
        sampledCanonicalHistoryTrace parameter root ftsSecret computation context fuel history cache] := by
  have hcomparison := probEvent_fst_le_erased_add_flag
    (sampledCanonicalHistoryTrace parameter root ftsSecret computation context fuel history cache)
    (LiveUnresolvedStartHit candidate)
  have hdist := evalDist_eraseFlagged_historyTrace_eq_guarded parameter root ftsSecret computation context fuel history cache
    hconsistent hpublished hcanonical
  rw [OracleComp.probEvent_congr' (fun _ _ => Iff.rfl) hdist] at hcomparison
  apply hcomparison.trans
  apply add_le_add _ le_rfl
  exact (probEvent_guardedCanonical_unresolvedStart_le parameter root ftsSecret computation context fuel bound history cache candidate
    hconsistent hcovered hpublished hbound hbudget).trans
      (mul_le_mul' (expected_sampledGuardedCanonical_le_historyTrace parameter root ftsSecret computation context fuel history cache
        (historyUnresolvedStartCharge candidate) rfl hconsistent hpublished hcanonical) le_rfl)

theorem evalDist_historyTrace_projection
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) :
    evalDist (Prod.fst <$> sampledCanonicalHistoryTrace parameter root ftsSecret computation context fuel history cache) =
      evalDist (do
        let base ← sampleOtsHashTable
        if ChainStartHistoryHit context history base then pure none
        else
          runSynchronizedResolved (canonicalChronologicalAdversaryImpl parameter root
            (completedStartTable context.state base) ftsSecret) computation context fuel
            (completedStartTable context.state base) cache) := by
  simp only [sampledCanonicalHistoryTrace, map_bind]
  apply evalDist_bind_congr
  intro base _
  split_ifs
  · simp
  · exact runCanonicalStartErasureTrace_projection parameter root (completedStartTable context.state base) ftsSecret computation
      context fuel cache false hconsistent (startTableAgrees_completedStartTable context.state base)

end SphincsSecurity.Concrete.OtsProbeSimulation
