import SphincsSecurity.Proof.OtsProbeCappedCost
import SphincsSecurity.Proof.OtsProbeSharedHistoryGame

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def initializedSourceDirectRisk
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (fuel q : Nat) : ENNReal :=
  (∑ ordinal ∈ Finset.range q, Pr[LiveUnresolvedStartHit nativeCutCandidate |
    sampledEnsuredNativeProbeCut targets computation fuel ordinal]) +
  ∑' table, Pr[= table | sampleOtsHashTable] *
    ∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
      Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
        runPrivateResolvedView target table (ensuredInitialContext targets) fuel
          (privatePositionProbeCutAt target computation ordinal)]

theorem initializedSourceDirectRisk_le_sharedHistory
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (fuel q : Nat)
    (hq : q ≤ Fintype.card Digest) (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe q) :
    initializedSourceDirectRisk targets computation fuel q ≤
      sharedHistoryCutCharge targets (capProbeQueries computation q) (ensuredInitialContext targets) q *
        (Fintype.card Digest : ENNReal)⁻¹ := by
  have hstart : (∑ ordinal ∈ Finset.range q, Pr[LiveUnresolvedStartHit nativeCutCandidate |
      sampledEnsuredNativeProbeCut targets computation fuel ordinal]) ≤
      (∑ ordinal ∈ Finset.range q,
        erasedHistoryStartCutCharge (capProbeQueries computation q) (ensuredInitialContext targets) ordinal) *
        (Fintype.card Digest : ENNReal)⁻¹ := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro ordinal hordinal
    have hord : ordinal < q := Finset.mem_range.mp hordinal
    apply (probEvent_sampledEnsuredNativeProbeCut_unresolvedStart_le_prefixCharge targets computation fuel ordinal (hord.trans_le hq)).trans
    apply mul_le_mul' _ le_rfl
    exact (nativeStartPrefixCharge_le_erasedHistoryStartCutCharge targets computation fuel ordinal (hord.trans_le hq)).trans_eq
      (erasedHistoryStartCutCharge_cap computation (ensuredInitialContext targets) q ordinal hord)
  have hprivate := sampled_privateResolvedRawCandidate_le_history_charge targets computation fuel q
    (fun table => liveResolvedQueryBound_of_syntactic LazyRevealProbe.IsProbe computation q hbound (ensuredInitialContext targets) fuel table)
  unfold initializedSourceDirectRisk sharedHistoryCutCharge
  rw [add_mul]
  exact add_le_add hstart hprivate

theorem initializedSourceDirectRisk_le_cost
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (fuel q : Nat)
    (hq : q ≤ Fintype.card Digest) (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe q) :
    initializedSourceDirectRisk targets computation fuel q ≤
      expectedErasedHistoryProbeCost computation (ensuredInitialContext ∅) * (Fintype.card Digest : ENNReal)⁻¹ :=
  (initializedSourceDirectRisk_le_sharedHistory targets computation fuel q hq hbound).trans
    (mul_le_mul' (sharedHistoryCutCharge_cap_ensuredInitial_le_cost computation targets q hbound) le_rfl)

end SphincsSecurity.Concrete.OtsProbeSimulation
