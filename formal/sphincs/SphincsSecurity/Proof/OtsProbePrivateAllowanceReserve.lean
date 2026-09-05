import SphincsSecurity.Proof.OtsProbePrivateAllowanceHit
import SphincsSecurity.Proof.OtsProbeInitializedJointRootRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem sum_targets_privateHits_eq_liveAllowance
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (q : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hhidden : ∀ target ∈ targets, .position target ∉ context.state.revealed)
    (hbound : ∀ target ∈ targets, computation.IsQueryBoundP (IsPrivatePositionProbe target) q) :
    (∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
      Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
        runPrivateResolvedView target table context fuel (privatePositionProbeCutAt target computation ordinal)]) =
      ∑ target ∈ targets, privateLiveProbeAllowance target computation context fuel table := by
  apply Finset.sum_congr rfl
  intro target htarget
  exact sum_privateProbeCut_hits_eq_liveAllowance target computation q context fuel table
    hconsistent hstarts (hhidden target htarget) (hbound target htarget)

theorem sum_targets_privateHits_ensuredInitial_eq_liveAllowance
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (q fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hbound : ∀ target ∈ targets, computation.IsQueryBoundP (IsPrivatePositionProbe target) q) :
    (∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
      Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
        runPrivateResolvedView target table (ensuredInitialContext targets) fuel (privatePositionProbeCutAt target computation ordinal)]) =
      ∑ target ∈ targets, privateLiveProbeAllowance target computation (ensuredInitialContext targets) fuel table := by
  apply sum_targets_privateHits_eq_liveAllowance targets computation q (ensuredInitialContext targets) fuel table
    (ensuredInitialContext_valid targets).valuesConsistent
    (startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable targets table)) _ hbound
  intro target _
  simp [ensuredInitialContext, LazyRevealProbe.State.empty]

theorem sum_privateLiveProbeAllowance_ensuredInitial_le_structuralCharge
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (q fuel : Nat) (table : OtsSecretIndex → HashOutput) (hq : q ≤ 2 ^ 126)
    (hbound : ∀ target ∈ targets, computation.IsQueryBoundP (IsPrivatePositionProbe target) q) :
    (∑ target ∈ targets, privateLiveProbeAllowance target computation (ensuredInitialContext targets) fuel table) ≤
      expectedLiveResolvedQueryCharge structuralProbeQueryCharge computation (ensuredInitialContext targets) fuel table *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  rw [← sum_targets_privateHits_ensuredInitial_eq_liveAllowance targets computation q fuel table hbound]
  exact sum_targets_privateHits_ensuredInitial_le_structuralCharge targets computation q fuel table hq

theorem initializedNativeDirectRisk_eq_startHits_add_privateAllowance
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel q : Nat)
    (hbound : ∀ target ∈ targets, (nativeChronologicalRetainedComputation adversary parameter ftsSecret).IsQueryBoundP
      (IsPrivatePositionProbe target) q) :
    initializedNativeDirectRisk targets adversary parameter ftsSecret fuel q =
      (∑ ordinal ∈ Finset.range q, Pr[LiveUnresolvedStartHit nativeCutCandidate |
        sampledEnsuredNativeProbeCut targets (nativeChronologicalRetainedComputation adversary parameter ftsSecret) fuel ordinal]) +
      ∑' table, Pr[= table | sampleOtsHashTable] *
        ∑ target ∈ targets, privateLiveProbeAllowance target
          (nativeChronologicalRetainedComputation adversary parameter ftsSecret) (ensuredInitialContext targets) fuel table := by
  unfold initializedNativeDirectRisk
  congr 1
  apply tsum_congr
  intro table
  rw [sum_targets_privateHits_ensuredInitial_eq_liveAllowance targets _ q fuel table hbound]

end SphincsSecurity.Concrete.OtsProbeSimulation
