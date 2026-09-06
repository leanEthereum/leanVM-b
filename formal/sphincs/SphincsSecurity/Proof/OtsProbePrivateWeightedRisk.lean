import SphincsSecurity.Proof.OtsProbePrivateHistoryRate
import SphincsSecurity.Proof.OtsProbePrivateValueLiveProbeCounting

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def privateProbeHistoryWeightedCharge
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat) : ENNReal :=
  privateHistoryWeightedOccurrence (runPrivateProbeRecords target computation context fuel table ordinal)
    (privateProbeRecordCandidate target) (fun record => record.context.state.pendingAt (.position target))

theorem probEvent_samplePrivateProbeRecords_hit_le_historyWeightedCharge
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (hstate : context.state.values (.position target) = none) (hhidden : .position target ∉ context.state.revealed)
    (hcard : (context.state.pendingAt (.position target)).card + ordinal < Fintype.card Digest) :
    Pr[fun pair => pair.2 = some (truncateHash pair.1) | samplePrivateHistoryGuess
      (runPrivateProbeRecords target computation context fuel table ordinal) (privateProbeRecordCandidate target)] ≤
      privateProbeHistoryWeightedCharge target computation context fuel table ordinal := by
  apply probEvent_samplePrivateHistoryGuess_hit_le_weighted
  · exact probOutput_runPrivateProbeRecords_eq_of_compatible target computation context fuel table ordinal hstate hhidden
  · intro output record hhit
    exact probOutput_runPrivateProbeRecords_eq_zero_of_history_hit target computation context fuel table ordinal
      output hstate hhidden record hhit
  · intro output record hrecord
    exact (runPrivateProbeRecords_supported_history target computation context fuel table ordinal output
      hstate hhidden record hrecord).2.1.trans_lt hcard

theorem privateProbeHistoryWeightedCharge_le_rate_mul_charge
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal budget : Nat)
    (hstate : context.state.values (.position target) = none) (hhidden : .position target ∉ context.state.revealed)
    (hcard : (context.state.pendingAt (.position target)).card + ordinal ≤ budget) :
    privateProbeHistoryWeightedCharge target computation context fuel table ordinal ≤
      sampledPrivateProbeCharge target computation context fuel table ordinal * privateHistoryGuessRate budget := by
  rw [← probEvent_samplePrivateProbeRecords_occurrence_eq_charge target computation context fuel table ordinal hstate hhidden]
  apply privateHistoryWeightedOccurrence_le_budget
  intro output record hrecord
  exact (runPrivateProbeRecords_supported_history target computation context fuel table ordinal output
    hstate hhidden record hrecord).2.1.trans hcard

theorem probEvent_privateResolvedRawCandidate_hit_le_historyWeightedCharge
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : .position target ∈ context.state.ensured)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = none)
    (hhidden : .position target ∉ context.state.revealed)
    (hcard : (context.state.pendingAt (.position target)).card + ordinal < Fintype.card Digest) :
    Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
      runPrivateResolvedView target table context fuel (privatePositionProbeCutAt target computation ordinal)] ≤
      privateProbeHistoryWeightedCharge target computation context fuel table ordinal := by
  have hdist := evalDist_privateResolvedRawCandidate_eq_sampled target computation context fuel table ordinal
    hvalid hcomplete hensured hstate hvalue hhidden
  rw [probEvent_congr' (fun _ _ => Iff.rfl) hdist, probEvent_map]
  have hevent (pair : HashOutput × Option Digest) : PrivateCandidatePairHit (privateSampledCandidatePair pair) ↔
      pair.2 = some (truncateHash pair.1) := by
    rcases pair with ⟨output, candidate⟩
    cases candidate <;> simp [privateSampledCandidatePair, PrivateCandidatePairHit]
  have hprob := probEvent_congr' (fun pair _ => hevent pair)
    (rfl : evalDist (samplePrivateHistoryGuess (runPrivateProbeRecords target computation context fuel table ordinal)
      (privateRawRecordCandidate target)) = _)
  simp only [Function.comp_def]
  rw [hprob, probEvent_samplePrivateProbeRecords_raw_hit_eq_fresh_hit target computation context fuel table ordinal hstate hhidden]
  exact probEvent_samplePrivateProbeRecords_hit_le_historyWeightedCharge target computation context fuel table ordinal
    hstate hhidden hcard

theorem probEvent_privateResolvedRawCandidate_hit_le_live_cut_rate
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal budget : Nat)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : .position target ∈ context.state.ensured)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = none)
    (hhidden : .position target ∉ context.state.revealed)
    (hcard : (context.state.pendingAt (.position target)).card + ordinal ≤ budget)
    (hbudget : budget < Fintype.card Digest) :
    Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
      runPrivateResolvedView target table context fuel (privatePositionProbeCutAt target computation ordinal)] ≤
      Pr[LivePrivateProbeCutReached target | runResolvedFromTable context fuel table (privatePositionProbeCutAt target computation ordinal)] *
        privateHistoryGuessRate budget := by
  apply (probEvent_privateResolvedRawCandidate_hit_le_historyWeightedCharge target computation context fuel table ordinal
    hvalid hcomplete hensured hstate hvalue hhidden (hcard.trans_lt hbudget)).trans
  apply (privateProbeHistoryWeightedCharge_le_rate_mul_charge target computation context fuel table ordinal budget
    hstate hhidden hcard).trans
  exact mul_le_mul' (sampledPrivateProbeCharge_le_live_cut target computation context fuel table ordinal
    hvalid hcomplete hensured hstate hvalue hhidden) le_rfl

theorem sum_targets_privateHits_le_live_structural_rate
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (q : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (budget : Nat)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : ∀ target ∈ targets, .position target ∈ context.state.ensured)
    (hstate : ∀ target ∈ targets, context.state.values (.position target) = none)
    (hvalue : ∀ target ∈ targets, context.values target = none)
    (hhidden : ∀ target ∈ targets, .position target ∉ context.state.revealed)
    (hcard : ∀ target ∈ targets, (context.state.pendingAt (.position target)).card + q ≤ budget)
    (hbudget : budget < Fintype.card Digest) :
    (∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
      Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
        runPrivateResolvedView target table context fuel (privatePositionProbeCutAt target computation ordinal)]) ≤
      expectedLiveResolvedQueryCharge structuralProbeQueryCharge computation context fuel table *
        privateHistoryGuessRate budget := by
  calc
    _ ≤ ∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
        Pr[LivePrivateProbeCutReached target | runResolvedFromTable context fuel table (privatePositionProbeCutAt target computation ordinal)] *
          privateHistoryGuessRate budget := by
      apply Finset.sum_le_sum
      intro target htarget
      apply Finset.sum_le_sum
      intro ordinal hordinal
      apply probEvent_privateResolvedRawCandidate_hit_le_live_cut_rate target computation context fuel table ordinal budget
        hvalid hcomplete (hensured target htarget) (hstate target htarget) (hvalue target htarget) (hhidden target htarget) _ hbudget
      exact (Nat.add_le_add_left (Nat.le_of_lt (Finset.mem_range.mp hordinal)) _).trans (hcard target htarget)
    _ = (∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
        Pr[LivePrivateProbeCutReached target | runResolvedFromTable context fuel table (privatePositionProbeCutAt target computation ordinal)]) *
          privateHistoryGuessRate budget := by simp only [Finset.sum_mul]
    _ ≤ _ := mul_le_mul' (sum_targets_livePrivateProbeCutReached_le_expectedStructuralCharge targets computation q context fuel table
      hvalid.valuesConsistent (startTableAgrees_of_deferredCompletable hcomplete)) le_rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
